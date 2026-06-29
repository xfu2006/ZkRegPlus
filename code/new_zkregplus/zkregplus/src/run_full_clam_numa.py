#!/usr/bin/env python3
"""Two-half NUMA driver for full_clam.

The 1TB box has 8 NUMA nodes; pinning a run to 4 nodes (cpu+mem) is as fast
as the 512GB box. So we run TWO independent halves in parallel (~2x):
  - proc1 = FOLD ONLY  over the SECOND manifest-half, pinned to nodes 0..n/2-1
  - proc2 = ONE SNARK  over the FIRST  manifest-half, pinned to nodes n/2..n-1
CPU is hard-pinned (--cpunodebind); memory is soft (--preferred-many) so a
half spills instead of OOMing. The SNARK (decider) is memory-heavy, so proc2
folds its half then BLOCKS in foldpot_main (10s poll on /tmp/snark_start/flag)
until this driver sees proc1 finish (freeing its RAM) and creates the flag.

full_clam itself is unchanged for a bare `cargo test`; this driver only sets
env knobs read by full_clam()/full_clamav():
  ZKR_CLAM_READ_MODE = full|first|second   manifest slice this job reads
  ZKR_CLAM_PCT       = percent of each manifest used (debug/numa speed mode)
  ZKR_CLAM_FOLD_ONLY = 1 -> b_folding_only (no snark)
  ZKR_CLAM_ONE_PROOF = 1 -> only one job proves (one snark proof)
  ZKR_SNARK_JOB_ID   = which (local) job emits the proof under ONE_PROOF
  ZKR_SNARK_WAIT_FLAG= flag path proc2's proving job waits on before decider
  ZKR_LOG_TAG        = per-process tag so log_job_<tag><id>.txt do not collide

Modes (--fold-only default: 1 for debug/numa, 0 for prod):
  --mode=debug : 10%, 8 jobs, ONE process, NO numactl, fold-only
                 -> /tmp/full_clam_run/full_clam.log.baseline.tgz
  --mode=numa  : 10%, two-process NUMA scheme, fold-only (NUMA shakeout)
  --mode=prod  : 100%, two-process NUMA scheme (DEFAULT); proc2 emits ONE
                 full snark proof from --id-snark-job (default job 3)
                 -> full_clam.log.part1.tgz (fold) + full_clam.log.part2.tgz
--fold-only=1 suppresses the proof; --fold-only=0 forces it (e.g. on numa).

After each run a PROBE verifier reads the per-job "PROBE CLAM ..." lines and
checks them against the real binexec_p<j>.dat manifests for the given pct.
PROD additionally checks the union of emitted files == the full 8-manifest
list, and that the batch proof verifies.

Usage:
  python3 run_full_clam_numa.py [--mode=prod|numa|debug] [--pct=N]
                                [--fold-only=0|1] [--id-snark-job=N]
                                [--dry-run]
"""
import os, sys, subprocess, time, datetime, tarfile, platform, re, glob, \
    shutil, threading


def getarg(name, default=None):
    pref = "--%s=" % name
    for a in sys.argv[1:]:
        if a.startswith(pref):
            return a.split("=", 1)[1]
    return default


MODE = getarg("mode", "prod")
if MODE not in ("prod", "numa", "debug"):
    raise SystemExit("--mode must be prod|numa|debug (got %r)" % MODE)
PCT = int(getarg("pct", "100" if MODE == "prod" else "10"))
PART2_DELAY = int(getarg("part2-delay", "900"))   # min stagger before part2 (s)
PART2_RAM_GB = float(getarg("part2-ram-gb", "500"))  # part2 waits until
                                                  # part1 tree RSS < this (GB)
ID_SNARK_JOB = int(getarg("id-snark-job", "3"))   # which job emits the proof
                                                  # (local==global for 1st half)
FOLD_ONLY = getarg("fold-only", "0" if MODE == "prod" else "1") \
    not in ("0", "false", "False", "no")          # default: prod proves,
                                                  # debug/numa fold-only
DRY = "--dry-run" in sys.argv
VMA_TARGET = int(os.environ.get("ZKR_VM_MAX_MAP_COUNT", "1073741824"))  # 0=skip

HERE = os.path.dirname(os.path.abspath(__file__))          # zkregplus/src
REPO = os.path.abspath(os.path.join(HERE, "..", ".."))     # new_zkregplus
LOGS_DIR = os.path.join(REPO, "data/cache/logs")           # log_job_*.txt
REPORT = os.path.join(REPO, "data/debug/full_clamav/reports/report2.dat")
CFG_DIR = os.path.join(REPO, "data/debug/full_clamav/config")  # binexec_p*.dat
FLAG_DIR = "/tmp/snark_start"
FLAG = os.path.join(FLAG_DIR, "flag")

OUT = "/tmp/full_clam_run"
os.makedirs(OUT, exist_ok=True)
TS = datetime.datetime.now().strftime("%Y%m%d_%H%M%S")

CARGO = ["cargo", "test", "-p", "zkregplus", "--release", "--",
         "zkp_driver::tests_zkp_driver::full_clam", "--exact", "--nocapture"]


def ensure_vma(target):
    """Best-effort raise vm.max_map_count so the fold's many small mimalloc
    mappings don't hit the VMA ceiling (SIGABRT with free RAM)."""
    if target <= 0:
        return
    path = "/proc/sys/vm/max_map_count"
    try:
        cur = int(open(path).read().strip())
    except Exception as e:
        print("[numa] vm.max_map_count: cannot read (%s); skip" % e)
        return
    if cur >= target:
        print("[numa] vm.max_map_count=%d already >= %d" % (cur, target))
        return
    print("[numa] raising vm.max_map_count %d -> %d via sudo sysctl"
          % (cur, target))
    rc = subprocess.run(["sudo", "sysctl", "-w",
                         "vm.max_map_count=%d" % target]).returncode
    if rc != 0:
        print("[numa] WARN: could not raise vm.max_map_count; run manually: "
              "sudo sysctl -w vm.max_map_count=%d" % target)


def nnodes():
    try:
        h = subprocess.run(["numactl", "-H"], capture_output=True,
                           text=True).stdout
        return max((int(x) for x in re.findall(r"node (\d+) cpus:", h)),
                   default=-1) + 1
    except Exception:
        return 0


def half_ranges():
    """(first_half, second_half) node ranges as numactl strings, or
    (None, None) on a single-node box (then numactl is skipped)."""
    n = nnodes()
    if n < 2:
        return None, None
    h = n // 2
    return "0-%d" % (h - 1), "%d-%d" % (h, n - 1)


def numa_prefix(nodes):
    """CPU hard-pin to `nodes` + memory soft-prefer the same nodes (spills,
    won't OOM). Empty when numactl is absent or nodes is None."""
    if not nodes or not shutil.which("numactl"):
        return []
    return ["numactl", "--cpunodebind=%s" % nodes,
            "--preferred-many=%s" % nodes]


def _ppid(pid):
    """Parent pid from /proc/<pid>/stat (ppid is the field after the last
    ')', robust to spaces/parens in comm)."""
    try:
        data = open("/proc/%d/stat" % pid).read()
        return int(data[data.rfind(")") + 2:].split()[1])
    except Exception:
        return None


def _vmrss_kb(pid):
    try:
        for ln in open("/proc/%d/status" % pid):
            if ln.startswith("VmRSS:"):
                return int(ln.split()[1])
    except Exception:
        pass
    return 0


def tree_rss_gb(root_pid):
    """Sum VmRSS (GB) over root_pid and all its descendants -- the whole
    cargo + test-binary + job-thread tree. Threads share one VmRSS, so no
    double counting. 0.0 if the tree is gone."""
    pids = [int(d) for d in os.listdir("/proc") if d.isdigit()]
    parent = {p: _ppid(p) for p in pids}
    total = 0
    for p in pids:
        cur, hops = p, 0
        while cur and hops < 64:
            if cur == root_pid:
                total += _vmrss_kb(p)
                break
            cur = parent.get(cur)
            hops += 1
    return total / (1024.0 * 1024.0)


def base_env(read_mode, fold_only, one_proof, wait_flag, log_tag):
    e = dict(os.environ)
    e.setdefault("RUSTFLAGS", "-C link-args=-fuse-ld=lld -Awarnings")
    e["ZKR_NUMA"] = "off"                       # Rust per-job pinning off
    e["ZKR_CLAM_READ_MODE"] = read_mode         # full|first|second
    e["ZKR_CLAM_PCT"] = str(PCT)
    e["ZKR_CLAM_FOLD_ONLY"] = "1" if fold_only else "0"
    e["ZKR_CLAM_ONE_PROOF"] = "1" if one_proof else "0"
    e["ZKR_SNARK_JOB_ID"] = str(ID_SNARK_JOB)   # which job emits the proof
    # The split is by whole manifest, so each job reads full per-job data;
    # the lkup-share invariant holds at pct=100 -> enforce only in prod.
    e["ZKR_CLAM_CHECK_LKUP"] = "1" if MODE == "prod" else "0"
    if wait_flag:
        e["ZKR_SNARK_WAIT_FLAG"] = wait_flag
    else:
        e.pop("ZKR_SNARK_WAIT_FLAG", None)
    e["ZKR_LOG_TAG"] = log_tag                  # "" | "p1_" | "p2_"
    return e


def spawn(nodes, env, log_path, label):
    """Launch one full_clam process; pump its stdout to log_path live."""
    cmd = numa_prefix(nodes) + CARGO
    print("[numa] %s: %s" % (label, " ".join(cmd)))
    lf = open(log_path, "w")
    lf.write("# %s host=%s label=%s\n# cmd=%s\n\n" % (
        datetime.datetime.now(), platform.node(), label, " ".join(cmd)))
    lf.flush()
    p = subprocess.Popen(cmd, cwd=REPO, env=env, stdout=subprocess.PIPE,
                         stderr=subprocess.STDOUT, text=True)

    def pump():
        for line in p.stdout:
            sys.stdout.write("[%s] %s" % (label, line))
            lf.write(line)
            lf.flush()
        lf.close()

    t = threading.Thread(target=pump, daemon=True)
    t.start()
    return p, t


# ---------------- PROBE verification ----------------
_FILE = re.compile(r"^PROBE FILE job (\d+) (.+)$")


def parse_loaded(log_path):
    """job_id -> set of file paths this process loaded, from the per-file
    'PROBE FILE job J <path>' lines. load_files runs twice per job (two
    passes) so each file is printed twice; the set dedups."""
    res = {}
    if not os.path.isfile(log_path):
        return res
    for ln in open(log_path, errors="replace"):
        m = _FILE.match(ln.rstrip("\n"))
        if m:
            res.setdefault(int(m.group(1)), set()).add(m.group(2))
    return res


def manifest(job):
    p = os.path.join(CFG_DIR, "binexec_p%d.dat" % job)
    return [x.strip() for x in open(p) if x.strip()]


def verify_split(part_logs):
    """Check the two parts together emit all 8 manifests' files. The split
    is by whole manifest (part1 = jobs 4-7, part2 = jobs 0-3), so each job
    lands in exactly one part. Per job, compare its dumped file set to the
    ORIGINAL manifest (binexec_p<j>.dat) -- pure set ops, any gap is named.

    prod (pct=100): each job's set must EQUAL its manifest. pct<100: the set
    is the first pct% sample, so only subset (no EXTRA) is checked. Either
    way, all 8 jobs must be covered across the parts."""
    per_part = [parse_loaded(p) for p in part_logs]
    jobs = sorted(set().union(*[set(d) for d in per_part])) if per_part else []
    ok = True
    print("\n[verify] split check (pct=%d, %d part-log(s))"
          % (PCT, len(part_logs)))
    want = set(range(8))
    if set(jobs) != want:
        print("[verify] COVERAGE FAIL: emitted jobs %s != expected %s"
              % (sorted(jobs), sorted(want)))
        ok = False
    for j in jobs:
        L = set(manifest(j))
        sets = [d.get(j, set()) for d in per_part]
        merged = set().union(*sets) if sets else set()
        overlap = set()
        for i in range(len(sets)):
            for k in range(i + 1, len(sets)):
                overlap |= sets[i] & sets[k]
        extra = merged - L
        sizes = "/".join(str(len(s)) for s in sets)
        if PCT >= 100:
            missing = L - merged
            good = not missing and not extra and not overlap
            print("[verify] job %d |manifest|=%d merged=%d parts=%s  %s"
                  % (j, len(L), len(merged), sizes,
                     "PASS" if good else "FAIL"))
            if missing:
                print("         MISSING %d e.g. %s"
                      % (len(missing), sorted(missing)[:3]))
        else:
            good = not extra and not overlap
            print("[verify] job %d merged=%d (~%d%% of %d) parts=%s  %s"
                  % (j, len(merged), PCT, len(L), sizes,
                     "PASS" if good else "FAIL"))
        if extra:
            print("         EXTRA(not in manifest) %d e.g. %s"
                  % (len(extra), sorted(extra)[:3]))
        if overlap:
            print("         OVERLAP between parts %d e.g. %s"
                  % (len(overlap), sorted(overlap)[:3]))
        ok = ok and good
    print("[verify] OVERALL: %s" % ("PASS" if ok else "FAIL"))
    return ok


_FAIL_BATCH = re.compile(r"BATCH PROOF VERIFICATION FAILED")
_VERIFY_STEP = re.compile(r"FoldPot Step 12: Verify Batch Proof")


def full_file_list():
    """Union of all 8 binexec_p<j>.dat manifests = the complete clam
    file set (prod, pct=100)."""
    s = set()
    for j in range(8):
        s |= set(manifest(j))
    return s


def prod_final_checks(part_logs):
    """PROD-only explicit checks. (1) the union of files emitted by all
    jobs at runtime must EQUAL the full 8-manifest file list; (2) the
    batch proof must verify (the verify step ran and no FAILED line).
    Prints a pass/fail banner. CHECK 2 is SKIPPED under --fold-only."""
    per = [parse_loaded(p) for p in part_logs]
    emitted = set()
    for d in per:
        for s in d.values():
            emitted |= s
    full = full_file_list()
    missing, extra = full - emitted, emitted - full
    ok1 = not missing and not extra
    failed = ran = False
    for p in part_logs:
        if not os.path.isfile(p):
            continue
        for ln in open(p, errors="replace"):
            if _FAIL_BATCH.search(ln):
                failed = True
            if _VERIFY_STEP.search(ln):
                ran = True
    print("\n============ FULL_CLAM PROD FINAL CHECKS ============")
    print("[CHECK 1] file-list match (union==full 8-manifest): %s"
          % ("PASS" if ok1 else "FAIL"))
    if missing:
        print("   MISSING %d e.g. %s" % (len(missing), sorted(missing)[:3]))
    if extra:
        print("   EXTRA   %d e.g. %s" % (len(extra), sorted(extra)[:3]))
    if FOLD_ONLY:
        ok2 = None
        print("[CHECK 2] batch proof verification: SKIPPED (fold-only)")
    else:
        ok2 = ran and not failed
        print("[CHECK 2] batch proof verification: %s"
              % ("PASS" if ok2 else "FAIL"))
        if not ran:
            print("   no 'Verify Batch Proof' step seen (decider not run)")
        if failed:
            print("   saw BATCH PROOF VERIFICATION FAILED")
    print("====================================================")
    if not ok1 or ok2 is False:
        print("FAIL: prod final checks did not all pass (see above).")
    return ok1, ok2


# ---------------- packing ----------------
def gz_one(path):
    """Wrap a single file into its own .tgz; return the .tgz path
    (sibling of the source), or None if the source is missing."""
    if not os.path.isfile(path):
        return None
    out = path + ".tgz"
    with tarfile.open(out, "w:gz", compresslevel=9) as t:
        t.add(path, arcname=os.path.basename(path))
    return out


def pack_part(part, log_path, with_report):
    """full_clam.log.<part>.tgz = the run log + this part's tagged per-job
    logs (+ report for part2). ALWAYS runs, even after a panic."""
    tag = {"part1": "p1_", "part2": "p2_", "baseline": ""}[part]
    tgz = os.path.join(OUT, "full_clam.log.%s.tgz" % part)
    try:
        with tarfile.open(tgz, "w:gz", compresslevel=9) as t:
            log_tgz = gz_one(log_path)
            if log_tgz:
                t.add(log_tgz, arcname=os.path.basename(log_tgz))
            patt = "log_job_%s*.txt" % tag if tag else "log_job_[0-9]*.txt"
            for jf in sorted(glob.glob(os.path.join(LOGS_DIR, patt))):
                t.add(jf, arcname="logs/" + os.path.basename(jf))
            if with_report and os.path.isfile(REPORT):
                t.add(REPORT, arcname=os.path.basename(REPORT))
        print("[numa] packed -> %s" % tgz)
    except Exception as e:
        print("[numa] WARN: pack %s failed: %s" % (part, e))


# ---------------- flows ----------------
def run_debug():
    log = os.path.join(OUT, "baseline_%s.log" % TS)
    env = base_env("full", fold_only=FOLD_ONLY, one_proof=True,
                   wait_flag=None, log_tag="")
    p, t = spawn(None, env, log, "debug")
    try:
        p.wait()
        t.join()
    finally:
        try:
            verify_split([log])
        except Exception as e:
            print("[numa] WARN: verify failed: %s" % e)
        pack_part("baseline", log, with_report=True)
    return p.returncode


def run_two():
    a, b = half_ranges()
    print("[numa] proc1 fold-only(2nd half) nodes=%s ; "
          "proc2 snark(1st half) nodes=%s ; flag=%s" % (a, b, FLAG))
    shutil.rmtree(FLAG_DIR, ignore_errors=True)     # clean stale flag
    log1 = os.path.join(OUT, "part1_%s.log" % TS)
    log2 = os.path.join(OUT, "part2_%s.log" % TS)
    # Halves switched: proc1 (fold-only) folds the SECOND half; proc2 folds
    # the FIRST half. With --fold-only=0, proc2's --id-snark-job job
    # (local==global for jobs 0-3) emits the single proof; else no proof.
    env1 = base_env("second", fold_only=True, one_proof=False,
                    wait_flag=None, log_tag="p1_")
    env2 = base_env("first", fold_only=FOLD_ONLY, one_proof=True,
                    wait_flag=None if FOLD_ONLY else FLAG, log_tag="p2_")
    p1 = p2 = None
    t1 = t2 = None
    try:
        p1, t1 = spawn(a, env1, log1, "part1")
        # Stagger part2 so the two halves don't fold (peak RAM) at once.
        # Gate: start part2 once BOTH >=PART2_DELAY s elapsed AND part1's
        # tree RSS < PART2_RAM_GB -- or immediately when part1 exits (its
        # RAM is freed then).
        print("[numa] part2 gate: t>=%ds AND part1 RSS<%.0fGB (or part1 exit)"
              % (PART2_DELAY, PART2_RAM_GB))
        waited = 0
        while p1.poll() is None:
            rss = tree_rss_gb(p1.pid)
            if waited >= PART2_DELAY and rss < PART2_RAM_GB:
                break
            if waited % 60 == 0:
                print("[numa] waiting part2: t=%ds rss=%.0fGB "
                      "(need t>=%d AND rss<%.0f)"
                      % (waited, rss, PART2_DELAY, PART2_RAM_GB))
            time.sleep(10)
            waited += 10
        p2, t2 = spawn(b, env2, log2, "part2")
        p1.wait()                                   # fold-only half done
        t1.join()
        if not FOLD_ONLY:
            print("[numa] proc1 rc=%s; releasing snark gate"
                  % p1.returncode)
            os.makedirs(FLAG_DIR, exist_ok=True)
            open(FLAG, "w").close()                 # -> proc2 runs decider
        else:
            print("[numa] proc1 rc=%s; fold-only, no snark gate"
                  % p1.returncode)
        p2.wait()
        t2.join()
        print("[numa] proc2 rc=%s" % p2.returncode)
    finally:
        # if we bailed before releasing, free proc2 so it can pack/exit.
        if p2 is not None and p2.poll() is None and not os.path.exists(FLAG):
            os.makedirs(FLAG_DIR, exist_ok=True)
            open(FLAG, "w").close()
        if p2 is not None:
            p2.wait()
        if t2 is not None:
            t2.join()
        try:
            verify_split([log1, log2])
        except Exception as e:
            print("[numa] WARN: verify failed: %s" % e)
        if MODE == "prod":
            try:
                prod_final_checks([log1, log2])
            except Exception as e:
                print("[numa] WARN: prod final checks failed: %s" % e)
        pack_part("part1", log1, with_report=False)
        pack_part("part2", log2, with_report=True)
    rc1 = p1.returncode if p1 else 1
    rc2 = p2.returncode if p2 else 1
    return rc1 or rc2


print("[numa] MODE=%s PCT=%d nodes=%d" % (MODE, PCT, nnodes()))
print("[numa] REPO=%s  OUT=%s" % (REPO, OUT))
if DRY:
    a, b = half_ranges()
    print("[numa] --dry-run: half ranges = %s / %s; flag=%s" % (a, b, FLAG))
    print("[numa] proc1 numactl:", numa_prefix(a) or "(none)")
    print("[numa] proc2 numactl:", numa_prefix(b) or "(none)")
    sys.exit(0)

ensure_vma(VMA_TARGET)
code = run_debug() if MODE == "debug" else run_two()
sys.exit(0 if code == 0 else (code or 1))
