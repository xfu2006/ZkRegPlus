#!/usr/bin/env python3
"""Two-half NUMA driver for full_clam.

The 1TB box has 8 NUMA nodes; pinning a run to 4 nodes (cpu+mem) is as fast
as the 512GB box. So we run TWO independent halves in parallel (~2x):
  - proc1 = FOLD ONLY  over the FIRST  manifest-half, pinned to nodes 0..n/2-1
  - proc2 = ONE SNARK  over the SECOND manifest-half, pinned to nodes n/2..n-1
CPU is hard-pinned (--cpunodebind); memory is soft (--preferred-many) so a
half spills instead of OOMing. The SNARK (decider) is memory-heavy, so proc2
folds its half then BLOCKS in foldpot_main (10s poll on /tmp/snark_start/flag)
until this driver sees proc1 finish (freeing its RAM) and creates the flag.

full_clam itself is unchanged for a bare `cargo test`; this driver only sets
env knobs read by full_clam()/full_clamav():
  ZKR_CLAM_READ_MODE = full|first|second   manifest slice this job reads
  ZKR_CLAM_PCT       = percent of each manifest used (split into two halves)
  ZKR_CLAM_NJOBS     = jobs per process (default 8)
  ZKR_CLAM_FOLD_ONLY = 1 -> b_folding_only (no snark)
  ZKR_CLAM_ONE_PROOF = 1 -> only Job 0 proves (one snark proof)
  ZKR_SNARK_WAIT_FLAG= flag path proc2's Job 0 waits on before the decider
  ZKR_LOG_TAG        = per-process tag so log_job_<tag><id>.txt do not collide

Modes:
  --mode=debug : 10%, 8 jobs, ONE process, NO numactl, full snark+1 proof
                 -> /tmp/full_clam_run/full_clam.log.baseline.tgz
  --mode=numa  : 10%, two-process NUMA scheme (fast NUMA shakeout)
  --mode=prod  : 100%, two-process NUMA scheme (DEFAULT)
                 -> full_clam.log.part1.tgz (fold) + full_clam.log.part2.tgz

After each run a PROBE verifier reads the per-job "PROBE CLAM ..." lines and
checks them against the real binexec_p<j>.dat manifests for the given pct.

Usage:
  python3 run_full_clam_numa.py [--mode=prod|numa|debug] [--pct=N]
                                [--jobs=N] [--dry-run]
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
NJOBS = int(getarg("jobs", "8"))
PART2_DELAY = int(getarg("part2-delay", "900"))   # min stagger before part2 (s)
PART2_RAM_GB = float(getarg("part2-ram-gb", "500"))  # part2 waits until
                                                  # part1 tree RSS < this (GB)
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
    e["ZKR_CLAM_NJOBS"] = str(NJOBS)
    e["ZKR_CLAM_FOLD_ONLY"] = "1" if fold_only else "0"
    e["ZKR_CLAM_ONE_PROOF"] = "1" if one_proof else "0"
    # lkup-share invariant holds only at full data -> enforce only in prod.
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
_PROBE = re.compile(
    r"PROBE CLAM job (\d+) mode (\w+) pct (\d+) n (\d+) "
    r"slice \[(\d+),(\d+)\) first (\S+) last (\S+)")


def parse_probe(log_path):
    res = {}
    if not os.path.isfile(log_path):
        return res
    for ln in open(log_path, errors="replace"):
        m = _PROBE.search(ln)
        if m:
            j = int(m.group(1))
            res[j] = dict(mode=m.group(2), pct=int(m.group(3)),
                          n=int(m.group(4)), lo=int(m.group(5)),
                          hi=int(m.group(6)), first=m.group(7),
                          last=m.group(8))
    return res


def manifest(job):
    p = os.path.join(CFG_DIR, "binexec_p%d.dat" % job)
    return [x.strip() for x in open(p) if x.strip()]


def _at(L, i):
    return L[i] if 0 <= i < len(L) else None


def verify_two(log1, log2):
    """Full coverage = proc1 first-half + proc2 second-half. Per job, the 4
    boundary names must match the manifest at [0], [mid-1], [mid], [hi-1]."""
    p1, p2 = parse_probe(log1), parse_probe(log2)
    ok = True
    print("\n[verify] two-half PROBE check (pct=%d)" % PCT)
    for j in sorted(set(p1) | set(p2)):
        L = manifest(j)
        n = len(L)
        hi = n * PCT // 100
        mid = n * PCT // 200
        e1f, e1l = _at(L, 0), _at(L, mid - 1)
        e2f, e2l = _at(L, mid), _at(L, hi - 1)
        g1, g2 = p1.get(j), p2.get(j)
        c1 = g1 and g1["first"] == e1f and g1["last"] == e1l
        c2 = g2 and g2["first"] == e2f and g2["last"] == e2l
        good = bool(c1 and c2)
        ok = ok and good
        print("[verify] job %d N=%d mid=%d hi=%d  %s"
              % (j, n, mid, hi, "PASS" if good else "FAIL"))
        print("         p1 got %s / %s  exp %s / %s"
              % (g1 and g1["first"], g1 and g1["last"], e1f, e1l))
        print("         p2 got %s / %s  exp %s / %s"
              % (g2 and g2["first"], g2 and g2["last"], e2f, e2l))
    print("[verify] OVERALL: %s" % ("PASS" if ok else "FAIL"))
    return ok


def verify_one(log):
    """Debug single-proc Full check: first=L[0], last=L[hi-1]."""
    p = parse_probe(log)
    ok = True
    print("\n[verify] debug PROBE check (full, pct=%d)" % PCT)
    for j in sorted(p):
        L = manifest(j)
        n = len(L)
        hi = n * PCT // 100
        ef, el = _at(L, 0), _at(L, hi - 1)
        g = p[j]
        good = g["first"] == ef and g["last"] == el
        ok = ok and good
        print("[verify] job %d N=%d hi=%d %s  got %s / %s  exp %s / %s"
              % (j, n, hi, "PASS" if good else "FAIL",
                 g["first"], g["last"], ef, el))
    print("[verify] OVERALL: %s" % ("PASS" if ok else "FAIL"))
    return ok


# ---------------- packing ----------------
def pack_part(part, log_path, with_report):
    """full_clam.log.<part>.tgz = the run log + this part's tagged per-job
    logs (+ report for part2). ALWAYS runs, even after a panic."""
    tag = {"part1": "p1_", "part2": "p2_", "baseline": ""}[part]
    tgz = os.path.join(OUT, "full_clam.log.%s.tgz" % part)
    try:
        with tarfile.open(tgz, "w:gz", compresslevel=9) as t:
            if os.path.isfile(log_path):
                t.add(log_path, arcname=os.path.basename(log_path))
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
    env = base_env("full", fold_only=False, one_proof=True,
                   wait_flag=None, log_tag="")
    p, t = spawn(None, env, log, "debug")
    try:
        p.wait()
        t.join()
    finally:
        try:
            verify_one(log)
        except Exception as e:
            print("[numa] WARN: verify failed: %s" % e)
        pack_part("baseline", log, with_report=True)
    return p.returncode


def run_two():
    a, b = half_ranges()
    print("[numa] proc1 fold-only nodes=%s ; proc2 snark nodes=%s ; flag=%s"
          % (a, b, FLAG))
    shutil.rmtree(FLAG_DIR, ignore_errors=True)     # clean stale flag
    log1 = os.path.join(OUT, "part1_%s.log" % TS)
    log2 = os.path.join(OUT, "part2_%s.log" % TS)
    env1 = base_env("first", fold_only=True, one_proof=False,
                    wait_flag=None, log_tag="p1_")
    env2 = base_env("second", fold_only=False, one_proof=True,
                    wait_flag=FLAG, log_tag="p2_")
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
        print("[numa] proc1 (fold-only) rc=%s; releasing snark gate"
              % p1.returncode)
        os.makedirs(FLAG_DIR, exist_ok=True)
        open(FLAG, "w").close()                     # -> proc2 runs decider
        p2.wait()
        t2.join()
        print("[numa] proc2 (snark) rc=%s" % p2.returncode)
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
            verify_two(log1, log2)
        except Exception as e:
            print("[numa] WARN: verify failed: %s" % e)
        pack_part("part1", log1, with_report=False)
        pack_part("part2", log2, with_report=True)
    rc1 = p1.returncode if p1 else 1
    rc2 = p2.returncode if p2 else 1
    return rc1 or rc2


print("[numa] MODE=%s PCT=%d NJOBS=%d nodes=%d" % (MODE, PCT, NJOBS, nnodes()))
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
