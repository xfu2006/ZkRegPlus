#!/usr/bin/env python3
"""Two-half NUMA driver for full_dlp (Enron/DLP corpus).

full_dlp() splits the master file list into --jobs balanced job files itself,
so this driver only:
  - chooses a strided pct sample (ZKR_DLP_PCT; full_dlp does the striding),
  - tells each half which job range to FOLD (ZKR_DLP_READ_MODE first|second),
  - pins each half to a NUMA node-half (cpu hard + mem soft).
Both halves read the SAME committed master tgz and split it identically; the
two read_modes fold disjoint halves (jobs 0..h-1 vs h..N-1). The discharge /
ladder cache is reused; pct<100 uses pct-tagged dirs (never clobbers 100%).

Modes (total --jobs N, default 8):
  baseline : 1 proc, all N jobs, no numactl, fold-only        -> .baseline.tgz
  numa     : 2 procs pinned 0..h-1 / h..n-1, fold 4+4, fold-only
  prod     : same two-half but FIXED 100%; --fold-only=false makes part2 run
             the ONE full SNARK (light_test=false), flag-gated like full_clam.

Options:
  --jobs N         total jobs (default 8)
  --mode M         baseline|numa|prod (default prod)
  --fold-only B    true|false (default true; false only honored in prod)
  --pct P          sample percent (default 1 for baseline/numa; forced 100 prod)
  --part2-delay S  min stagger before part2 starts (default 900)
  --part2-ram-gb G part2 waits until part1 tree-RSS < G (default 500)
  --ladder-only    build+save the REAL (pct=100) ladder then stop before the
                   fold (1 proc, forces pct=100); harvest the ladder cheaply
  --dry-run

Env knobs full_dlp() reads (unset => byte-identical bare `cargo test full_dlp`):
  ZKR_DLP_PCT, ZKR_DLP_READ_MODE, ZKR_DLP_FOLD_ONLY, ZKR_DLP_ONE_PROOF,
  ZKR_SNARK_WAIT_FLAG, ZKR_DLP_PROBE_FILES, ZKR_LOG_TAG.

After the run a set-based verifier checks the split (see verify_split):
files folded by all jobs == the strided sample S (== full corpus T at prod).
On any failure it prints a final `DLP SPLIT VERIFY: FAIL` block and exits != 0.
"""
import os, sys, subprocess, time, datetime, tarfile, json, platform, re, \
    glob, shutil, threading


def getarg(name, default=None):
    pref = "--%s=" % name
    for a in sys.argv[1:]:
        if a.startswith(pref):
            return a.split("=", 1)[1]
    return default


MODE = getarg("mode", "prod")
if MODE not in ("prod", "numa", "baseline"):
    raise SystemExit("--mode must be prod|numa|baseline (got %r)" % MODE)
LADDER_ONLY = "--ladder-only" in sys.argv   # build+save ladder, stop pre-fold
JOBS = int(getarg("jobs", "8"))
FOLD_ONLY = getarg("fold-only", "true").lower() not in ("false", "0", "no")
# fold-only=false (full snark) is only honored in prod; force true elsewhere.
if not FOLD_ONLY and MODE != "prod":
    print("[numa] --fold-only=false only valid in prod; forcing fold-only.")
    FOLD_ONLY = True
# prod is fixed at 100%; baseline/numa default to 1% (fast shakeout).
# ladder-only always harvests the REAL ladder => force the full corpus.
PCT = 100 if (MODE == "prod" or LADDER_ONLY) else int(getarg("pct", "1"))
PART2_DELAY = int(getarg("part2-delay", "900"))
PART2_RAM_GB = float(getarg("part2-ram-gb", "500"))
DRY = "--dry-run" in sys.argv
VMA_TARGET = int(os.environ.get("ZKR_VM_MAX_MAP_COUNT", "1073741824"))

HERE = os.path.dirname(os.path.abspath(__file__))          # zkregplus/src
REPO = os.path.abspath(os.path.join(HERE, "..", ".."))     # new_zkregplus
CFG_DIR = os.path.join(REPO, "data/paper_data/dlp/cfg/config")
RUNCFG = os.path.join(CFG_DIR, "runcfg_full.json")
LOGS_DIR = os.path.join(REPO, "data/cache/logs")           # log_job_*.txt
FLAG_DIR = "/tmp/snark_start"
FLAG = os.path.join(FLAG_DIR, "flag")
OUT = "/tmp/full_dlp_numa_run"
os.makedirs(OUT, exist_ok=True)
TS = datetime.datetime.now().strftime("%Y%m%d_%H%M%S")

rc = json.load(open(RUNCFG))
rc["num_jobs"] = JOBS
CD = rc["config_dir"]                                       # data/paper_data/...
MASTER = os.path.join(REPO, CD, rc["full_list"])           # committed tgz
TAG = "" if PCT >= 100 else "_pct%d" % PCT                 # mirrors full_dlp
JOBS_DIR = os.path.join(REPO, CD, "jobs", "jobs%d%s" % (JOBS, TAG))
EFF = os.path.join(OUT, "runcfg_effective_%s.json" % TS)
json.dump(rc, open(EFF, "w"), indent=2)

CARGO = ["cargo", "test", "-p", "zkregplus", "--release", "--",
         "zkp_driver::tests_zkp_driver::full_dlp", "--exact", "--nocapture"]


def stride_k(pct):
    return max(1, (100 + pct // 2) // pct)                  # == Rust k


def ensure_vma(target):
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
    rc_ = subprocess.run(["sudo", "sysctl", "-w",
                          "vm.max_map_count=%d" % target]).returncode
    if rc_ != 0:
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
    n = nnodes()
    if n < 2:
        return None, None
    h = n // 2
    return "0-%d" % (h - 1), "%d-%d" % (h, n - 1)


def numa_prefix(nodes):
    if not nodes or not shutil.which("numactl"):
        return []
    return ["numactl", "--cpunodebind=%s" % nodes,
            "--preferred-many=%s" % nodes]


def _ppid(pid):
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
    e["ZKR_DLP_RUNCFG"] = EFF
    e["ZKR_DLP_PCT"] = str(PCT)
    e["ZKR_DLP_READ_MODE"] = read_mode          # full|first|second
    e["ZKR_DLP_FOLD_ONLY"] = "1" if fold_only else "0"
    e["ZKR_DLP_ONE_PROOF"] = "1" if one_proof else "0"
    e["ZKR_DLP_PROBE_FILES"] = "1"              # emit PROBE DLP per job
    e.setdefault("ZKR_DC_THREADS", "8")
    if wait_flag:
        e["ZKR_SNARK_WAIT_FLAG"] = wait_flag
    else:
        e.pop("ZKR_SNARK_WAIT_FLAG", None)
    e["ZKR_LOG_TAG"] = log_tag                  # "" | "p1_" | "p2_"
    e.pop("ZKR_DLP_LADDER_ONLY", None)          # set only by run_ladder_only
    return e


def spawn(nodes, env, log_path, label):
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


# ---------------- target set + ground-truth split ----------------
def filtered_master():
    """The master tgz after read_path_list's filter (drop blanks + dotfile
    basenames), in on-disk order. This is the full corpus T."""
    out = subprocess.run(["tar", "-xzO", "-f", MASTER],
                         capture_output=True, text=True).stdout
    res = []
    for ln in out.splitlines():
        s = ln.strip()
        if s and not s.rsplit("/", 1)[-1].startswith("."):
            res.append(s)
    return res


def sample_S():
    """Strided every-k-th of the filtered master == full_dlp's sample."""
    fl = filtered_master()
    k = stride_k(PCT)
    return fl[::k], fl, k


def job_file_sets():
    """{job_id: set(paths)} read from the on-disk balanced split."""
    res = {}
    for i in range(JOBS):
        p = os.path.join(JOBS_DIR, "job_%d.dat" % i)
        if os.path.isfile(p):
            res[i] = set(x.strip() for x in open(p) if x.strip())
    return res


_PROBE = re.compile(r"^PROBE DLP job (\d+) n (\d+)$")


def probe_jobs(log_path):
    """{job_id: folded_count} from this process's 'PROBE DLP job J n M'."""
    res = {}
    if not os.path.isfile(log_path):
        return res
    for ln in open(log_path, errors="replace"):
        m = _PROBE.match(ln.strip())
        if m:
            res[int(m.group(1))] = int(m.group(2))
    return res


def verify_split(part_logs):
    """Set-based split check. Accumulates failures and prints one final
    PASS/FAIL block; returns True iff all checks pass.

    part_logs: [baseline_log] or [part1_log, part2_log]."""
    S, FL, k = sample_S()
    S = set(S)
    h = JOBS // 2
    jobs = job_file_sets()
    probes = [probe_jobs(p) for p in part_logs]
    fails = []                                  # (check, brief, examples)
    npass = 0

    def ex(s):
        return ", ".join(sorted(s)[:3])

    # check 1: split coverage  -- union of job files == sample S
    union = set().union(*jobs.values()) if jobs else set()
    miss, extra = S - union, union - S
    if not miss and not extra:
        npass += 1
    else:
        d = []
        if miss:
            d.append("%d MISSING e.g. %s" % (len(miss), ex(miss)))
        if extra:
            d.append("%d EXTRA e.g. %s" % (len(extra), ex(extra)))
        fails.append(("1 split coverage",
                      "|S|=%d |union|=%d: %s" % (len(S), len(union),
                                                 "; ".join(d)), None))

    # check 2: split disjoint  -- job files pairwise disjoint
    ov = set()
    ids = sorted(jobs)
    for a in range(len(ids)):
        for b in range(a + 1, len(ids)):
            ov |= jobs[ids[a]] & jobs[ids[b]]
    if not ov:
        npass += 1
    else:
        fails.append(("2 split disjoint",
                      "%d file(s) in >1 job e.g. %s" % (len(ov), ex(ov)),
                      None))

    # check 3: each process folded its whole job file (count match)
    bad = []
    for pr in probes:
        for j, m in pr.items():
            want = len(jobs.get(j, set()))
            if m != want:
                bad.append("job %d folded %d != |file| %d" % (j, m, want))
    if not bad:
        npass += 1
    else:
        fails.append(("3 per-job count", "; ".join(bad[:4]), None))

    # check 4: half coverage  -- which jobs each part folded
    emitted = [set(pr) for pr in probes]
    allj = set().union(*emitted) if emitted else set()
    want_all = set(range(JOBS))
    c4 = []
    if len(part_logs) == 2:
        if emitted[0] != set(range(h)):
            c4.append("part1 folded %s != %s"
                      % (sorted(emitted[0]), sorted(range(h))))
        if emitted[1] != set(range(h, JOBS)):
            c4.append("part2 folded %s != %s"
                      % (sorted(emitted[1]), sorted(range(h, JOBS))))
    if allj != want_all:
        c4.append("union %s != %s" % (sorted(allj), sorted(want_all)))
    if not c4:
        npass += 1
    else:
        fails.append(("4 half coverage", "; ".join(c4), None))

    # check 5: sample correctness  -- S is exactly the strided pick
    if set(FL[::k]) == S and len(S) > 0:
        npass += 1
    else:
        fails.append(("5 sample", "S != filtered-master[::%d]" % k, None))

    ntot = 5
    # check 6 (prod only, ADDITIVE): union == entire filtered corpus T
    if MODE == "prod":
        ntot = 6
        T = set(FL)
        miss6, extra6 = T - union, union - T
        if PCT == 100 and not miss6 and not extra6 and len(union) == len(T):
            npass += 1
        else:
            d = ["|union|=%d T=%d" % (len(union), len(T))]
            if miss6:
                d.append("%d MISSING e.g. %s" % (len(miss6), ex(miss6)))
            if extra6:
                d.append("%d EXTRA e.g. %s" % (len(extra6), ex(extra6)))
            if PCT != 100:
                d.append("pct=%d != 100" % PCT)
            fails.append(("6 prod completeness", "; ".join(d), None))

    ok = not fails
    print("")
    if ok:
        print("DLP SPLIT VERIFY: PASS (%d/%d, mode=%s jobs=%d pct=%d)"
              % (npass, ntot, MODE, JOBS, PCT))
    else:
        print("================ DLP SPLIT VERIFY: FAIL ================")
        for chk, brief, _ in fails:
            print("[FAIL] check %s: %s" % (chk, brief))
        print("mode=%s jobs=%d pct=%d  ->  %d/%d checks FAILED"
              % (MODE, JOBS, PCT, len(fails), ntot))
        print("=======================================================")
    return ok


# ---------------- packing ----------------
def gz_one(path):
    if not os.path.isfile(path):
        return None
    out = path + ".tgz"
    with tarfile.open(out, "w:gz", compresslevel=9) as t:
        t.add(path, arcname=os.path.basename(path))
    return out


def pack_part(part, log_path):
    """full_dlp.log.jobs<N>.<part>.tgz = inner gzipped run log + this part's
    tagged per-job logs. part in baseline|part1|part2."""
    tag = {"part1": "p1_", "part2": "p2_", "baseline": ""}[part]
    tgz = os.path.join(OUT, "full_dlp.log.jobs%d.%s.tgz" % (JOBS, part))
    try:
        with tarfile.open(tgz, "w:gz", compresslevel=9) as t:
            inner = gz_one(log_path)
            if inner:
                t.add(inner, arcname=os.path.basename(inner))
            patt = "log_job_%s*.txt" % tag if tag else "log_job_[0-9]*.txt"
            for jf in sorted(glob.glob(os.path.join(LOGS_DIR, patt))):
                t.add(jf, arcname="logs/" + os.path.basename(jf))
        print("[numa] packed -> %s" % tgz)
    except Exception as e:
        print("[numa] WARN: pack %s failed: %s" % (part, e))


# ---------------- flows ----------------
def run_ladder_only():
    """Steps 1-5 only: build + save the REAL (pct=100) ladder, then the Rust
    side returns before the fold (ZKR_DLP_LADDER_ONLY=1). One process, no
    numactl, no split verify (no fold => no PROBE lines to check)."""
    log = os.path.join(OUT, "ladder_%s.log" % TS)
    env = base_env("full", fold_only=True, one_proof=False,
                   wait_flag=None, log_tag="")
    env["ZKR_DLP_LADDER_ONLY"] = "1"
    p, t = spawn(None, env, log, "ladder")
    try:
        p.wait()
        t.join()
    finally:
        pack_part("baseline", log)
    lp = os.path.join(REPO, rc["config_out"])
    ok = os.path.isfile(lp) and os.path.getsize(lp) > 0
    print("[numa] ladder %s: %s" % ("READY" if ok else "MISSING", lp))
    return (p.returncode or 0) or (0 if ok else 3)


def run_baseline():
    log = os.path.join(OUT, "baseline_%s.log" % TS)
    env = base_env("full", fold_only=FOLD_ONLY, one_proof=False,
                   wait_flag=None, log_tag="")
    p, t = spawn(None, env, log, "baseline")
    ok = False
    try:
        p.wait()
        t.join()
    finally:
        try:
            ok = verify_split([log])
        except Exception as e:
            print("[numa] WARN: verify failed: %s" % e)
        pack_part("baseline", log)
    return (p.returncode or 0) or (0 if ok else 3)


def run_two():
    a, b = half_ranges()
    print("[numa] part1 fold nodes=%s ; part2 nodes=%s ; flag=%s ; snark=%s"
          % (a, b, FLAG, "no" if FOLD_ONLY else "part2"))
    shutil.rmtree(FLAG_DIR, ignore_errors=True)
    log1 = os.path.join(OUT, "part1_%s.log" % TS)
    log2 = os.path.join(OUT, "part2_%s.log" % TS)
    env1 = base_env("first", fold_only=True, one_proof=False,
                    wait_flag=None, log_tag="p1_")
    # part2: fold-only unless prod+full-snark, in which case it runs the ONE
    # decider gated on the flag (touched when part1 exits, freeing its RAM).
    p2_fold_only = FOLD_ONLY
    env2 = base_env("second", fold_only=p2_fold_only,
                    one_proof=not p2_fold_only,
                    wait_flag=None if p2_fold_only else FLAG, log_tag="p2_")
    p1 = p2 = t1 = t2 = None
    ok = False
    try:
        p1, t1 = spawn(a, env1, log1, "part1")
        print("[numa] part2 gate: t>=%ds AND part1 RSS<%.0fGB (or part1 exit)"
              % (PART2_DELAY, PART2_RAM_GB))
        waited = 0
        while p1.poll() is None:
            rss = tree_rss_gb(p1.pid)
            if waited >= PART2_DELAY and rss < PART2_RAM_GB:
                break
            if waited % 60 == 0:
                print("[numa] waiting part2: t=%ds rss=%.0fGB" % (waited, rss))
            time.sleep(10)
            waited += 10
        p2, t2 = spawn(b, env2, log2, "part2")
        p1.wait()
        t1.join()
        print("[numa] part1 rc=%s" % p1.returncode)
        if not p2_fold_only:                    # release the single decider
            os.makedirs(FLAG_DIR, exist_ok=True)
            open(FLAG, "w").close()
        p2.wait()
        t2.join()
        print("[numa] part2 rc=%s" % p2.returncode)
    finally:
        if p2 is not None and p2.poll() is None and not os.path.exists(FLAG):
            os.makedirs(FLAG_DIR, exist_ok=True)
            open(FLAG, "w").close()
        if p2 is not None:
            p2.wait()
        if t2 is not None:
            t2.join()
        try:
            ok = verify_split([log1, log2])
        except Exception as e:
            print("[numa] WARN: verify failed: %s" % e)
        pack_part("part1", log1)
        pack_part("part2", log2)
    rc1 = p1.returncode if p1 else 1
    rc2 = p2.returncode if p2 else 1
    return (rc1 or rc2) or (0 if ok else 3)


def main():
    print("[numa] MODE=%s JOBS=%d PCT=%d FOLD_ONLY=%s LADDER_ONLY=%s nodes=%d"
          % (MODE, JOBS, PCT, FOLD_ONLY, LADDER_ONLY, nnodes()))
    print("[numa] REPO=%s OUT=%s" % (REPO, OUT))
    print("[numa] MASTER=%s JOBS_DIR=%s" % (MASTER, JOBS_DIR))
    if DRY:
        a, b = half_ranges()
        S, FL, k = sample_S()
        if LADDER_ONLY:
            print("[numa] --dry-run ladder-only: 1 proc, pct=100, stop after"
                  " step 5; ladder ->", os.path.join(REPO, rc["config_out"]))
        print("[numa] --dry-run: halves=%s/%s flag=%s" % (a, b, FLAG))
        print("[numa] part1 numactl:", numa_prefix(a) or "(none)")
        print("[numa] part2 numactl:", numa_prefix(b) or "(none)")
        print("[numa] sample: stride k=%d -> %d of %d files (T=%d)"
              % (k, len(S), len(FL), len(FL)))
        return 0
    ensure_vma(VMA_TARGET)
    if LADDER_ONLY:
        return run_ladder_only()
    return run_baseline() if MODE == "baseline" else run_two()


if __name__ == "__main__":
    code = main()
    sys.exit(0 if code == 0 else (code or 1))
