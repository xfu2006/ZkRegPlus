#!/usr/bin/env python3
"""Run full_dna (single-job ZK discharge of the clean chr17 sample against
the DNA DB) and pack all artifacts. Repo root resolved from this file, so
cwd is free. Unlike run_full_dlp, full_dna takes NO runcfg -- its capacities
are hardcoded in the test body -- so this driver only runs + packs.

Usage:
  python3 run_full_dna.py [--dry-run]
    --dry-run  : print resolved paths + command, do not run cargo.

Env:  ZKR_VM_MAX_MAP_COUNT  target vm.max_map_count (default 1073741824 = 1G;
                 0 skips). Raised via `sudo sysctl` before the run so the
                 fold's many small mimalloc mappings don't hit the VMA
                 ceiling (the PREFLIGHT ABORT / SIGABRT-with-free-RAM case).

Output (ALWAYS packed, even on OOM/panic/exception):
  /tmp/run_full_dna.tar.gz
    full_dna_dump.tgz   <- gzip -9 of the full run log (ALL jobs' stdout)
    summary_<ts>.txt
    report_zk.dat       <- DNA report, if produced
    logs/log_job_*.txt  <- per-job logs, if any
"""
import os, sys, subprocess, time, datetime, tarfile, json, platform, re, glob

VMA_TARGET = int(os.environ.get("ZKR_VM_MAX_MAP_COUNT", "1073741824"))  # 0=skip


def ensure_vma(target):
    """Best-effort raise vm.max_map_count (the VMA ceiling). mimalloc frees
    RAM via many small OS mappings; the fold can exhaust the default 1048576
    and SIGABRT on a tiny alloc while RAM is free (or trip the in-prover
    PREFLIGHT ABORT). Non-fatal -- prints the manual command if sudo fails."""
    if target <= 0:
        return
    path = "/proc/sys/vm/max_map_count"
    try:
        cur = int(open(path).read().strip())
    except Exception as e:
        print("[run_full_dna] vm.max_map_count: cannot read (%s); skip" % e)
        return
    if cur >= target:
        print("[run_full_dna] vm.max_map_count=%d already >= %d" % (cur, target))
        return
    print("[run_full_dna] vm.max_map_count=%d < %d; raising via sudo sysctl"
          % (cur, target))
    rc_ = subprocess.run(["sudo", "sysctl", "-w",
                          "vm.max_map_count=%d" % target]).returncode
    if rc_ != 0:
        print("[run_full_dna] WARN: could not raise vm.max_map_count (sudo?). "
              "Run manually: sudo sysctl -w vm.max_map_count=%d" % target)
    else:
        try:
            print("[run_full_dna] vm.max_map_count now %s"
                  % open(path).read().strip())
        except Exception:
            pass


HERE = os.path.dirname(os.path.abspath(__file__))          # zkregplus/src
REPO = os.path.abspath(os.path.join(HERE, "..", ".."))     # bora
LOGS_DIR = os.path.join(REPO, "data/cache/logs")           # log_job_*.txt
REPORT = os.path.join(REPO, "data/paper_data/dna/reports/report_zk.dat")

DRY = "--dry-run" in sys.argv

OUT = "/tmp/full_dna_run"
TS = datetime.datetime.now().strftime("%Y%m%d_%H%M%S")
os.makedirs(OUT, exist_ok=True)
LOG = os.path.join(OUT, "run_%s.log" % TS)                 # ALL-jobs dump
SUM = os.path.join(OUT, "summary_%s.txt" % TS)
DUMP_TGZ = os.path.join(OUT, "full_dna_dump.tgz")          # gzip -9 of LOG
TAR = "/tmp/run_full_dna.tar.gz"                           # literal name

env = dict(os.environ)
env.setdefault("RUSTFLAGS", "-C link-args=-fuse-ld=lld -Awarnings")

time_prefix = ["/usr/bin/time", "-v"] if os.path.exists("/usr/bin/time") else []
cmd = time_prefix + ["cargo", "test", "-p", "zkregplus", "--release", "--",
    "zkp_driver::tests_zkp_driver::test_full_dna", "--exact", "--nocapture"]

print("[run_full_dna] REPO   =", REPO)
print("[run_full_dna] LOG    =", LOG)
print("[run_full_dna] cmd    =", " ".join(cmd))
print("[run_full_dna] out    =", TAR, "(inner:", os.path.basename(DUMP_TGZ) + ")")
print("[run_full_dna] vm.max_map_count target =", VMA_TARGET or "skip")
if DRY:
    print("[run_full_dna] --dry-run: not executing.")
    sys.exit(0)


def pack(code, wall):
    """Build the dump.tgz (gzip -9 of the full run log) and the outer
    run_full_dna.tar.gz. ALWAYS runs, even after a panic/exception."""
    # full_dna_dump.tgz: best compression ratio (gzip level 9) over the log.
    try:
        with tarfile.open(DUMP_TGZ, "w:gz", compresslevel=9) as d:
            if os.path.isfile(LOG):
                d.add(LOG, arcname=os.path.basename(LOG))
    except Exception as e:
        print("[run_full_dna] WARN: could not build dump.tgz: %s" % e)
    # outer archive (literal name requested).
    with tarfile.open(TAR, "w:gz") as t:
        if os.path.isfile(DUMP_TGZ):
            t.add(DUMP_TGZ, arcname=os.path.basename(DUMP_TGZ))
        for f in [SUM, REPORT]:
            if f and os.path.isfile(f):
                t.add(f, arcname=os.path.basename(f))
        for jf in sorted(glob.glob(os.path.join(LOGS_DIR, "log_job_*.txt"))):
            t.add(jf, arcname="logs/" + os.path.basename(jf))
    print("[run_full_dna] packed -> %s  (exit=%s, wall=%.0fs)"
          % (TAR, code, wall))


def write_summary(code, wall):
    def grep(pats):
        out = []
        for l in open(LOG, errors="replace"):
            if any(pat in l for pat in pats):
                out.append(l.rstrip("\n"))
        return out
    agg = {}
    for l in open(LOG, errors="replace"):
        if "prove_step cost: i:" in l:
            m = re.search(
                r"circ_id: (\d+).*stmt_len: (\d+).*wtns size: (\d+) (\d+) ms", l)
            if m:
                c = int(m.group(1)); d = agg.setdefault(c, [0, 0, 0, 0])
                d[0] += 1; d[1] += int(m.group(4))
                d[2] = int(m.group(2)); d[3] = int(m.group(3))
    git = subprocess.run(["git", "rev-parse", "HEAD"], cwd=REPO,
                         capture_output=True, text=True).stdout.strip()
    with open(SUM, "w") as s:
        s.write("host=%s cpu=%s exit=%s wall_s=%.1f\n" % (
            platform.node(), os.cpu_count(), code, wall))
        s.write("git=%s\n\n" % git)
        for l in grep(["PERF WORKFLOW", "PROGRESS step", "PROGRESS fold",
                       "PERF 1006", "cs1e", "KEYS info", "snark", "decider",
                       "Maximum resident set size", "Killed",
                       "Out of memory", "panicked", "test result",
                       "verify", "Job", "CapErr"]):
            s.write(l + "\n")
        s.write("\n-- per-circuit fold step cost --\n")
        for c in sorted(agg):
            n, ms, st, wt = agg[c]
            s.write("circ%d: steps=%d stmt_len=%d wtns=%d avg=%.0fms "
                    "total=%.1fs\n" % (c, n, st, wt, ms / max(n, 1),
                                       ms / 1000.0))
    print("\n" + open(SUM).read())


ensure_vma(VMA_TARGET)
t0 = time.time()
code = None
try:
    with open(LOG, "w") as lf:
        lf.write("# %s host=%s cpu=%s\n# cmd=%s\n\n" % (
            datetime.datetime.now(), platform.node(), os.cpu_count(),
            " ".join(cmd)))
        lf.flush()
        p = subprocess.Popen(cmd, cwd=REPO, env=env, stdout=subprocess.PIPE,
                             stderr=subprocess.STDOUT, text=True)
        for line in p.stdout:
            sys.stdout.write(line); lf.write(line); lf.flush()
        p.wait()
        code = p.returncode
finally:
    wall = time.time() - t0
    try:
        write_summary(code, wall)
    except Exception as e:
        print("[run_full_dna] WARN: summary failed: %s" % e)
    pack(code, wall)

sys.exit(0 if code == 0 else (code or 1))
