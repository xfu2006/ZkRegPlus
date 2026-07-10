#!/usr/bin/env python3
"""Run full_clam (8-job ZK discharge of the ClamAV binexec corpus against the
full_clamav DB, one full-mode proof) and pack all artifacts. Repo root resolved
from this file, so cwd is free. Like run_full_dna, full_clam takes NO runcfg --
its capacities are hardcoded in the test body -- so this driver only runs + packs.

full_clam reads the snark cache under data/cache/full_clamav. If the cache is
cold/partial the prover rebuilds + persists keys this run (driver.rs auto-build),
so the first run is slow and later runs reuse the keys.

Usage:
  python3 run_full_clam.py [--dry-run] [--numa=P]
    --dry-run  : print resolved paths + command, do not run cargo.
    --numa=P   : whole-process numactl policy. Default 'interleave' (proving is
                 capacity-bound and may exceed one socket -> balanced bandwidth,
                 no membind cap, won't OOM). 'socket' = pin cores to socket 0
                 (faster IF peak RSS fits one socket). 'off' = no numactl.

Env:  ZKR_VM_MAX_MAP_COUNT  target vm.max_map_count (default 1073741824 = 1G;
                 0 skips). Raised via `sudo sysctl` before the run so the
                 8-job fold's many small mimalloc mappings don't hit the VMA
                 ceiling (the PREFLIGHT ABORT / SIGABRT-with-free-RAM case).

Output (ALWAYS packed, even on OOM/panic/exception):
  /tmp/full_clam.tgz
    full_clam.log.tgz   <- gzip -9 of the full run log (ALL jobs' stdout)
    summary_<ts>.txt
    report2.dat         <- ClamAV report, if produced
    logs/log_job_*.txt  <- per-job logs, if any
"""
import os, sys, subprocess, time, datetime, tarfile, json, platform, re, glob

VMA_TARGET = int(os.environ.get("ZKR_VM_MAX_MAP_COUNT", "1073741824"))  # 0=skip

# NUMA policy applied as a whole-process numactl wrapper. UNLIKE full_dlp (advice
# gen, bandwidth-bound, fits one socket -> 'socket' wins), full_clam is the
# PROVING run: capacity-bound (snark keys + fold state) and can exceed one
# socket's RAM, where --membind would OOM. So the default here is 'interleave'
# -- spread pages over all nodes for balanced bandwidth, no per-socket cap.
# Override with --numa=socket (only if a run's peak RSS fits one socket, for the
# all-local speedup) or --numa=off. The Rust per-job pinning stays off.
NUMA = os.environ.get("ZKR_NUMA", "interleave")
for a in sys.argv[1:]:
    if a.startswith("--numa="):
        NUMA = a.split("=", 1)[1]
if "--numa" in sys.argv:                       # also accept "--numa P"
    NUMA = sys.argv[sys.argv.index("--numa") + 1]


def numa_prefix(policy):
    """Whole-process numactl wrapper. Returns [] when numactl is absent, the box
    is single-NUMA, or policy is off/none/perjob.
      interleave -> --interleave=all (DEFAULT for proving): balanced bandwidth
                    over all nodes, no per-socket cap -> won't OOM at >512GB.
      socket     -> pin cores to the FIRST socket's nodes (--cpunodebind only):
                    all-local first-touch, faster IF the run fits one socket.
      off/none/perjob -> no numactl (perjob lets the Rust path pin per job)."""
    import shutil
    if policy in ("off", "none", "perjob"):
        return []
    if not shutil.which("numactl"):
        print("[run_full_clam] numactl not found; NUMA '%s' skipped" % policy)
        return []
    try:
        h = subprocess.run(["numactl", "-H"], capture_output=True,
                           text=True).stdout
        nnodes = max((int(x) for x in re.findall(r"node (\d+) cpus:", h)),
                     default=-1) + 1
    except Exception:
        nnodes = 0
    if nnodes <= 1:
        print("[run_full_clam] single NUMA node; no policy needed")
        return []
    if policy == "interleave":
        print("[run_full_clam] NUMA: --interleave=all over %d nodes" % nnodes)
        return ["numactl", "--interleave=all"]
    half = max(1, nnodes // 2)                  # 'socket'
    rng = "0-%d" % (half - 1)
    print("[run_full_clam] NUMA: pin cores to nodes %s of %d (local first-touch, "
          "no membind cap)" % (rng, nnodes))
    return ["numactl", "--cpunodebind=%s" % rng]


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
        print("[run_full_clam] vm.max_map_count: cannot read (%s); skip" % e)
        return
    if cur >= target:
        print("[run_full_clam] vm.max_map_count=%d already >= %d" % (cur, target))
        return
    print("[run_full_clam] vm.max_map_count=%d < %d; raising via sudo sysctl"
          % (cur, target))
    rc_ = subprocess.run(["sudo", "sysctl", "-w",
                          "vm.max_map_count=%d" % target]).returncode
    if rc_ != 0:
        print("[run_full_clam] WARN: could not raise vm.max_map_count (sudo?). "
              "Run manually: sudo sysctl -w vm.max_map_count=%d" % target)
    else:
        try:
            print("[run_full_clam] vm.max_map_count now %s"
                  % open(path).read().strip())
        except Exception:
            pass


HERE = os.path.dirname(os.path.abspath(__file__))          # zkregplus/src
REPO = os.path.abspath(os.path.join(HERE, "..", ".."))     # new_zkregplus
LOGS_DIR = os.path.join(REPO, "data/cache/logs")           # log_job_*.txt
REPORT = os.path.join(REPO, "data/debug/full_clamav/reports/report2.dat")

DRY = "--dry-run" in sys.argv

OUT = "/tmp/full_clam_run"
TS = datetime.datetime.now().strftime("%Y%m%d_%H%M%S")
os.makedirs(OUT, exist_ok=True)
LOG = os.path.join(OUT, "run_%s.log" % TS)                 # ALL-jobs dump
SUM = os.path.join(OUT, "summary_%s.txt" % TS)
DUMP_TGZ = os.path.join(OUT, "full_clam.log.tgz")          # gzip -9 of LOG
TAR = "/tmp/full_clam.tgz"                                 # literal name

env = dict(os.environ)
env.setdefault("RUSTFLAGS", "-C link-args=-fuse-ld=lld -Awarnings")
env["ZKR_NUMA"] = "perjob" if NUMA == "perjob" else "off"   # Rust pinning off

time_prefix = ["/usr/bin/time", "-v"] if os.path.exists("/usr/bin/time") else []
cmd = time_prefix + numa_prefix(NUMA) + ["cargo", "test", "-p", "zkregplus",
    "--release", "--",
    "zkp_driver::tests_zkp_driver::full_clam", "--exact", "--nocapture"]

print("[run_full_clam] REPO   =", REPO)
print("[run_full_clam] LOG    =", LOG)
print("[run_full_clam] cmd    =", " ".join(cmd))
print("[run_full_clam] out    =", TAR, "(inner:", os.path.basename(DUMP_TGZ) + ")")
print("[run_full_clam] vm.max_map_count target =", VMA_TARGET or "skip")
if DRY:
    print("[run_full_clam] --dry-run: not executing.")
    sys.exit(0)


def pack(code, wall):
    """Build full_clam.log.tgz (gzip -9 of the full run log) and the outer
    full_clam.tgz. ALWAYS runs, even after a panic/exception."""
    # full_clam.log.tgz: best compression ratio (gzip level 9) over the log.
    try:
        with tarfile.open(DUMP_TGZ, "w:gz", compresslevel=9) as d:
            if os.path.isfile(LOG):
                d.add(LOG, arcname=os.path.basename(LOG))
    except Exception as e:
        print("[run_full_clam] WARN: could not build log.tgz: %s" % e)
    # outer archive (literal name requested).
    with tarfile.open(TAR, "w:gz") as t:
        if os.path.isfile(DUMP_TGZ):
            t.add(DUMP_TGZ, arcname=os.path.basename(DUMP_TGZ))
        for f in [SUM, REPORT]:
            if f and os.path.isfile(f):
                t.add(f, arcname=os.path.basename(f))
        for jf in sorted(glob.glob(os.path.join(LOGS_DIR, "log_job_*.txt"))):
            t.add(jf, arcname="logs/" + os.path.basename(jf))
    print("[run_full_clam] packed -> %s  (exit=%s, wall=%.0fs)"
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
                       "PERF 1004", "PERF 1006", "cs1e", "KEYS info", "snark",
                       "decider", "Maximum resident set size", "Killed",
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
        print("[run_full_clam] WARN: summary failed: %s" % e)
    pack(code, wall)

sys.exit(0 if code == 0 else (code or 1))
