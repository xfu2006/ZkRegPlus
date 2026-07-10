#!/usr/bin/env python3
"""Run full_dlp (split + cached discharge/ladder + multi-job fold) and
pack all artifacts. Repo root resolved from this file, so cwd is free.

Usage:
  python3 run_full_dlp.py [runcfg] [--jobs N] [--reset] [--probe-reset]
                          [--numa=P] [--dry-run]
    runcfg     : path or name under data/paper_data/dlp/cfg/config/
                 (default runcfg_full.json)
    --jobs N   : override num_jobs in the runcfg for this run
    --reset    : override reset=true (recompute split/discharge/ladder)
    --probe-reset : perc probes (aggressive) -- 64600.1 per-file old
                  cross-chunk vs new chunk-local-reset estimate, and
                  64601.3 the exact per-rung StepFwdPrf perc demand
                  (route+back-solve) applied to the ladder
    --numa=P   : whole-process numactl policy (default socket). MEASURED best:
                 8 jobs socket-confined is ~0.89x the 512GB baseline; 16 jobs
                 across both sockets saturates memory bandwidth (~2.5x slower).
                   socket     -> confine to the FIRST socket's nodes
                     (--cpunodebind/--membind), 8 jobs all-local. DEFAULT/best.
                   interleave -> --interleave=all (spread); only if you need >1
                     socket's cores/RAM.
                   off        -> no numactl (Linux first-touch).
                   perjob     -> no numactl; let the Rust foldpot::numa pin per
                     job (ZKR_NUMA=perjob). NOT recommended -- fragments the pool.
    --dry-run  : print resolved paths + command, do not run cargo.

Defaults bake in the winning config: --jobs 8 --numa socket. Just run:
  nohup python3 -u run_full_dlp.py &

Env:  ZKR_NUMA       numa policy (socket|interleave|off|perjob); --numa= overrides
      ZKR_DC_THREADS  determine_config probe threads (default 8)
      ZKR_VM_MAX_MAP_COUNT  target vm.max_map_count (default 1073741824 = 1G;
                 0 skips). Raised via `sudo sysctl` before the run so the
                 8-job fold's many small mimalloc mappings don't hit the VMA
                 ceiling (the PREFLIGHT ABORT / SIGABRT-with-free-RAM case).

Output (always packed, even on OOM/panic):
  /tmp/full_dlp_artifacts_<ts>.tar.gz
    {effective runcfg, ladder json, needs_dist.txt, run log (dump.txt),
     per-job log_job_*.txt, summary}
"""
import os, sys, subprocess, time, datetime, tarfile, json, platform, re, glob

VMA_TARGET = int(os.environ.get("ZKR_VM_MAX_MAP_COUNT", "1073741824"))  # 0=skip


def ensure_vma(target):
    """Best-effort raise vm.max_map_count (the VMA ceiling). mimalloc frees
    RAM via many small OS mappings; the multi-job fold can exhaust the default
    1048576 and SIGABRT on a tiny alloc while RAM is free (or trip the in-prover
    PREFLIGHT ABORT). Non-fatal -- prints the manual command if sudo fails."""
    if target <= 0:
        return
    path = "/proc/sys/vm/max_map_count"
    try:
        cur = int(open(path).read().strip())
    except Exception as e:
        print("[run_full_dlp] vm.max_map_count: cannot read (%s); skip" % e)
        return
    if cur >= target:
        print("[run_full_dlp] vm.max_map_count=%d already >= %d" % (cur, target))
        return
    print("[run_full_dlp] vm.max_map_count=%d < %d; raising via sudo sysctl"
          % (cur, target))
    rc_ = subprocess.run(["sudo", "sysctl", "-w",
                          "vm.max_map_count=%d" % target]).returncode
    if rc_ != 0:
        print("[run_full_dlp] WARN: could not raise vm.max_map_count (sudo?). "
              "Run manually: sudo sysctl -w vm.max_map_count=%d" % target)
    else:
        try:
            print("[run_full_dlp] vm.max_map_count now %s"
                  % open(path).read().strip())
        except Exception:
            pass


HERE = os.path.dirname(os.path.abspath(__file__))          # zkregplus/src
REPO = os.path.abspath(os.path.join(HERE, "..", ".."))     # new_zkregplus
CFG_DIR = os.path.join(REPO, "data/paper_data/dlp/cfg/config")
LOGS_DIR = os.path.join(REPO, "data/cache/logs")           # log_job_*.txt

# positional args = non-flag tokens, EXCLUDING the value consumed by a
# space-form value flag (e.g. "--jobs 16" -> 16 must not become the runcfg).
VALUE_FLAGS = {"--jobs", "--numa"}
args, _skip = [], False
for a in sys.argv[1:]:
    if _skip:
        _skip = False
        continue
    if a in VALUE_FLAGS:          # "--jobs 16" / "--numa off": consume value
        _skip = True
        continue
    if a.startswith("--"):        # "--jobs=16", "--reset", "--dry-run", ...
        continue
    args.append(a)
DRY = "--dry-run" in sys.argv
RESET = "--reset" in sys.argv
PROBE_RESET = "--probe-reset" in sys.argv     # 64600 reset-vs-cross perc est
JOBS = 8           # default 8 jobs (measured best: 16 saturates mem bandwidth)
for a in sys.argv[1:]:
    if a.startswith("--jobs="):
        JOBS = int(a.split("=", 1)[1])
if "--jobs" in sys.argv:                       # also accept "--jobs N"
    JOBS = int(sys.argv[sys.argv.index("--jobs") + 1])

# NUMA policy applied by THIS runner as a whole-process numactl wrapper (the
# measured-best lever; the Rust per-job pinning is off by default -- it
# fragmented the rayon pool). Default 'socket': confine the 8 jobs to the first
# socket, all-local memory -- ~0.89x the 512GB baseline. Override with --numa=.
NUMA = os.environ.get("ZKR_NUMA", "socket")
for a in sys.argv[1:]:
    if a.startswith("--numa="):
        NUMA = a.split("=", 1)[1]
if "--numa" in sys.argv:                       # also accept "--numa P"
    NUMA = sys.argv[sys.argv.index("--numa") + 1]


def numa_prefix(policy):
    """Whole-process numactl wrapper (measured best). Returns [] when numactl is
    absent, the box is single-NUMA, or policy is off/none/perjob.
      socket     -> pin cores to the FIRST socket's nodes (--cpunodebind only):
                    8 jobs run on one socket; default first-touch keeps memory
                    local -> ~0.89x the 512GB baseline. No --membind, so no 512GB
                    cap (won't OOM on bigger footprints); only spills remote if a
                    socket-0 node actually fills. 16 jobs saturate bandwidth.
      interleave -> --interleave=all (spread across all nodes); only worth it if
                    you genuinely need >1 socket's cores/RAM.
      off/none/perjob -> no numactl (perjob lets the Rust path pin per job)."""
    import shutil
    if policy in ("off", "none", "perjob"):
        return []
    if not shutil.which("numactl"):
        print("[run_full_dlp] numactl not found; NUMA '%s' skipped" % policy)
        return []
    try:
        h = subprocess.run(["numactl", "-H"], capture_output=True,
                           text=True).stdout
        nnodes = max((int(x) for x in re.findall(r"node (\d+) cpus:", h)),
                     default=-1) + 1
    except Exception:
        nnodes = 0
    if nnodes <= 1:
        print("[run_full_dlp] single NUMA node; no policy needed")
        return []
    if policy == "interleave":
        print("[run_full_dlp] NUMA: --interleave=all over %d nodes" % nnodes)
        return ["numactl", "--interleave=all"]
    half = max(1, nnodes // 2)                  # 'socket' (default)
    rng = "0-%d" % (half - 1)
    print("[run_full_dlp] NUMA: pin cores to nodes %s of %d (local first-touch, "
          "no membind cap)" % (rng, nnodes))
    return ["numactl", "--cpunodebind=%s" % rng]

runcfg_name = args[0] if args else "runcfg_full.json"
RUNCFG = runcfg_name if os.path.isabs(runcfg_name) \
    else os.path.join(CFG_DIR, runcfg_name)
if not os.path.isfile(RUNCFG):
    sys.exit("ERROR: runcfg not found: %s" % RUNCFG)
rc = json.load(open(RUNCFG))
if JOBS is not None:
    rc["num_jobs"] = JOBS
if RESET:
    rc["reset"] = True

OUT = "/tmp/full_dlp_run"
TS = datetime.datetime.now().strftime("%Y%m%d_%H%M%S")
os.makedirs(OUT, exist_ok=True)
EFF = os.path.join(OUT, "runcfg_effective_%s.json" % TS)   # patched runcfg
LOG = os.path.join(OUT, "run_%s.log" % TS)                 # dump.txt
SUM = os.path.join(OUT, "summary_%s.txt" % TS)
TAR = "/tmp/full_dlp_artifacts_%s.tar.gz" % TS
json.dump(rc, open(EFF, "w"), indent=2)

env = dict(os.environ)
env.setdefault("RUSTFLAGS", "-C link-args=-fuse-ld=lld -Awarnings")
env["ZKR_DLP_RUNCFG"] = EFF
# Rust per-job pinning only when policy is 'perjob'; otherwise off (we use the
# whole-process numactl wrapper instead -- the Rust pinning fragmented the pool).
env["ZKR_NUMA"] = "perjob" if NUMA == "perjob" else "off"
env.setdefault("ZKR_DC_THREADS", "8")
if PROBE_RESET:
    env["ZKR_PROBE_64600"] = "1"   # per-file old cross-chunk vs new reset est
    env["ZKR_PROBE_64601"] = "1"   # exact per-rung perc demand (64601.3)

time_prefix = ["/usr/bin/time", "-v"] if os.path.exists("/usr/bin/time") else []
# numactl wraps cargo (children inherit the policy); time stays outermost for RSS.
cmd = time_prefix + numa_prefix(NUMA) + ["cargo", "test", "-p", "zkregplus",
    "--release", "--",
    "zkp_driver::tests_zkp_driver::full_dlp", "--exact", "--nocapture"]

def repo(p):  return os.path.join(REPO, p) if p else None
artifacts = [EFF,
    repo(rc.get("config_out")),
    os.path.join(REPO, rc.get("config_dir", ""), "config", "needs_dist.txt")]

print("[run_full_dlp] REPO   =", REPO)
print("[run_full_dlp] RUNCFG =", RUNCFG, "(jobs=%s reset=%s numa=%s)"
      % (rc.get("num_jobs"), rc.get("reset"), NUMA))
print("[run_full_dlp] LOG    =", LOG)
print("[run_full_dlp] cmd    =", " ".join(cmd))
print("[run_full_dlp] cache  =", rc.get("cache_dir"),
      "(first run builds it from regex, ~0.5hr)")
print("[run_full_dlp] vm.max_map_count target =", VMA_TARGET or "skip")
if DRY:
    print("[run_full_dlp] --dry-run: not executing.")
    sys.exit(0)

ensure_vma(VMA_TARGET)
t0 = time.time()
with open(LOG, "w") as lf:
    lf.write("# %s host=%s cpu=%s\n# cmd=%s\n# runcfg=%s\n\n" % (
        datetime.datetime.now(), platform.node(), os.cpu_count(),
        " ".join(cmd), json.dumps(rc)))
    lf.flush()
    p = subprocess.Popen(cmd, cwd=REPO, env=env, stdout=subprocess.PIPE,
                         stderr=subprocess.STDOUT, text=True)
    for line in p.stdout:
        sys.stdout.write(line); lf.write(line); lf.flush()
    p.wait()
    code = p.returncode
wall = time.time() - t0

# ---- summary ----
def grep(pats):
    out = []
    for l in open(LOG, errors="replace"):
        if any(pat in l for pat in pats):
            out.append(l.rstrip("\n"))
    return out
agg = {}
for l in open(LOG, errors="replace"):
    if "prove_step cost: i:" in l:
        m = re.search(r"circ_id: (\d+).*stmt_len: (\d+).*wtns size: (\d+) (\d+) ms", l)
        if m:
            c = int(m.group(1)); d = agg.setdefault(c, [0, 0, 0, 0])
            d[0] += 1; d[1] += int(m.group(4))
            d[2] = int(m.group(2)); d[3] = int(m.group(3))
git = subprocess.run(["git", "rev-parse", "HEAD"], cwd=REPO,
                     capture_output=True, text=True).stdout.strip()
with open(SUM, "w") as s:
    s.write("host=%s cpu=%s exit=%s wall_s=%.1f\n" % (
        platform.node(), os.cpu_count(), code, wall))
    s.write("git=%s\nruncfg=%s\n\n" % (git, json.dumps(rc)))
    for l in grep(["PERF WORKFLOW", "PROGRESS step", "PROGRESS fold",
                   "ladder:", "PERF 1002", "cs1e", "KEYS info",
                   "Maximum resident set size", "Killed",
                   "Out of memory", "panicked", "test result",
                   "64600.1", "64601.3", "Job", "CapErr"]):
        s.write(l + "\n")
    s.write("\n-- per-circuit fold step cost --\n")
    for c in sorted(agg):
        n, ms, st, wt = agg[c]
        s.write("circ%d: steps=%d stmt_len=%d wtns=%d avg=%.0fms total=%.1fs\n"
                % (c, n, st, wt, ms / max(n, 1), ms / 1000.0))
print("\n" + open(SUM).read())

# ---- pack (always): artifacts + per-job logs + run log ----
with tarfile.open(TAR, "w:gz") as t:
    for f in artifacts + [LOG, SUM]:
        if f and os.path.isfile(f):
            t.add(f, arcname=os.path.basename(f))
    for jf in sorted(glob.glob(os.path.join(LOGS_DIR, "log_job_*.txt"))):
        t.add(jf, arcname="logs/" + os.path.basename(jf))
print("[run_full_dlp] packed -> %s  (exit=%s, wall=%.0fs)" % (TAR, code, wall))
sys.exit(0)
