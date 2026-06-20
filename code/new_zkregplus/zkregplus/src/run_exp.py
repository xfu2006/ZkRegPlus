#!/usr/bin/env python3
"""Run full_dlp_sample (determine + fold) and pack all artifacts for analysis.

Resolves the repo root from THIS file's location, so it works no matter the
cwd (run it from zkregplus/src, the repo root, or anywhere).

Usage:
  python3 run_exp.py [runcfg_name] [--dry-run]
    runcfg_name : a file under data/debug/full_dlp_sample/ (default
                  runcfg_exp.json)
    --dry-run   : print resolved paths + command, do not run cargo.

Env:
  ZKR_DC_THREADS   thread count (default 8)
  ZKR_EXP_SKIP_FAIL passed through if set (drop non-foldable from the fold)
  ZKR_VM_MAX_MAP_COUNT  target vm.max_map_count (default 8388608 = 8M; 0
                  skips). Raised via `sudo sysctl` before the run so
                  mimalloc's many small mappings don't hit the VMA ceiling
                  and SIGABRT the decider with a tiny-alloc failure while
                  RAM is free.

Output (always packed, even on OOM/panic):
  data/debug/full_dlp_sample/exp_out/artifacts_<ts>.tar.gz
    {runcfg, ladder json, needs_dist.txt, fold report, scan list, run log,
     summary} -- summary has per-rung r1cs/cs1e/max_pp, per-circuit fold step
    cost, peak RSS, wall, exit code.

Server (Jetstream2): git pull, then `python3 zkregplus/src/run_exp.py`.
First run builds the DB cache from the in-git regex (~0.5hr), then reuses it.
"""
import os, sys, subprocess, time, datetime, tarfile, json, platform, re, shutil

HERE = os.path.dirname(os.path.abspath(__file__))          # .../zkregplus/src
REPO = os.path.abspath(os.path.join(HERE, "..", ".."))     # .../new_zkregplus
CFG_REL = "data/debug/full_dlp_sample"
CFG_DIR = os.path.join(REPO, CFG_REL)

FLAGS = {"--dry-run", "--fsm-dist", "--probe-fwd", "--probe-route",
         "--probe-caps", "--log6"}
args = [a for a in sys.argv[1:] if a not in FLAGS]
DRY = "--dry-run" in sys.argv
# --fsm-dist: determine-only (ZKR_FSM_DIST=1) -- builds the ladder + the real
# fwd queue (CapacityPlanner) but RETURNS before the fold, so it fits locally
# (no 119M-lkup OOM). --probe-fwd: 64300 estimate-vs-real probe.
# --probe-route: 64212 per-seg rung-FAIL probe (which cap flips a chunk up).
# --probe-caps: 64400 per-rung member breakdown (why perc/avg_act so high).
# --log6: LOG6 per-gadget constraint breakdown at preprocess (which gadget
#   bloats each rung). Verbose -- kill the run after the per-rung breakdown.
FSM_DIST = "--fsm-dist" in sys.argv
PROBE_FWD = "--probe-fwd" in sys.argv
PROBE_ROUTE = "--probe-route" in sys.argv
PROBE_CAPS = "--probe-caps" in sys.argv
LOG6 = "--log6" in sys.argv
runcfg_name = args[0] if args else "runcfg_exp.json"
RUNCFG = os.path.join(CFG_DIR, runcfg_name)
OUT = "/tmp/full_dlp_exp"                                   # logs + summary
TS = datetime.datetime.now().strftime("%Y%m%d_%H%M%S")
LOG = os.path.join(OUT, "run_%s.log" % TS)
SUM = os.path.join(OUT, "summary_%s.txt" % TS)
TAR = "/tmp/full_dlp_exp_artifacts_%s.tar.gz" % TS          # tarball in /tmp
VMA_TARGET = int(os.environ.get("ZKR_VM_MAX_MAP_COUNT", "8388608"))  # 0=skip


def ensure_vma(target):
    """Best-effort raise vm.max_map_count (VMA ceiling). mimalloc frees RAM
    via many small OS mappings; the 204M-constraint decider can exhaust the
    default 1048576 and SIGABRT on a tiny alloc while RAM is free. Non-fatal."""
    if target <= 0:
        return
    path = "/proc/sys/vm/max_map_count"
    try:
        cur = int(open(path).read().strip())
    except Exception as e:
        print("[run_exp] vm.max_map_count: cannot read (%s); skip" % e)
        return
    if cur >= target:
        print("[run_exp] vm.max_map_count=%d already >= %d" % (cur, target))
        return
    print("[run_exp] vm.max_map_count=%d < %d; raising via sudo sysctl"
          % (cur, target))
    rc_ = subprocess.run(["sudo", "sysctl", "-w",
                          "vm.max_map_count=%d" % target]).returncode
    if rc_ != 0:
        print("[run_exp] WARN: could not raise vm.max_map_count (sudo?). "
              "Run manually: sudo sysctl -w vm.max_map_count=%d" % target)
    else:
        try:
            print("[run_exp] vm.max_map_count now %s"
                  % open(path).read().strip())
        except Exception:
            pass

if not os.path.isfile(RUNCFG):
    sys.exit("ERROR: runcfg not found: %s" % RUNCFG)
rc = json.load(open(RUNCFG))

env = dict(os.environ)
env.setdefault("RUSTFLAGS", "-C link-args=-fuse-ld=lld -Awarnings")
env["ZKR_DLP_RUNCFG"] = RUNCFG
env.setdefault("ZKR_DC_THREADS", "8")
if FSM_DIST:
    env["ZKR_FSM_DIST"] = "1"        # determine-only (skip the fold)
if PROBE_FWD:
    env["ZKR_PROBE_64300"] = "1"     # fwd-queue estimate-vs-real probe
if PROBE_ROUTE:
    env["ZKR_PROBE_64212"] = "1"     # per-seg rung-FAIL (which cap flips up)
if PROBE_CAPS:
    env["ZKR_PROBE_CAPS"] = "1"      # per-rung member breakdown (64400)
if LOG6:
    env["ZKR_LOG6"] = "1"            # per-gadget constraint breakdown

time_prefix = ["/usr/bin/time", "-v"] if os.path.exists("/usr/bin/time") else []
cmd = time_prefix + ["cargo", "test", "-p", "zkregplus", "--release", "--",
    "zkp_driver::tests_zkp_driver::full_dlp_sample", "--exact", "--nocapture"]

# artifacts to pack: config_out/report_out are repo-root-relative; scan_file is
# config_dir-relative; needs_dist.txt is written by the Rust to config/.
def repo(p):  return os.path.join(REPO, p) if p else None
def cfg(p):   return os.path.join(CFG_DIR, p) if p else None
artifacts = [RUNCFG,
    repo(rc.get("config_out")),
    repo(rc.get("report_out")),
    cfg(rc.get("scan_file")),
    os.path.join(CFG_DIR, "config", "needs_dist.txt")]

print("[run_exp] REPO   =", REPO)
print("[run_exp] RUNCFG =", RUNCFG)
print("[run_exp] LOG    =", LOG)
print("[run_exp] cmd    =", " ".join(cmd))
print("[run_exp] cache  = %s (first run builds it from regex, ~0.5hr)"
      % rc.get("cache_dir"))
print("[run_exp] artifacts:", [a for a in artifacts if a])
print("[run_exp] vm.max_map_count target =", VMA_TARGET or "skip")
if DRY:
    print("[run_exp] --dry-run: not executing.")
    sys.exit(0)

ensure_vma(VMA_TARGET)
os.makedirs(OUT, exist_ok=True)
t0 = time.time()
with open(LOG, "w") as lf:
    lf.write("# %s  host=%s cpu=%s\n# cmd=%s\n# runcfg=%s\n\n" % (
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
    for l in grep(["ladder:", "peel rung0'", "PERF 1002", "cs1e_pp",
                   "KEYS info", "gen_step_cs step 3", "gen_cs step 3.2",
                   "Maximum resident set size", "Killed",
                   "Out of memory", "panicked", "test result",
                   "64300.TALLY", "64300.BAD", "64400.rung",
                   "after msg3 of module"]):
        s.write(l + "\n")
    s.write("\n-- per-circuit fold step cost --\n")
    for c in sorted(agg):
        n, ms, st, wt = agg[c]
        s.write("circ%d: steps=%d stmt_len=%d wtns=%d avg=%.0fms total=%.1fs\n"
                % (c, n, st, wt, ms / max(n, 1), ms / 1000.0))
print("\n" + open(SUM).read())

# ---- pack (always): artifacts + full run log (as dump.txt) + summary ----
with tarfile.open(TAR, "w:gz") as t:
    for f in artifacts:
        if f and os.path.isfile(f):
            t.add(f, arcname=os.path.basename(f))
    if os.path.isfile(LOG):
        t.add(LOG, arcname="dump.txt")
    if os.path.isfile(SUM):
        t.add(SUM, arcname=os.path.basename(SUM))
print("[run_exp] packed -> %s  (exit=%s, wall=%.0fs)" % (TAR, code, wall))
sys.exit(0)
