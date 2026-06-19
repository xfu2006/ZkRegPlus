#!/usr/bin/env python3
"""Run full_dlp (split + cached discharge/ladder + multi-job fold) and
pack all artifacts. Repo root resolved from this file, so cwd is free.

Usage:
  python3 run_full_dlp.py [runcfg] [--jobs N] [--reset] [--dry-run]
    runcfg     : path or name under data/paper_data/dlp/cfg/config/
                 (default runcfg_full.json)
    --jobs N   : override num_jobs in the runcfg for this run
    --reset    : override reset=true (recompute split/discharge/ladder)
    --dry-run  : print resolved paths + command, do not run cargo.

Env:  ZKR_DC_THREADS  determine_config probe threads (default 8)

Output (always packed, even on OOM/panic):
  /tmp/full_dlp_artifacts_<ts>.tar.gz
    {effective runcfg, ladder json, needs_dist.txt, run log (dump.txt),
     per-job log_job_*.txt, summary}
"""
import os, sys, subprocess, time, datetime, tarfile, json, platform, re, glob

HERE = os.path.dirname(os.path.abspath(__file__))          # zkregplus/src
REPO = os.path.abspath(os.path.join(HERE, "..", ".."))     # new_zkregplus
CFG_DIR = os.path.join(REPO, "data/paper_data/dlp/cfg/config")
LOGS_DIR = os.path.join(REPO, "data/cache/logs")           # log_job_*.txt

args = [a for a in sys.argv[1:] if not a.startswith("--")]
DRY = "--dry-run" in sys.argv
RESET = "--reset" in sys.argv
JOBS = None
for a in sys.argv[1:]:
    if a.startswith("--jobs="):
        JOBS = int(a.split("=", 1)[1])
if "--jobs" in sys.argv:                       # also accept "--jobs N"
    JOBS = int(sys.argv[sys.argv.index("--jobs") + 1])

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
env.setdefault("ZKR_DC_THREADS", "8")

time_prefix = ["/usr/bin/time", "-v"] if os.path.exists("/usr/bin/time") else []
cmd = time_prefix + ["cargo", "test", "-p", "zkregplus", "--release", "--",
    "zkp_driver::tests_zkp_driver::full_dlp", "--exact", "--nocapture"]

def repo(p):  return os.path.join(REPO, p) if p else None
artifacts = [EFF,
    repo(rc.get("config_out")),
    os.path.join(REPO, rc.get("config_dir", ""), "config", "needs_dist.txt")]

print("[run_full_dlp] REPO   =", REPO)
print("[run_full_dlp] RUNCFG =", RUNCFG, "(jobs=%s reset=%s)"
      % (rc.get("num_jobs"), rc.get("reset")))
print("[run_full_dlp] LOG    =", LOG)
print("[run_full_dlp] cmd    =", " ".join(cmd))
print("[run_full_dlp] cache  =", rc.get("cache_dir"),
      "(first run builds it from regex, ~0.5hr)")
if DRY:
    print("[run_full_dlp] --dry-run: not executing.")
    sys.exit(0)

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
                   "Out of memory", "panicked", "test result"]):
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
