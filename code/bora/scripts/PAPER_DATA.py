#!/usr/bin/env python3
# ---------------------------------------------------------------------
# PAPER_DATA.py -- one-shot paper-data runner for bora.
#
# A 4-item menu of the runs behind the paper's numbers.  Standalone:
# it RE-implements the four flows (does not import run_*.py), anchored
# on this file so it runs from the repo root regardless of cwd:
#
#   (1) small data    light-test demo (ships its own config).
#   (2) full dna set   single-job ZK discharge of the chr17 sample.
#   (3) full clamav    8-job (4+4) two-process NUMA prod run.
#   (4) full dlp set   8-job (4+4) two-process NUMA prod run.
#
# Run from the repo root (self-detaches into the background; survives
# logout, so nohup is NOT needed):
#   python3 PAPER_DATA.py --run clam    detach immediately, run clam
#   python3 PAPER_DATA.py               show menu, pick, then detach
#   python3 PAPER_DATA.py --run clam --no-daemon   stay in foreground
# Follow a detached run with: tail -f <the daemon-log path it prints>.
#
# CONTRACT: every run ALWAYS packs exactly ONE download bundle
#   /tmp/paper_data_<key>_<ts>/paper_data_<key>_BUNDLE_<ts>.tgz
# on success, panic, OOM, Ctrl-C, or TERM (only `kill -9` skips it).
# Lessons carried from one_time_numa_test_dlp.sh: always-pack finalizer,
# process-tree kill on signal, verify-before-wipe preflight, and a
# greppable failure-signature scan in the summary.
#
# NOTE: python file generated under the instruction of paper author;
#   code reviewed and tested manually by paper author.
# ---------------------------------------------------------------------

import argparse
import datetime
import glob
import os
import platform
import re
import shutil
import signal
import subprocess
import sys
import tarfile
import threading
import time

# =====================================================================
# paths (anchored on this file; cwd never matters) + tunables
# =====================================================================

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))  # bora (scripts/ -> root)
LOGS_DIR = os.path.join(REPO, "data/cache/logs")        # Rust log_job_*.txt
OUT_ROOT = "/tmp"                                        # per-run bundle dir

# shared snark-gate flag: proc2's decider blocks until this file appears.
FLAG_DIR = "/tmp/snark_start"
FLAG = os.path.join(FLAG_DIR, "flag")

# vm.max_map_count target (the VMA ceiling).  The fold frees RAM via many
# small mimalloc mappings and can SIGABRT on a tiny alloc with free RAM if
# the default 1048576 is hit.  Raised via `sudo sysctl`; 0 = skip.
VMA_TARGET = int(os.environ.get("ZKR_VM_MAX_MAP_COUNT", "1073741824"))

# two-half stagger gate: start part2 only after part1 has run >= DELAY s
# AND its tree-RSS has dropped below RAM_GB (or part1 has exited), so the
# two halves do not hit their fold RAM peak at the same time.
PART2_DELAY = 900
PART2_RAM_GB = 500.0

RUSTFLAGS_DEFAULT = "-C link-args=-fuse-ld=lld -Awarnings"
CARGO_TEST = ["cargo", "test", "-p", "zkregplus", "--release", "--"]

# ---- (3) full clamav config -----------------------------------------
CLAM_CFG_DIR = os.path.join(REPO, "data/debug/full_clamav/config")
CLAM_MAIN_SIG = os.path.join(CLAM_CFG_DIR, "main.dat")   # DB source sig
CLAM_REPORT = os.path.join(REPO,
                           "data/debug/full_clamav/reports/report2.dat")
CLAM_DB_DIR = os.path.join(REPO, "data/cache/full_data")  # rebuildable DB
CLAM_SNARK_DIR = os.path.join(REPO, "data/cache/full_clamav")  # g16 keys
CLAM_TEST = "zkp_driver::tests_zkp_driver::full_clam"
CLAM_SNARK_JOB = 3               # which of proc2's local jobs 0-3 proves
CLAM_REBUILD_TIMEOUT = 18000     # DB-rebuild gate cap (s)
# clam_db::cache_exists set -- gate the DB-ready check on all of these.
CLAM_DB_FILES = [
    "vec_sigs.txt", "vec_crit_pat.txt", "vec_crit_pat_igc.txt",
    "vec_bag_words.txt", "vec_bag_words_igc.txt", "map_crit_pat.txt",
    "map_crit_pat_igc.txt", "dfa_crit.txt", "dfa_crit_igc.txt",
    "sig_to_id.txt", "lkup.txt", "bundle_subsig.txt",
    "bundle_subsig_igc.txt",
]

# ---- (4) full dlp config --------------------------------------------
DLP_CFG_DIR = os.path.join(REPO, "data/paper_data/dlp/cfg/config")
DLP_RUNCFG = os.path.join(DLP_CFG_DIR, "runcfg_full.json")
DLP_REPORT_DIR = os.path.join(REPO, "data/paper_data/dlp/report")
DLP_TEST = "zkp_driver::tests_zkp_driver::full_dlp"

# ---- (2) full dna / (1) small data config ---------------------------
DNA_TEST = "zkp_driver::tests_zkp_driver::test_full_dna"
DNA_REPORT = os.path.join(REPO, "data/paper_data/dna/reports/report_zk.dat")
SMALL_TEST = "zkp_driver::tests_zkp_driver::test_zkreg_main"
SMALL_REPORT = os.path.join(REPO, "data/small_data_set/reports/report.dat")

# ---- run-shape toggles (defaults reproduce each driver's prod default;
#      flip via the CLI flags wired up in main()) ----------------------
CLAM_WIPE_DB = True      # prod default: wipe+rebuild the ~40GB DB
CLAM_FOLD_ONLY = False   # prod default: proc2 emits ONE verified proof
DLP_EMIT_PROOF = False   # prod default: fold-only, no decider/proof
# Job count is FIXED at 8 and is NOT configurable (no CLI flag): the
# paper's two-process NUMA scheme is exactly 4+4, clam is bound to its 8
# binexec_p0..p7 manifests, and the two-half split assumes N/2==4.  8 is
# an invariant of both the clam and dlp runs -- do not change it.
JOBS = 8
DRY = False              # --dry-run: print the plan, spawn nothing

# failure signatures scanned into every SUMMARY.txt.
FAIL_RE = re.compile(
    r"panic|panicked|SIGABRT|Killed|out of memory|cannot allocate|"
    r"CapErr|FATAL|error\[|VERIFICATION FAILED|SPLIT VERIFY: FAIL")


# =====================================================================
# tiny logging + process-tree bookkeeping
# =====================================================================

_CHILDREN = []           # live Popen handles, reaped on signal/exit


def log(msg):
    """Timestamped line to stdout (nohup.out under nohup)."""
    print("[paper_data %s] %s" % (
        datetime.datetime.now().strftime("%H:%M:%S"), msg), flush=True)


def _terminate_all():
    """TERM each tracked child's whole process group (start_new_session
    gives every child its own group, so this reaps numactl+cargo+test)."""
    for p in _CHILDREN:
        try:
            if p.poll() is None:
                os.killpg(os.getpgid(p.pid), signal.SIGTERM)
        except (ProcessLookupError, PermissionError, OSError):
            pass


def _on_signal(signum, _frame):
    """INT/TERM -> stop the child tree, then raise so the runner's finally
    still builds the bundle (the always-pack lesson)."""
    log("SIGNAL %d caught -> stopping children; bundle will still pack"
        % signum)
    _terminate_all()
    raise SystemExit(128 + signum)


# =====================================================================
# preflight helpers: vm.max_map_count + NUMA topology
# =====================================================================

def ensure_vma(target):
    """Best-effort raise vm.max_map_count via sudo sysctl.  Non-fatal:
    prints the manual command if sudo is unavailable."""
    if target <= 0 or DRY:
        return
    path = "/proc/sys/vm/max_map_count"
    try:
        cur = int(open(path).read().strip())
    except OSError as e:
        log("vm.max_map_count: cannot read (%s); skip" % e)
        return
    if cur >= target:
        log("vm.max_map_count=%d already >= %d" % (cur, target))
        return
    log("vm.max_map_count=%d < %d; raising via sudo sysctl" % (cur, target))
    rc = subprocess.run(
        ["sudo", "sysctl", "-w", "vm.max_map_count=%d" % target]).returncode
    if rc != 0:
        log("WARN: could not raise vm.max_map_count (sudo?). Run manually: "
            "sudo sysctl -w vm.max_map_count=%d" % target)


def nnodes():
    """NUMA node count from `numactl -H` (1 if numactl absent/single-node)."""
    if not shutil.which("numactl"):
        return 1
    try:
        out = subprocess.run(["numactl", "-H"], capture_output=True,
                             text=True).stdout
    except OSError:
        return 1
    n = len(re.findall(r"^node (\d+) cpus:", out, re.M))
    return n or 1


def half_ranges():
    """Split the nodes in two: ("0-3", "4-7") on an 8-node box.  Returns
    (None, None) on <2 nodes so the run degrades to plain two-process."""
    n = nnodes()
    if n < 2:
        return None, None
    h = n // 2
    return "0-%d" % (h - 1), "%d-%d" % (h, n - 1)


def numa_prefix(nodes):
    """numactl wrapper: HARD cpu pin (--cpunodebind) + SOFT memory pin
    (--preferred-many, spills instead of OOM).  [] when not applicable."""
    if not nodes or not shutil.which("numactl"):
        return []
    return ["numactl", "--cpunodebind=%s" % nodes,
            "--preferred-many=%s" % nodes]


# ---- tree RSS (sum VmRSS over a process and all its descendants) -----

def _ppid(pid):
    try:
        line = open("/proc/%d/stat" % pid).read()
        return int(line[line.rfind(")") + 2:].split()[1])
    except (OSError, IndexError, ValueError):
        return 0


def _vmrss_kb(pid):
    try:
        for ln in open("/proc/%d/status" % pid):
            if ln.startswith("VmRSS:"):
                return int(ln.split()[1])
    except OSError:
        pass
    return 0


def tree_rss_gb(root_pid):
    """Sum VmRSS across every pid whose parent chain reaches root_pid."""
    total = 0
    for entry in os.listdir("/proc"):
        if not entry.isdigit():
            continue
        pid, hops = int(entry), 0
        while pid > 1 and hops < 64:
            if pid == root_pid:
                total += _vmrss_kb(int(entry))
                break
            pid = _ppid(pid)
            hops += 1
    return total / (1024.0 * 1024.0)


# =====================================================================
# subprocess launch (live-pumped to a per-part log) + env builders
# =====================================================================

class _DryProc:
    """Stand-in returned by spawn() under --dry-run."""
    returncode = 0
    pid = os.getpid()

    def poll(self):
        return 0

    def wait(self):
        return 0


def base_rust_env():
    e = dict(os.environ)
    e.setdefault("RUSTFLAGS", RUSTFLAGS_DEFAULT)
    return e


def spawn(cmd, env, log_path, label):
    """Launch one process (cwd=REPO, own session group), pumping its merged
    stdout live to console and log_path.  Returns (proc, pump_thread)."""
    log("%s: %s" % (label, " ".join(cmd)))
    if DRY:
        return _DryProc(), None
    lf = open(log_path, "w")
    lf.write("# %s host=%s label=%s\n# cmd=%s\n\n" % (
        datetime.datetime.now(), platform.node(), label, " ".join(cmd)))
    lf.flush()
    p = subprocess.Popen(cmd, cwd=REPO, env=env, stdout=subprocess.PIPE,
                         stderr=subprocess.STDOUT, text=True,
                         start_new_session=True)
    _CHILDREN.append(p)

    def pump():
        for line in p.stdout:
            sys.stdout.write("[%s] %s" % (label, line))
            lf.write(line)
            lf.flush()
        lf.close()

    t = threading.Thread(target=pump, daemon=True)
    t.start()
    return p, t


def clam_env(read_mode, fold_only, one_proof, wait_flag, tag):
    """full_clam per-process env.  The only job-split knob is READ_MODE
    (full|first|second); ZKR_NUMA=off leaves pinning to numactl."""
    e = base_rust_env()
    e["ZKR_NUMA"] = "off"
    e["ZKR_CLAM_READ_MODE"] = read_mode
    e["ZKR_CLAM_PCT"] = "100"
    e["ZKR_CLAM_FOLD_ONLY"] = "1" if fold_only else "0"
    e["ZKR_CLAM_ONE_PROOF"] = "1" if one_proof else "0"
    e["ZKR_SNARK_JOB_ID"] = str(CLAM_SNARK_JOB)
    e["ZKR_CLAM_CHECK_LKUP"] = "1"        # valid at pct=100
    if wait_flag:
        e["ZKR_SNARK_WAIT_FLAG"] = wait_flag
    else:
        e.pop("ZKR_SNARK_WAIT_FLAG", None)
    e["ZKR_LOG_TAG"] = tag
    return e


def dlp_env(read_mode, fold_only, one_proof, wait_flag, tag):
    """full_dlp per-process env.  RUNCFG carries num_jobs; READ_MODE picks
    the job half; ZKR_NUMA=off leaves pinning to numactl."""
    e = base_rust_env()
    e["ZKR_NUMA"] = "off"
    e["ZKR_DLP_RUNCFG"] = _DLP_EFF
    e["ZKR_DLP_PCT"] = "100"
    e["ZKR_DLP_READ_MODE"] = read_mode
    e["ZKR_DLP_FOLD_ONLY"] = "1" if fold_only else "0"
    e["ZKR_DLP_ONE_PROOF"] = "1" if one_proof else "0"
    e["ZKR_DLP_PROBE_FILES"] = "1"
    e.setdefault("ZKR_DC_THREADS", "8")
    if wait_flag:
        e["ZKR_SNARK_WAIT_FLAG"] = wait_flag
    else:
        e.pop("ZKR_SNARK_WAIT_FLAG", None)
    e["ZKR_LOG_TAG"] = tag
    e.pop("ZKR_DLP_LADDER_ONLY", None)
    return e


# =====================================================================
# bundle / summary (the always-pack finalizer)
# =====================================================================

def _gz_one(path):
    """Wrap a single file as <path>.tgz (gzip -9)."""
    if not os.path.isfile(path):
        return None
    out = path + ".tgz"
    with tarfile.open(out, "w:gz", compresslevel=9) as t:
        t.add(path, arcname=os.path.basename(path))
    return out


class RunContext:
    """Per-run scratch + the always-pack finalizer.  Runners append their
    logs / job-log globs / reports / notes / per-part return codes; bundle()
    packs exactly one download tgz and is safe to call after any failure."""

    def __init__(self, key):
        self.key = key
        self.ts = datetime.datetime.now().strftime("%Y%m%d_%H%M%S")
        self.out = os.path.join(OUT_ROOT,
                                "paper_data_%s_%s" % (key, self.ts))
        os.makedirs(self.out, exist_ok=True)
        self.run_logs = []       # raw driver-side run logs
        self.job_globs = []      # LOGS_DIR patterns for per-job logs
        self.reports = []        # extra files (reports, effective cfg)
        self.rc = {}             # label -> returncode
        self.note = []           # summary lines (mode/toggles/verdict)
        self.t0 = time.time()

    def log_path(self, name):
        return os.path.join(self.out, "%s_%s.log" % (name, self.ts))

    def _fail_lines(self):
        srcs = list(self.run_logs)
        for g in self.job_globs:
            srcs += glob.glob(os.path.join(LOGS_DIR, g))
        out = []
        for s in srcs:
            if os.path.isfile(s):
                for ln in open(s, errors="replace"):
                    if FAIL_RE.search(ln):
                        out.append(ln.rstrip("\n"))
        return out

    def bundle(self, overall_rc):
        """Write SUMMARY.txt and pack ONE bundle tgz.  Always safe."""
        wall = time.time() - self.t0
        summ = os.path.join(self.out, "SUMMARY_%s.txt" % self.ts)
        try:
            fails = self._fail_lines()
        except Exception as e:                        # never block packing
            fails = ["(fail-scan error: %s)" % e]
        with open(summ, "w") as f:
            f.write("PAPER_DATA -- %s\n" % self.key)
            f.write("host=%s ts=%s end=%s\n" % (
                platform.node(), self.ts,
                datetime.datetime.now().strftime("%Y%m%d_%H%M%S")))
            f.write("overall_rc=%s wall_s=%.1f\n" % (overall_rc, wall))
            f.write("part_rc=%s\n" % self.rc)
            for ln in self.note:
                f.write(ln + "\n")
            f.write("\n== failure signatures (last 40) ==\n")
            f.write(("\n".join(fails[-40:]) or "(none)") + "\n")
        bundle = os.path.join(self.out,
                              "paper_data_%s_BUNDLE_%s.tgz" % (
                                  self.key, self.ts))
        try:
            with tarfile.open(bundle, "w:gz", compresslevel=6) as t:
                t.add(summ, arcname="SUMMARY.txt")
                for lg in self.run_logs:
                    gz = _gz_one(lg)
                    if gz:
                        t.add(gz, arcname="logs/" + os.path.basename(gz))
                seen = set()
                for g in self.job_globs:
                    for jf in sorted(glob.glob(
                            os.path.join(LOGS_DIR, g))):
                        if jf not in seen:
                            seen.add(jf)
                            t.add(jf, arcname="logs/" +
                                  os.path.basename(jf))
                for rp in self.reports:
                    if rp and os.path.isfile(rp):
                        t.add(rp, arcname=os.path.basename(rp))
        except Exception as e:
            log("WARN: bundle pack failed: %s" % e)
            return None
        log("BUNDLE READY (download this ONE file): %s" % bundle)
        try:
            log("  " + subprocess.run(["ls", "-la", bundle],
                                      capture_output=True,
                                      text=True).stdout.strip())
        except OSError:
            pass
        print("\n----- SUMMARY (also inside the bundle) -----")
        print(open(summ).read())
        return bundle


# =====================================================================
# two-half NUMA engine (shared by clam + dlp)
# =====================================================================

def _wait_stagger(p1):
    """Hold until part1 has run >= PART2_DELAY s AND its tree-RSS has
    dropped below PART2_RAM_GB (or part1 exits)."""
    log("part2 gate: t>=%ds AND part1 RSS<%.0fGB (or part1 exit)"
        % (PART2_DELAY, PART2_RAM_GB))
    waited = 0
    while p1.poll() is None:
        rss = tree_rss_gb(p1.pid)
        if waited >= PART2_DELAY and rss < PART2_RAM_GB:
            break
        if waited % 60 == 0:
            log("waiting part2: t=%ds rss=%.0fGB" % (waited, rss))
        time.sleep(10)
        waited += 10


def _clam_db_ready():
    if not all(os.path.isfile(os.path.join(CLAM_DB_DIR, f))
               for f in CLAM_DB_FILES):
        return False
    return True


def _clam_wait_db(p1):
    """Block until part1 rebuilt+saved full_data (all files present AND
    lkup.txt size stable across two 10s polls), part1 exits, or timeout.
    RSS can't distinguish 'rebuilding' from 'done' -> gate on files."""
    log("DB gate: waiting for part1 to rebuild full_data (%d files + "
        "lkup.txt stable); cap=%ds"
        % (len(CLAM_DB_FILES), CLAM_REBUILD_TIMEOUT))
    lk = os.path.join(CLAM_DB_DIR, "lkup.txt")
    waited, last = 0, -1
    while True:
        if p1.poll() is not None:
            return "p1_exit"
        if waited >= CLAM_REBUILD_TIMEOUT:
            return "timeout"
        if _clam_db_ready():
            sz = os.path.getsize(lk)
            if sz > 0 and sz == last:
                return "ready"
            last = sz
        if waited % 60 == 0:
            log("DB gate: t=%ds ready=%s" % (waited, _clam_db_ready()))
        time.sleep(10)
        waited += 10


def run_two_half(ctx, spec):
    """Fold jobs 0..h-1 in part1 (nodes a) and h..N-1 in part2 (nodes b),
    staggered so their RAM peaks don't overlap.  part2 optionally runs the
    single decider, released by the snark flag once part1 frees its RAM.
    spec keys: test, env_fn, p1_read, p2_read, part2_proves, pre_part2,
    report (part2 only)."""
    a, b = half_ranges()
    log("part1 nodes=%s ; part2 nodes=%s ; flag=%s ; snark=%s"
        % (a, b, FLAG, "part2" if spec["part2_proves"] else "no"))
    shutil.rmtree(FLAG_DIR, ignore_errors=True)
    cargo = CARGO_TEST + [spec["test"], "--exact", "--nocapture"]
    log1, log2 = ctx.log_path("part1"), ctx.log_path("part2")
    ctx.run_logs += [log1, log2]
    ctx.job_globs += ["log_job_p1_*.txt", "log_job_p2_*.txt"]

    env1 = spec["env_fn"](spec["p1_read"], fold_only=True, one_proof=False,
                          wait_flag=None, tag="p1_")
    p2_fold_only = not spec["part2_proves"]
    env2 = spec["env_fn"](spec["p2_read"], fold_only=p2_fold_only,
                          one_proof=not p2_fold_only,
                          wait_flag=None if p2_fold_only else FLAG,
                          tag="p2_")
    if DRY:
        spawn(numa_prefix(a) + cargo, env1, log1, "part1")
        spawn(numa_prefix(b) + cargo, env2, log2, "part2")
        log("--dry-run: not executing.")
        return 0

    p1 = p2 = t1 = t2 = None
    try:
        p1, t1 = spawn(numa_prefix(a) + cargo, env1, log1, "part1")
        if spec["pre_part2"]:
            st = spec["pre_part2"](p1)
            if st != "ready":
                log("DB gate: part1 %s before DB ready -> abort" % st)
                ctx.note.append("db_gate=%s (abort)" % st)
                _terminate_all()
                p1.wait()
                ctx.rc["part1"] = p1.returncode
                return 4
            log("DB gate: full_data ready; part1 now folding")
        _wait_stagger(p1)
        p2, t2 = spawn(numa_prefix(b) + cargo, env2, log2, "part2")
        p1.wait()
        if t1:
            t1.join()
        ctx.rc["part1"] = p1.returncode
        log("part1 rc=%s" % p1.returncode)
        if spec["part2_proves"]:                      # release the decider
            os.makedirs(FLAG_DIR, exist_ok=True)
            open(FLAG, "w").close()
            log("snark gate released -> part2 runs the decider")
        p2.wait()
        if t2:
            t2.join()
        ctx.rc["part2"] = p2.returncode
        log("part2 rc=%s" % p2.returncode)
    finally:
        # safety: never leave part2's decider blocked on a flag we forgot.
        if p2 is not None and p2.poll() is None and not os.path.exists(FLAG):
            os.makedirs(FLAG_DIR, exist_ok=True)
            open(FLAG, "w").close()
        if p2 is not None:
            p2.wait()
            ctx.rc.setdefault("part2", p2.returncode)
        if t2:
            t2.join()
        if p1 is not None:                    # record part1 even on a
            p1.wait()                         # mid-fold signal/abort
            ctx.rc.setdefault("part1", p1.returncode)
        if t1:
            t1.join()
        if spec.get("report"):
            ctx.reports.append(spec["report"])
        _scan_verdict(ctx, [log1, log2])
    rc1 = ctx.rc.get("part1", 1)
    rc2 = ctx.rc.get("part2", 1)
    return rc1 or rc2


def _scan_verdict(ctx, logs):
    """Light pass/fail read from the run logs -- records the last split-
    verify / batch-proof verdict lines into the summary note.  (Lighter
    than the drivers' full coverage/disjointness verify_split.)"""
    verdict = []
    pat = re.compile(r"SPLIT VERIFY|batch.*verif|VERIFICATION|"
                     r"verify_batch|proof verif", re.I)
    for lg in logs:
        if os.path.isfile(lg):
            for ln in open(lg, errors="replace"):
                if pat.search(ln):
                    verdict.append(ln.strip())
    if verdict:
        ctx.note.append("verdict: " + verdict[-1])


# =====================================================================
# single-process runners
# =====================================================================

def run_single(ctx, test_name, report, use_time, vma):
    """One-process `cargo test <test> --exact --nocapture` + pack."""
    if vma:
        ensure_vma(VMA_TARGET)
    prefix = (["/usr/bin/time", "-v"]
              if use_time and os.path.exists("/usr/bin/time") else [])
    cmd = prefix + CARGO_TEST + [test_name, "--exact", "--nocapture"]
    logf = ctx.log_path("run")
    ctx.run_logs.append(logf)
    ctx.job_globs.append("log_job_[0-9]*.txt")
    if report:
        ctx.reports.append(report)
    if DRY:
        spawn(cmd, base_rust_env(), logf, ctx.key)
        log("--dry-run: not executing.")
        return 0
    p, t = spawn(cmd, base_rust_env(), logf, ctx.key)
    p.wait()
    if t:
        t.join()
    ctx.rc["run"] = p.returncode
    return p.returncode


def run_small(ctx):
    ctx.note.append("mode=small_data (light-test, single proc)")
    return run_single(ctx, SMALL_TEST, SMALL_REPORT,
                      use_time=False, vma=False)


def run_dna(ctx):
    ctx.note.append("mode=full_dna (single job, light-test)")
    return run_single(ctx, DNA_TEST, DNA_REPORT, use_time=True, vma=True)


# ---- (3) full clamav: verify-before-wipe preflight then two-half -----

def _clam_preflight():
    """All cheap checks first, cargo compile last; accumulate every
    failure so one pass reports them all.  Returns (ok, reasons)."""
    reasons = []
    if not os.path.isfile(CLAM_MAIN_SIG):
        reasons.append("missing DB sig %s" % CLAM_MAIN_SIG)
    for j in range(JOBS):
        m = os.path.join(CLAM_CFG_DIR, "binexec_p%d.dat" % j)
        if not os.path.isfile(m):
            reasons.append("missing manifest %s" % m)
    a, b = half_ranges()
    for nodes in (a, b):
        if nodes and shutil.which("numactl"):
            rc = subprocess.run(
                ["numactl", "--cpunodebind=%s" % nodes,
                 "--preferred-many=%s" % nodes, "true"],
                stdout=subprocess.DEVNULL,
                stderr=subprocess.DEVNULL).returncode
            if rc != 0:
                reasons.append("numactl --preferred-many=%s unsupported"
                               % nodes)
    log("preflight: cargo test --no-run (cold build may be slow)")
    rc = subprocess.run(
        CARGO_TEST[:-1] + ["--no-run"], cwd=REPO,
        env=base_rust_env(),
        stdout=subprocess.DEVNULL, stderr=subprocess.STDOUT).returncode
    if rc != 0:
        reasons.append("cargo test --no-run failed (rc=%d)" % rc)
    return (not reasons), reasons


def _clam_wipe_db():
    """prod clean slate: drop full_data (part1 rebuilds+saves it) and any
    stale per-job logs + snark flag.  NEVER touches the g16 keys or the
    static config inputs (main.dat, binexec_p*, report)."""
    log("WIPE: rm DB %s (part1 will rebuild+save)" % CLAM_DB_DIR)
    shutil.rmtree(CLAM_DB_DIR, ignore_errors=True)
    for f in glob.glob(os.path.join(LOGS_DIR, "log_job_*.txt")):
        try:
            os.remove(f)
        except OSError:
            pass
    shutil.rmtree(FLAG_DIR, ignore_errors=True)
    log("WIPE done; kept snark keys %s" % CLAM_SNARK_DIR)


def run_clam(ctx):
    ctx.note.append(
        "mode=full_clam prod pct=100 jobs=%d wipe_db=%s fold_only=%s "
        "id_snark_job=%d" % (JOBS, CLAM_WIPE_DB, CLAM_FOLD_ONLY,
                             CLAM_SNARK_JOB))
    ensure_vma(VMA_TARGET)
    if DRY and CLAM_WIPE_DB:
        log("--dry-run: would preflight (verify-before-wipe) then wipe %s"
            % CLAM_DB_DIR)
    if not DRY and CLAM_WIPE_DB:
        ok, reasons = _clam_preflight()      # verify BEFORE the wipe
        if not ok:
            log("PREFLIGHT ABORT (DB untouched):")
            for r in reasons:
                log("  - " + r)
            ctx.note.append("preflight=FAIL: " + "; ".join(reasons))
            return 3
        _clam_wipe_db()
    spec = {
        "test": CLAM_TEST,
        "env_fn": clam_env,
        "p1_read": "second",                 # part1 folds jobs 4-7
        "p2_read": "first",                  # part2 folds jobs 0-3 (+proof)
        "part2_proves": not CLAM_FOLD_ONLY,
        "pre_part2": _clam_wait_db if (CLAM_WIPE_DB and not DRY) else None,
        "report": CLAM_REPORT,
    }
    return run_two_half(ctx, spec)


# ---- (4) full dlp: write effective runcfg then two-half --------------

_DLP_EFF = None      # path to the effective runcfg (set in run_dlp)


def _dlp_write_runcfg(ctx):
    """Copy runcfg_full.json with num_jobs=JOBS to the run's out dir; the
    Rust side reads it via ZKR_DLP_RUNCFG."""
    import json
    global _DLP_EFF
    with open(DLP_RUNCFG) as f:
        rc = json.load(f)
    rc["num_jobs"] = JOBS
    _DLP_EFF = os.path.join(ctx.out, "runcfg_effective_%s.json" % ctx.ts)
    with open(_DLP_EFF, "w") as f:
        json.dump(rc, f, indent=2)
    ctx.reports.append(_DLP_EFF)


def run_dlp(ctx):
    ctx.note.append(
        "mode=full_dlp prod pct=100 jobs=%d emit_proof=%s"
        % (JOBS, DLP_EMIT_PROOF))
    ensure_vma(VMA_TARGET)
    _dlp_write_runcfg(ctx)
    report = os.path.join(DLP_REPORT_DIR, "report.dat")
    spec = {
        "test": DLP_TEST,
        "env_fn": dlp_env,
        "p1_read": "first",                  # part1 folds jobs 0-3
        "p2_read": "second",                 # part2 folds jobs 4-7
        "part2_proves": DLP_EMIT_PROOF,
        "pre_part2": None,
        "report": report if os.path.isfile(report) else None,
    }
    return run_two_half(ctx, spec)


# =====================================================================
# menu + dispatch
# =====================================================================

# (key, number, label, description, requirement, est-time, runner)
MENUS = [
    ("small", 1, "small data",
     "Light-test ZK discharge of the small_data_set (one sample per "
     "signature category); a fast sanity/demo run.",
     "Ships its own config (data/debug/small_data_set); ~7 GB RAM; "
     "single process, no NUMA.",
     "~40 s", run_small),
    ("dna", 2, "full dna set",
     "Single-job ZK discharge of the clean chr17 sample against the DNA "
     "DB (light-test).",
     "DNA data installed (INSTALL.py --data dna); large RAM; raises "
     "vm.max_map_count.",
     "single job; ~hours", run_dna),
    ("clam", 3, "full clamav set",
     "8-job (4+4) two-process NUMA prod run of the ClamAV binexec corpus "
     "against the full ClamAV DB; part2 emits one verified Groth16 proof.",
     "binexec + ClamAV DB installed; ideally ~1 TB RAM / 8 NUMA nodes; "
     "default rebuilds the ~40 GB DB (+~2 h).",
     "~5-8 h", run_clam),
    ("dlp", 4, "full dlp set",
     "8-job (4+4) two-process NUMA prod run of the MS-DLP DB over the "
     "Enron corpus (100%).",
     "email data installed (INSTALL.py --data email); large RAM / NUMA.",
     "~5-6 h", run_dlp),
]
BY_KEY = {m[0]: m for m in MENUS}
BY_NUM = {str(m[1]): m for m in MENUS}


def show_menu(dest=sys.stdout):
    dest.write("PAPER_DATA -- select a run:\n")
    for key, num, label, desc, req, est, _fn in MENUS:
        dest.write("\n  (%d) %-16s [%s]\n" % (num, label, est))
        dest.write("        %s\n" % desc)
        dest.write("        requires: %s\n" % req)
    dest.write("\nnon-interactive: python3 PAPER_DATA.py --run "
               "{small|dna|clam|dlp}\n")


def resolve_choice(s):
    s = (s or "").strip().lower()
    if s in BY_KEY:
        return s
    if s in BY_NUM:
        return BY_NUM[s][0]
    return None


def select(run_arg):
    """--run wins; else interactive prompt on a tty; else a piped choice;
    else print the menu + usage and exit 0 (safe under bare nohup)."""
    if run_arg:
        return run_arg
    if sys.stdin.isatty():
        show_menu()
        try:
            return resolve_choice(input("\nchoice [1]: ")) or "small"
        except EOFError:
            return "small"
    piped = ""
    try:
        piped = sys.stdin.read()
    except Exception:
        pass
    key = resolve_choice(piped.splitlines()[0] if piped.strip() else "")
    if key:
        return key
    show_menu()
    log("no tty and no --run: nothing selected. Re-run e.g. "
        "`nohup python3 PAPER_DATA.py --run clam &`")
    return None


def dispatch(ctx):
    """Run one menu item, ALWAYS packing its bundle (even on crash/signal)."""
    _, num, label, _desc, _req, _est, fn = BY_KEY[ctx.key]
    log("=== (%d) %s -> %s ===" % (num, label, ctx.out))
    rc = 1
    try:
        rc = fn(ctx)
    finally:
        ctx.bundle(rc)
    return rc


def go_background(log_path):
    """Double-fork into a daemon and redirect stdio to log_path so the run
    survives logout with no nohup.  Returns only in the daemon; the whole
    parent chain exits, handing the shell prompt back immediately."""
    if os.fork() > 0:
        os._exit(0)                       # original -> shell prompt returns
    os.setsid()
    if os.fork() > 0:
        os._exit(0)                       # session leader exits (no tty)
    os.chdir(REPO)
    sys.stdout.flush()
    sys.stderr.flush()
    di = os.open(os.devnull, os.O_RDONLY)
    lo = os.open(log_path, os.O_WRONLY | os.O_CREAT | os.O_APPEND, 0o644)
    os.dup2(di, 0)
    os.dup2(lo, 1)
    os.dup2(lo, 2)
    os.close(di)
    os.close(lo)
    try:                                  # line-buffer so `tail -f` is live
        sys.stdout.reconfigure(line_buffering=True)
        sys.stderr.reconfigure(line_buffering=True)
    except Exception:
        pass


def main():
    global CLAM_WIPE_DB, CLAM_FOLD_ONLY, DLP_EMIT_PROOF, DRY
    ap = argparse.ArgumentParser(
        description="Paper-data runner for bora (4-item menu).")
    ap.add_argument("--run", choices=[m[0] for m in MENUS],
                    help="non-interactive run selection")
    ap.add_argument("--list", action="store_true",
                    help="print the menu and exit")
    ap.add_argument("--dry-run", action="store_true",
                    help="print the resolved plan; spawn nothing")
    ap.add_argument("--no-daemon", action="store_true",
                    help="stay in the foreground (do not self-detach)")
    ap.add_argument("--clam-reuse-db", action="store_true",
                    help="clam: reuse data/cache/full_data (skip the "
                         "~2 h rebuild + DB gate)")
    ap.add_argument("--clam-fold-only", action="store_true",
                    help="clam: fold only, no Groth16 proof")
    ap.add_argument("--dlp-proof", action="store_true",
                    help="dlp: emit + verify the single Groth16 proof "
                         "(default is fold-only)")
    args = ap.parse_args()

    if JOBS != 8:                         # hard invariant, not a knob
        raise SystemExit(
            "PAPER_DATA: JOBS is fixed at 8 (two-process 4+4 NUMA "
            "scheme; clam is bound to its 8 binexec_p* manifests).")

    if args.list:
        show_menu()
        return 0

    DRY = args.dry_run
    if args.clam_reuse_db:
        CLAM_WIPE_DB = False
    if args.clam_fold_only:
        CLAM_FOLD_ONLY = True
    if args.dlp_proof:
        DLP_EMIT_PROOF = True

    key = select(args.run)                # menu / --run while on the tty
    if key is None:
        return 2

    ctx = RunContext(key)                 # fixes the out dir + timestamp
    daemon_log = os.path.join(ctx.out, "daemon_%s.log" % ctx.ts)
    if not DRY and not args.no_daemon:    # detach AFTER the choice is made
        print("[paper_data] detaching into the background "
              "(survives logout; no nohup needed).")
        print("  live log: tail -f %s" % daemon_log)
        print("  bundle:   %s/paper_data_%s_BUNDLE_%s.tgz (on finish)"
              % (ctx.out, key, ctx.ts))
        sys.stdout.flush()
        go_background(daemon_log)         # returns only in the daemon

    signal.signal(signal.SIGINT, _on_signal)
    signal.signal(signal.SIGTERM, _on_signal)
    return dispatch(ctx)


if __name__ == "__main__":
    sys.exit(main())
