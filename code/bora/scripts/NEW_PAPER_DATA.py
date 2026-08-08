#!/usr/bin/env python3
# ---------------------------------------------------------------------
# NEW_PAPER_DATA.py -- paper-data runner for bora.
#
# Interactive (menu) and non-interactive (--run/--items) driver for the
# paper's data-generation runs.  Built up in layers: D (common infra) ->
# C (leaf registry) -> B (sequencer) -> A (CLI/menu), landing shared
# infra first with stub leaves before any leaf gets a real
# implementation.
# ---------------------------------------------------------------------

import argparse
import datetime
import glob
import importlib.util
import io
import os
import platform
import re
import shutil
import signal
import subprocess
import sys
import tarfile
import tempfile
import threading
import time
import traceback
import unittest
from dataclasses import dataclass
from unittest import mock

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


# =====================================================================
# Layer D -- common infra
# =====================================================================

# ---- D1: NUMA / socket topology --------------------------------------

def nsockets():
    """Distinct physical socket count (/proc/cpuinfo 'physical id', or
    `lscpu -p=socket` fallback); 1 if undetectable."""
    try:
        ids = set()
        with open("/proc/cpuinfo") as f:
            for line in f:
                if line.startswith("physical id"):
                    ids.add(line.split(":", 1)[1].strip())
        if ids:
            return len(ids)
    except OSError:
        pass
    try:
        out = subprocess.run(["lscpu", "-p=socket"], capture_output=True,
                              text=True).stdout
        ids = {ln.strip() for ln in out.splitlines()
               if ln and not ln.startswith("#")}
        if ids:
            return len(ids)
    except OSError:
        pass
    return 1


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


def numa_available():
    """numactl exists AND nnodes() >= 2."""
    return bool(shutil.which("numactl")) and nnodes() >= 2


def half_node_ranges():
    """Split nnodes() into two contiguous ranges, e.g. ("0-3", "4-7") on
    an 8-node box.  Only computes ranges -- resolve_process_model()
    decides WHETHER to split.  (None, None) if nnodes() < 2."""
    n = nnodes()
    if n < 2:
        return None, None
    h = n // 2
    return "0-%d" % (h - 1), "%d-%d" % (h, n - 1)


@dataclass
class ProcessModel:
    n_parts: int                    # 1 or 2
    node_ranges: list               # len == n_parts; [None] if n_parts==1


def resolve_process_model(force_single=False):
    """1 process unless >=2 sockets AND numactl is usable; else 2
    processes split by half_node_ranges().  N>2 is explicitly deferred."""
    if force_single or nsockets() <= 1 or not numa_available():
        return ProcessModel(1, [None])
    lo, hi = half_node_ranges()
    return ProcessModel(2, [lo, hi])


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
# process launch (live-pumped to a per-job log)
# =====================================================================

_CHILDREN = []            # live Popen handles, reaped by the sequencer on signal


def log(msg):
    """Timestamped line to stdout (the daemon's own combined log once
    backgrounded)."""
    print("[paper_data %s] %s" % (
        datetime.datetime.now().strftime("%H:%M:%S"), msg), flush=True)


def spawn(cmd, env, log_path, label):
    """Launch one process (cwd=REPO, own session group), pumping its merged
    stdout live to console and log_path.  Returns (proc, pump_thread)."""
    log("%s: %s" % (label, " ".join(cmd)))
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


# =====================================================================
# Rust job launch (single- and two-half NUMA processes)
# =====================================================================

CARGO_TEST = ["cargo", "test", "-p", "zkregplus", "--release", "--"]

FLAG_DIR = "/tmp/snark_start"       # snark-decider release gate
FLAG = os.path.join(FLAG_DIR, "flag")

PART2_DELAY = 900          # seconds part1 must run before part2 launches
PART2_RAM_GB = 500.0       # ...or part1's tree RSS must drop below this


@dataclass
class TwoHalfSpec:
    test: str
    env_fn: object            # (half, *, fold_only, one_proof, wait_flag) -> dict
    node_ranges: list         # [nodes_a, nodes_b]
    part2_proves: bool
    pre_part2: object = None  # optional (Popen) -> "ready"|other


@dataclass
class TwoHalfExtra:
    part2_proves: bool
    pre_part2: object = None


def cargo_test_cmd(test_path):
    """`cargo test <test_path> --exact --nocapture`, release profile."""
    return CARGO_TEST + [test_path, "--exact", "--nocapture"]


def run_rust_single(ctx, test_path, env):
    """One-process `cargo test` run; waits and returns its exit code."""
    p, t = spawn(cargo_test_cmd(test_path), env, ctx.log_path("run"), ctx.key)
    ctx.watch(p.pid)
    p.wait()
    if t:
        t.join()
    return p.returncode


def _wait_stagger(p1):
    """Hold until part1 has run >= PART2_DELAY s AND its tree-RSS has
    dropped below PART2_RAM_GB (or part1 exits)."""
    waited = 0
    while p1.poll() is None:
        if waited >= PART2_DELAY and tree_rss_gb(p1.pid) < PART2_RAM_GB:
            break
        time.sleep(10)
        waited += 10


def _kill_proc(p):
    """SIGTERM the whole process group spawn() gave p its own session for."""
    try:
        os.killpg(os.getpgid(p.pid), signal.SIGTERM)
    except (OSError, ProcessLookupError):
        pass


def run_rust_two_half(ctx, spec):
    """part1 on node_ranges[0], part2 on node_ranges[1] (staggered so
    their RAM peaks don't overlap); if part2_proves, part1's exit
    releases the snark-gate flag so part2's decider proceeds."""
    a, b = spec.node_ranges
    cmd = cargo_test_cmd(spec.test)
    log1, log2 = ctx.log_path("part1"), ctx.log_path("part2")

    env1 = spec.env_fn("p1", fold_only=True, one_proof=False, wait_flag=None)
    env2 = spec.env_fn("p2", fold_only=not spec.part2_proves,
                        one_proof=spec.part2_proves,
                        wait_flag=FLAG if spec.part2_proves else None)

    p1, t1 = spawn(numa_prefix(a) + cmd, env1, log1, "part1")
    ctx.watch(p1.pid)
    if spec.pre_part2:
        status = spec.pre_part2(p1)
        if status != "ready":
            ctx.note("pre_part2 gate: %s (abort)" % status)
            _kill_proc(p1)
            p1.wait()
            if t1:
                t1.join()
            return 4

    _wait_stagger(p1)
    p2 = t2 = None
    try:
        p2, t2 = spawn(numa_prefix(b) + cmd, env2, log2, "part2")
        ctx.watch(p2.pid)
        p1.wait()
        if t1:
            t1.join()
        if spec.part2_proves:
            os.makedirs(FLAG_DIR, exist_ok=True)
            open(FLAG, "w").close()
    finally:
        # never leave part2's decider blocked on a flag we forgot to set
        if p2 is not None and p2.poll() is None and not os.path.exists(FLAG):
            os.makedirs(FLAG_DIR, exist_ok=True)
            open(FLAG, "w").close()
    p2.wait()
    if t2:
        t2.join()
    return p1.returncode or p2.returncode


def run_rust_job(ctx, test_path, env_fn, force_single=False, two_half=None):
    """Dispatch to run_rust_single or run_rust_two_half based on
    resolve_process_model(); the only place a leaf's NUMA fan-out is
    decided."""
    model = resolve_process_model(force_single)
    if model.n_parts == 1:
        env = env_fn(None, fold_only=False, one_proof=True, wait_flag=None)
        return run_rust_single(ctx, test_path, env)
    assert two_half is not None, "two_half required for a 2-process leaf"
    spec = TwoHalfSpec(test_path, env_fn, model.node_ranges,
                        two_half.part2_proves, two_half.pre_part2)
    return run_rust_two_half(ctx, spec)


def run_external_python(ctx, script, args, env):
    """Single-process launch of a plain python script (Zombie / Reef),
    not a cargo test -- no NUMA split, no env_fn convention."""
    cmd = [sys.executable, str(script)] + list(args)
    p, t = spawn(cmd, env, ctx.log_path("run"), ctx.key)
    ctx.watch(p.pid)
    p.wait()
    if t:
        t.join()
    return p.returncode


def run_rust_example(ctx, example_name, args, env):
    """Single-process `cargo run --release --example <name> -- <args>`,
    mirrors run_external_python but for a real bora_data_driver-style
    binary instead of a cargo test."""
    cmd = ["cargo", "run", "--release", "--example", example_name,
           "--"] + list(args)
    p, t = spawn(cmd, env, ctx.log_path("run"), ctx.key)
    ctx.watch(p.pid)
    p.wait()
    if t:
        t.join()
    return p.returncode


# =====================================================================
# raw_data placement (fixed output paths for gen_*.py figure scripts)
# =====================================================================

RAW_DATA_ROOT = os.path.join(REPO, "data", "paper_data", "run_data",
                              "data", "raw_data")
SERVER = "jet1tb"

def raw_data_path(name, server_specific=True):
    sub = SERVER if server_specific else "any_server"
    return os.path.join(RAW_DATA_ROOT, sub, name)

def place_raw_data(src, dest_name, server_specific=True):
    dest = raw_data_path(dest_name, server_specific)
    os.makedirs(os.path.dirname(dest), exist_ok=True)
    shutil.copy2(src, dest)
    return dest


# =====================================================================
# per-leaf job context (D5): JobHandle + CURRENT_JOB symlinks
# =====================================================================

CURRENT_JOB_LOG = "/tmp/bora/CURRENT_JOB.log"
CURRENT_JOB_LOG_PART2 = "/tmp/bora/CURRENT_JOB_part2.log"
SUMMARY_LOG = "/tmp/bora/SUMMARY.log"

JOB_LOG_DIR = "/tmp/bora/logs"
LOGS_DIR = os.path.join(REPO, "data", "cache", "logs")
FAILED_TGZ_DIR = os.path.join(RAW_DATA_ROOT, "failed_tgz")

RSS_POLL_S = 10   # peak-RSS sampling interval, matches _wait_stagger's

FAIL_RE = re.compile(
    r"panic|panicked|SIGABRT|Killed|out of memory|cannot allocate|"
    r"CapErr|FATAL|error\[|VERIFICATION FAILED|SPLIT VERIFY: FAIL")


@dataclass
class LeafResult:
    rc: int
    wall_s: float
    raw_data_written: list
    failed: bool
    triage_tgz: object          # str path, or None
    peak_rss_gb: float
    note: str


def _atomic_symlink(target, link_path):
    """os.symlink to a tmp name, then os.rename() over link_path, so a
    concurrent `tail -F` reader never sees a missing/half-written link."""
    os.makedirs(os.path.dirname(link_path), exist_ok=True)
    tmp = link_path + ".tmp"
    if os.path.lexists(tmp):
        os.unlink(tmp)
    os.symlink(target, tmp)
    os.rename(tmp, link_path)


def point_current_job(part1_log, part2_log):
    """Repoint CURRENT_JOB.log (and _part2.log) at the leaf now running."""
    _atomic_symlink(part1_log, CURRENT_JOB_LOG)
    if part2_log:
        _atomic_symlink(part2_log, CURRENT_JOB_LOG_PART2)
    else:
        try:
            os.unlink(CURRENT_JOB_LOG_PART2)
        except FileNotFoundError:
            pass


def _watch_rss(pid, ctx):
    """Background poller: keeps ctx.peak_rss_gb as the max tree-RSS seen
    for this pid.  Exits on its own once the pid is gone."""
    while os.path.exists("/proc/%d" % pid):
        gb = tree_rss_gb(pid)
        if gb > ctx.peak_rss_gb:
            ctx.peak_rss_gb = gb
        time.sleep(RSS_POLL_S)


class JobHandle:
    def __init__(self, key, mode):
        self.key = key
        self.mode = mode
        self.peak_rss_gb = 0.0
        self.raw_data = []
        self.reports = []
        self._t0 = time.time()
        self._ts = datetime.datetime.now().strftime("%Y%m%d_%H%M%S")
        self._dir = os.path.join(JOB_LOG_DIR,
                                  "%s_%s_%s" % (key, mode, self._ts))
        os.makedirs(self._dir, exist_ok=True)
        self._log_paths = []
        self._notes = []

    def log_path(self, name):
        p = os.path.join(self._dir, "%s.log" % name)
        self._log_paths.append(p)
        return p

    def note(self, line):
        self._notes.append(line)

    def watch(self, pid):
        t = threading.Thread(target=_watch_rss, args=(pid, self),
                              daemon=True)
        t.start()
        return t

    def _fail_lines(self):
        srcs = list(self._log_paths)
        srcs += glob.glob(os.path.join(LOGS_DIR, "log_job_*.txt"))
        lines = []
        for s in srcs:
            if os.path.isfile(s):
                with open(s, errors="replace") as f:
                    for ln in f:
                        if FAIL_RE.search(ln):
                            lines.append(ln.rstrip("\n"))
        return lines

    def _pack_bundle(self, rc, wall, fails):
        os.makedirs(FAILED_TGZ_DIR, exist_ok=True)
        tgz = os.path.join(
            FAILED_TGZ_DIR, "paper_data_%s_%s_%s_BUNDLE.tgz" % (
                self.key, self.mode, self._ts))
        summ = os.path.join(self._dir, "SUMMARY.txt")
        with open(summ, "w") as f:
            f.write("NEW_PAPER_DATA -- %s (%s)\n" % (self.key, self.mode))
            f.write("host=%s ts=%s\n" % (platform.node(), self._ts))
            f.write("rc=%s wall_s=%.1f peak_rss_gb=%.1f\n" %
                     (rc, wall, self.peak_rss_gb))
            for ln in self._notes:
                f.write(ln + "\n")
            f.write("\n== failure signatures (last 40) ==\n")
            f.write(("\n".join(fails[-40:]) or "(none)") + "\n")
        with tarfile.open(tgz, "w:gz", compresslevel=6) as t:
            t.add(summ, arcname="SUMMARY.txt")
            for p in self._log_paths:
                if os.path.isfile(p):
                    t.add(p, arcname="logs/" + os.path.basename(p))
            for jf in glob.glob(os.path.join(LOGS_DIR, "log_job_*.txt")):
                t.add(jf, arcname="logs/" + os.path.basename(jf))
            for rp in self.reports:
                if rp and os.path.isfile(rp):
                    t.add(rp, arcname=os.path.basename(rp))
        return tgz

    def finish(self, rc):
        wall = time.time() - self._t0
        fails = self._fail_lines()
        failed = rc != 0 or bool(fails)
        triage_tgz = None
        if failed:
            triage_tgz = self._pack_bundle(rc, wall, fails)
            self.note("triage: %s" % triage_tgz)
        return LeafResult(rc=rc, wall_s=wall,
                           raw_data_written=self.raw_data, failed=failed,
                           triage_tgz=triage_tgz,
                           peak_rss_gb=self.peak_rss_gb,
                           note="; ".join(self._notes))


# =====================================================================
# Layer D -- common infra (D6: preflight)
# =====================================================================

def ensure_vma(target):
    """Best-effort raise vm.max_map_count via sudo sysctl.  Non-fatal:
    logs the manual command if sudo is unavailable.  No-op if
    target <= 0."""
    if target <= 0:
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


def preflight_numactl(node_ranges):
    """Verify numactl --preferred-many works for each non-None entry in
    node_ranges (a ProcessModel.node_ranges list).  Returns (ok,
    reasons); accumulates every failure so one pass reports them all."""
    reasons = []
    for nodes in node_ranges:
        if not nodes:
            continue
        if not shutil.which("numactl"):
            reasons.append("numactl not found for nodes=%s" % nodes)
            continue
        rc = subprocess.run(
            ["numactl", "--cpunodebind=%s" % nodes,
             "--preferred-many=%s" % nodes, "true"],
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL).returncode
        if rc != 0:
            reasons.append("numactl --preferred-many=%s unsupported"
                            % nodes)
    return (not reasons), reasons


def check_required_files(paths):
    """Verify every path in paths exists.  Returns (ok, reasons);
    accumulates every missing path so one pass reports them all."""
    reasons = []
    for p in paths:
        if not os.path.isfile(p):
            reasons.append("missing file %s" % p)
    return (not reasons), reasons


# =====================================================================
# Layer C -- leaf registry (contract only; real entries land in Stage 2)
# =====================================================================

@dataclass
class JobSpec:
    key: str
    label: str
    run_fn: object       # (mode, ctx) -> LeafResult


JOB_SPECS = {}            # leaf_key -> JobSpec, filled in one by one


def stub_leaf(name, milestone):
    """Factory for the Stage-1 stub leaves: no real science, just proves
    the Sequencer/JobHandle wiring end-to-end."""
    def run_fn(mode, ctx):
        msg = "STUB -- blocked on %s" % milestone
        log("%s: %s (mode=%s)" % (name, msg, mode))
        ctx.note(msg)
        return ctx.finish(0)
    return run_fn


run_leaf_dlp          = stub_leaf("dlp",        "M102")
run_leaf_dna           = stub_leaf("dna",        "M103")
run_leaf_clamav        = stub_leaf("clam",       "M104")
run_leaf_scale_clamav  = stub_leaf("scale_clam", "M104")
run_leaf_scale_dlp     = stub_leaf("scale_dlp",  "M102")

# dry_run's collect_lookup_stats_adv perc -- kept small so the leaf
# builds a deterministically-thinned DB per dataset instead of the real
# full-size one. full_run always uses perc=100 (the real report).
LKUP_DRY_PERC = 5


def run_leaf_analyze_lkup(mode, ctx):
    """Q2 lookup-composition report (Mal+Dna+Dlp), via
    bora_data_driver::collect_lookup_stats_adv. dry builds each
    dataset's DB over a deterministically-thinned perc% subset of its
    signatures; full builds every real signature (perc=100)."""
    perc = LKUP_DRY_PERC if mode == "dry" else 100
    local_out = ctx.log_path("lookup_stats")
    env = dict(os.environ)
    env["RUSTFLAGS"] = "-C link-args=-fuse-ld=lld -Awarnings"
    rc = run_rust_example(ctx, "bora_data_driver",
                           ["lkup", str(perc), local_out], env)
    if rc == 0:
        dest = place_raw_data(local_out, "lookup_stats.dat",
                               server_specific=False)
        ctx.raw_data.append(dest)
    return ctx.finish(rc)


MS_DLP_DIR = os.path.join(REPO, "data", "src_sig", "ms_dlp")
MS_DLP_SCRIPTS_DIR = os.path.join(MS_DLP_DIR, "scripts")
ZOMBIE_LOG_NAME = "run_zombie_regex_zombie_international.log"
ZOMBIE_DRY_PERC = 2


def run_leaf_zombie(mode, ctx):
    """Spartan-NIZK proximity-non-membership circuits over
    regex_zombie_international/ policies. dry delegates to
    dry_run_zombie.py (evenly-spaced ZOMBIE_DRY_PERC% of policies, small
    proximity-safe VEC_SIZE); full runs run_zombie.py untouched."""
    env = dict(os.environ)
    if mode == "dry":
        script = os.path.join(MS_DLP_SCRIPTS_DIR, "dry_run_zombie.py")
        args = [str(ZOMBIE_DRY_PERC)]
    else:
        script = os.path.join(MS_DLP_SCRIPTS_DIR, "run_zombie.py")
        args = []
    rc = run_external_python(ctx, script, args, env)
    if rc == 0:
        src = os.path.join(MS_DLP_DIR, "docs", ZOMBIE_LOG_NAME)
        dest = place_raw_data(src, ZOMBIE_LOG_NAME)
        ctx.raw_data.append(dest)
    return ctx.finish(rc)


REEF_DIR = os.path.join(REPO, "data", "src_sig", "chr17_variants")
REEF_SCRIPTS_DIR = os.path.join(REEF_DIR, "scripts")
REEF_LOG_NAME = "reef_sample_run.log"
REEF_DRY_PERC = 10


def run_leaf_reef(mode, ctx):
    """Reef nlookup non-match baseline over chr17_variants/reef_regex/.
    dry delegates to dry_run_eval_reef.py (REEF_DRY_PERC%-scaled
    sample_size, same 6-category sweep); full runs eval_reef.py
    untouched (its own real config is already a 10/category sample)."""
    env = dict(os.environ)
    if mode == "dry":
        script = os.path.join(REEF_SCRIPTS_DIR, "dry_run_eval_reef.py")
        args = [str(REEF_DRY_PERC)]
    else:
        script = os.path.join(REEF_SCRIPTS_DIR, "eval_reef.py")
        args = []
    rc = run_external_python(ctx, script, args, env)
    if rc == 0:
        src = os.path.join(REEF_DIR, "docs", REEF_LOG_NAME)
        dest = place_raw_data(src, REEF_LOG_NAME)
        ctx.raw_data.append(dest)
    return ctx.finish(rc)


JOB_SPECS.update({
    "dlp":        JobSpec("dlp",        "DLP",          run_leaf_dlp),
    "dna":        JobSpec("dna",        "Dna",          run_leaf_dna),
    "clam":       JobSpec("clam",       "Clamav",       run_leaf_clamav),
    "scale_clam": JobSpec("scale_clam", "Scale-ClamAV", run_leaf_scale_clamav),
    "scale_dlp":  JobSpec("scale_dlp",  "Scale-DLP",    run_leaf_scale_dlp),
    "lkup":       JobSpec("lkup",       "Analyze lkup", run_leaf_analyze_lkup),
    "zombie":     JobSpec("zombie",     "Zombie",       run_leaf_zombie),
    "reef":       JobSpec("reef",       "Reef",         run_leaf_reef),
})


# =====================================================================
# Layer B -- sequencer
# =====================================================================

def _ts():
    return datetime.datetime.now().strftime("%H:%M:%S")


def _summary_line(line):
    """Emit one line to both the console (log()) and SUMMARY.log."""
    log(line)
    os.makedirs(os.path.dirname(SUMMARY_LOG), exist_ok=True)
    with open(SUMMARY_LOG, "a") as f:
        f.write("[%s] %s\n" % (_ts(), line))


def _terminate_all():
    """SIGTERM every tracked child's whole process group (spawn() gives
    each child its own session, so this reaps numactl+cargo+test)."""
    for p in _CHILDREN:
        try:
            if p.poll() is None:
                os.killpg(os.getpgid(p.pid), signal.SIGTERM)
        except (ProcessLookupError, PermissionError, OSError):
            pass


class Sequencer:
    def __init__(self, plan, dry_run=False):
        self.plan = plan
        self.dry_run = dry_run
        self._aborted = False   # set ONLY by SIGINT/SIGTERM

    def run(self):
        """Continue-on-failure is the only policy: an organic leaf
        failure never stops the sequence, only a signal does."""
        overall_rc = 0
        for leaf_key in self.plan.leaf_keys:
            if self._aborted:
                self._append_skipped(leaf_key)
                continue
            result = self._run_one_leaf(leaf_key)
            self._append_summary(leaf_key, result)
            if result.failed:
                overall_rc = 1
        self._finalize(overall_rc)
        return overall_rc

    def _run_one_leaf(self, leaf_key):
        spec = JOB_SPECS[leaf_key]
        mode = self.plan.mode
        _summary_line("START  %-6s (%s/%s)" % (
            leaf_key, self.plan.top, mode))
        ctx = JobHandle(leaf_key, mode)
        try:
            return spec.run_fn(mode, ctx)
        except Exception:
            # A run_fn bug (bad launch args, a helper raising outside the
            # subprocess it launched, etc.) must not kill the whole
            # Sequencer -- funnel it through the same finish()/triage-tgz
            # path as an ordinary rc!=0 failure, so it's visible in
            # SUMMARY.log and bundled instead of an uncaught traceback
            # silently killing the sequence (fatal under go_background(),
            # whose stdio goes to /dev/null).
            ctx.note("UNCAUGHT EXCEPTION in %s.run_fn:\n%s" % (
                leaf_key, traceback.format_exc()))
            return ctx.finish(1)

    def _append_summary(self, leaf_key, result):
        status = "FAIL" if result.failed else "OK"
        _summary_line("%-6s %-6s rc=%s wall=%ds" % (
            status, leaf_key, result.rc, int(result.wall_s)))
        if result.triage_tgz:
            _summary_line("       triage: %s" % result.triage_tgz)

    def _append_skipped(self, leaf_key):
        _summary_line("SKIP   %-6s" % leaf_key)

    def _finalize(self, overall_rc):
        _summary_line("DONE   overall_rc=%d" % overall_rc)


def install_signal_handlers(seq):
    """SIGINT/SIGTERM: log it, kill the child tree, mark the sequence
    aborted.  Does not raise -- killing the children makes the blocked
    p.wait() in run_rust_single/run_rust_two_half return on its own, so
    _run_one_leaf finishes its NORMAL path (rc != 0 already means
    failed, so the triage tgz packs exactly like an organic crash
    would).  This only decides whether run()'s loop starts the NEXT
    leaf_key; it never touches the leaf already in flight."""
    def _on_signal(signum, _frame):
        _summary_line("SIGNAL %s caught -> current leaf finishing, "
                       "then aborting sequence"
                       % signal.Signals(signum).name)
        _terminate_all()
        seq._aborted = True
    signal.signal(signal.SIGINT, _on_signal)
    signal.signal(signal.SIGTERM, _on_signal)


# =====================================================================
# Layer A -- CLI / menu resolution
# =====================================================================

TOP_CHOICES = [
    ("small", "small data"),
    ("dry_run", "dry_run"),
    ("full_run", "full_run"),
    ("figs", "generate list of figures"),
]

LEAF_CHOICES = [
    ("dlp", "DLP"),
    ("dna", "Dna"),
    ("clam", "Clamav"),
    ("zombie", "Zombie [dry ~1-2min, ~23GB]"),
    ("reef", "Reef"),
    ("lkup", "Analyze lkup [dry ~59s, ~17.4GB]"),
    ("scale_clam", "Scale-ClamAV"),
    ("scale_dlp", "Scale-DLP"),
]
_LEAF_KEYS = [k for k, _ in LEAF_CHOICES]     # canonical order (2.2)


@dataclass
class ResolvedPlan:
    top: str
    mode: object            # "dry" | "full" | None
    leaf_keys: list


def _parse_items(items):
    """'1,3,5' / 'dlp,clam' / 'A' / 'all' -> ordered, deduped leaf keys."""
    tokens = [t.strip() for t in items.split(",") if t.strip()]
    if any(t.lower() in ("a", "all") for t in tokens):
        if len(tokens) > 1:
            log("--items: 'A' selects every leaf; other tokens ignored")
        return list(_LEAF_KEYS)
    keys = []
    for t in tokens:
        if t.isdigit():
            idx = int(t) - 1
            if not 0 <= idx < len(_LEAF_KEYS):
                raise SystemExit(
                    "--items: %r out of range 1..%d" % (t, len(_LEAF_KEYS)))
            key = _LEAF_KEYS[idx]
        elif t in _LEAF_KEYS:
            key = t
        else:
            raise SystemExit("--items: unknown item %r" % t)
        if key not in keys:
            keys.append(key)
    return keys


def resolve_plan(run, items):
    if run in ("small", "figs"):
        return ResolvedPlan(top=run, mode=None, leaf_keys=[])
    if run not in ("dry_run", "full_run"):
        raise SystemExit("--run: unknown value %r" % run)
    if not items:
        raise SystemExit("--run %s requires --items" % run)
    mode = "dry" if run == "dry_run" else "full"
    return ResolvedPlan(top=run, mode=mode, leaf_keys=_parse_items(items))


def build_argparser():
    ap = argparse.ArgumentParser(description="Paper-data runner for bora.")
    ap.add_argument("--run", choices=[k for k, _ in TOP_CHOICES],
                     help="non-interactive run selection")
    ap.add_argument("--items",
                     help="comma-separated leaf list for dry_run/full_run "
                          "(numbers, keys, or 'A'/'all')")
    ap.add_argument("--list", action="store_true",
                     help="print the menu and exit")
    ap.add_argument("--dry-run", action="store_true", dest="plan_only",
                     help="print the resolved plan; spawn nothing")
    return ap


def _show_menu():
    print("NEW_PAPER_DATA -- select a run:")
    for i, (_, label) in enumerate(TOP_CHOICES, 1):
        print("  (%d) %s" % (i, label))


def _show_submenu(top):
    print("NEW_PAPER_DATA -- %s: select one or more "
          "(e.g. \"1,3,5\", \"dlp,clam\", or \"A\"):" % top)
    for i, (_, label) in enumerate(LEAF_CHOICES, 1):
        print("  (%d) %s" % (i, label))
    print("  (A) All")


def interactive_select():
    _show_menu()
    choice = input("choice [1]: ").strip() or "1"
    if not choice.isdigit() or not 1 <= int(choice) <= len(TOP_CHOICES):
        raise SystemExit("invalid choice %r" % choice)
    top = TOP_CHOICES[int(choice) - 1][0]
    if top in ("small", "figs"):
        return resolve_plan(top, None)
    _show_submenu(top)
    items = input("choice(s) [1]: ").strip() or "1"
    return resolve_plan(top, items)


def go_background():
    """Double-fork into a daemon and redirect stdio to /dev/null so the run
    survives logout with no nohup.  Returns only in the daemon; the whole
    parent chain exits, handing the shell prompt back immediately.  Nothing
    meaningful is lost -- every leaf already writes its own per-job log
    (JOB_LOG_DIR), and Sequencer writes SUMMARY_LOG independently."""
    if os.fork() > 0:
        os._exit(0)
    os.setsid()
    if os.fork() > 0:
        os._exit(0)
    os.chdir(REPO)
    sys.stdout.flush()
    sys.stderr.flush()
    di = os.open(os.devnull, os.O_RDONLY)
    do = os.open(os.devnull, os.O_WRONLY)
    os.dup2(di, 0)
    os.dup2(do, 1)
    os.dup2(do, 2)
    os.close(di)
    os.close(do)


# =====================================================================
# Layer A -- figs (menu #4: regenerate every figure + review PDF)
# =====================================================================

RUN_DATA_DIR = os.path.join(REPO, "data", "paper_data", "run_data")
EVAL_DIR = os.path.join(RUN_DATA_DIR, "scripts", "eval")
PDF_DIR = os.path.join(REPO, "data", "paper_data", "pdf")
PDF_PATH = os.path.join(PDF_DIR, "list_figures.pdf")


def run_figs():
    """Menu item #4: regenerate every figs/*.tex fragment from whatever
    is currently in raw_data/ (RUNALL.sh tolerates per-generator
    failures -- an ungenerated table just keeps its prior content),
    then compile list_figures.pdf. Runs in the foreground: this takes
    seconds, unlike a Sequencer leaf, so no daemonizing."""
    log("figs: running RUNALL.sh (per-generator failures are non-fatal)")
    rc = subprocess.run(["bash", "RUNALL.sh"], cwd=EVAL_DIR).returncode
    if rc != 0:
        log("figs: RUNALL.sh reported %d failing generator(s); "
            "continuing with whatever fragments exist" % rc)

    log("figs: compiling list_figures.tex")
    out = None
    for _ in range(2):
        p = subprocess.run(
            ["pdflatex", "-interaction=nonstopmode", "list_figures.tex"],
            cwd=RUN_DATA_DIR, stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT, text=True)
        out = p.stdout
    built = os.path.join(RUN_DATA_DIR, "list_figures.pdf")
    if not os.path.isfile(built):
        log("figs: pdflatex did not produce a PDF:\n%s"
            % (out or "")[-4000:])
        return 1

    os.makedirs(PDF_DIR, exist_ok=True)
    shutil.copy2(built, PDF_PATH)
    log("figs: wrote %s" % PDF_PATH)
    return 0


def main():
    ap = build_argparser()
    args = ap.parse_args()

    if args.list:
        _show_menu()
        _show_submenu("dry_run")
        return 0

    plan = resolve_plan(args.run, args.items) if args.run \
        else interactive_select()

    log("resolved: python3 NEW_PAPER_DATA.py --run %s%s" % (
        plan.top,
        " --items %s" % ",".join(plan.leaf_keys) if plan.leaf_keys else ""))

    if plan.top == "small":
        log("%s: not yet implemented in this framework version" % plan.top)
        return 0

    if plan.top == "figs":
        if args.plan_only:
            return 0
        return run_figs()

    if args.plan_only:
        return 0

    ts = _ts()
    print("[paper_data %s] detaching into the background "
          "(survives logout; no nohup needed)." % ts)
    print("[paper_data %s]   summary log:    tail -F %s" % (ts, SUMMARY_LOG))
    print("[paper_data %s]   current job:    tail -F %s"
          % (ts, CURRENT_JOB_LOG))
    print("[paper_data %s]   current job 2:  tail -F %s"
          % (ts, CURRENT_JOB_LOG_PART2))
    print("[paper_data %s]     (part2 only exists while a 2-process leaf "
          "is active)" % ts)
    sys.stdout.flush()
    go_background()

    seq = Sequencer(plan, dry_run=(plan.mode == "dry"))
    install_signal_handlers(seq)
    return seq.run()


# =====================================================================
# unit tests -- run with: python3 -m unittest NEW_PAPER_DATA
# =====================================================================

_MOD = sys.modules[__name__]


def _fake_open(path_map):
    """open() replacement: StringIO(content) for known paths, else
    FileNotFoundError."""
    def _open(path, *a, **kw):
        if path in path_map:
            return io.StringIO(path_map[path])
        raise FileNotFoundError(path)
    return _open


class NSocketsTest(unittest.TestCase):
    def test_from_cpuinfo_two_sockets(self):
        cpuinfo = (
            "processor\t: 0\nphysical id\t: 0\n\n"
            "processor\t: 1\nphysical id\t: 1\n\n"
            "processor\t: 2\nphysical id\t: 0\n\n"
        )
        with mock.patch("builtins.open",
                         _fake_open({"/proc/cpuinfo": cpuinfo})):
            self.assertEqual(nsockets(), 2)

    def test_fallback_lscpu(self):
        with mock.patch("builtins.open", side_effect=FileNotFoundError):
            with mock.patch("subprocess.run") as run:
                run.return_value.stdout = "# comment\n0\n0\n1\n"
                self.assertEqual(nsockets(), 2)

    def test_undetectable_defaults_to_one(self):
        with mock.patch("builtins.open", side_effect=FileNotFoundError):
            with mock.patch("subprocess.run", side_effect=OSError):
                self.assertEqual(nsockets(), 1)


class NNodesTest(unittest.TestCase):
    def test_no_numactl(self):
        with mock.patch("shutil.which", return_value=None):
            self.assertEqual(nnodes(), 1)

    def test_multi_node(self):
        out = "node 0 cpus: 0 1 2 3\nnode 1 cpus: 4 5 6 7\n"
        with mock.patch("shutil.which", return_value="/usr/bin/numactl"):
            with mock.patch("subprocess.run") as run:
                run.return_value.stdout = out
                self.assertEqual(nnodes(), 2)


class NumaAvailableTest(unittest.TestCase):
    def test_true_when_numactl_and_multi_node(self):
        with mock.patch("shutil.which", return_value="/usr/bin/numactl"):
            with mock.patch.object(_MOD, "nnodes", return_value=2):
                self.assertTrue(numa_available())

    def test_false_when_single_node(self):
        with mock.patch("shutil.which", return_value="/usr/bin/numactl"):
            with mock.patch.object(_MOD, "nnodes", return_value=1):
                self.assertFalse(numa_available())

    def test_false_when_no_numactl(self):
        with mock.patch("shutil.which", return_value=None):
            self.assertFalse(numa_available())


class HalfNodeRangesTest(unittest.TestCase):
    def test_eight_nodes(self):
        with mock.patch.object(_MOD, "nnodes", return_value=8):
            self.assertEqual(half_node_ranges(), ("0-3", "4-7"))

    def test_single_node(self):
        with mock.patch.object(_MOD, "nnodes", return_value=1):
            self.assertEqual(half_node_ranges(), (None, None))


class ResolveProcessModelTest(unittest.TestCase):
    def test_force_single(self):
        model = resolve_process_model(force_single=True)
        self.assertEqual(model.n_parts, 1)
        self.assertEqual(model.node_ranges, [None])

    def test_single_socket(self):
        with mock.patch.object(_MOD, "nsockets", return_value=1):
            model = resolve_process_model()
            self.assertEqual(model.n_parts, 1)
            self.assertEqual(model.node_ranges, [None])

    def test_two_sockets_no_numactl(self):
        with mock.patch.object(_MOD, "nsockets", return_value=2):
            with mock.patch.object(_MOD, "numa_available",
                                    return_value=False):
                model = resolve_process_model()
                self.assertEqual(model.n_parts, 1)

    def test_two_sockets_splits(self):
        with mock.patch.object(_MOD, "nsockets", return_value=2):
            with mock.patch.object(_MOD, "numa_available",
                                    return_value=True):
                with mock.patch.object(_MOD, "half_node_ranges",
                                        return_value=("0-3", "4-7")):
                    model = resolve_process_model()
                    self.assertEqual(model.n_parts, 2)
                    self.assertEqual(model.node_ranges, ["0-3", "4-7"])


class NumaPrefixTest(unittest.TestCase):
    def test_no_nodes(self):
        self.assertEqual(numa_prefix(None), [])

    def test_with_nodes(self):
        with mock.patch("shutil.which", return_value="/usr/bin/numactl"):
            self.assertEqual(
                numa_prefix("0-3"),
                ["numactl", "--cpunodebind=0-3", "--preferred-many=0-3"])


class TreeRssGbTest(unittest.TestCase):
    def test_sums_descendants_only(self):
        stat = {
            200: "200 (a) S 100 200 200 0 -1",
            300: "300 (b) S 200 200 200 0 -1",
            400: "400 (c) S 1 400 400 0 -1",
        }
        status = {
            100: "VmRSS:\t    1000 kB\n",
            200: "VmRSS:\t    2000 kB\n",
            300: "VmRSS:\t    3000 kB\n",
            400: "VmRSS:\t     500 kB\n",
        }
        path_map = {}
        for pid, content in stat.items():
            path_map["/proc/%d/stat" % pid] = content
        for pid, content in status.items():
            path_map["/proc/%d/status" % pid] = content

        with mock.patch(
                "os.listdir",
                return_value=["100", "200", "300", "400", "self"]):
            with mock.patch("builtins.open", _fake_open(path_map)):
                gb = tree_rss_gb(100)
        self.assertAlmostEqual(gb, 6000 / (1024.0 * 1024.0))


class SpawnTest(unittest.TestCase):
    def setUp(self):
        _CHILDREN.clear()

    def test_pumps_output_to_console_and_log(self):
        fake_proc = mock.Mock()
        fake_proc.stdout = iter(["line one\n", "line two\n"])
        with tempfile.TemporaryDirectory() as d:
            log_path = os.path.join(d, "job.log")
            out = io.StringIO()
            with mock.patch("subprocess.Popen",
                             return_value=fake_proc) as popen:
                with mock.patch("sys.stdout", out):
                    proc, thread = spawn(["echo", "hi"], {"X": "1"},
                                          log_path, "mylabel")
                    thread.join(timeout=2)
            with open(log_path) as f:
                logged = f.read()

        args, kwargs = popen.call_args
        self.assertEqual(args[0], ["echo", "hi"])
        self.assertEqual(kwargs["cwd"], REPO)
        self.assertEqual(kwargs["env"], {"X": "1"})
        self.assertEqual(kwargs["stdout"], subprocess.PIPE)
        self.assertEqual(kwargs["stderr"], subprocess.STDOUT)
        self.assertTrue(kwargs["start_new_session"])
        self.assertIs(proc, fake_proc)
        self.assertIn(fake_proc, _CHILDREN)

        printed = out.getvalue()
        self.assertIn("[mylabel] line one", printed)
        self.assertIn("[mylabel] line two", printed)
        self.assertIn("line one", logged)
        self.assertIn("line two", logged)
        self.assertIn("mylabel", logged)


class _FakeProc:
    def __init__(self, pid=111, rc=0):
        self.pid = pid
        self.returncode = None
        self._rc = rc

    def poll(self):
        return self.returncode

    def wait(self):
        self.returncode = self._rc
        return self.returncode


class CargoTestCmdTest(unittest.TestCase):
    def test_shape(self):
        self.assertEqual(
            cargo_test_cmd("mod::tests_foo"),
            CARGO_TEST + ["mod::tests_foo", "--exact", "--nocapture"])


class RunRustSingleTest(unittest.TestCase):
    def test_waits_and_returns_rc(self):
        fake = _FakeProc(pid=5, rc=3)
        ctx = mock.Mock()
        ctx.key = "lkup"
        ctx.log_path.return_value = "/tmp/whatever.log"
        with mock.patch.object(_MOD, "spawn",
                                return_value=(fake, None)) as sp:
            rc = run_rust_single(ctx, "mod::tests_foo", {"E": "1"})
        self.assertEqual(rc, 3)
        sp.assert_called_once_with(
            cargo_test_cmd("mod::tests_foo"), {"E": "1"},
            "/tmp/whatever.log", "lkup")


class RunRustTwoHalfTest(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.flag_dir = os.path.join(self.tmp.name, "snark_start")
        self.flag = os.path.join(self.flag_dir, "flag")
        for p in (mock.patch.object(_MOD, "FLAG_DIR", self.flag_dir),
                  mock.patch.object(_MOD, "FLAG", self.flag),
                  mock.patch.object(_MOD, "_wait_stagger", lambda p: None)):
            p.start()
            self.addCleanup(p.stop)
        self.ctx = mock.Mock()
        self.ctx.log_path.side_effect = lambda name: os.path.join(
            self.tmp.name, name + ".log")

    def test_part2_proves_releases_flag(self):
        p1, p2 = _FakeProc(pid=1, rc=0), _FakeProc(pid=2, rc=0)
        env_fn = mock.Mock(side_effect=[{"H": "p1"}, {"H": "p2"}])
        spec = TwoHalfSpec("some::test", env_fn, ["0-3", "4-7"],
                            part2_proves=True, pre_part2=None)
        with mock.patch.object(_MOD, "spawn",
                                side_effect=[(p1, None), (p2, None)]):
            rc = run_rust_two_half(self.ctx, spec)
        self.assertEqual(rc, 0)
        self.assertTrue(os.path.isfile(self.flag))
        env_fn.assert_any_call("p1", fold_only=True, one_proof=False,
                                wait_flag=None)
        env_fn.assert_any_call("p2", fold_only=False, one_proof=True,
                                wait_flag=self.flag)

    def test_pre_part2_gate_failure_kills_part1_and_skips_part2(self):
        p1 = _FakeProc(pid=1, rc=0)
        env_fn = mock.Mock(return_value={})
        spec = TwoHalfSpec("some::test", env_fn, ["0-3", "4-7"],
                            part2_proves=True,
                            pre_part2=lambda p: "timeout")
        with mock.patch.object(_MOD, "spawn",
                                return_value=(p1, None)) as sp:
            with mock.patch.object(_MOD, "_kill_proc") as kill:
                rc = run_rust_two_half(self.ctx, spec)
        self.assertEqual(rc, 4)
        kill.assert_called_once_with(p1)
        sp.assert_called_once()   # part2 never spawned
        self.ctx.note.assert_called_once()


class RunRustJobTest(unittest.TestCase):
    def setUp(self):
        self.ctx = mock.Mock()

    def test_single_process(self):
        with mock.patch.object(_MOD, "resolve_process_model",
                                return_value=ProcessModel(1, [None])):
            with mock.patch.object(_MOD, "run_rust_single",
                                    return_value=0) as single:
                env_fn = mock.Mock(return_value={"E": "1"})
                rc = run_rust_job(self.ctx, "some::test", env_fn)
        self.assertEqual(rc, 0)
        env_fn.assert_called_once_with(None, fold_only=False,
                                        one_proof=True, wait_flag=None)
        single.assert_called_once_with(self.ctx, "some::test", {"E": "1"})

    def test_two_process(self):
        model = ProcessModel(2, ["0-3", "4-7"])
        with mock.patch.object(_MOD, "resolve_process_model",
                                return_value=model):
            with mock.patch.object(_MOD, "run_rust_two_half",
                                    return_value=0) as two_half:
                env_fn = mock.Mock()
                extra = TwoHalfExtra(part2_proves=False, pre_part2=None)
                rc = run_rust_job(self.ctx, "some::test", env_fn,
                                   two_half=extra)
        self.assertEqual(rc, 0)
        spec = two_half.call_args[0][1]
        self.assertEqual(spec.test, "some::test")
        self.assertEqual(spec.node_ranges, ["0-3", "4-7"])
        self.assertFalse(spec.part2_proves)


class RunExternalPythonTest(unittest.TestCase):
    def test_builds_cmd_and_returns_rc(self):
        fake = _FakeProc(pid=9, rc=2)
        ctx = mock.Mock()
        ctx.key = "zombie"
        ctx.log_path.return_value = "/tmp/run.log"
        with mock.patch.object(_MOD, "spawn",
                                return_value=(fake, None)) as sp:
            rc = run_external_python(ctx, "/x/run_zombie.py",
                                      ["--a", "1"], {"E": "1"})
        self.assertEqual(rc, 2)
        sp.assert_called_once_with(
            [sys.executable, "/x/run_zombie.py", "--a", "1"],
            {"E": "1"}, "/tmp/run.log", "zombie")


class RawDataPathTest(unittest.TestCase):
    def test_server_specific(self):
        p = raw_data_path("full_clam.tgz")
        self.assertTrue(p.endswith(
            os.path.join("raw_data", SERVER, "full_clam.tgz")))

    def test_any_server(self):
        p = raw_data_path("lookup_stats.dat", server_specific=False)
        self.assertTrue(p.endswith(
            os.path.join("raw_data", "any_server", "lookup_stats.dat")))


class PlaceRawDataTest(unittest.TestCase):
    def test_copies_and_overwrites(self):
        with tempfile.TemporaryDirectory() as tmp:
            src = os.path.join(tmp, "src.txt")
            with open(src, "w") as f:
                f.write("v1")
            fake_root = os.path.join(tmp, "raw_data")
            with mock.patch.object(_MOD, "RAW_DATA_ROOT", fake_root):
                dest = place_raw_data(src, "out.txt", server_specific=False)
                with open(dest) as f:
                    self.assertEqual(f.read(), "v1")

                with open(src, "w") as f:
                    f.write("v2")
                dest2 = place_raw_data(src, "out.txt", server_specific=False)
                self.assertEqual(dest, dest2)
                with open(dest2) as f:
                    self.assertEqual(f.read(), "v2")


class RunLeafZombieTest(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        patches = [
            mock.patch.object(_MOD, "JOB_LOG_DIR",
                               os.path.join(self.tmp.name, "logs")),
            mock.patch.object(_MOD, "FAILED_TGZ_DIR",
                               os.path.join(self.tmp.name, "failed_tgz")),
            mock.patch.object(_MOD, "LOGS_DIR",
                               os.path.join(self.tmp.name, "job_logs")),
            mock.patch.object(_MOD, "RAW_DATA_ROOT",
                               os.path.join(self.tmp.name, "raw_data")),
        ]
        for p in patches:
            p.start()
            self.addCleanup(p.stop)
        os.makedirs(os.path.join(self.tmp.name, "job_logs"))

    def test_dry_mode_uses_dry_script_and_perc_arg(self):
        ctx = JobHandle("zombie", "dry")
        with mock.patch.object(_MOD, "run_external_python",
                                return_value=0) as rep:
            with mock.patch.object(_MOD, "place_raw_data",
                                    return_value="/fake/dest") as prd:
                result = run_leaf_zombie("dry", ctx)
        self.assertEqual(result.rc, 0)
        self.assertFalse(result.failed)
        script, args = rep.call_args[0][1], rep.call_args[0][2]
        self.assertTrue(script.endswith("dry_run_zombie.py"))
        self.assertEqual(args, [str(ZOMBIE_DRY_PERC)])
        prd.assert_called_once()
        self.assertEqual(ctx.raw_data, ["/fake/dest"])

    def test_full_mode_uses_real_script_no_args(self):
        ctx = JobHandle("zombie", "full")
        with mock.patch.object(_MOD, "run_external_python",
                                return_value=0) as rep:
            with mock.patch.object(_MOD, "place_raw_data",
                                    return_value="/fake/dest"):
                run_leaf_zombie("full", ctx)
        script, args = rep.call_args[0][1], rep.call_args[0][2]
        self.assertTrue(script.endswith(
            os.path.join("ms_dlp", "scripts", "run_zombie.py")))
        self.assertEqual(args, [])

    def test_nonzero_rc_skips_raw_data_placement(self):
        ctx = JobHandle("zombie", "dry")
        with mock.patch.object(_MOD, "run_external_python",
                                return_value=1):
            with mock.patch.object(_MOD, "place_raw_data") as prd:
                result = run_leaf_zombie("dry", ctx)
        prd.assert_not_called()
        self.assertEqual(ctx.raw_data, [])
        self.assertTrue(result.failed)


class RunLeafReefTest(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        patches = [
            mock.patch.object(_MOD, "JOB_LOG_DIR",
                               os.path.join(self.tmp.name, "logs")),
            mock.patch.object(_MOD, "FAILED_TGZ_DIR",
                               os.path.join(self.tmp.name, "failed_tgz")),
            mock.patch.object(_MOD, "LOGS_DIR",
                               os.path.join(self.tmp.name, "job_logs")),
            mock.patch.object(_MOD, "RAW_DATA_ROOT",
                               os.path.join(self.tmp.name, "raw_data")),
        ]
        for p in patches:
            p.start()
            self.addCleanup(p.stop)
        os.makedirs(os.path.join(self.tmp.name, "job_logs"))

    def test_dry_mode_uses_dry_script_and_perc_arg(self):
        ctx = JobHandle("reef", "dry")
        with mock.patch.object(_MOD, "run_external_python",
                                return_value=0) as rep:
            with mock.patch.object(_MOD, "place_raw_data",
                                    return_value="/fake/dest") as prd:
                result = run_leaf_reef("dry", ctx)
        self.assertEqual(result.rc, 0)
        self.assertFalse(result.failed)
        script, args = rep.call_args[0][1], rep.call_args[0][2]
        self.assertTrue(script.endswith("dry_run_eval_reef.py"))
        self.assertEqual(args, [str(REEF_DRY_PERC)])
        prd.assert_called_once()
        self.assertEqual(ctx.raw_data, ["/fake/dest"])

    def test_full_mode_uses_real_script_no_args(self):
        ctx = JobHandle("reef", "full")
        with mock.patch.object(_MOD, "run_external_python",
                                return_value=0) as rep:
            with mock.patch.object(_MOD, "place_raw_data",
                                    return_value="/fake/dest"):
                run_leaf_reef("full", ctx)
        script, args = rep.call_args[0][1], rep.call_args[0][2]
        self.assertTrue(script.endswith(
            os.path.join("chr17_variants", "scripts", "eval_reef.py")))
        self.assertEqual(args, [])

    def test_nonzero_rc_skips_raw_data_placement(self):
        ctx = JobHandle("reef", "dry")
        with mock.patch.object(_MOD, "run_external_python",
                                return_value=1):
            with mock.patch.object(_MOD, "place_raw_data") as prd:
                result = run_leaf_reef("dry", ctx)
        prd.assert_not_called()
        self.assertEqual(ctx.raw_data, [])
        self.assertTrue(result.failed)


def _load_dry_run_eval_reef():
    """Import dry_run_eval_reef.py by path (it lives under
    chr17_variants/scripts/, outside this file's own directory). Its
    own `import eval_reef as m` is import-time-cheap (one os.path
    .getsize stat call on the chr17 doc) but DOES require the chr17
    doc file to be physically present on this machine -- same
    precondition the real leaf has, just surfaced earlier."""
    path = os.path.join(REEF_SCRIPTS_DIR, "dry_run_eval_reef.py")
    spec = importlib.util.spec_from_file_location(
        "dry_run_eval_reef", path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


class DrySampleSizeTest(unittest.TestCase):
    def setUp(self):
        self.drr = _load_dry_run_eval_reef()

    def test_100_percent_is_module_baseline(self):
        self.assertEqual(self.drr.dry_sample_size(100), 10)

    def test_floors_at_one(self):
        self.assertEqual(self.drr.dry_sample_size(1), 1)
        self.assertEqual(self.drr.dry_sample_size(5), 1)

    def test_scales_proportionally(self):
        self.assertEqual(self.drr.dry_sample_size(50), 5)


class DryRunEvalReefMainTest(unittest.TestCase):
    def setUp(self):
        self.drr = _load_dry_run_eval_reef()

    def test_missing_perc_arg_raises(self):
        with self.assertRaises(SystemExit):
            self.drr.main(["dry_run_eval_reef.py"])

    def test_non_integer_perc_raises(self):
        with self.assertRaises(SystemExit):
            self.drr.main(["dry_run_eval_reef.py", "abc"])

    def test_calls_six_fns_with_scaled_size_and_syncs_global(self):
        m = self.drr.m
        original = m.sample_size
        try:
            with mock.patch.object(m, "verify_tool_existence") as vte, \
                 mock.patch.object(m, "setup") as setup, \
                 mock.patch.object(m, "gen_assessment",
                                    return_value="FULLCAT") as ga, \
                 mock.patch.object(m, "gen_sample_pool",
                                    return_value="POOL") as gsp, \
                 mock.patch.object(m, "seq_run_categories",
                                    return_value=("RES", "DISC")) as src, \
                 mock.patch.object(m, "write_log") as wl:
                rc = self.drr.main(["dry_run_eval_reef.py", "10"])
            self.assertEqual(rc, 0)
            vte.assert_called_once_with()
            setup.assert_called_once_with()
            ga.assert_called_once_with()
            gsp.assert_called_once_with()
            src.assert_called_once_with(
                "POOL", m.timeout, m.threshold_perc, 1, m.max_discard)
            wl.assert_called_once_with("RES", "FULLCAT", "DISC")
            self.assertEqual(m.sample_size, 1)
        finally:
            m.sample_size = original


def _load_dry_run_zombie():
    """Import dry_run_zombie.py by path (it lives under ms_dlp/scripts/,
    outside this file's own directory, and does its own sys.path/import
    of run_zombie.py -- both side effects are import-time-cheap)."""
    path = os.path.join(MS_DLP_SCRIPTS_DIR, "dry_run_zombie.py")
    spec = importlib.util.spec_from_file_location("dry_run_zombie", path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


class EvenlySpacedSubsetTest(unittest.TestCase):
    def setUp(self):
        self.drz = _load_dry_run_zombie()

    def test_empty_input(self):
        self.assertEqual(self.drz.evenly_spaced_subset([], 2), [])

    def test_zero_or_negative_perc(self):
        self.assertEqual(self.drz.evenly_spaced_subset(["a", "b"], 0), [])
        self.assertEqual(self.drz.evenly_spaced_subset(["a", "b"], -5), [])

    def test_perc_100_is_identity(self):
        items = list("abcdef")
        self.assertEqual(self.drz.evenly_spaced_subset(items, 100), items)

    def test_small_n_always_keeps_at_least_one(self):
        self.assertEqual(self.drz.evenly_spaced_subset(["a"], 1), ["a"])

    def test_spread_across_194_matches_hand_worked_indices(self):
        items = ["p%03d" % i for i in range(194)]
        # keep = ceil(194*2/100) = 4, step = 194/4 = 48.5
        got = self.drz.evenly_spaced_subset(items, 2)
        want = [items[round(i * 48.5)] for i in range(4)]
        self.assertEqual(got, want)
        self.assertEqual(len(set(got)), 4)


class MakeDryListPolicyNamesTest(unittest.TestCase):
    def test_subsets_whatever_the_original_fn_returns(self):
        drz = _load_dry_run_zombie()
        original = mock.Mock(return_value=["a", "b", "c", "d"])
        patched = drz._make_dry_list_policy_names(50, original)
        got = patched("regex_zombie_international")
        original.assert_called_once_with("regex_zombie_international")
        self.assertEqual(got, drz.evenly_spaced_subset(
            ["a", "b", "c", "d"], 50))


class DryRunZombieMainTest(unittest.TestCase):
    def setUp(self):
        self.drz = _load_dry_run_zombie()

    def test_missing_perc_arg_raises(self):
        with self.assertRaises(SystemExit):
            self.drz.main(["dry_run_zombie.py"])

    def test_non_integer_perc_raises(self):
        with self.assertRaises(SystemExit):
            self.drz.main(["dry_run_zombie.py", "abc"])

    def test_patches_vec_size_and_list_policy_names_then_delegates(self):
        original = self.drz.run_zombie.list_policy_names
        try:
            with mock.patch.object(self.drz.run_zombie, "main",
                                    return_value=0) as real_main:
                rc = self.drz.main(["dry_run_zombie.py", "2"])
            self.assertEqual(rc, 0)
            real_main.assert_called_once_with()
            self.assertEqual(self.drz.run_zombie.VEC_SIZE,
                              self.drz.DRY_VEC_SIZE)
            self.assertIsNot(self.drz.run_zombie.list_policy_names,
                              original)
        finally:
            self.drz.run_zombie.list_policy_names = original


class PointCurrentJobTest(unittest.TestCase):
    def test_two_proc_symlinks(self):
        with tempfile.TemporaryDirectory() as tmp:
            link1 = os.path.join(tmp, "CURRENT_JOB.log")
            link2 = os.path.join(tmp, "CURRENT_JOB_part2.log")
            log1 = os.path.join(tmp, "real_part1.log")
            log2 = os.path.join(tmp, "real_part2.log")
            open(log1, "w").close()
            open(log2, "w").close()
            with mock.patch.object(_MOD, "CURRENT_JOB_LOG", link1), \
                 mock.patch.object(_MOD, "CURRENT_JOB_LOG_PART2", link2):
                point_current_job(log1, log2)
                self.assertEqual(os.readlink(link1), log1)
                self.assertEqual(os.readlink(link2), log2)

                log1b = os.path.join(tmp, "real_part1_b.log")
                open(log1b, "w").close()
                point_current_job(log1b, None)
                self.assertEqual(os.readlink(link1), log1b)
                self.assertFalse(os.path.exists(link2))


class JobHandleFinishTest(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        patches = [
            mock.patch.object(_MOD, "JOB_LOG_DIR",
                               os.path.join(self.tmp.name, "logs")),
            mock.patch.object(_MOD, "FAILED_TGZ_DIR",
                               os.path.join(self.tmp.name, "failed_tgz")),
            mock.patch.object(_MOD, "LOGS_DIR",
                               os.path.join(self.tmp.name, "job_logs")),
        ]
        for p in patches:
            p.start()
            self.addCleanup(p.stop)
        os.makedirs(os.path.join(self.tmp.name, "job_logs"))

    def test_success_no_tgz(self):
        ctx = JobHandle("lkup", "dry")
        with open(ctx.log_path("run"), "w") as f:
            f.write("all good\n")
        result = ctx.finish(0)
        self.assertFalse(result.failed)
        self.assertIsNone(result.triage_tgz)
        self.assertFalse(os.path.isdir(_MOD.FAILED_TGZ_DIR))

    def test_nonzero_rc_packs_tgz(self):
        ctx = JobHandle("clam", "full")
        with open(ctx.log_path("run"), "w") as f:
            f.write("nothing bad here\n")
        result = ctx.finish(1)
        self.assertTrue(result.failed)
        self.assertTrue(os.path.isfile(result.triage_tgz))
        self.assertIn("triage:", result.note)

    def test_fail_re_hit_with_rc_zero(self):
        ctx = JobHandle("dlp", "full")
        with open(ctx.log_path("run"), "w") as f:
            f.write("everything fine\nCapErr: oops\n")
        result = ctx.finish(0)
        self.assertTrue(result.failed)
        self.assertIsNotNone(result.triage_tgz)
        with tarfile.open(result.triage_tgz) as t:
            names = t.getnames()
        self.assertIn("SUMMARY.txt", names)
        self.assertTrue(any(n.startswith("logs/") for n in names))

    def test_peak_rss_and_raw_data_pass_through(self):
        ctx = JobHandle("reef", "dry")
        ctx.peak_rss_gb = 12.3
        ctx.raw_data.append("/x/out.dat")
        result = ctx.finish(0)
        self.assertEqual(result.peak_rss_gb, 12.3)
        self.assertEqual(result.raw_data_written, ["/x/out.dat"])


class WatchRssTest(unittest.TestCase):
    def test_polls_until_pid_gone_and_keeps_max(self):
        samples = [5.0, 20.0, 3.0]
        exists_seq = [True, True, True, False]

        def fake_exists(path):
            return exists_seq.pop(0)

        ctx = mock.Mock()
        ctx.peak_rss_gb = 0.0
        with mock.patch.object(_MOD, "RSS_POLL_S", 0), \
             mock.patch.object(_MOD, "tree_rss_gb",
                                side_effect=samples), \
             mock.patch("os.path.exists", side_effect=fake_exists), \
             mock.patch("time.sleep"):
            _watch_rss(999, ctx)
        self.assertEqual(ctx.peak_rss_gb, 20.0)


class JobHandleWatchTest(unittest.TestCase):
    def test_starts_daemon_thread(self):
        ctx = JobHandle.__new__(JobHandle)
        ctx.peak_rss_gb = 0.0
        with mock.patch.object(_MOD, "_watch_rss") as fake_watch:
            t = ctx.watch(123)
            t.join(timeout=1)
        fake_watch.assert_called_once_with(123, ctx)


class EnsureVmaTest(unittest.TestCase):
    def test_noop_on_nonpositive_target(self):
        with mock.patch("builtins.open") as op:
            ensure_vma(0)
            op.assert_not_called()

    def test_already_high_enough(self):
        with mock.patch("builtins.open",
                         _fake_open({"/proc/sys/vm/max_map_count":
                                     "999999\n"})), \
             mock.patch("subprocess.run") as run:
            ensure_vma(1000)
            run.assert_not_called()

    def test_raises_via_sudo(self):
        with mock.patch("builtins.open",
                         _fake_open({"/proc/sys/vm/max_map_count":
                                     "100\n"})), \
             mock.patch("subprocess.run") as run:
            run.return_value.returncode = 0
            ensure_vma(1000)
            run.assert_called_once_with(
                ["sudo", "sysctl", "-w", "vm.max_map_count=1000"])

    def test_unreadable_is_nonfatal(self):
        with mock.patch("builtins.open", side_effect=OSError("nope")):
            ensure_vma(1000)   # must not raise


class PreflightNumactlTest(unittest.TestCase):
    def test_skips_none_entries(self):
        with mock.patch("subprocess.run") as run:
            ok, reasons = preflight_numactl([None])
            self.assertTrue(ok)
            self.assertEqual(reasons, [])
            run.assert_not_called()

    def test_missing_numactl(self):
        with mock.patch("shutil.which", return_value=None):
            ok, reasons = preflight_numactl(["0-3"])
            self.assertFalse(ok)
            self.assertIn("0-3", reasons[0])

    def test_all_pass(self):
        with mock.patch("shutil.which", return_value="/usr/bin/numactl"), \
             mock.patch("subprocess.run") as run:
            run.return_value.returncode = 0
            ok, reasons = preflight_numactl(["0-3", "4-7"])
            self.assertTrue(ok)
            self.assertEqual(reasons, [])

    def test_accumulates_all_failures(self):
        with mock.patch("shutil.which", return_value="/usr/bin/numactl"), \
             mock.patch("subprocess.run") as run:
            run.return_value.returncode = 1
            ok, reasons = preflight_numactl(["0-3", "4-7"])
            self.assertFalse(ok)
            self.assertEqual(len(reasons), 2)


class RunFigsTest(unittest.TestCase):
    def test_success_runs_runall_then_pdflatex_twice_places_pdf(self):
        with mock.patch("subprocess.run") as run, \
             mock.patch("os.path.isfile", return_value=True), \
             mock.patch("os.makedirs"), \
             mock.patch("shutil.copy2") as copy2:
            run.return_value.returncode = 0
            run.return_value.stdout = ""
            rc = run_figs()
            self.assertEqual(rc, 0)
            self.assertEqual(run.call_count, 3)  # RUNALL + 2x pdflatex
            runall_call = run.call_args_list[0]
            self.assertEqual(runall_call.args[0], ["bash", "RUNALL.sh"])
            self.assertEqual(runall_call.kwargs["cwd"], EVAL_DIR)
            for c in run.call_args_list[1:]:
                self.assertEqual(c.args[0][0], "pdflatex")
                self.assertEqual(c.kwargs["cwd"], RUN_DATA_DIR)
            copy2.assert_called_once_with(
                os.path.join(RUN_DATA_DIR, "list_figures.pdf"), PDF_PATH)

    def test_runall_failure_is_nonfatal(self):
        with mock.patch("subprocess.run") as run, \
             mock.patch("os.path.isfile", return_value=True), \
             mock.patch("os.makedirs"), \
             mock.patch("shutil.copy2"):
            run.return_value.returncode = 1
            run.return_value.stdout = ""
            rc = run_figs()
            self.assertEqual(rc, 0)  # RUNALL failures don't fail the run

    def test_missing_pdf_after_compile_is_reported(self):
        with mock.patch("subprocess.run") as run, \
             mock.patch("os.path.isfile", return_value=False), \
             mock.patch("shutil.copy2") as copy2:
            run.return_value.returncode = 0
            run.return_value.stdout = "some pdflatex error"
            rc = run_figs()
            self.assertEqual(rc, 1)
            copy2.assert_not_called()


class CheckRequiredFilesTest(unittest.TestCase):
    def test_all_present(self):
        with mock.patch("os.path.isfile", return_value=True):
            ok, reasons = check_required_files(["/a", "/b"])
            self.assertTrue(ok)
            self.assertEqual(reasons, [])

    def test_accumulates_all_missing(self):
        with mock.patch("os.path.isfile", return_value=False):
            ok, reasons = check_required_files(["/a", "/b"])
            self.assertFalse(ok)
            self.assertEqual(len(reasons), 2)
            self.assertIn("/a", reasons[0])
            self.assertIn("/b", reasons[1])


@dataclass
class _FakePlan:
    top: str
    mode: str
    leaf_keys: list


def _leaf_result(failed, triage_tgz=None):
    return LeafResult(rc=1 if failed else 0, wall_s=1.0,
                       raw_data_written=[], failed=failed,
                       triage_tgz=triage_tgz, peak_rss_gb=0.0, note="")


class StubLeafTest(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        patches = [
            mock.patch.object(_MOD, "JOB_LOG_DIR",
                               os.path.join(self.tmp.name, "logs")),
            mock.patch.object(_MOD, "FAILED_TGZ_DIR",
                               os.path.join(self.tmp.name, "failed_tgz")),
            mock.patch.object(_MOD, "LOGS_DIR",
                               os.path.join(self.tmp.name, "job_logs")),
        ]
        for p in patches:
            p.start()
            self.addCleanup(p.stop)
        os.makedirs(os.path.join(self.tmp.name, "job_logs"))

    def test_stub_returns_clean_leafresult(self):
        run_fn = stub_leaf("dlp", "M102")
        ctx = JobHandle("dlp", "dry")
        result = run_fn("dry", ctx)
        self.assertEqual(result.rc, 0)
        self.assertFalse(result.failed)
        self.assertIsNone(result.triage_tgz)
        self.assertIn("M102", result.note)

    def test_all_five_stub_keys_registered(self):
        expected = {"dlp": "M102", "dna": "M103", "clam": "M104",
                    "scale_clam": "M104", "scale_dlp": "M102"}
        for key, milestone in expected.items():
            self.assertIn(key, JOB_SPECS)
            ctx = JobHandle(key, "dry")
            result = JOB_SPECS[key].run_fn("dry", ctx)
            self.assertFalse(result.failed)
            self.assertIn(milestone, result.note)


class SequencerRunTest(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        patches = [
            mock.patch.object(_MOD, "SUMMARY_LOG",
                               os.path.join(self.tmp.name, "SUMMARY.log")),
            mock.patch.object(_MOD, "JOB_LOG_DIR",
                               os.path.join(self.tmp.name, "logs")),
        ]
        for p in patches:
            p.start()
            self.addCleanup(p.stop)

    def test_continues_after_organic_failure(self):
        bad = _leaf_result(True, triage_tgz="/x/bundle.tgz")
        ok = _leaf_result(False)
        specs = {"a": JobSpec("a", "a", lambda m, c: bad),
                  "b": JobSpec("b", "b", lambda m, c: ok)}
        with mock.patch.object(_MOD, "JOB_SPECS", specs):
            seq = Sequencer(_FakePlan("full_run", "full", ["a", "b"]))
            rc = seq.run()
        self.assertEqual(rc, 1)
        with open(_MOD.SUMMARY_LOG) as f:
            text = f.read()
        self.assertIn("FAIL   a", text)
        self.assertIn("triage: /x/bundle.tgz", text)
        self.assertIn("OK     b", text)

    def test_signal_mid_sequence_skips_remaining(self):
        ok = _leaf_result(False)
        seq_holder = {}

        def abort_then_ok(mode, ctx):
            seq_holder["seq"]._aborted = True
            return ok

        specs = {"a": JobSpec("a", "a", lambda m, c: ok),
                  "b": JobSpec("b", "b", abort_then_ok),
                  "c": JobSpec("c", "c", lambda m, c: ok)}
        with mock.patch.object(_MOD, "JOB_SPECS", specs):
            seq = Sequencer(_FakePlan("full_run", "full", ["a", "b", "c"]))
            seq_holder["seq"] = seq
            rc = seq.run()
        self.assertEqual(rc, 0)
        with open(_MOD.SUMMARY_LOG) as f:
            text = f.read()
        self.assertIn("START  a", text)
        self.assertIn("START  b", text)
        self.assertIn("SKIP   c", text)
        self.assertNotIn("START  c", text)


class SequencerRunFnExceptionTest(unittest.TestCase):
    """A run_fn bug that raises instead of returning a LeafResult (e.g. a
    launch-level failure outside the subprocess it started) must not kill
    the whole Sequencer -- see _run_one_leaf's try/except."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        patches = [
            mock.patch.object(_MOD, "SUMMARY_LOG",
                               os.path.join(self.tmp.name, "SUMMARY.log")),
            mock.patch.object(_MOD, "JOB_LOG_DIR",
                               os.path.join(self.tmp.name, "logs")),
            mock.patch.object(_MOD, "FAILED_TGZ_DIR",
                               os.path.join(self.tmp.name, "failed_tgz")),
            mock.patch.object(_MOD, "LOGS_DIR",
                               os.path.join(self.tmp.name, "job_logs")),
        ]
        for p in patches:
            p.start()
            self.addCleanup(p.stop)
        os.makedirs(os.path.join(self.tmp.name, "job_logs"))

    def test_uncaught_exception_becomes_a_failed_result_not_a_crash(self):
        def boom(mode, ctx):
            raise RuntimeError("launch-level bug")
        ok = _leaf_result(False)
        specs = {"a": JobSpec("a", "a", boom),
                  "b": JobSpec("b", "b", lambda m, c: ok)}
        with mock.patch.object(_MOD, "JOB_SPECS", specs):
            seq = Sequencer(_FakePlan("full_run", "full", ["a", "b"]))
            rc = seq.run()   # must NOT raise
        self.assertEqual(rc, 1)
        with open(_MOD.SUMMARY_LOG) as f:
            text = f.read()
        self.assertIn("FAIL   a", text)
        self.assertIn("triage:", text)
        self.assertIn("OK     b", text)   # sequence continued past the crash

        tgz = glob.glob(os.path.join(self.tmp.name, "failed_tgz", "*.tgz"))
        self.assertEqual(len(tgz), 1)
        with tarfile.open(tgz[0]) as t:
            summary = t.extractfile("SUMMARY.txt").read().decode()
        self.assertIn("UNCAUGHT EXCEPTION", summary)
        self.assertIn("RuntimeError: launch-level bug", summary)


class TerminateAllTest(unittest.TestCase):
    def setUp(self):
        _CHILDREN.clear()
        self.addCleanup(_CHILDREN.clear)

    def test_kills_only_live_children(self):
        live = _FakeProc(pid=111)
        dead = _FakeProc(pid=222)
        dead.returncode = 0
        _CHILDREN.extend([live, dead])
        with mock.patch("os.getpgid", return_value=999), \
             mock.patch("os.killpg") as killpg:
            _terminate_all()
        killpg.assert_called_once_with(999, signal.SIGTERM)


class InstallSignalHandlersTest(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        p = mock.patch.object(
            _MOD, "SUMMARY_LOG", os.path.join(self.tmp.name, "SUMMARY.log"))
        p.start()
        self.addCleanup(p.stop)
        _CHILDREN.clear()
        self.addCleanup(_CHILDREN.clear)
        self.addCleanup(signal.signal, signal.SIGINT,
                         signal.getsignal(signal.SIGINT))
        self.addCleanup(signal.signal, signal.SIGTERM,
                         signal.getsignal(signal.SIGTERM))

    def test_sets_aborted_and_writes_summary(self):
        seq = Sequencer(_FakePlan("full_run", "full", []))
        install_signal_handlers(seq)
        signal.getsignal(signal.SIGINT)(signal.SIGINT, None)
        self.assertTrue(seq._aborted)
        with open(_MOD.SUMMARY_LOG) as f:
            text = f.read()
        self.assertIn("SIGNAL SIGINT caught", text)


class ResolvePlanTest(unittest.TestCase):
    def test_small_and_figs_need_no_items(self):
        self.assertEqual(resolve_plan("small", None),
                          ResolvedPlan("small", None, []))
        self.assertEqual(resolve_plan("figs", None),
                          ResolvedPlan("figs", None, []))

    def test_numeric_items(self):
        plan = resolve_plan("dry_run", "1,3,5")
        self.assertEqual(plan.mode, "dry")
        self.assertEqual(plan.leaf_keys, ["dlp", "clam", "reef"])

    def test_key_items(self):
        plan = resolve_plan("full_run", "dlp,clam")
        self.assertEqual(plan.mode, "full")
        self.assertEqual(plan.leaf_keys, ["dlp", "clam"])

    def test_all_expansion(self):
        plan = resolve_plan("dry_run", "all")
        self.assertEqual(plan.leaf_keys, _LEAF_KEYS)

    def test_all_wins_over_mixed_tokens(self):
        plan = resolve_plan("dry_run", "dlp,A,clam")
        self.assertEqual(plan.leaf_keys, _LEAF_KEYS)

    def test_dedup_preserves_first_order(self):
        plan = resolve_plan("dry_run", "1,3,1")
        self.assertEqual(plan.leaf_keys, ["dlp", "clam"])

    def test_unknown_run_rejected(self):
        with self.assertRaises(SystemExit):
            resolve_plan("bogus", "1")

    def test_missing_items_rejected(self):
        with self.assertRaises(SystemExit):
            resolve_plan("dry_run", None)

    def test_bad_item_rejected(self):
        with self.assertRaises(SystemExit):
            resolve_plan("dry_run", "9")
        with self.assertRaises(SystemExit):
            resolve_plan("dry_run", "bogus_key")


class BuildArgparserTest(unittest.TestCase):
    def test_parses_run_and_items(self):
        args = build_argparser().parse_args(
            ["--run", "dry_run", "--items", "dlp,clam"])
        self.assertEqual(args.run, "dry_run")
        self.assertEqual(args.items, "dlp,clam")
        self.assertFalse(args.plan_only)

    def test_dry_run_flag_maps_to_plan_only(self):
        args = build_argparser().parse_args(["--dry-run", "--run", "small"])
        self.assertTrue(args.plan_only)


class InteractiveSelectTest(unittest.TestCase):
    def test_top_level_only(self):
        with mock.patch("builtins.input", side_effect=["1"]):
            plan = interactive_select()
        self.assertEqual(plan, ResolvedPlan("small", None, []))

    def test_submenu_selection(self):
        with mock.patch("builtins.input", side_effect=["2", "dlp,clam"]):
            plan = interactive_select()
        self.assertEqual(plan.top, "dry_run")
        self.assertEqual(plan.leaf_keys, ["dlp", "clam"])

    def test_default_choices_on_blank_input(self):
        with mock.patch("builtins.input", side_effect=["", ""]):
            plan = interactive_select()
        self.assertEqual(plan.top, "small")

    def test_invalid_top_choice_rejected(self):
        with mock.patch("builtins.input", side_effect=["9"]):
            with self.assertRaises(SystemExit):
                interactive_select()


class GoBackgroundTest(unittest.TestCase):
    def test_child_redirects_stdio_and_returns(self):
        with mock.patch("os.fork", side_effect=[0, 0]), \
             mock.patch("os.setsid"), \
             mock.patch("os.chdir"), \
             mock.patch("os.dup2"), \
             mock.patch("os.close"), \
             mock.patch("os.open", return_value=3) as mopen:
            go_background()  # both forks return 0 -> falls through
        self.assertTrue(mopen.called)
        for call in mopen.call_args_list:
            self.assertEqual(call.args[0], os.devnull)

    def test_parent_exits(self):
        with mock.patch("os.fork", return_value=123), \
             mock.patch("os._exit", side_effect=SystemExit) as mexit:
            with self.assertRaises(SystemExit):
                go_background()
            mexit.assert_called_once_with(0)


class MainTest(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        p = mock.patch.object(
            _MOD, "SUMMARY_LOG", os.path.join(self.tmp.name, "SUMMARY.log"))
        p.start()
        self.addCleanup(p.stop)

    def test_list_flag_prints_and_returns(self):
        with mock.patch("sys.argv", ["prog", "--list"]):
            self.assertEqual(main(), 0)

    def test_small_is_a_stub_no_backgrounding(self):
        with mock.patch("sys.argv", ["prog", "--run", "small"]), \
             mock.patch.object(_MOD, "go_background") as gb:
            self.assertEqual(main(), 0)
            gb.assert_not_called()

    def test_figs_dispatch_calls_run_figs(self):
        with mock.patch("sys.argv", ["prog", "--run", "figs"]), \
             mock.patch.object(_MOD, "go_background") as gb, \
             mock.patch.object(_MOD, "run_figs", return_value=0) as rf:
            self.assertEqual(main(), 0)
            gb.assert_not_called()
            rf.assert_called_once()

    def test_figs_plan_only_skips_run_figs(self):
        with mock.patch("sys.argv",
                         ["prog", "--dry-run", "--run", "figs"]), \
             mock.patch.object(_MOD, "run_figs") as rf:
            self.assertEqual(main(), 0)
            rf.assert_not_called()

    def test_plan_only_skips_execution(self):
        with mock.patch("sys.argv",
                         ["prog", "--dry-run", "--run", "dry_run",
                          "--items", "dlp"]), \
             mock.patch.object(_MOD, "go_background") as gb:
            self.assertEqual(main(), 0)
            gb.assert_not_called()

    def test_full_dispatch_calls_sequencer(self):
        fake_seq = mock.Mock()
        fake_seq.run.return_value = 0
        with mock.patch("sys.argv",
                         ["prog", "--run", "dry_run", "--items", "dlp"]), \
             mock.patch.object(_MOD, "go_background") as gb, \
             mock.patch.object(_MOD, "Sequencer",
                                return_value=fake_seq) as SeqCls, \
             mock.patch.object(_MOD, "install_signal_handlers") as ish:
            self.assertEqual(main(), 0)
            gb.assert_called_once()
            SeqCls.assert_called_once()
            ish.assert_called_once_with(fake_seq)
            fake_seq.run.assert_called_once()


class EndToEndWiringTest(unittest.TestCase):
    """Proves CLI -> resolve_plan -> Sequencer -> JobHandle wiring across
    all 8 canonical leaf keys, standing in stub_leaf() run_fns for the 3
    not-yet-real leaves (lkup/zombie/reef) so this doesn't wait on
    Stage 2. CURRENT_JOB.log is out of scope here -- only a real leaf's
    spawn helper calls point_current_job()."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        patches = [
            mock.patch.object(_MOD, "SUMMARY_LOG",
                               os.path.join(self.tmp.name, "SUMMARY.log")),
            mock.patch.object(_MOD, "JOB_LOG_DIR",
                               os.path.join(self.tmp.name, "logs")),
            mock.patch.object(_MOD, "FAILED_TGZ_DIR",
                               os.path.join(self.tmp.name, "failed_tgz")),
            mock.patch.object(_MOD, "LOGS_DIR",
                               os.path.join(self.tmp.name, "job_logs")),
        ]
        for p in patches:
            p.start()
            self.addCleanup(p.stop)
        os.makedirs(os.path.join(self.tmp.name, "job_logs"))

        specs = dict(JOB_SPECS)
        for key in ("lkup", "zombie", "reef"):
            specs[key] = JobSpec(key, key, stub_leaf(key, "Stage 2"))
        p = mock.patch.object(_MOD, "JOB_SPECS", specs)
        p.start()
        self.addCleanup(p.stop)

    def test_full_8_leaf_plan_runs_end_to_end(self):
        with mock.patch("sys.argv",
                         ["prog", "--run", "dry_run", "--items", "A"]), \
             mock.patch.object(_MOD, "go_background") as gb, \
             mock.patch.object(_MOD, "install_signal_handlers") as ish:
            rc = main()
        self.assertEqual(rc, 0)
        gb.assert_called_once()
        ish.assert_called_once()
        with open(_MOD.SUMMARY_LOG) as f:
            text = f.read()
        self.assertEqual(re.findall(r"START\s+(\S+)", text),
                          list(_LEAF_KEYS))
        self.assertEqual(re.findall(r"OK\s+(\S+)", text),
                          list(_LEAF_KEYS))
        self.assertIn("DONE   overall_rc=0", text)


if __name__ == "__main__":
    sys.exit(main())
