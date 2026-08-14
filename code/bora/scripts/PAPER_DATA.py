#!/usr/bin/env python3
# ---------------------------------------------------------------------
# PAPER_DATA.py -- paper-data runner for bora.
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


# Cleared by _preflight() when the numactl probe fails.  ONE decision
# point: resolve_process_model() is numa_available()'s only caller, so
# every leaf degrades to a single unpinned process together.
_NUMA_PROBE_OK = True


def numa_available():
    """numactl exists, nnodes() >= 2, and the launch probe passed."""
    return (bool(shutil.which("numactl")) and nnodes() >= 2
            and _NUMA_PROBE_OK)


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


# ---- process-tree sampling (RSS + CPU, one /proc walk per sample) ----

_CLK_TCK = os.sysconf("SC_CLK_TCK")   # stat utime/stime unit, 100 on Linux


def _stat_fields(proc_dir):
    """<proc_dir>/stat split AFTER the comm column, so a comm containing
    spaces or ')' cannot shift the indices.  [] when the task is gone."""
    try:
        line = open(os.path.join(proc_dir, "stat")).read()
        return line[line.rfind(")") + 2:].split()
    except OSError:
        return []


def _stat_field(proc_dir, idx):
    """One post-comm stat field, None when absent."""
    f = _stat_fields(proc_dir)
    return f[idx] if idx < len(f) else None


def _ppid(pid):
    v = _stat_field("/proc/%d" % pid, 1)
    return int(v) if v is not None else 0


def _cpu_ticks(pid):
    """utime+stime for pid in clock ticks (stat fields 14/15), 0 when
    the pid is gone.  One read, not two: this is the watchdog hot loop."""
    f = _stat_fields("/proc/%d" % pid)
    return int(f[11]) + int(f[12]) if len(f) > 12 else 0


def _proc_state(pid):
    """State char ('R','S','D','Z',...), "" when the pid is gone.  'Z'
    and "" both mean there is nothing left to supervise."""
    return _stat_field("/proc/%d" % pid, 0) or ""


def _wchan(proc_dir):
    """Kernel function the task is blocked in, "-" when running or
    unreadable.  Takes a dir so it serves pids and /task/<tid> alike."""
    try:
        return open(os.path.join(proc_dir, "wchan")).read().strip() or "-"
    except OSError:
        return "-"


def _vmrss_kb(pid):
    try:
        for ln in open("/proc/%d/status" % pid):
            if ln.startswith("VmRSS:"):
                return int(ln.split()[1])
    except OSError:
        pass
    return 0


def _tree_pids(root_pid):
    """Every pid whose parent chain reaches root_pid, root included.
    SORTED: os.listdir order is not stable, and an unsorted tuple would
    read as progress to _watch_child's liveness key."""
    out = []
    for entry in os.listdir("/proc"):
        if not entry.isdigit():
            continue
        pid, hops = int(entry), 0
        while pid > 1 and hops < 64:
            if pid == root_pid:
                out.append(int(entry))
                break
            pid = _ppid(pid)
            hops += 1
    return sorted(out)


def _rss_gb(pids):
    """Summed VmRSS over pids, in GiB."""
    return sum(_vmrss_kb(p) for p in pids) / (1024.0 * 1024.0)


def _cpu_s(pids):
    """Summed CPU seconds over pids.  NOT monotone -- the sum FALLS when
    a child exits, which is why _watch_child tests its progress key for
    INEQUALITY instead of ratcheting a high-water mark."""
    return sum(_cpu_ticks(p) for p in pids) / float(_CLK_TCK)


def tree_rss_gb(root_pid):
    """Sum VmRSS across every pid whose parent chain reaches root_pid."""
    return _rss_gb(_tree_pids(root_pid))


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
    run_log = ctx.log_path("run")
    point_current_job(run_log, None)
    p, t = spawn(cargo_test_cmd(test_path), env, run_log, ctx.key)
    ctx.watch(p, run_log)
    p.wait()
    _join_pump(t)
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


def _kill_proc(p, sig=signal.SIGTERM):
    """Signal the whole process group spawn() gave p its own session
    for."""
    try:
        os.killpg(os.getpgid(p.pid), sig)
    except (OSError, ProcessLookupError):
        pass


def run_rust_two_half(ctx, spec):
    """part1 on node_ranges[0], part2 on node_ranges[1] (staggered so
    their RAM peaks don't overlap); if part2_proves, part1's exit
    releases the snark-gate flag so part2's decider proceeds."""
    a, b = spec.node_ranges
    cmd = cargo_test_cmd(spec.test)
    log1, log2 = ctx.log_path("part1"), ctx.log_path("part2")
    point_current_job(log1, log2)
    shutil.rmtree(FLAG_DIR, ignore_errors=True)  # stale gate = no gate

    env1 = spec.env_fn("p1", fold_only=True, one_proof=False, wait_flag=None)
    env2 = spec.env_fn("p2", fold_only=not spec.part2_proves,
                        one_proof=spec.part2_proves,
                        wait_flag=FLAG if spec.part2_proves else None)

    p1, t1 = spawn(numa_prefix(a) + cmd, env1, log1, "part1")
    ctx.watch(p1, log1)
    if spec.pre_part2:
        status = spec.pre_part2(p1)
        if status != "ready":
            ctx.note("pre_part2 gate: %s (abort)" % status)
            _kill_proc(p1)
            p1.wait()
            _join_pump(t1)
            return 4

    _wait_stagger(p1)
    p2 = t2 = None
    try:
        p2, t2 = spawn(numa_prefix(b) + cmd, env2, log2, "part2")
        ctx.watch(p2, log2)
        p1.wait()
        _join_pump(t1)
        if spec.part2_proves:
            os.makedirs(FLAG_DIR, exist_ok=True)
            open(FLAG, "w").close()
    finally:
        # never leave part2's decider blocked on a flag we forgot to set
        if p2 is not None and p2.poll() is None and not os.path.exists(FLAG):
            os.makedirs(FLAG_DIR, exist_ok=True)
            open(FLAG, "w").close()
    p2.wait()
    _join_pump(t2)
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
    not a cargo test -- no NUMA split, no env_fn convention.  -u because
    a piped python child block-buffers stdout, which would leave the
    watchdog's log axis frozen for the whole run."""
    cmd = [sys.executable, "-u", str(script)] + list(args)
    run_log = ctx.log_path("run")
    point_current_job(run_log, None)
    p, t = spawn(cmd, env, run_log, ctx.key)
    ctx.watch(p, run_log)
    p.wait()
    _join_pump(t)
    return p.returncode


def run_rust_example(ctx, example_name, args, env, log_name="run"):
    """Single-process `cargo run --release --example <name> -- <args>`,
    mirrors run_external_python but for a real bora_cli-style
    binary instead of a cargo test."""
    cmd = example_cmd(example_name, args)
    run_log = ctx.log_path(log_name)
    point_current_job(run_log, None)
    p, t = spawn(cmd, env, run_log, ctx.key)
    ctx.watch(p, run_log)
    p.wait()
    _join_pump(t)
    return p.returncode


# =====================================================================
# neo example launch (M102 D101): env scrub + two-half + scale packer
# =====================================================================

RUSTFLAGS_NEO = "-C link-args=-fuse-ld=lld -Awarnings"

PART_TOKEN = "{part_id}"   # substituted by run_example_two_half

KILL_GRACE_S = 60          # SIGTERM -> SIGKILL, and the pump-join bound


def neo_env(b_show_dropped=False):
    """The one env builder for bora_cli and small's cargo-test spawns:
    os.environ minus every ZKR_* (neo is argv-only; ~90 legacy env
    knobs must not leak in), RUSTFLAGS forced for deterministic
    builds."""
    dropped = sorted(k for k in os.environ if k.startswith("ZKR_"))
    e = {k: v for k, v in os.environ.items()
         if not k.startswith("ZKR_")}
    e["RUSTFLAGS"] = RUSTFLAGS_NEO
    if b_show_dropped and dropped:
        log("neo_env: dropped %s" % " ".join(dropped))
    return e


def example_cmd(example_name, args):
    """`cargo run --release --example <name> -- <args>`."""
    return ["cargo", "run", "--release", "--example", example_name,
            "--"] + list(args)


def _join_pump(t):
    """Bounded join for a spawn() pump thread.  A descendant that escaped
    the group can hold the stdout pipe open past its leader; the pump is
    a daemon, so an expired join is harmless -- every completed line is
    already in the log.  No-op for a part that never started."""
    if t:
        t.join(timeout=KILL_GRACE_S)


def _reap(p, t):
    """Wait out p and join its log pump.  Bounded (SIGTERM -> SIGKILL,
    capped join) except the post-SIGKILL wait, which only D-state can
    delay.  No-op for a part that never started."""
    if p is None:
        return
    try:
        p.wait(timeout=KILL_GRACE_S)
    except subprocess.TimeoutExpired:
        _kill_proc(p, signal.SIGKILL)
        p.wait()
    _join_pump(t)


# ---- sequence-level abort ---------------------------------------------

ABORT_RC = 8       # leaf stopped by an operator signal, not by a bug

# Set ONLY by install_signal_handlers' handler.  A module global rather
# than a Sequencer attribute because the leaf helpers that must stop
# mid-flight (two-half gates, scale sweep loops) hold no Sequencer.
_ABORTED = False


def aborted():
    """True once SIGINT/SIGTERM has been seen.  Read at every point a
    leaf is about to commit to another multi-hour unit of work."""
    return _ABORTED


def _abort_leaf(ctx, why, rc=ABORT_RC):
    """Record an abort where the operator sees it -- SUMMARY.log, not
    only the triage bundle (nothing prints LeafResult.note).  Returns
    the rc the leaf should carry."""
    line = "%s -- abort" % why
    _summary_line("       %s" % line)
    ctx.note(line)
    return rc


def _abort_two_half(ctx, rc, when):
    """part1 is dead: part2 must not be launched, nor its decider
    released.  Carries part1's own rc, not ABORT_RC."""
    return _abort_leaf(ctx, "part1 rc=%s %s" % (rc, when), rc)


def run_example_two_half(ctx, example_name, args, env, node_ranges):
    """Two-part neo launch: the spawns differ ONLY in the part_id argv
    token (PART_TOKEN -> "0"/"1"; role logic lives in Rust; Python
    labels part1/part2 = part_id 0/1); part2 always proves.  Unlike
    run_rust_two_half, a dead part1 aborts instead of releasing part2's
    decider, and the finally signals BOTH halves before waiting."""
    assert args.count(PART_TOKEN) == 1, args
    a, b = node_ranges

    def argv(pid):
        return [str(pid) if t == PART_TOKEN else t for t in args]

    log1, log2 = ctx.log_path("part1"), ctx.log_path("part2")
    point_current_job(log1, log2)
    shutil.rmtree(FLAG_DIR, ignore_errors=True)  # stale gate = no gate
    p1 = p2 = t1 = t2 = None
    try:
        p1, t1 = spawn(
            numa_prefix(a) + example_cmd(example_name, argv(0)),
            env, log1, "part1")
        ctx.watch(p1, log1)
        _wait_stagger(p1)
        # part2 waits for part1's RAM, never for its data, so a clean
        # early exit is fine -- a dry part1 exits well inside the 900 s
        # stagger.  A dead part1 is not: the leaf is already lost.
        rc1 = p1.poll()      # None = still folding, 0 = done early
        if rc1:              # crash / OOM / operator kill
            return _abort_two_half(ctx, rc1, "before part2 launch")
        # GATE 1 of 2.  Both gates are load-bearing: the operator's kill
        # lands at an arbitrary point, and each gate guards a distinct
        # multi-hour commitment (a whole second half; a Groth16
        # decider).  Signalling alone is not enough -- _terminate_all
        # kills what is RUNNING, not what we are about to start.
        if aborted():
            return _abort_leaf(ctx, "signal before part2 launch")
        p2, t2 = spawn(
            numa_prefix(b) + example_cmd(example_name, argv(1)),
            env, log2, "part2")
        ctx.watch(p2, log2)
        # the stagger normally exits with part1 ALIVE (900 s + RSS
        # drop), so part1 usually dies HERE -- and the flag below would
        # release part2's Groth16 decider for a leaf already lost.
        rc1 = p1.wait()
        if rc1:
            return _abort_two_half(ctx, rc1, "mid-fold")
        if aborted():        # GATE 2 of 2
            return _abort_leaf(ctx, "signal before snark-gate release")
        os.makedirs(FLAG_DIR, exist_ok=True)
        open(FLAG, "w").close()      # part1's RAM is free: prove
        p2.wait()
        return p1.returncode or p2.returncode
    finally:
        # anything alive here is on an abort path: signal BOTH halves
        # before waiting on either -- part2 holds a whole socket, and
        # part1 can take minutes to tear down a 500 GB fold.
        for p in (p1, p2):
            if p is not None and p.poll() is None:
                _kill_proc(p)
        # cleanup must never mask the leaf's real exception -- but a
        # failed reap must not vanish either.
        for p, t in ((p1, t1), (p2, t2)):
            try:
                _reap(p, t)
            except Exception as e:
                ctx.note("reap failed: %s" % e)


SCALE_BEGIN_RE = re.compile(r"==== SCALE ROUND BEGIN count=(\d+)\b")
SCALE_END_RE = re.compile(r"==== SCALE ROUND END count=(\d+)")


def pack_scale_bundle(run_log, dest):
    """Split run_log on the SCALE ROUND markers and pack one
    log_<count>.txt.tgz per round into dest (attic split_and_pack
    port; a trailing BEGIN with no END -- crash mid-round -- is kept).
    dest is replaced only by a sweep that COMPLETED >=1 round, so a
    crash can never clobber a committed bundle.
    Returns the number of rounds packed; placement is atomic."""
    rounds, cur_cnt, buf = [], None, []
    for line in open(run_log, errors="replace"):
        mb = SCALE_BEGIN_RE.search(line)
        if mb:
            if cur_cnt is not None:
                rounds.append((cur_cnt, buf))
            cur_cnt, buf = int(mb.group(1)), [line]
            continue
        if cur_cnt is None:
            continue
        buf.append(line)
        if SCALE_END_RE.search(line):
            rounds.append((cur_cnt, buf))
            cur_cnt, buf = None, []
    if cur_cnt is not None:                # trailing (un-ENDed) round
        rounds.append((cur_cnt, buf))
    # A partial round carries no usable data point, so a sweep that
    # died before its first END must leave the committed bundle alone
    # (2026-08-11: such a crash replaced a 4.5 MB bundle with a 695 B
    # log). Partial rounds still ride along once one round completed.
    n_end = sum(1 for _, lines in rounds
                if any(SCALE_END_RE.search(ln) for ln in lines))
    if not n_end:
        log("pack_scale_bundle: 0 completed rounds in %s (%d partial);"
            " %s left untouched" % (run_log, len(rounds), dest))
        return 0

    os.makedirs(os.path.dirname(dest), exist_ok=True)
    tmp = dest + ".tmp"
    if os.path.exists(tmp):
        os.unlink(tmp)
    with tempfile.TemporaryDirectory() as td:
        inner = []
        for cnt, lines in rounds:
            txt = os.path.join(td, "log_%d.txt" % cnt)
            with open(txt, "w") as f:
                f.writelines(lines)
            tgz = os.path.join(td, "log_%d.txt.tgz" % cnt)
            with tarfile.open(tgz, "w:gz", compresslevel=9) as t:
                t.add(txt, arcname=os.path.basename(txt))
            inner.append(tgz)
            ended = any(SCALE_END_RE.search(ln) for ln in lines)
            log("pack_scale_bundle: round count=%d: %d lines%s" % (
                cnt, len(lines),
                "" if ended else " (NO END -- partial)"))
        with tarfile.open(tmp, "w:gz", compresslevel=9) as t:
            for tgz in inner:
                t.add(tgz, arcname=os.path.basename(tgz))
    os.replace(tmp, dest)
    log("pack_scale_bundle: packed %d round(s) -> %s"
        % (len(rounds), dest))
    return len(rounds)


def _tgz_single(dest, src, arcname):
    """dest <- gzip tar holding exactly src, named arcname."""
    with tarfile.open(dest, "w:gz", compresslevel=9) as t:
        t.add(src, arcname=arcname)


def pack_full_dump(base, run_logs, ts):
    """Place raw_data/<SERVER>/<base>{,.partN}.tgz from the run
    log(s): 1 log -> plain single-member tgz (extract_tgz contract),
    2 logs -> one nested partN_<ts>.log.tgz each (_read_part_log
    contract). Stale <base>{,.part*}.tgz unlinked first --
    resolve_server_dump prefers surviving parts. Returns dest paths."""
    assert len(run_logs) in (1, 2), run_logs
    dest_dir = os.path.dirname(raw_data_path(base + ".tgz"))
    os.makedirs(dest_dir, exist_ok=True)
    built = []                        # (dest_name, tmp_path)
    with tempfile.TemporaryDirectory() as td:
        if len(run_logs) == 1:
            tmp = os.path.join(dest_dir, base + ".tgz.tmp")
            if os.path.exists(tmp):
                os.unlink(tmp)
            _tgz_single(tmp, run_logs[0], "run_%s.log" % ts)
            built.append((base + ".tgz", tmp))
        else:
            for i, lg in enumerate(run_logs, 1):
                nested = os.path.join(td,
                                       "part%d_%s.log.tgz" % (i, ts))
                _tgz_single(nested, lg, "part%d_%s.log" % (i, ts))
                name = "%s.part%d.tgz" % (base, i)
                tmp = os.path.join(dest_dir, name + ".tmp")
                if os.path.exists(tmp):
                    os.unlink(tmp)
                _tgz_single(tmp, nested, os.path.basename(nested))
                built.append((name, tmp))
        for stale in ([os.path.join(dest_dir, base + ".tgz")]
                       + sorted(glob.glob(os.path.join(
                           dest_dir, base + ".part*.tgz")))):
            if os.path.exists(stale):
                os.unlink(stale)
        dests = []
        for name, tmp in built:
            dest = os.path.join(dest_dir, name)
            os.replace(tmp, dest)
            log("pack_full_dump: placed %s" % dest)
            dests.append(dest)
    return dests


BORA_PLAN_ROOT = "/tmp/bora"   # Rust plan_dir() sandboxes live here


def ladders_diverge(name):
    """True when the two parts' tuned ladders differ (byte compare;
    missing file = divergence). Identical argv must yield identical
    ladders (C103), so divergence invalidates the combined dump."""
    lads = []
    for pid in (0, 1):
        p = os.path.join(BORA_PLAN_ROOT,
                          "%s_neo_p%d" % (name, pid), "ladder.json")
        if not os.path.isfile(p):
            return True
        lads.append(open(p, "rb").read())
    return lads[0] != lads[1]


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


def stale_artifact(path, t0):
    """Reason when path is missing or older than t0 -- a leftover from
    an EARLIER run that this child never rewrote, which would otherwise
    be harvested as fresh data.  None when the file is this run's."""
    if not os.path.isfile(path):
        return "missing artifact %s" % path
    if os.path.getmtime(path) < t0:
        return "stale artifact %s (not rewritten by this run)" % path
    return None


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

# No-progress window before the watchdog kills a child tree.  Calibrated
# against MEASURED healthy silence on the archived production runs:
# 7.67 h (full_dlp) and 2.14 h (full_clam) of whole-LOG silence, when
# every job sits in "Phase 1 step 3: generate cmF" at once.  Only the
# second axis (tree cpu) makes 4 h survivable at all -- a log-silence
# watchdog is refuted outright by those numbers.  ctx.peak_idle_s
# reports each run's actual margin against this, so the calibration is
# re-measured by every run instead of standing on those two.
STALL_S = 4 * 3600

EVIDENCE_PIDS = 12   # per-pid evidence lines in SUMMARY.log; rest in the dump

# "panicked", never bare "panic".  A Rust panic always prints
# "panicked at"; the bare token only ever matched source text, and on
# 2026-08-14 it failed a zombie leaf that had passed (rc 0, 24/24 ok)
# on one rustc warning quoting `use std::{.., panic, ..}` from circ.
FAIL_RE = re.compile(
    r"panicked|SIGABRT|Killed|out of memory|cannot allocate|"
    r"CapErr|FATAL|error\[|VERIFICATION FAILED|SPLIT VERIFY: FAIL")

# advisory lines that legitimately contain failure keywords
ADVISORY_RE = re.compile(r"CAVEAT:|WARN big job")

# A rustc/cargo diagnostic quoting the source it is complaining about:
# "32 | use std::..." or the "   |    ^^^" underline beneath it.  That
# text is the compiler's INPUT, not its verdict, so a keyword inside it
# proves nothing -- and every leaf that shells out to cargo puts these
# in run.log.  Narrower than dropping "panic" alone: it also covers a
# warning that happens to quote a line containing CapErr or FATAL.
# A real diagnostic is still caught by its own "error[Ennnn]" header,
# which carries no gutter.
ECHO_RE = re.compile(r"^\s*(?:\d+\s*)?\|")


@dataclass
class LeafResult:
    rc: int
    wall_s: float
    raw_data_written: list
    failed: bool
    triage_tgz: object          # str path, or None
    peak_rss_gb: float
    note: str
    # Largest no-progress gap the watchdog saw, in seconds.  Defaulted so
    # the error paths that build a LeafResult by hand need not care; the
    # point is that every run reports its own margin against STALL_S.
    peak_idle_s: float = 0.0


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


# ---- greppable run trailer (peak RSS + wall clock) -------------------
# spawn() writes ONLY the child's stdout into the per-job run log, and
# point_current_job() symlinks CURRENT_JOB.log at that file, so neither
# the wall clock nor the peak RSS appears there unless we append it.
# Each line below starts with a FIXED prefix at column 0 so a grep
# matches the label, never the number.
#
# PEAK RSS SOURCE: JobHandle.peak_rss_gb, filled by _watch_child from
# _rss_gb(_tree_pids(pid)) -- the max, over samples, of the SUM of
# /proc/<pid>/status VmRSS across every process whose parent chain
# reaches the spawned child.  UNIT: GiB (1024^3 bytes).
#   COVERS   the whole descendant tree alive at sample time: numactl,
#            cargo, the test binary and any grandchildren (the pid walk
#            follows parent chains to any depth, not just direct
#            children).
#   MISSES   (a) a spike shorter than the RSS_POLL_S (10 s) sampling
#            interval; (b) a process that both starts and exits between
#            two samples; (c) PAPER_DATA.py's own RSS, which is not in
#            the child's tree.
#   INFLATES pages SHARED between tree members (mapped libraries, COW
#            after fork) count once per process, so a many-process fold
#            reads higher than the kernel's true unique footprint.
# Deliberately NOT resource.getrusage(RUSAGE_CHILDREN): its ru_maxrss is
# the max over INDIVIDUAL reaped children and never their sum, so it
# under-reports a parallel multi-job fold -- exactly this run's shape --
# and it only counts children already waited for.
RC_PREFIX = "PAPER_DATA_RC"
RSS_PREFIX = "PAPER_DATA_PEAK_RSS_GIB"
WALL_PREFIX = "PAPER_DATA_WALL_CLOCK_S"


def append_run_trailer(log_path, res):
    """Append the rc / peak-RSS / wall-clock trailer to the per-job run
    log -- the file CURRENT_JOB.log points at.  Call AFTER ctx.finish()
    so these lines are never seen by the failure scan."""
    with open(log_path, "a") as f:
        f.write("\n%s %d\n" % (RC_PREFIX, res.rc))
        f.write("%s %.3f\n" % (RSS_PREFIX, res.peak_rss_gb))
        f.write("%s %.1f\n" % (WALL_PREFIX, res.wall_s))


def _log_mtime(path):
    try:
        return os.path.getmtime(path)
    except OSError:
        return 0.0


def _stall_evidence(pids, log_path, idle):
    """Brief, quotable proof that a tree is WEDGED and not merely quiet:
    what each pid is blocked in, plus both liveness axes as numbers."""
    out = ["no progress for %.0f s (threshold %d s)" % (idle, STALL_S),
           "log %s silent for %.0f s" % (
               os.path.basename(log_path),
               time.time() - _log_mtime(log_path)),
           "tree cpu %.1f s across %d pids (unchanged)" % (
               _cpu_s(pids), len(pids))]
    for p in pids[:EVIDENCE_PIDS]:
        out.append("pid %d state=%s cpu=%.1fs wchan=%s" % (
            p, _proc_state(p) or "gone",
            _cpu_ticks(p) / float(_CLK_TCK), _wchan("/proc/%d" % p)))
    if len(pids) > EVIDENCE_PIDS:
        out.append("... %d more pids (see stall dump)"
                   % (len(pids) - EVIDENCE_PIDS))
    return out


def _stall_dump(ctx, pids, log_path, idle):
    """Full per-THREAD wedge dump into the job dir, registered so the
    triage bundle carries it.  Best-effort -- a watchdog must never die
    of a /proc read that lost its race with process exit."""
    try:
        path = ctx.report_path("stall_%d" % int(time.time() - ctx._t0))
        with open(path, "w") as f:
            f.write("\n".join(_stall_evidence(pids, log_path, idle)))
            f.write("\n\n== per-thread ==\n")
            for p in pids:
                d = "/proc/%d/task" % p
                for tid in sorted(os.listdir(d), key=str):
                    td = os.path.join(d, tid)
                    f.write("pid %d tid %s state=%s wchan=%s\n" % (
                        p, tid, _stat_field(td, 0) or "gone", _wchan(td)))
        return path
    except Exception as e:      # a watchdog must never die of a dump
        ctx.note("stall dump failed: %s" % e)
        return None


def _stall_kill(p, ctx, pids, log_path, idle, label):
    """SIGTERM then SIGKILL a wedged tree.  Records the reason and its
    evidence BEFORE signalling, so both are in ctx._notes by the time
    the leaf reaches finish() no matter how the teardown goes."""
    try:
        pgid = os.getpgid(p.pid)   # ONCE, before any wait can reap it
    except OSError:
        return                     # already gone; nothing to kill
    ev = _stall_evidence(pids, log_path, idle)
    ctx.note("STALL %s: %s" % (label, ev[0]))
    _summary_line("       STALL %s -- killing: %s" % (label, ev[0]))
    for ln in ev[1:]:
        _summary_line("           %s" % ln)
    _stall_dump(ctx, pids, log_path, idle)
    for sig in (signal.SIGTERM, signal.SIGKILL):
        try:
            os.killpg(pgid, sig)
        except OSError:
            return
        try:
            p.wait(timeout=KILL_GRACE_S)
            return
        except subprocess.TimeoutExpired:
            pass
    ctx.note("STALL %s: survived SIGKILL" % label)
    _summary_line("       STALL %s: survived SIGKILL -- re-escalating"
                  % label)


def _watch_child(p, log_path, ctx):
    """Supervisor thread for one spawned child: tracks peak tree-RSS and
    kills a tree that has made no progress on EITHER axis for STALL_S.
    Progress = any change in (pids, tree cpu, log mtime).  The cpu sum
    falls when a child exits, so the test is inequality with a re-based
    key, never a high-water mark: a shrinking tree IS progress."""
    pid, label = p.pid, os.path.basename(log_path)
    key, last, warned = None, time.time(), False
    # p.returncode is a plain attribute read: never poll()/wait() here,
    # or this thread reaps the child and every later os.getpgid(p.pid)
    # races pid reuse.  _proc_state covers the child that died while the
    # main thread was blocked on its sibling.
    while p.returncode is None and _proc_state(pid) not in ("", "Z"):
        pids = _tree_pids(pid)
        gb = _rss_gb(pids)
        if gb > ctx.peak_rss_gb:
            ctx.peak_rss_gb = gb
        now = (tuple(pids), _cpu_s(pids), _log_mtime(log_path))
        idle = time.time() - last
        if idle > ctx.peak_idle_s:
            ctx.peak_idle_s = idle     # the run's own margin vs STALL_S
        if now != key:
            key, last, warned = now, time.time(), False
        elif idle >= STALL_S:
            _stall_kill(p, ctx, pids, log_path, idle, label)
            last, warned = time.time(), False      # re-arm on a survivor
        elif idle >= STALL_S // 2 and not warned:
            warned = True
            _summary_line("       %s: no progress for %.0f s "
                          "(kill at %d s)" % (label, idle, STALL_S))
        time.sleep(RSS_POLL_S)


class JobHandle:
    def __init__(self, key, mode):
        self.key = key
        self.mode = mode
        self.peak_rss_gb = 0.0
        self.peak_idle_s = 0.0    # largest no-progress gap seen vs STALL_S
        self.raw_data = []
        self.reports = []
        self._t0 = time.time()
        self._ts = datetime.datetime.now().strftime("%Y%m%d_%H%M%S")
        self._dir = os.path.join(JOB_LOG_DIR,
                                  "%s_%s_%s" % (key, mode, self._ts))
        os.makedirs(self._dir, exist_ok=True)
        # Per-job logs from a PRIOR run must not counterfeit this leaf's
        # failure scan.  SNAPSHOT what already exists rather than
        # deleting it: this code also runs under `python3 -m unittest
        # PAPER_DATA`, where deleting wiped the live run's logs out from
        # under it (A2017).  _job_logs() scopes the scan instead.
        self._pre_logs = set(
            glob.glob(os.path.join(LOGS_DIR, "log_job_*.txt")))
        self._log_paths = []
        self._notes = []

    def log_path(self, name):
        p = os.path.join(self._dir, "%s.log" % name)
        if p not in self._log_paths:
            self._log_paths.append(p)
        return p

    def report_path(self, name):
        """A file the leaf PRODUCES, as opposed to a spawn log: bundled
        on failure but never fail-scanned, because a report's own text
        is data, not evidence about the run that made it."""
        p = os.path.join(self._dir, "%s.dat" % name)
        if p not in self.reports:
            self.reports.append(p)
        return p

    def note(self, line):
        self._notes.append(line)

    def watch(self, p, log_path):
        t = threading.Thread(target=_watch_child, args=(p, log_path, self),
                              daemon=True)
        t.start()
        return t

    def _job_logs(self):
        """The Rust per-job logs belonging to THIS leaf: anything absent
        at job start, plus pre-existing names rewritten since.  Errs
        toward inclusion -- a missed panic is a silent false PASS, an
        extra one is a loud FAIL."""
        out = []
        for jf in glob.glob(os.path.join(LOGS_DIR, "log_job_*.txt")):
            if jf not in self._pre_logs:
                out.append(jf)
                continue
            try:
                if os.path.getmtime(jf) >= self._t0:
                    out.append(jf)
            except OSError:
                pass
        return out

    def _fail_lines(self):
        srcs = list(self._log_paths) + self._job_logs()
        lines = []
        for s in srcs:
            if os.path.isfile(s):
                with open(s, errors="replace") as f:
                    for ln in f:
                        if FAIL_RE.search(ln) \
                                and not ADVISORY_RE.search(ln) \
                                and not ECHO_RE.match(ln):
                            lines.append(ln.rstrip("\n"))
        return lines

    def _pack_bundle(self, rc, wall, fails):
        os.makedirs(FAILED_TGZ_DIR, exist_ok=True)
        tgz = os.path.join(
            FAILED_TGZ_DIR, "paper_data_%s_%s_%s_BUNDLE.tgz" % (
                self.key, self.mode, self._ts))
        summ = os.path.join(self._dir, "SUMMARY.txt")
        with open(summ, "w") as f:
            f.write("PAPER_DATA -- %s (%s)\n" % (self.key, self.mode))
            f.write("host=%s ts=%s\n" % (platform.node(), self._ts))
            f.write("rc=%s wall_s=%.1f peak_rss_gb=%.1f "
                     "peak_idle_s=%.0f/%d\n" %
                     (rc, wall, self.peak_rss_gb, self.peak_idle_s,
                      STALL_S))
            for ln in self._notes:
                f.write(ln + "\n")
            f.write("\n== failure signatures (last 40) ==\n")
            f.write(("\n".join(fails[-40:]) or "(none)") + "\n")
        with tarfile.open(tgz, "w:gz", compresslevel=6) as t:
            t.add(summ, arcname="SUMMARY.txt")
            for p in self._log_paths:
                if os.path.isfile(p):
                    t.add(p, arcname="logs/" + os.path.basename(p))
            for jf in self._job_logs():
                t.add(jf, arcname="logs/" + os.path.basename(jf))
            for rp in self.reports:
                if rp and os.path.isfile(rp):
                    t.add(rp, arcname=os.path.basename(rp))
        return tgz

    def finish(self, rc, b_fail_scan=True):
        # b_fail_scan=False: the leaf verdicts by rc + its own positive
        # markers (scale: EXPECTED CapErr bump-retries print panic text
        # into a successful log, which the scan would counterfeit).
        # The scan still RUNS on an rc != 0 leaf so _pack_bundle keeps
        # its "failure signatures" section -- it just gets no VOTE.
        wall = time.time() - self._t0
        failed = rc != 0
        fails = self._fail_lines() if (b_fail_scan or failed) else []
        failed = failed or (b_fail_scan and bool(fails))
        triage_tgz = None
        if failed:
            triage_tgz = self._pack_bundle(rc, wall, fails)
            self.note("triage: %s" % triage_tgz)
        return LeafResult(rc=rc, wall_s=wall,
                           raw_data_written=self.raw_data, failed=failed,
                           triage_tgz=triage_tgz,
                           peak_rss_gb=self.peak_rss_gb,
                           note="; ".join(self._notes),
                           peak_idle_s=self.peak_idle_s)


# =====================================================================
# Layer D -- common infra (D6: preflight)
# =====================================================================

# vm.max_map_count floor requested at launch.  Rust re-checks with a
# data-derived estimate and aborts after the DB build (foldpot/driver
# .rs:2453); 8M covers that formula for the measured full run (8 jobs
# x 34071 packed fields: 32768 + 8*34071*16 -> next power of two).
VMA_TARGET = 8_388_608


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


def plan_required_files(plan):
    """Ordered union of every selected leaf's required files for this
    mode.  Leaves with no declaration contribute nothing."""
    out = []
    for key in plan.leaf_keys:
        fn = JOB_SPECS[key].required_files
        for p in (fn(plan.mode) if fn else []):
            if p not in out:
                out.append(p)
    return out


def _preflight(plan):
    """Sequenced-top launch gate, run BEFORE go_background() so a
    failure lands on the terminal.  A missing input file aborts (nonzero
    rc); a failed numactl probe only degrades the run to one unpinned
    process per leaf.  The vm.max_map_count raise is main()'s, not this
    gate's -- three tops never reach here."""
    global _NUMA_PROBE_OK
    ok, reasons = check_required_files(plan_required_files(plan))
    if not ok:
        for r in reasons:
            log("PREFLIGHT ABORT: %s" % r)
        return 2
    ok, reasons = preflight_numactl(
        resolve_process_model().node_ranges)
    if not ok:
        _NUMA_PROBE_OK = False
        for r in reasons:
            log("PREFLIGHT WARN: %s" % r)
        log("PREFLIGHT: NUMA split disabled; one unpinned process "
            "per leaf")
    return 0


# =====================================================================
# Layer C -- leaf registry (contract only; real entries land in Stage 2)
# =====================================================================

@dataclass
class JobSpec:
    key: str
    label: str
    run_fn: object       # (mode, ctx) -> LeafResult
    # optional (mode) -> list of files this leaf cannot run without.
    # Mode-dependent because dry and full launch DIFFERENT children.
    # None = nothing Python owns to check (the Rust leaves assert on
    # their own config/corpus paths, which live in DatasetSpec).
    required_files: object = None


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


# dry_run's collect_lookup_stats_adv perc -- kept small so the leaf
# builds a deterministically-thinned DB per dataset instead of the real
# full-size one. full_run always uses perc=100 (the real report).
LKUP_DRY_PERC = 5

# Markers collect_lookup_stats_adv actually emits: one
# "Lookup Composition: <name>" header per dataset (clam_db.rs
# fmt_lkup_dist), the cross table (zkp_driver.rs fmt_cross_rollup), and
# the closing banner.  Anything short of all of them is a truncated
# report.
LKUP_SECTIONS = ("Lookup Composition: Mal", "Lookup Composition: Dna",
                 "Lookup Composition: Dlp", "Cross-Dataset Roll-up")
LKUP_END = "END LOOKUP COMPOSITION REPORT"


def lkup_missing_success(path, t0):
    """None when the lkup report is complete and was written by THIS
    run, else the reason.  A positive predicate because the fail scan
    cannot be used here: collect_lookup_stats_adv println!s the whole
    report before writing it, so the report's own text -- signature
    names, category labels -- is in run.log either way."""
    if not os.path.isfile(path):
        return "no report at %s" % path
    if os.path.getmtime(path) < t0:
        return "stale report, not rewritten this run"
    text = open(path, errors="replace").read()
    missing = [s for s in LKUP_SECTIONS if s not in text]
    if missing:
        return "report missing: %s" % ", ".join(missing)
    if LKUP_END not in text:
        return "report has no END banner (truncated)"
    return None


def run_leaf_analyze_lkup(mode, ctx):
    """Q2 lookup-composition report (Mal+Dna+Dlp), via
    bora_data_driver::collect_lookup_stats_adv. dry builds each
    dataset's DB over a deterministically-thinned perc% subset of its
    signatures; full builds every real signature (perc=100)."""
    perc = LKUP_DRY_PERC if mode == "dry" else 100
    local_out = ctx.report_path("lookup_stats")
    env = neo_env()
    rc = run_rust_example(ctx, "bora_cli",
                           ["lkup", str(perc), local_out], env)
    if rc == 0:
        missing = lkup_missing_success(local_out, ctx._t0)
        if missing:
            ctx.note("lkup: %s" % missing)
            rc = 6
        else:
            dest = place_raw_data(local_out, "lookup_stats.dat",
                                   server_specific=False)
            ctx.raw_data.append(dest)
    return ctx.finish(rc, b_fail_scan=False)


# bora_cli full_dlp constants (spec 8.7/8.10a): dry = 0.25% DB
# (25 rules) x 0.0198% samples (100 files of the 504,854 master),
# light (light also drops the cover check); full = legacy
# full_dlp()'s own defaults. (perc_db, perc_samples, circs, jobs,
# light); numa_num/part_id/ladder_only are call-site tokens.
DLP_LEAF_ARGS = {
    "dry":  ("0.25", "0.0198", "2", "2", "1"),
    "full": ("100", "100", "4", "8", "0"),
}


def dlp_argv(mode, numa_num, part):
    """The 9-token bora_cli argv for one full_dlp part; part is "0"
    (single process) or PART_TOKEN (two-half). ladder_only always 0."""
    pdb, ps, nc, nj, light = DLP_LEAF_ARGS[mode]
    return ["full_dlp", pdb, ps, nc, nj, str(numa_num), part,
            light, "0"]


# The THREE per-job fold-completion markers the driver can emit
# (foldpot/driver.rs:3216 skip-snark, :3247 fold-only, :3254 proving).
# A two-half part_id 0 is non-proving (b_folding_only), so it reaches
# ONLY the :3247 form -- omitting it scores a healthy 8-job run as 4
# and silently skips pack_full_dump. The optional ":" is that form's
# separator ("Job 0: b_folding_only set").
FOLD_OK_RE = re.compile(
    r"Job (\d+):? (?:folding done|generating SNARK proof|"
    r"b_folding_only set)")
VERIFY_IND_RE = re.compile(r"Verify Individual Proof")

# The NEGATIVE marker. A failed self-verification is LOGGED and the run
# deliberately CONTINUES, so one bad job cannot kill its expensive
# siblings (driver.rs:3553-3560 batch, :3573-3580 individual) -- the
# process still exits 0. VERIFY_IND_RE above cannot see it either: that
# log_perf (:3582) sits AFTER the failure branch and prints either way.
# So this is the only thing standing between a bad proof and a PASS.
VERIFY_FAIL_RE = re.compile(r"PROOF VERIFICATION FAILED")


def dlp_missing_success(logs, num_jobs):
    """Verdict for a one_proof neo run: no job logged a verification
    failure, every job logged a completed fold, and exactly ONE
    individual proof verified.  None when satisfied, else the reason."""
    done, n_ver = 0, 0
    for lg in logs:
        text = open(lg, errors="replace").read()
        # Checked FIRST: a bad proof outranks any marker-count reason.
        if VERIFY_FAIL_RE.search(text):
            return "PROOF VERIFICATION FAILED in %s" % os.path.basename(lg)
        # per-log distinct set: two-half parts number jobs locally
        done += len({int(m.group(1))
                     for m in FOLD_OK_RE.finditer(text)})
        n_ver += len(VERIFY_IND_RE.findall(text))
    if done != num_jobs:
        return "fold-done markers %d != num_jobs %d" % (done, num_jobs)
    if n_ver != 1:
        return "Verify Individual Proof count %d != 1" % n_ver
    return None


def run_leaf_full_neo(mode, ctx, argv_fn, base, num_jobs, name,
                       b_fail_scan):
    """Shared full-run leaf body (DLP/Clamav): one process on a
    1-socket box, two-half + p0/p1 ladder tripwire otherwise;
    verdict = rc + positive markers; packs <base>{,.partN}.tgz."""
    model = resolve_process_model()
    env = neo_env()
    if model.n_parts == 1:
        rc = run_rust_example(ctx, "bora_cli",
                               argv_fn(mode, 1, "0"), env)
        logs = [ctx.log_path("run")]
    else:
        rc = run_example_two_half(ctx, "bora_cli",
                                   argv_fn(mode, 2, PART_TOKEN),
                                   env, model.node_ranges)
        logs = [ctx.log_path("part1"), ctx.log_path("part2")]
        if rc == 0 and ladders_diverge(name):
            ctx.note("p0/p1 ladder.json diverge: dump invalid")
            rc = 5
    if rc == 0:
        missing = dlp_missing_success(logs, num_jobs)
        if missing:
            ctx.note("success markers missing: %s" % missing)
            rc = 6
    if rc == 0:
        for dest in pack_full_dump(base, logs, ctx._ts):
            ctx.raw_data.append(dest)
    return ctx.finish(rc, b_fail_scan=b_fail_scan)


def run_leaf_dlp(mode, ctx):
    """M102 DLP leaf: bora_cli full_dlp (neo, argv-only)."""
    # b_fail_scan=False, as dna/clam. A check-on aggressive fold runs
    # under a CatchGuard, which makes install_fail_fast_panic_hook
    # return early (driver.rs:2411-2417), so the DEFAULT hook prints
    # the EXPECTED self-cover CapErr (composable_gadget_mapper.rs:1213)
    # into a SUCCESSFUL log -- both its "panicked at" line and its
    # "CapErr(..)" payload line match FAIL_RE, and no whitelist can
    # cover the first (it carries no marker). full mode only: dry
    # clears b_check_lkup (bora_data_driver.rs:1344), so no dry sweep
    # can see it. Verdict = rc + dlp_missing_success's markers, which
    # now include the PROOF VERIFICATION FAILED negative marker.
    return run_leaf_full_neo(mode, ctx, dlp_argv, "full_dlp",
                              int(DLP_LEAF_ARGS[mode][3]), "dlp",
                              False)


# bora_cli full_dna constants (M103): dry = 1% DB (276 of 27,501
# sigs) x 2% sample (the lone chr17 file byte-shrinks Rust-side to
# ~832KB ~ 7 fold steps), light; full = legacy test_full_dna's shape
# (whole 41.6MB sample, 1 circuit, heavy one-proof snark). Always 1
# job / 1 process (user decision: the sample is offset-anchored and
# cannot split). (perc_db, perc_samples, circs, jobs, light).
DNA_LEAF_ARGS = {
    "dry":  ("1", "2", "1", "1", "1"),
    "full": ("100", "100", "1", "1", "0"),
}


def dna_argv(mode):
    """The 9-token bora_cli argv for full_dna; numa_num/part_id are
    hardwired 1/0 (never two-half) and ladder_only is 0."""
    pdb, ps, nc, nj, light = DNA_LEAF_ARGS[mode]
    return ["full_dna", pdb, ps, nc, nj, "1", "0", light, "0"]


def run_leaf_dna(mode, ctx):
    """M103 DNA leaf: bora_cli full_dna (neo, argv-only), always one
    process/one job; packs the single run log as full_dna.tgz."""
    rc = run_rust_example(ctx, "bora_cli", dna_argv(mode), neo_env())
    logs = [ctx.log_path("run")]
    if rc == 0:
        missing = dlp_missing_success(logs, 1)  # generic in num_jobs
        if missing:
            ctx.note("success markers missing: %s" % missing)
            rc = 6
    if rc == 0:
        for dest in pack_full_dump("full_dna", logs, ctx._ts):
            ctx.raw_data.append(dest)
    # b_fail_scan=False (D103 pattern): the NON-AGGR tuner prints its
    # caught CapErr probe panics into the run log, so FAIL_RE would
    # counterfeit a FAIL on every successful run. Verdict = rc + the
    # positive markers above.
    return ctx.finish(rc, b_fail_scan=False)


# bora_cli full_clam constants (M104): dry = 0.5% DB (195 sigs of
# the in-range pool) x 0.1% corpus (deterministic subset = gpg2 +
# xtables-multi, 843,688 B ~ 106 steps at dry chunk 256), light;
# full = legacy production full_clamav's shape (8 jobs, heavy).
# num_circs is 2 in BOTH modes: the spec ladder [2] is structural.
# (perc_db, perc_samples, circs, jobs, light).
CLAM_LEAF_ARGS = {
    "dry":  ("0.5", "0.1", "2", "2", "1"),
    "full": ("100", "100", "2", "8", "0"),
}


def clam_argv(mode, numa_num, part):
    """The 9-token bora_cli argv for one full_clam part; part is "0"
    (single process) or PART_TOKEN (two-half). ladder_only always 0."""
    pdb, ps, nc, nj, light = CLAM_LEAF_ARGS[mode]
    return ["full_clam", pdb, ps, nc, nj, str(numa_num), part,
            light, "0"]


def run_leaf_clamav(mode, ctx):
    """M104 Clamav leaf: bora_cli full_clam (neo, argv-only);
    verdicts scan-free (the non-aggr tuner prints caught CapErr
    probe panics into every successful log, M103 11.4)."""
    return run_leaf_full_neo(mode, ctx, clam_argv, "full_clam",
                              int(CLAM_LEAF_ARGS[mode][3]), "clam",
                              False)


# bora_cli scale_dlp counts (spec 8.10c), pin-INCLUSIVE units: each
# legacy entry +1; top 9861 = the complete rule set. Bundles land under
# the literal any_server names gen_scale_all.py hardcodes.
SCALE_DLP_COUNTS = {
    # dry top halved 987 -> 494 (493 + pin) 2026-08-11: measured
    # peak RSS is 22.3GB + 0.0136*count GB, so the count buys 6.7GB
    # of the cut and DLP's new dry_range2_bit 22 buys the rest.
    "dry":  [2, 494],
    "full": [2, 987, 1973, 2959, 3945, 4931, 5917, 6903, 7889,
             8875, 9861],
}

# (corpus_idx, bundle, log tag); order = DLP.scale_sources (idx 0 =
# griffith-j/continental/2. sparse, idx 1 = donohoe-t/sent/6. dense).
SCALE_DLP_RUNS = [(0, "scale_data_dlp_2.tgz", "scale_2"),
                  (1, "scale_data_dlp_6.tgz", "scale_6")]


def scale_missing_rounds(log_path, counts):
    """Positive success check: every requested count printed its ROUND
    END marker (emitted only after that round's fold succeeded).
    Returns None when satisfied, else the missing-counts reason."""
    text = open(log_path, errors="replace").read()
    ended = {int(m.group(1)) for m in SCALE_END_RE.finditer(text)}
    missing = [c for c in counts if c not in ended]
    if missing:
        return "no ROUND END for counts %s" % missing
    return None


def run_leaf_scale_dlp(mode, ctx):
    """M102 Scale-DLP leaf: two sequential bora_cli scale_dlp sweeps,
    one per fixed corpus, the second running even if the first failed;
    dry passes dry=1 (22-bit range table, corpus left whole). Each log
    is packed into its any_server bundle even on a crash (partial
    rounds kept; 0 rounds leave the bundle untouched)."""
    counts = SCALE_DLP_COUNTS[mode]
    arg = ",".join(str(c) for c in counts)
    dry = "1" if mode == "dry" else "0"
    env = neo_env()
    rc = 0
    for idx, bundle, tag in SCALE_DLP_RUNS:
        # Each sweep is hours; the operator's kill must not be followed
        # by the NEXT one.  Record first, combine after -- `rc or
        # _abort_leaf(...)` would skip the recorder in exactly the case
        # where sweep 1 had already failed.
        if aborted():
            arc = _abort_leaf(ctx, "signal before %s" % tag)
            rc = rc or arc
            break
        lg = ctx.log_path(tag)
        try:
            rc_i = run_rust_example(ctx, "bora_cli",
                                     ["scale_dlp", str(idx), arg, dry],
                                     env, log_name=tag)
        finally:
            dest = raw_data_path(bundle, server_specific=False)
            if os.path.isfile(lg) and pack_scale_bundle(lg, dest):
                ctx.raw_data.append(dest)
        if rc_i == 0:
            missing = scale_missing_rounds(lg, counts)
            if missing:
                ctx.note("%s: %s" % (tag, missing))
                rc_i = 7
        else:
            ctx.note("%s: rc=%s" % (tag, rc_i))
        rc = rc or rc_i
    return ctx.finish(rc, b_fail_scan=False)


# bora_cli scale_clam counts: CLAM legacy pins nothing, so counts
# keep legacy cardinality (subset swaps one perm rule for the pin).
# full = [1] + rounded 10%..100% of 38,875 (legacy formula
# (p*38875+5)/10); dry = [1, 300] (user 2026-08-10).
SCALE_CLAM_COUNTS = {
    "dry":  [1, 300],
    "full": [1, 3888, 7775, 11663, 15550, 19438, 23325, 27213,
             31100, 34988, 38875],
}

# (corpus_idx, bundle, log tag); order = CLAM.scale_sources (idx 0 =
# readelf sparse/easy, idx 1 = gdb dense).
SCALE_CLAM_RUNS = [(0, "scale_data_readelf.tgz", "scale_readelf"),
                   (1, "scale_data_gdb.tgz", "scale_gdb")]


def run_leaf_scale_clamav(mode, ctx):
    """M104 Scale-ClamAV leaf: two sequential bora_cli scale_clam
    sweeps (readelf then gdb), the second running even if the first
    failed; dry passes light=1 (dry chunk shape). Bundles pack in a
    finally, partial rounds kept."""
    counts = SCALE_CLAM_COUNTS[mode]
    arg = ",".join(str(c) for c in counts)
    light = "1" if mode == "dry" else "0"
    env = neo_env()
    rc = 0
    for idx, bundle, tag in SCALE_CLAM_RUNS:
        if aborted():        # see run_leaf_scale_dlp for why not `rc or`
            arc = _abort_leaf(ctx, "signal before %s" % tag)
            rc = rc or arc
            break
        lg = ctx.log_path(tag)
        try:
            rc_i = run_rust_example(
                ctx, "bora_cli",
                ["scale_clam", str(idx), arg, light], env,
                log_name=tag)
        finally:
            dest = raw_data_path(bundle, server_specific=False)
            if os.path.isfile(lg) and pack_scale_bundle(lg, dest):
                ctx.raw_data.append(dest)
        if rc_i == 0:
            missing = scale_missing_rounds(lg, counts)
            if missing:
                ctx.note("%s: %s" % (tag, missing))
                rc_i = 7
        else:
            ctx.note("%s: rc=%s" % (tag, rc_i))
        rc = rc or rc_i
    return ctx.finish(rc, b_fail_scan=False)


MS_DLP_DIR = os.path.join(REPO, "data", "src_sig", "ms_dlp")
MS_DLP_SCRIPTS_DIR = os.path.join(MS_DLP_DIR, "scripts")
ZOMBIE_LOG_NAME = "run_zombie_regex_zombie_international.log"
ZOMBIE_DRY_PERC = 4


# The child's per-ruleset summary (run_zombie.py:1085) and its
# do-nothing exit (:1118): an absent ruleset dir is only a print, after
# which main() returns 0 having measured nothing.
ZOMBIE_OK_RE = re.compile(r"\[run_zombie\] \S+ : (\d+) results, (\d+) ok")
ZOMBIE_SKIP_RE = re.compile(r"\[run_zombie\] ruleset (\S+) absent")


def zombie_missing_success(run_log, docs_log, t0):
    """Verdict for a zombie run: every ruleset ran, measured >0 policies
    with >=1 ok, and rewrote the docs log.  Returns (reason, note);
    reason None when satisfied, note set when some policies were not ok
    -- recorded, not fatal (run_zombie.py:617 is failure-tolerant)."""
    text = open(run_log, errors="replace").read()
    skip = ZOMBIE_SKIP_RE.search(text)
    if skip:
        return ("ruleset %s never ran" % skip.group(1), None)
    rows = ZOMBIE_OK_RE.findall(text)
    if not rows:
        return ("no [run_zombie] summary line in %s"
                % os.path.basename(run_log), None)
    n_res = sum(int(a) for a, _ in rows)
    n_ok = sum(int(b) for _, b in rows)
    if n_res == 0:
        return ("0 results measured", None)
    if n_ok == 0:
        return ("0 of %d results ok" % n_res, None)
    stale = stale_artifact(docs_log, t0)
    if stale:
        return (stale, None)
    note = None
    if n_ok < n_res:
        note = "%d of %d policy runs not ok" % (n_res - n_ok, n_res)
    return (None, note)


def zombie_script(mode):
    """Child script for this mode; ONE site so the launch and the
    preflight can never disagree about which file must exist."""
    return os.path.join(MS_DLP_SCRIPTS_DIR,
                        "dry_run_zombie.py" if mode == "dry"
                        else "run_zombie.py")


def run_leaf_zombie(mode, ctx):
    """Spartan-NIZK proximity-non-membership circuits over
    regex_zombie_international/ policies. dry delegates to
    dry_run_zombie.py (evenly-spaced ZOMBIE_DRY_PERC% of policies, small
    proximity-safe VEC_SIZE); full runs run_zombie.py untouched.
    Verdict = rc + a fresh docs log with >=1 ok measurement (the child
    exits 0 after a total failure)."""
    env = dict(os.environ)
    args = [str(ZOMBIE_DRY_PERC)] if mode == "dry" else []
    rc = run_external_python(ctx, zombie_script(mode), args, env)
    src = os.path.join(MS_DLP_DIR, "docs", ZOMBIE_LOG_NAME)
    if rc == 0:
        reason, note = zombie_missing_success(
            ctx.log_path("run"), src, ctx._t0)
        if note:
            ctx.note(note)
        if reason:
            ctx.note("success markers missing: %s" % reason)
            rc = 6
    if rc == 0:
        dest = place_raw_data(src, ZOMBIE_LOG_NAME)
        ctx.raw_data.append(dest)
    return ctx.finish(rc)


REEF_DIR = os.path.join(REPO, "data", "src_sig", "chr17_variants")
REEF_SCRIPTS_DIR = os.path.join(REEF_DIR, "scripts")
REEF_LOG_NAME = "reef_sample_run.log"
REEF_DRY_PERC = 10


# The sweep's three hard-STOP exits (eval_reef.py:496/510/533), its soft
# pool-exhaustion warning (:544), the terminal write (:724), and the
# executed-sample count in the docs log (:652).  EVERY stop still writes
# the log and exits 0.
REEF_STOP_RE = re.compile(r"^\s*STOP: (.+)$", re.M)
REEF_EXHAUST_RE = re.compile(r"^\s*WARN: (\S+) pool exhausted", re.M)
REEF_WROTE_RE = re.compile(r"^wrote \S+ and \S+", re.M)
REEF_SAMPLES_RE = re.compile(r"^timed_out: \d+ of (\d+) samples", re.M)


def reef_missing_success(run_log, docs_log, t0):
    """Verdict for a reef run: no hard STOP, the sweep reached its final
    write, >0 samples executed, and the docs log is this run's.  Returns
    (reason, note); note set when a category's pool ran out (fewer
    samples than targeted, but the data is still usable)."""
    text = open(run_log, errors="replace").read()
    stop = REEF_STOP_RE.search(text)
    if stop:
        return ("sweep STOPped: %s" % stop.group(1).strip(), None)
    if not REEF_WROTE_RE.search(text):
        return ("no terminal 'wrote' line in %s"
                % os.path.basename(run_log), None)
    stale = stale_artifact(docs_log, t0)
    if stale:
        return (stale, None)
    m = REEF_SAMPLES_RE.search(open(docs_log, errors="replace").read())
    if m is None:
        return ("no sample count in %s" % os.path.basename(docs_log),
                None)
    if int(m.group(1)) == 0:
        return ("0 samples executed", None)
    ex = REEF_EXHAUST_RE.findall(text)
    return (None, ("pool exhausted: %s" % ", ".join(ex)) if ex else None)


def reef_script(mode):
    """Child script for this mode; ONE site so the launch and the
    preflight can never disagree about which file must exist."""
    return os.path.join(REEF_SCRIPTS_DIR,
                        "dry_run_eval_reef.py" if mode == "dry"
                        else "eval_reef.py")


def run_leaf_reef(mode, ctx):
    """Reef nlookup non-match baseline over chr17_variants/reef_regex/.
    dry delegates to dry_run_eval_reef.py (REEF_DRY_PERC%-scaled
    sample_size, same 6-category sweep); full runs eval_reef.py
    untouched (its own real config is already a 10/category sample).
    Verdict = rc + a completed, un-STOPped sweep with a fresh docs log
    (the child exits 0 after every hard STOP)."""
    env = dict(os.environ)
    args = [str(REEF_DRY_PERC)] if mode == "dry" else []
    rc = run_external_python(ctx, reef_script(mode), args, env)
    src = os.path.join(REEF_DIR, "docs", REEF_LOG_NAME)
    if rc == 0:
        reason, note = reef_missing_success(
            ctx.log_path("run"), src, ctx._t0)
        if note:
            ctx.note(note)
        if reason:
            ctx.note("success markers missing: %s" % reason)
            rc = 6
    if rc == 0:
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
    "zombie":     JobSpec("zombie",     "Zombie",       run_leaf_zombie,
                          lambda m: [zombie_script(m)]),
    "reef":       JobSpec("reef",       "Reef",         run_leaf_reef,
                          lambda m: [reef_script(m)]),
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


def reset_summary_log(top):
    """Truncate SUMMARY.log and stamp one NEW RUN banner, so a stale
    FAIL from an earlier run can never be misread as the current state.

    Destroys nothing durable: a failed leaf's rc / wall / peak RSS /
    failure signatures and every log already go into its
    FAILED_TGZ_DIR bundle (_pack_bundle), a succeeded leaf's numbers
    survive in the run-log trailer under LOGS_DIR, and NOTHING in
    production reads this file -- it is purely a `tail -F` target.

    The banner deliberately avoids the word START: the per-leaf marker
    at _summary_line("START  %-6s ...") is scanned as START\\s+(\\S+),
    and a banner carrying that token joins the leaf list."""
    os.makedirs(os.path.dirname(SUMMARY_LOG), exist_ok=True)
    with open(SUMMARY_LOG, "w") as f:
        f.write("=== NEW RUN %s | %s | host=%s ===\n"
                % (_ts(), top, platform.node()))


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

    def run(self):
        """Continue-on-failure is the only policy: an organic leaf
        failure never stops the sequence, only a signal does."""
        overall_rc = 0
        for leaf_key in self.plan.leaf_keys:
            if aborted():
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
        # INSIDE the try: JobHandle() itself does I/O (makedirs, a glob
        # of LOGS_DIR), so a full disk or a bad LOGS_DIR must not escape
        # as an uncaught traceback either.
        ctx = None
        try:
            ctx = JobHandle(leaf_key, mode)
            return spec.run_fn(mode, ctx)
        except Exception:
            # A run_fn bug (bad launch args, a helper raising outside the
            # subprocess it launched, etc.) must not kill the whole
            # Sequencer -- funnel it through the same finish()/triage-tgz
            # path as an ordinary rc!=0 failure, so it's visible in
            # SUMMARY.log and bundled instead of an uncaught traceback
            # silently killing the sequence (fatal under go_background(),
            # whose stdio goes to /dev/null).
            return self._failed_leaf(leaf_key, ctx)

    def _failed_leaf(self, leaf_key, ctx):
        """Turn the in-flight exception into a FAILED LeafResult.  Never
        raises: the triage bundle is best-effort because _pack_bundle may
        be exactly what threw."""
        tb = traceback.format_exc()
        if ctx is None:
            _summary_line("       %s: JobHandle init failed:\n%s"
                          % (leaf_key, tb))
            return LeafResult(rc=1, wall_s=0.0, raw_data_written=[],
                              failed=True, triage_tgz=None,
                              peak_rss_gb=0.0,
                              note="JobHandle init failed")
        ctx.note("UNCAUGHT EXCEPTION in %s.run_fn:\n%s" % (leaf_key, tb))
        try:
            return ctx.finish(1)
        except Exception:
            _summary_line("       %s: triage bundle failed:\n%s"
                          % (leaf_key, traceback.format_exc()))
            return LeafResult(rc=1, wall_s=time.time() - ctx._t0,
                              raw_data_written=[], failed=True,
                              triage_tgz=None,
                              peak_rss_gb=ctx.peak_rss_gb,
                              note="triage bundle failed")

    def _append_summary(self, leaf_key, result):
        status = "FAIL" if result.failed else "OK"
        _summary_line(
            "%-6s %-6s rc=%s wall=%ds peak_rss=%.1fGB idle=%ds/%ds" % (
                status, leaf_key, result.rc, int(result.wall_s),
                result.peak_rss_gb, int(result.peak_idle_s), STALL_S))
        if result.triage_tgz:
            _summary_line("       triage: %s" % result.triage_tgz)

    def _append_skipped(self, leaf_key):
        _summary_line("SKIP   %-6s" % leaf_key)

    def _finalize(self, overall_rc):
        _summary_line("DONE   overall_rc=%d" % overall_rc)


def install_signal_handlers():
    """SIGINT/SIGTERM: log it, kill the child tree, set the abort flag.
    Does not raise -- killing the children makes the blocked p.wait()s
    return on their own, so _run_one_leaf finishes its NORMAL path (rc
    != 0 already means failed, so the triage tgz packs exactly like an
    organic crash would).  The flag decides both whether run()'s loop
    starts the NEXT leaf_key and, via aborted(), whether a leaf already
    in flight commits to another sweep or another half."""
    def _on_signal(signum, _frame):
        global _ABORTED
        _summary_line("SIGNAL %s caught -> current leaf finishing, "
                       "then aborting sequence"
                       % signal.Signals(signum).name)
        _terminate_all()
        _ABORTED = True
    signal.signal(signal.SIGINT, _on_signal)
    signal.signal(signal.SIGTERM, _on_signal)


# =====================================================================
# Layer A -- CLI / menu resolution
# =====================================================================

# Dry cost per leaf: (display name, wall MINUTES, peak RSS GiB, note).
# gb None = never measured. Every row below is measured: one `--items
# all` run on 2026-08-11 on a 32-core / 125 GiB box, 8/8 rc=0, 4015s
# total. RSS is tree-wide peak in GiB (watch_rss divides by 1024^2).
#   zombie ran genuinely COLD here -- its partial cache
#   (/tmp/bora_zombie_run + the docs/ mirror) was cleared first, so 6.8
#   min is a from-scratch figure. It still resumes instantly when that
#   cache survives, hence the "cold" note.
#   CAVEAT: zombie's 26.4 GiB is over the 24 GiB dry budget. It is
#   recorded as measured; the pool/concurrency retune is pending.
DRY_COST = [
    ("dlp",        "DLP",           2.4,  6.5,  ""),
    ("dna",        "Dna",           7.0,  15.9, ""),
    ("clam",       "Clamav",        8.7,  17.1, ""),
    ("zombie",     "Zombie",        6.8,  26.4, " cold"),
    ("reef",       "Reef",          23.0, 28.4, ""),
    ("lkup",       "Analyze lkup",  3.5,  8.3,  ""),
    ("scale_clam", "Scale-ClamAV",  7.3,  5.2,  ""),
    ("scale_dlp",  "Scale-DLP",     8.5,  13.0, ""),
]

# small_full_snark is MEASURED, not dry -- a real 4-job fold plus a full
# decider.  Source is the run's own trailer (PAPER_DATA_WALL_CLOCK_S /
# PAPER_DATA_PEAK_RSS_GIB, rc 0, 2026-08-14, 512 GB Jetstream2 box), NOT
# the log's "RAM: nnn GB" lines: those topped out at 327 GB and under-
# report the tree-wide peak by ~106 GiB because they sample only at step
# boundaries.  433 GiB is ~91 percent of a 512 GB box, so this entry is
# marginal there -- it aborted mid-decider on 2026-08-13 and completed
# on the retry.  Units match DRY_COST (GiB, printed as GB).
SNARK_COST_MIN = 113.4     # 6804.8 s, whole leaf including cargo build
SNARK_COST_GIB = 433.2     # tree-wide peak RSS across the 4 jobs


def _fmt_min(m):
    """9.0 -> '9', 2.5 -> '2.5' (no trailing .0 in the menu)."""
    return ("%.1f" % m).rstrip("0").rstrip(".")


def _cost_tag(mins, gb, note="", lead="dry "):
    """'[dry ~9min, ~16.4GB]'; RSS omitted when never measured. The
    rollups pass lead="" -- their context already says dry."""
    if gb is None:
        return "[%s~%smin%s]" % (lead, _fmt_min(mins), note)
    return "[%s~%smin%s, ~%.1fGB]" % (lead, _fmt_min(mins), note, gb)


def dry_total():
    """Cost of `--items all`: wall SUMS (leaves run in sequence) and
    peak RSS is the MAX, not the sum, for the same reason. Uses
    zombie's cold wall, so it is a from-scratch estimate."""
    mins = sum(c[2] for c in DRY_COST)
    gb = max(c[3] for c in DRY_COST if c[3] is not None)
    return mins, gb


TOP_CHOICES = [
    ("small", "small data"),
    ("small_full_snark", "small sample, one full SNARK proof %s"
                         % _cost_tag(SNARK_COST_MIN, SNARK_COST_GIB,
                                     lead="measured ")),
    ("dry_run", "dry_run %s" % _cost_tag(*dry_total(), lead="")),
    ("full_run", "full_run"),
    ("figs", "generate list of figures"),
]

LEAF_CHOICES = [(k, "%s %s" % (name, _cost_tag(mins, gb, note)))
                 for k, name, mins, gb, note in DRY_COST]
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


NO_ITEM_TOPS = ("small", "figs", "small_full_snark")


def resolve_plan(run, items):
    if run in NO_ITEM_TOPS:
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
    print("PAPER_DATA -- select a run:")
    for i, (_, label) in enumerate(TOP_CHOICES, 1):
        print("  (%d) %s" % (i, label))


def _show_submenu(top):
    print("PAPER_DATA -- %s: select one or more "
          "(e.g. \"1,3,5\", \"dlp,clam\", or \"A\"):" % top)
    for i, (_, label) in enumerate(LEAF_CHOICES, 1):
        print("  (%d) %s" % (i, label))
    # the per-leaf costs are DRY measurements, so only dry_run's All
    # gets the rollup; full_run's leaf costs are not measured.
    if top == "dry_run":
        print("  (A) All %s" % _cost_tag(*dry_total(), lead=""))
    else:
        print("  (A) All")


def interactive_select():
    _show_menu()
    choice = input("choice [1]: ").strip() or "1"
    if not choice.isdigit() or not 1 <= int(choice) <= len(TOP_CHOICES):
        raise SystemExit("invalid choice %r" % choice)
    top = TOP_CHOICES[int(choice) - 1][0]
    if top in NO_ITEM_TOPS:
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
# Layer A -- small (menu #1: small_data demo / basic test)
# =====================================================================

SMALL_TEST = "zkp_driver::tests_zkp_driver::test_zkreg_main"
SMALL_REPORT = os.path.join(REPO, "data", "small_data_set",
                             "reports", "report.dat")


def run_small():
    """Menu item #1: one-process cargo test of the small_data_set
    end-to-end ZK proof (~40 s, ~7 GB). Foreground like figs -- far too
    short to be worth daemonizing."""
    ctx = JobHandle("small", "demo")
    ctx.note("mode=small_data (single proc)")
    ctx.reports.append(SMALL_REPORT)
    rc = run_rust_single(ctx, SMALL_TEST, neo_env())
    res = ctx.finish(rc)
    log("small: rc=%d wall=%ds peak_rss=%.1fGB" % (
        res.rc, int(res.wall_s), res.peak_rss_gb))
    if res.failed:
        log("small: FAILED -- triage: %s" % res.triage_tgz)
        return 1
    log("small: report -> %s" % SMALL_REPORT)
    return 0


# =====================================================================
# Layer A -- small_full_snark (menu #2: small sample, one full
# SNARK proof)
# =====================================================================

# Same small_data_set config and capacities as small_data_par (the
# 4-parallel-job small sample), but with the decider run for real.  The
# three flags that define this entry are Rust GlobalConfig fields
# (crates/utils/src/consts.rs), NOT env vars or CLI args, and they are
# set in small_full_snark() in crates/zkregplus/src/bora_data_driver.rs
# -- a deliberate COPY of zkp_driver's small_par_full_snark, so retuning
# that one cannot silently change this menu entry:
#   b_light_test   = false  -- nothing in the decider circuit is elided
#   b_folding_only = false  -- a proof IS produced after the folding
#   b_one_proof    = true   -- every job folds, only Job 0 proves
# Selecting the Rust test that sets them is the same mechanism menu #1
# uses for SMALL_TEST; neo_env() strips every ZKR_* knob, so nothing
# from the operator's shell can override the three.
SMALL_SNARK_TEST = ("bora_data_driver::tests_bora_data_driver::"
                     "test_small_full_snark")
SMALL_SNARK_REPORT = os.path.join(REPO, "data", "small_data_set",
                                   "reports", "report.dat")


def run_small_full_snark():
    """Menu item #2: one-process cargo test of the small_data_par
    config that folds every job and then emits ONE complete SNARK
    proof, with no light-test elision of the decider circuit.  The
    caller has already daemonized, so this runs with stdio on
    /dev/null: the operator follows CURRENT_JOB.log (repointed by
    run_rust_single) and SUMMARY.log.  CURRENT_JOB.log gains a trailer
    carrying peak RSS and wall clock once the run finishes."""
    ctx = JobHandle("small_snark", "full_snark")
    ctx.note("mode=small_full_snark (single proc; b_light_test="
             "false, b_folding_only=false, b_one_proof=true)")
    ctx.reports.append(SMALL_SNARK_REPORT)
    run_log = ctx.log_path("run")
    rc = run_rust_single(ctx, SMALL_SNARK_TEST, neo_env())
    res = ctx.finish(rc)
    # After finish(): the trailer must not be visible to the fail scan,
    # and res is where peak_rss_gb / wall_s become final.
    append_run_trailer(run_log, res)
    _summary_line("%-4s   small_full_snark rc=%s wall=%ds "
                  "peak_rss=%.1fGB idle=%ds/%ds" % (
                      "FAIL" if res.failed else "OK", res.rc,
                      int(res.wall_s), res.peak_rss_gb,
                      int(res.peak_idle_s), STALL_S))
    log("small_full_snark: peak RSS and wall clock -> %s"
        % CURRENT_JOB_LOG)
    if res.failed:
        log("small_full_snark: FAILED -- triage: %s"
            % res.triage_tgz)
        return 1
    log("small_full_snark: report -> %s" % SMALL_SNARK_REPORT)
    return 0


# =====================================================================
# Layer A -- figs (menu #5: regenerate every figure + review PDF)
# =====================================================================

RUN_DATA_DIR = os.path.join(REPO, "data", "paper_data", "run_data")
EVAL_DIR = os.path.join(RUN_DATA_DIR, "scripts", "eval")
PDF_DIR = os.path.join(REPO, "data", "paper_data", "pdf")
PDF_PATH = os.path.join(PDF_DIR, "list_figures.pdf")


def run_figs():
    """Menu item #5: regenerate every figs/*.tex fragment from whatever
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

    # vm.max_map_count for EVERY top, raised here and NOT in _preflight:
    # small / figs / small_full_snark return before that gate, so a box
    # at the kernel default hits the mimalloc VMA ceiling as "memory
    # allocation of N bytes failed" / SIGABRT with RAM still free
    # (small_full_snark, 512GB box, 2026-08-13).  Rust's own check
    # (foldpot/driver.rs:2467) sizes off packed fields and false-passed
    # it at 52,544 est vs >1M actual.  Earliest point with a tty for sudo.
    ensure_vma(VMA_TARGET)

    plan = resolve_plan(args.run, args.items) if args.run \
        else interactive_select()

    log("resolved: python3 PAPER_DATA.py --run %s%s" % (
        plan.top,
        " --items %s" % ",".join(plan.leaf_keys) if plan.leaf_keys else ""))

    # Wipe SUMMARY.log HERE, not next to ensure_vma: this is the first
    # point where a run is actually committed.  Past the --list return
    # and past interactive_select(), so neither --list nor a Ctrl-C at
    # the prompt destroys the previous run's record; guarded on
    # plan_only so "just show me the plan" does not either.  In the
    # parent, before go_background(), so exactly one truncation per
    # invocation and no daemon race.  NOT at module scope -- the unit
    # suite imports this module and would wipe a live operator run.
    if not args.plan_only:
        reset_summary_log(plan.top)

    if plan.top == "small":
        if args.plan_only:
            return 0
        return run_small()

    if plan.top == "figs":
        if args.plan_only:
            return 0
        return run_figs()

    if plan.top == "small_full_snark":
        if args.plan_only:
            return 0
        # Unlike small/figs this runs for hours, so it detaches like the
        # sequenced tops do.  Only ONE process runs, so there is no
        # part2 log to advertise.  run_rust_single() repoints
        # CURRENT_JOB.log and the leaf writes SUMMARY.log, so nothing is
        # lost when stdio goes to /dev/null.
        ts = _ts()
        print("[paper_data %s] detaching into the background "
              "(survives logout; no nohup needed)." % ts)
        print("[paper_data %s]   summary log:    tail -F %s"
              % (ts, SUMMARY_LOG))
        print("[paper_data %s]   current job:    tail -F %s"
              % (ts, CURRENT_JOB_LOG))
        sys.stdout.flush()
        go_background()
        install_signal_handlers()
        return run_small_full_snark()

    if args.plan_only:
        return 0

    rc = _preflight(plan)
    if rc:
        return rc

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
    install_signal_handlers()
    return seq.run()


# =====================================================================
# unit tests -- run with: python3 -m unittest PAPER_DATA
# =====================================================================

_MOD = sys.modules[__name__]

# The suite must be runnable WHILE a production job is live.  Every
# spawn helper repoints the CURRENT_JOB symlinks, and JobHandle globs
# LOGS_DIR, so both are redirected into a temp dir for the whole module
# -- a test must never touch the operator's `tail -F` target or the live
# run's per-job logs (A2017).
_TEST_TMP = None
_TEST_PATCHES = []

# name -> basename under the module temp dir; ".log" ones are files, the
# rest directories that individual tests create as needed.
_TEST_REDIRECTS = {
    "CURRENT_JOB_LOG": "current_job.log",
    "CURRENT_JOB_LOG_PART2": "current_job_part2.log",
    "SUMMARY_LOG": "summary.log",
    "LOGS_DIR": "job_logs",
    "JOB_LOG_DIR": "jobs",
    "FAILED_TGZ_DIR": "failed_tgz",
}


def setUpModule():
    global _TEST_TMP
    _TEST_TMP = tempfile.TemporaryDirectory()
    for name, base in _TEST_REDIRECTS.items():
        p = mock.patch.object(_MOD, name,
                               os.path.join(_TEST_TMP.name, base))
        p.start()
        _TEST_PATCHES.append(p)
    os.makedirs(os.path.join(_TEST_TMP.name, "job_logs"), exist_ok=True)


def tearDownModule():
    for p in _TEST_PATCHES:
        p.stop()
    _TEST_PATCHES.clear()
    _TEST_TMP.cleanup()


def _sandbox_aborted():
    """Un-started patch pinning _ABORTED False for one test.  The flag is
    a module global, so a test that sets it would otherwise leak into
    every later class -- mock restores it on teardown instead."""
    return mock.patch.object(_MOD, "_ABORTED", False)


def _fake_open(path_map):
    """open() replacement: StringIO(content) for known paths, else
    FileNotFoundError."""
    def _open(path, *a, **kw):
        if path in path_map:
            return io.StringIO(path_map[path])
        raise FileNotFoundError(path)
    return _open


def _load_common():
    """The REAL paper-side readers, for packing-contract tests."""
    import importlib.util
    p = os.path.join(RUN_DATA_DIR, "scripts", "common.py")
    spec = importlib.util.spec_from_file_location("bora_common", p)
    m = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(m)
    return m


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

    def test_tree_pids_is_sorted(self):
        """Unsorted pids would fake progress in _watch_child's key."""
        path_map = {
            "/proc/200/stat": "200 (a) S 100 200 200 0 -1",
            "/proc/300/stat": "300 (b) S 100 300 300 0 -1",
        }
        with mock.patch("os.listdir",
                         return_value=["300", "100", "200"]), \
             mock.patch("builtins.open", _fake_open(path_map)):
            self.assertEqual(_tree_pids(100), [100, 200, 300])


class ProcStatFieldTest(unittest.TestCase):
    # utime=700 stime=300 sit at post-comm indices 11/12; the comm here
    # contains both a space and a ')' to prove the rfind split.
    STAT = ("999 (ca(r go) test) R 42 999 999 0 -1 4194304 1 2 3 4 "
            "700 300 5 6 20 0 8 0 100 0 0")

    def _map(self):
        return {"/proc/999/stat": self.STAT}

    def test_cpu_ticks_sums_utime_and_stime(self):
        with mock.patch("builtins.open", _fake_open(self._map())):
            self.assertEqual(_cpu_ticks(999), 1000)

    def test_ppid_and_state(self):
        with mock.patch("builtins.open", _fake_open(self._map())):
            self.assertEqual(_ppid(999), 42)
            self.assertEqual(_proc_state(999), "R")

    def test_missing_pid_is_zero_and_empty(self):
        """A pid that exits mid-sample must not raise in a watchdog."""
        with mock.patch("builtins.open", _fake_open({})):
            self.assertEqual(_cpu_ticks(999), 0)
            self.assertEqual(_ppid(999), 0)
            self.assertEqual(_proc_state(999), "")

    def test_cpu_s_converts_ticks_to_seconds(self):
        with mock.patch("builtins.open", _fake_open(self._map())):
            self.assertAlmostEqual(_cpu_s([999]), 1000.0 / _CLK_TCK)


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

    def wait(self, timeout=None):
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

    def test_stale_flag_cleared_at_entry(self):
        os.makedirs(self.flag_dir, exist_ok=True)
        open(self.flag, "w").close()          # stale from a prior run
        p1, p2 = _FakeProc(pid=1, rc=0), _FakeProc(pid=2, rc=0)
        seen = []

        def fake_spawn(cmd, env, lp, label):
            seen.append(os.path.exists(self.flag))
            return (p1, None) if len(seen) == 1 else (p2, None)

        env_fn = mock.Mock(return_value={})
        spec = TwoHalfSpec("some::test", env_fn, ["0-3", "4-7"],
                            part2_proves=True, pre_part2=None)
        with mock.patch.object(_MOD, "spawn", side_effect=fake_spawn):
            run_rust_two_half(self.ctx, spec)
        self.assertEqual(seen, [False, False])


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


class NeoEnvTest(unittest.TestCase):
    def test_drops_zkr_and_forces_rustflags(self):
        with mock.patch.dict(os.environ,
                              {"ZKR_FOO": "1", "KEEP_ME": "y",
                               "RUSTFLAGS": "user-junk"}):
            with mock.patch.object(_MOD, "log") as lg:
                e = neo_env()
        self.assertNotIn("ZKR_FOO", e)
        self.assertEqual(e.get("KEEP_ME"), "y")
        self.assertEqual(e["RUSTFLAGS"], RUSTFLAGS_NEO)
        lg.assert_not_called()                # silent by default

    def test_show_dropped_logs_names(self):
        with mock.patch.dict(os.environ, {"ZKR_FOO": "1"}), \
             mock.patch.object(_MOD, "log") as lg:
            neo_env(b_show_dropped=True)
        self.assertTrue(any("ZKR_FOO" in str(c)
                            for c in lg.call_args_list))


class RunExampleTwoHalfTest(unittest.TestCase):
    ARGS = ["full_dlp", "1", "1", "2", "2", "2", PART_TOKEN, "1", "0"]

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.flag_dir = os.path.join(self.tmp.name, "snark_start")
        self.flag = os.path.join(self.flag_dir, "flag")
        for p in (mock.patch.object(_MOD, "FLAG_DIR", self.flag_dir),
                  mock.patch.object(_MOD, "FLAG", self.flag),
                  _sandbox_aborted(),
                  mock.patch.object(_MOD, "_wait_stagger",
                                     lambda p: None)):
            p.start()
            self.addCleanup(p.stop)
        # _FakeProc pids are 1/2 and os.getpgid(2) is 0 = our OWN
        # group, so the real _kill_proc must never run in a test.
        kp = mock.patch.object(_MOD, "_kill_proc")
        self.kill = kp.start()
        self.addCleanup(kp.stop)
        self.ctx = mock.Mock()
        self.ctx.log_path.side_effect = lambda name: os.path.join(
            self.tmp.name, name + ".log")

    def test_argvs_differ_only_in_part_id(self):
        os.makedirs(self.flag_dir, exist_ok=True)
        open(self.flag, "w").close()          # stale from a prior run
        p1, p2 = _FakeProc(pid=1, rc=0), _FakeProc(pid=2, rc=0)
        seen = []

        def fake_spawn(cmd, env, lp, label):
            seen.append(os.path.exists(self.flag))
            return (p1, None) if len(seen) == 1 else (p2, None)

        with mock.patch.object(_MOD, "spawn",
                                side_effect=fake_spawn) as sp:
            rc = run_example_two_half(self.ctx, "bora_cli",
                                       self.ARGS, {"E": "1"},
                                       ["0-3", "4-7"])
        self.assertEqual(rc, 0)
        self.assertEqual(seen, [False, False])   # stale cleared
        self.assertTrue(os.path.isfile(self.flag))  # released after p1
        cmd1, cmd2 = (c.args[0] for c in sp.call_args_list)
        i1, i2 = cmd1.index("cargo"), cmd2.index("cargo")
        diff = [(x, y)
                for x, y in zip(cmd1[i1:], cmd2[i2:]) if x != y]
        self.assertEqual(diff, [("0", "1")])

    def test_part1_failure_mid_fold_aborts_part2(self):
        """part1 dying AFTER part2 launched must withhold the flag and
        kill part2, not release its decider."""
        p1, p2 = _FakeProc(pid=1, rc=7), _FakeProc(pid=2, rc=0)
        with mock.patch.object(_MOD, "spawn",
                                side_effect=[(p1, None), (p2, None)]):
            rc = run_example_two_half(self.ctx, "bora_cli",
                                       self.ARGS, {}, ["0-3", "4-7"])
        self.assertEqual(rc, 7)
        self.assertFalse(os.path.exists(self.flag))
        self.kill.assert_called_once_with(p2)

    def test_part1_failure_before_stagger_skips_part2(self):
        """part1 already dead when the stagger returns: part2 is never
        spawned at all."""
        p1 = _FakeProc(pid=1, rc=9)
        p1.returncode = 9                      # dead before the gate
        with mock.patch.object(_MOD, "spawn",
                                side_effect=[(p1, None)]) as sp:
            rc = run_example_two_half(self.ctx, "bora_cli",
                                       self.ARGS, {}, ["0-3", "4-7"])
        self.assertEqual(rc, 9)
        self.assertEqual(sp.call_count, 1)
        self.assertFalse(os.path.exists(self.flag))
        self.kill.assert_not_called()
        self.ctx.note.assert_called_once()

    def test_signal_before_part2_skips_the_second_half(self):
        """A2014 gate 1: the operator's kill must not be followed by a
        whole second half starting."""
        p1 = _FakeProc(pid=1, rc=0)
        with mock.patch.object(_MOD, "_ABORTED", True), \
             mock.patch.object(_MOD, "_summary_line") as sl, \
             mock.patch.object(_MOD, "spawn",
                                side_effect=[(p1, None)]) as sp:
            rc = run_example_two_half(self.ctx, "bora_cli",
                                       self.ARGS, {}, ["0-3", "4-7"])
        self.assertEqual(rc, ABORT_RC)
        self.assertEqual(sp.call_count, 1)
        self.assertFalse(os.path.exists(self.flag))
        self.assertTrue(any("signal before part2 launch" in c[0][0]
                            for c in sl.call_args_list))

    def test_signal_before_flag_withholds_the_decider(self):
        """A2014 gate 2: a kill during the fold must not release part2's
        Groth16 decider -- hours of proving for a dead sequence."""
        p1, p2 = _FakeProc(pid=1, rc=0), _FakeProc(pid=2, rc=0)
        flips = iter([False, True])

        with mock.patch.object(_MOD, "aborted",
                                side_effect=lambda: next(flips)), \
             mock.patch.object(_MOD, "_summary_line") as sl, \
             mock.patch.object(_MOD, "spawn",
                                side_effect=[(p1, None), (p2, None)]) as sp:
            rc = run_example_two_half(self.ctx, "bora_cli",
                                       self.ARGS, {}, ["0-3", "4-7"])
        self.assertEqual(rc, ABORT_RC)
        self.assertEqual(sp.call_count, 2)
        self.assertFalse(os.path.exists(self.flag))
        self.kill.assert_called_once_with(p2)
        self.assertTrue(any("snark-gate release" in c[0][0]
                            for c in sl.call_args_list))

    def test_part1_clean_early_exit_still_spawns_part2(self):
        """A dry part1 finishing inside the stagger is NOT a failure --
        part2 waits on its RAM, never on its data."""
        p1, p2 = _FakeProc(pid=1, rc=0), _FakeProc(pid=2, rc=0)
        p1.returncode = 0                      # exited, cleanly
        with mock.patch.object(_MOD, "spawn",
                                side_effect=[(p1, None), (p2, None)]) as sp:
            rc = run_example_two_half(self.ctx, "bora_cli",
                                       self.ARGS, {}, ["0-3", "4-7"])
        self.assertEqual(rc, 0)
        self.assertEqual(sp.call_count, 2)
        self.assertTrue(os.path.isfile(self.flag))

    def test_part2_spawn_failure_kills_part1(self):
        """A raising part2 spawn must not orphan part1, and must not
        swallow the exception."""
        p1 = _FakeProc(pid=1, rc=0)
        with mock.patch.object(_MOD, "spawn",
                                side_effect=[(p1, None), OSError("no")]):
            with self.assertRaises(OSError):
                run_example_two_half(self.ctx, "bora_cli",
                                      self.ARGS, {}, ["0-3", "4-7"])
        self.kill.assert_called_once_with(p1)
        self.assertIsNotNone(p1.returncode)    # reaped, not orphaned
        self.assertFalse(os.path.exists(self.flag))

    def test_rejects_missing_token(self):
        with self.assertRaises(AssertionError):
            run_example_two_half(self.ctx, "bora_cli",
                                  ["full_dlp", "0"], {},
                                  ["0-3", "4-7"])


class ReapTest(unittest.TestCase):
    """_reap against REAL children -- the fake-proc tests cannot show
    the SIGTERM -> SIGKILL escalation or the pump join."""

    def setUp(self):
        _CHILDREN.clear()
        self.addCleanup(_CHILDREN.clear)
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)

    def _spawn(self, code):
        return spawn([sys.executable, "-c", code], os.environ,
                     os.path.join(self.tmp.name, "c.log"), "child")

    def test_exited_child_is_waited_and_pump_joined(self):
        """A child that already exited: rc recorded, pump thread done."""
        p, t = self._spawn("print('hi')")
        _reap(p, t)
        self.assertEqual(p.returncode, 0)
        self.assertFalse(t.is_alive())

    def test_sigtermed_child_is_reaped(self):
        """The normal abort path: caller SIGTERMs, _reap collects."""
        p, t = self._spawn("import time; time.sleep(300)")
        _kill_proc(p)
        _reap(p, t)
        self.assertEqual(p.returncode, -signal.SIGTERM)

    def test_unkillable_child_is_sigkilled(self):
        """A child still alive after the grace is SIGKILLed by _reap
        itself -- _reap never sends the SIGTERM, so none is sent here."""
        p, t = self._spawn("import time; time.sleep(300)")
        with mock.patch.object(_MOD, "KILL_GRACE_S", 1):
            _reap(p, t)
        self.assertEqual(p.returncode, -signal.SIGKILL)

    def test_none_is_a_noop(self):
        """A part that never started must not raise on cleanup."""
        _reap(None, None)


SCALE_LOG = (
    "preamble noise\n"
    "==== SCALE ROUND BEGIN count=2 corpus=x ====\n"
    "round two body\n"
    "==== SCALE ROUND END count=2 ====\n"
    "between noise\n"
    "==== SCALE ROUND BEGIN count=987 corpus=x ====\n"
    "round 987 body (truncated -- no END)\n")


class PackScaleBundleTest(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.log = os.path.join(self.tmp.name, "run.log")
        self.dest = os.path.join(self.tmp.name, "raw", "scale.tgz")

    def test_packs_rounds_incl_truncated_final(self):
        with open(self.log, "w") as f:
            f.write(SCALE_LOG)
        n = pack_scale_bundle(self.log, self.dest)
        self.assertEqual(n, 2)
        self.assertFalse(os.path.exists(self.dest + ".tmp"))
        with tarfile.open(self.dest) as t:
            self.assertEqual(sorted(t.getnames()),
                              ["log_2.txt.tgz", "log_987.txt.tgz"])
            inner = t.extractfile("log_2.txt.tgz")
            with tarfile.open(fileobj=inner) as t2:
                body = t2.extractfile("log_2.txt").read().decode()
        self.assertIn("round two body", body)
        self.assertIn("BEGIN count=2", body)

    def test_zero_rounds_leaves_dest_untouched(self):
        with open(self.log, "w") as f:
            f.write("no markers here\n")
        os.makedirs(os.path.dirname(self.dest))
        with open(self.dest, "w") as f:
            f.write("precious committed bundle")
        n = pack_scale_bundle(self.log, self.dest)
        self.assertEqual(n, 0)
        self.assertEqual(open(self.dest).read(),
                          "precious committed bundle")

    def test_partial_only_leaves_dest_untouched(self):
        """A sweep that crashed inside its FIRST round has no completed
        data point, so it must not replace a committed bundle."""
        with open(self.log, "w") as f:
            f.write("==== SCALE ROUND BEGIN count=1 corpus=x ====\n"
                    "thread panicked at alpha_size\n")
        os.makedirs(os.path.dirname(self.dest))
        with open(self.dest, "w") as f:
            f.write("precious committed bundle")
        n = pack_scale_bundle(self.log, self.dest)
        self.assertEqual(n, 0)
        self.assertEqual(open(self.dest).read(),
                          "precious committed bundle")


class DlpArgvTest(unittest.TestCase):
    def test_dry_tokens(self):
        self.assertEqual(
            dlp_argv("dry", 2, PART_TOKEN),
            ["full_dlp", "0.25", "0.0198", "2", "2", "2",
             PART_TOKEN, "1", "0"])

    def test_full_tokens(self):
        self.assertEqual(
            dlp_argv("full", 1, "0"),
            ["full_dlp", "100", "100", "4", "8", "1", "0",
             "0", "0"])


class PackFullDumpTest(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        p = mock.patch.object(_MOD, "RAW_DATA_ROOT",
                               os.path.join(self.tmp.name, "raw"))
        p.start()
        self.addCleanup(p.stop)
        self.common = _load_common()

    def _log(self, name, text):
        p = os.path.join(self.tmp.name, name)
        with open(p, "w") as f:
            f.write(text)
        return p

    def test_one_part_real_reader_roundtrip(self):
        lg = self._log("run.log", "hello dlp\n[job 0] done\n")
        dests = pack_full_dump("full_dlp", [lg], "20260810_010203")
        self.assertEqual([os.path.basename(d) for d in dests],
                          ["full_dlp.tgz"])
        out = self.common.extract_tgz(
            dests[0], os.path.join(self.tmp.name, "x"))
        self.assertEqual(open(out).read(),
                          "hello dlp\n[job 0] done\n")

    def test_two_part_real_reader_roundtrip(self):
        l1 = self._log("p1.log", "part one\n")
        l2 = self._log("p2.log", "part two\n")
        dests = pack_full_dump("full_dlp", [l1, l2],
                                "20260810_010203")
        self.assertEqual([os.path.basename(d) for d in dests],
                          ["full_dlp.part1.tgz", "full_dlp.part2.tgz"])
        self.assertEqual(self.common._read_part_log(dests[0]),
                          "part one\n")
        self.assertEqual(self.common._read_part_log(dests[1]),
                          "part two\n")

    def test_unlink_stale_both_directions(self):
        lg = self._log("run.log", "x\n")
        d2 = pack_full_dump("full_dlp", [lg, lg], "t1")
        d1 = pack_full_dump("full_dlp", [lg], "t2")
        for d in d2:
            self.assertFalse(os.path.exists(d))    # parts gone
        self.assertTrue(os.path.exists(d1[0]))
        d2b = pack_full_dump("full_dlp", [lg, lg], "t3")
        self.assertFalse(os.path.exists(d1[0]))    # single gone
        self.assertTrue(all(os.path.exists(d) for d in d2b))

    def test_stale_tmp_leftover_is_replaced(self):
        lg = self._log("run.log", "y\n")
        dest_dir = os.path.dirname(raw_data_path("full_dlp.tgz"))
        os.makedirs(dest_dir, exist_ok=True)
        open(os.path.join(dest_dir, "full_dlp.tgz.tmp"), "w").close()
        dests = pack_full_dump("full_dlp", [lg], "t4")
        self.assertTrue(os.path.exists(dests[0]))
        self.assertFalse(os.path.exists(
            os.path.join(dest_dir, "full_dlp.tgz.tmp")))


class LaddersDivergeTest(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        p = mock.patch.object(_MOD, "BORA_PLAN_ROOT", self.tmp.name)
        p.start()
        self.addCleanup(p.stop)

    def _write(self, name, pid, blob):
        d = os.path.join(self.tmp.name, "%s_neo_p%d" % (name, pid))
        os.makedirs(d, exist_ok=True)
        with open(os.path.join(d, "ladder.json"), "wb") as f:
            f.write(blob)

    def test_missing_and_differing_diverge(self):
        """Missing part dirs or differing bytes both count as
        divergence, per dataset name."""
        self.assertTrue(ladders_diverge("dlp"))     # both missing
        self._write("dlp", 0, b"{a}")
        self.assertTrue(ladders_diverge("dlp"))     # p1 missing
        self._write("dlp", 1, b"{b}")
        self.assertTrue(ladders_diverge("dlp"))     # differ

    def test_identical_ladders_pass(self):
        """Byte-identical p0/p1 ladders pass; names are disjoint
        (a clam pair must not satisfy a dlp check)."""
        self._write("clam", 0, b"{same}")
        self._write("clam", 1, b"{same}")
        self.assertFalse(ladders_diverge("clam"))
        self.assertTrue(ladders_diverge("dlp"))


class RunLeafDlpTest(unittest.TestCase):
    def setUp(self):
        self.ctx = mock.Mock()
        self.ctx._ts = "20260810_000000"
        self.ctx.raw_data = []
        self.ctx.finish.side_effect = \
            lambda rc, b_fail_scan=True: rc
        self.ctx.log_path.side_effect = \
            lambda n: "/lp/%s.log" % n

    def test_single_part_dry_wiring(self):
        with mock.patch.object(_MOD, "resolve_process_model",
                                return_value=ProcessModel(1, [None])), \
             mock.patch.object(_MOD, "neo_env",
                                return_value={"E": "1"}), \
             mock.patch.object(_MOD, "run_rust_example",
                                return_value=0) as rre, \
             mock.patch.object(_MOD, "dlp_missing_success",
                                return_value=None), \
             mock.patch.object(_MOD, "pack_full_dump",
                                return_value=["/d/full_dlp.tgz"]) as pk:
            rc = run_leaf_dlp("dry", self.ctx)
        self.assertEqual(rc, 0)
        rre.assert_called_once_with(
            self.ctx, "bora_cli", dlp_argv("dry", 1, "0"), {"E": "1"})
        pk.assert_called_once_with(
            "full_dlp", ["/lp/run.log"], "20260810_000000")
        self.assertEqual(self.ctx.raw_data, ["/d/full_dlp.tgz"])

    def test_two_part_full_wiring(self):
        model = ProcessModel(2, ["0-3", "4-7"])
        with mock.patch.object(_MOD, "resolve_process_model",
                                return_value=model), \
             mock.patch.object(_MOD, "neo_env",
                                return_value={"E": "1"}), \
             mock.patch.object(_MOD, "run_example_two_half",
                                return_value=0) as reth, \
             mock.patch.object(_MOD, "ladders_diverge",
                                return_value=False), \
             mock.patch.object(_MOD, "dlp_missing_success",
                                return_value=None), \
             mock.patch.object(_MOD, "pack_full_dump",
                                return_value=["/d/p1", "/d/p2"]) as pk:
            rc = run_leaf_dlp("full", self.ctx)
        self.assertEqual(rc, 0)
        reth.assert_called_once_with(
            self.ctx, "bora_cli", dlp_argv("full", 2, PART_TOKEN),
            {"E": "1"}, ["0-3", "4-7"])
        pk.assert_called_once_with(
            "full_dlp", ["/lp/part1.log", "/lp/part2.log"],
            "20260810_000000")
        self.assertEqual(self.ctx.raw_data, ["/d/p1", "/d/p2"])

    def test_nonzero_rc_never_packs(self):
        with mock.patch.object(_MOD, "resolve_process_model",
                                return_value=ProcessModel(1, [None])), \
             mock.patch.object(_MOD, "neo_env", return_value={}), \
             mock.patch.object(_MOD, "run_rust_example",
                                return_value=3), \
             mock.patch.object(_MOD, "pack_full_dump") as pk:
            rc = run_leaf_dlp("dry", self.ctx)
        self.assertEqual(rc, 3)
        pk.assert_not_called()

    def test_dlp_verdicts_scan_free(self):
        """DLP must NOT fail-scan: its own self-cover CapErr prints
        panic text into a SUCCESSFUL full-mode log."""
        with mock.patch.object(_MOD, "resolve_process_model",
                                return_value=ProcessModel(1, [None])), \
             mock.patch.object(_MOD, "neo_env", return_value={}), \
             mock.patch.object(_MOD, "run_rust_example",
                                return_value=0), \
             mock.patch.object(_MOD, "dlp_missing_success",
                                return_value=None), \
             mock.patch.object(_MOD, "pack_full_dump",
                                return_value=[]):
            run_leaf_dlp("full", self.ctx)
        self.ctx.finish.assert_called_once_with(0, b_fail_scan=False)

    def test_ladder_divergence_fails_no_pack(self):
        model = ProcessModel(2, ["0-3", "4-7"])
        with mock.patch.object(_MOD, "resolve_process_model",
                                return_value=model), \
             mock.patch.object(_MOD, "neo_env", return_value={}), \
             mock.patch.object(_MOD, "run_example_two_half",
                                return_value=0), \
             mock.patch.object(_MOD, "ladders_diverge",
                                return_value=True), \
             mock.patch.object(_MOD, "pack_full_dump") as pk:
            rc = run_leaf_dlp("dry", self.ctx)
        self.assertEqual(rc, 5)
        pk.assert_not_called()
        self.ctx.note.assert_called_once()

    def test_missing_success_markers_fail_no_pack(self):
        with mock.patch.object(_MOD, "resolve_process_model",
                                return_value=ProcessModel(1, [None])), \
             mock.patch.object(_MOD, "neo_env", return_value={}), \
             mock.patch.object(_MOD, "run_rust_example",
                                return_value=0), \
             mock.patch.object(_MOD, "dlp_missing_success",
                                return_value="no markers") as ms, \
             mock.patch.object(_MOD, "pack_full_dump") as pk:
            rc = run_leaf_dlp("dry", self.ctx)
        self.assertEqual(rc, 6)
        ms.assert_called_once_with(["/lp/run.log"], 2)
        pk.assert_not_called()
        self.ctx.note.assert_called_once()


class DlpMissingSuccessTest(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)

    def _log(self, name, text):
        p = os.path.join(self.tmp.name, name)
        with open(p, "w") as f:
            f.write(text)
        return p

    def test_dry_shape_ok(self):
        lg = self._log("run.log",
                        "Job 0 generating SNARK proof\n"
                        "Job 1 folding done; b_one_proof set\n"
                        "FOLDPOT Step 13. Verify Individual Proof. 17 ms\n")
        self.assertIsNone(dlp_missing_success([lg], 2))

    def test_missing_job_and_verify_counts(self):
        lg = self._log("a.log",
                        "Job 0 generating SNARK proof\n"
                        "Verify Individual Proof\n")
        self.assertIn("1 != num_jobs 2", dlp_missing_success([lg], 2))
        lg2 = self._log("b.log",
                        "Job 0 generating SNARK proof\n"
                        "Job 1 folding done\n")
        self.assertIn("count 0 != 1", dlp_missing_success([lg2], 2))

    def test_two_half_local_numbering_sums(self):
        """A NON-proving part emits the b_folding_only marker, never
        "folding done"; both parts' local job 0s must still sum."""
        l1 = self._log(
            "p1.log", "Job 0: b_folding_only set, no snark generated\n")
        l2 = self._log("p2.log",
                        "Job 0 generating SNARK proof\n"
                        "Verify Individual Proof\n")
        self.assertIsNone(dlp_missing_success([l1, l2], 2))

    def test_two_half_production_shape_counts_all_8(self):
        """The real 8-job/2-part shape: part0 folds only, part1 proves
        one job. All 8 must count, else the dump is never packed."""
        l1 = self._log("prod1.log", "".join(
            "Job %d: b_folding_only set, no snark generated\n" % i
            for i in range(4)))
        l2 = self._log("prod2.log",
                        "Job 0 generating SNARK proof\n"
                        + "".join("Job %d folding done; b_one_proof\n" % i
                                   for i in range(1, 4))
                        + "Verify Individual Proof\n")
        self.assertIsNone(dlp_missing_success([l1, l2], 8))

    def test_individual_verify_failure_is_caught(self):
        """A bad proof is LOGGED and the run exits 0, so without this
        marker an otherwise-perfect log scores PASS."""
        lg = self._log("bad.log",
                        "Job 0 generating SNARK proof\n"
                        "Job 1 folding done; b_one_proof set\n"
                        "[job 0] ERR:  Job 0 INDIVIDUAL PROOF "
                        "VERIFICATION FAILED (verify_individual "
                        "returned false); continuing other jobs.\n"
                        "FOLDPOT Step 13. Verify Individual Proof. 17 ms\n")
        self.assertIn("PROOF VERIFICATION FAILED",
                       dlp_missing_success([lg], 2))

    def test_batch_verify_failure_is_caught(self):
        """The batch proof can fail while the individual one passes;
        every positive marker still lines up, so only this catches it."""
        lg = self._log("badbatch.log",
                        "Job 0 generating SNARK proof\n"
                        "Job 1 folding done; b_one_proof set\n"
                        "[job 0] ERR:  Job 0 BATCH PROOF VERIFICATION "
                        "FAILED (verify_batch returned false); "
                        "continuing other jobs.\n"
                        "FOLDPOT Step 13. Verify Individual Proof. 17 ms\n")
        self.assertIn("PROOF VERIFICATION FAILED",
                       dlp_missing_success([lg], 2))

    def test_verify_failure_outranks_marker_counts(self):
        """A bad proof must be reported ahead of any missing-marker
        reason, which is the less severe diagnosis."""
        lg = self._log("both.log",
                        "Job 0 generating SNARK proof\n"
                        "Job 0 BATCH PROOF VERIFICATION FAILED\n")
        self.assertIn("PROOF VERIFICATION FAILED",
                       dlp_missing_success([lg], 8))


class RunLeafDnaTest(unittest.TestCase):
    def setUp(self):
        self.ctx = mock.Mock()
        self.ctx._ts = "20260810_000000"
        self.ctx.raw_data = []
        self.ctx.finish.side_effect = \
            lambda rc, b_fail_scan=True: rc
        self.ctx.log_path.side_effect = lambda n: "/lp/%s.log" % n

    def test_dry_wiring(self):
        """Dry leaf spawns bora_cli full_dna with the dry argv and
        packs the single run log as full_dna.tgz."""
        with mock.patch.object(_MOD, "neo_env",
                                return_value={"E": "1"}), \
             mock.patch.object(_MOD, "run_rust_example",
                                return_value=0) as rre, \
             mock.patch.object(_MOD, "dlp_missing_success",
                                return_value=None) as ms, \
             mock.patch.object(_MOD, "pack_full_dump",
                                return_value=["/d/full_dna.tgz"]) as pk:
            rc = run_leaf_dna("dry", self.ctx)
        self.assertEqual(rc, 0)
        rre.assert_called_once_with(
            self.ctx, "bora_cli", dna_argv("dry"), {"E": "1"})
        ms.assert_called_once_with(["/lp/run.log"], 1)
        pk.assert_called_once_with(
            "full_dna", ["/lp/run.log"], "20260810_000000")
        self.assertEqual(self.ctx.raw_data, ["/d/full_dna.tgz"])
        # D103 pattern: the non-aggr tuner's caught CapErr probe text
        # would counterfeit a FAIL, so the leaf verdicts scan-free.
        self.ctx.finish.assert_called_once_with(0, b_fail_scan=False)

    def test_argv_shapes(self):
        """dry/full argv are 9 tokens with numa/part pinned 1/0;
        dry is light, full is heavy."""
        self.assertEqual(dna_argv("dry"),
            ["full_dna", "1", "2", "1", "1", "1", "0", "1", "0"])
        self.assertEqual(dna_argv("full"),
            ["full_dna", "100", "100", "1", "1", "1", "0", "0", "0"])

    def test_nonzero_rc_never_packs(self):
        """A failed spawn skips both the marker check and packing."""
        with mock.patch.object(_MOD, "neo_env", return_value={}), \
             mock.patch.object(_MOD, "run_rust_example",
                                return_value=3), \
             mock.patch.object(_MOD, "pack_full_dump") as pk:
            rc = run_leaf_dna("dry", self.ctx)
        self.assertEqual(rc, 3)
        pk.assert_not_called()

    def test_missing_success_markers_fail_no_pack(self):
        """rc=6 and no pack when the positive fold/verify markers
        are absent from the run log."""
        with mock.patch.object(_MOD, "neo_env", return_value={}), \
             mock.patch.object(_MOD, "run_rust_example",
                                return_value=0), \
             mock.patch.object(_MOD, "dlp_missing_success",
                                return_value="no markers"), \
             mock.patch.object(_MOD, "pack_full_dump") as pk:
            rc = run_leaf_dna("dry", self.ctx)
        self.assertEqual(rc, 6)
        pk.assert_not_called()
        self.ctx.note.assert_called_once()


class RunLeafClamavTest(unittest.TestCase):
    def setUp(self):
        self.ctx = mock.Mock()
        self.ctx._ts = "20260810_000000"
        self.ctx.raw_data = []
        self.ctx.finish.side_effect = \
            lambda rc, b_fail_scan=True: rc
        self.ctx.log_path.side_effect = lambda n: "/lp/%s.log" % n

    def test_single_part_dry_wiring(self):
        """Dry leaf spawns bora_cli full_clam with the dry argv,
        packs full_clam.tgz, and verdicts scan-free."""
        with mock.patch.object(_MOD, "resolve_process_model",
                                return_value=ProcessModel(1, [None])), \
             mock.patch.object(_MOD, "neo_env",
                                return_value={"E": "1"}), \
             mock.patch.object(_MOD, "run_rust_example",
                                return_value=0) as rre, \
             mock.patch.object(_MOD, "dlp_missing_success",
                                return_value=None) as ms, \
             mock.patch.object(_MOD, "pack_full_dump",
                                return_value=["/d/full_clam.tgz"]) as pk:
            rc = run_leaf_clamav("dry", self.ctx)
        self.assertEqual(rc, 0)
        rre.assert_called_once_with(
            self.ctx, "bora_cli", clam_argv("dry", 1, "0"),
            {"E": "1"})
        ms.assert_called_once_with(["/lp/run.log"], 2)
        pk.assert_called_once_with(
            "full_clam", ["/lp/run.log"], "20260810_000000")
        self.ctx.finish.assert_called_once_with(
            0, b_fail_scan=False)

    def test_two_part_full_wiring_and_argv(self):
        """Argv shapes are the locked constants; the two-half path
        reads the CLAM ladder tripwire (name='clam')."""
        self.assertEqual(clam_argv("full", 2, PART_TOKEN),
            ["full_clam", "100", "100", "2", "8", "2", PART_TOKEN,
             "0", "0"])
        self.assertEqual(clam_argv("dry", 1, "0"),
            ["full_clam", "0.5", "0.1", "2", "2", "1", "0", "1",
             "0"])
        model = ProcessModel(2, ["0-3", "4-7"])
        with mock.patch.object(_MOD, "resolve_process_model",
                                return_value=model), \
             mock.patch.object(_MOD, "neo_env", return_value={}), \
             mock.patch.object(_MOD, "run_example_two_half",
                                return_value=0), \
             mock.patch.object(_MOD, "ladders_diverge",
                                return_value=True) as ld, \
             mock.patch.object(_MOD, "pack_full_dump") as pk:
            rc = run_leaf_clamav("full", self.ctx)
        self.assertEqual(rc, 5)
        ld.assert_called_once_with("clam")
        pk.assert_not_called()


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
            [sys.executable, "-u", "/x/run_zombie.py", "--a", "1"],
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
            _sandbox_aborted(),
        ]
        for p in patches:
            p.start()
            self.addCleanup(p.stop)
        os.makedirs(os.path.join(self.tmp.name, "job_logs"))

    def test_dry_mode_uses_dry_script_and_perc_arg(self):
        ctx = JobHandle("zombie", "dry")
        with mock.patch.object(_MOD, "run_external_python",
                                return_value=0) as rep, \
             mock.patch.object(_MOD, "zombie_missing_success",
                                return_value=(None, None)):
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
                                return_value=0) as rep, \
             mock.patch.object(_MOD, "zombie_missing_success",
                                return_value=(None, None)):
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

    def test_missing_markers_fail_no_placement(self):
        """A predicate reason must block raw_data and FAIL the leaf."""
        ctx = JobHandle("zombie", "dry")
        with mock.patch.object(_MOD, "run_external_python",
                                return_value=0), \
             mock.patch.object(_MOD, "zombie_missing_success",
                                return_value=("0 of 24 results ok", None)), \
             mock.patch.object(_MOD, "place_raw_data") as prd:
            result = run_leaf_zombie("dry", ctx)
        self.assertEqual(result.rc, 6)
        self.assertTrue(result.failed)
        prd.assert_not_called()
        self.assertIn("0 of 24", result.note)

    def test_partial_note_still_places(self):
        """A note without a reason still PASSES and publishes."""
        ctx = JobHandle("zombie", "dry")
        with mock.patch.object(_MOD, "run_external_python",
                                return_value=0), \
             mock.patch.object(_MOD, "zombie_missing_success",
                                return_value=(None, "3 of 8 not ok")), \
             mock.patch.object(_MOD, "place_raw_data",
                                return_value="/fake/dest") as prd:
            result = run_leaf_zombie("dry", ctx)
        self.assertEqual(result.rc, 0)
        prd.assert_called_once()
        self.assertIn("3 of 8", result.note)


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
            _sandbox_aborted(),
        ]
        for p in patches:
            p.start()
            self.addCleanup(p.stop)
        os.makedirs(os.path.join(self.tmp.name, "job_logs"))

    def test_dry_mode_uses_dry_script_and_perc_arg(self):
        ctx = JobHandle("reef", "dry")
        with mock.patch.object(_MOD, "run_external_python",
                                return_value=0) as rep, \
             mock.patch.object(_MOD, "reef_missing_success",
                                return_value=(None, None)):
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
                                return_value=0) as rep, \
             mock.patch.object(_MOD, "reef_missing_success",
                                return_value=(None, None)):
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

    def test_missing_markers_fail_no_placement(self):
        """A predicate reason must block raw_data and FAIL the leaf."""
        ctx = JobHandle("reef", "dry")
        with mock.patch.object(_MOD, "run_external_python",
                                return_value=0), \
             mock.patch.object(_MOD, "reef_missing_success",
                                return_value=("sweep STOPped: x", None)), \
             mock.patch.object(_MOD, "place_raw_data") as prd:
            result = run_leaf_reef("dry", ctx)
        self.assertEqual(result.rc, 6)
        self.assertTrue(result.failed)
        prd.assert_not_called()
        self.assertIn("STOPped", result.note)

    def test_partial_note_still_places(self):
        """A note without a reason still PASSES and publishes."""
        ctx = JobHandle("reef", "dry")
        with mock.patch.object(_MOD, "run_external_python",
                                return_value=0), \
             mock.patch.object(_MOD, "reef_missing_success",
                                return_value=(None, "pool exhausted: p")), \
             mock.patch.object(_MOD, "place_raw_data",
                                return_value="/fake/dest") as prd:
            result = run_leaf_reef("dry", ctx)
        self.assertEqual(result.rc, 0)
        prd.assert_called_once()
        self.assertIn("pool exhausted", result.note)


class ZombieMissingSuccessTest(unittest.TestCase):
    OK = ("[run_zombie] docs/run_zombie_x.log : 24 results, 24 ok "
          "across sizes [700, 800, 1000]\n")

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.t0 = time.time() - 10
        self.docs = os.path.join(self.tmp.name, "zombie.log")
        with open(self.docs, "w") as f:
            f.write("fresh\n")

    def _log(self, text):
        p = os.path.join(self.tmp.name, "run.log")
        with open(p, "w") as f:
            f.write(text)
        return p

    def test_all_ok_passes(self):
        """24/24 ok with a docs log written by this run is a PASS."""
        self.assertEqual(
            zombie_missing_success(self._log(self.OK), self.docs,
                                    self.t0), (None, None))

    def test_partial_ok_passes_with_note(self):
        """Some not-ok policies are RECORDED, not fatal (M>0 rule)."""
        lg = self._log(self.OK.replace("24 results, 24 ok",
                                        "8 results, 5 ok"))
        reason, note = zombie_missing_success(lg, self.docs, self.t0)
        self.assertIsNone(reason)
        self.assertIn("3 of 8", note)

    def test_zero_ok_fails(self):
        """Every policy failing is a total failure, not a partial one."""
        lg = self._log(self.OK.replace("24 ok", "0 ok"))
        self.assertIn("0 of 24",
                       zombie_missing_success(lg, self.docs, self.t0)[0])

    def test_zero_results_fails(self):
        """An empty policy list measured nothing."""
        lg = self._log(self.OK.replace("24 results, 24 ok",
                                        "0 results, 0 ok"))
        self.assertIn("0 results",
                       zombie_missing_success(lg, self.docs, self.t0)[0])

    def test_absent_ruleset_fails(self):
        """The skip line is the child's silent do-nothing exit."""
        lg = self._log("[run_zombie] ruleset regex_zombie_x/ absent "
                       "-- skipping\n")
        self.assertIn("never ran",
                       zombie_missing_success(lg, self.docs, self.t0)[0])

    def test_no_summary_line_fails(self):
        """No summary line at all means the run never reached write_log."""
        self.assertIn(
            "no [run_zombie]",
            zombie_missing_success(self._log("[run] size=700\n"),
                                    self.docs, self.t0)[0])

    def test_stale_docs_log_fails(self):
        """A docs log older than the job is a leftover, not this run's."""
        os.utime(self.docs, (self.t0 - 100, self.t0 - 100))
        self.assertIn(
            "stale",
            zombie_missing_success(self._log(self.OK), self.docs,
                                    self.t0)[0])


class ReefMissingSuccessTest(unittest.TestCase):
    OK = ("[non_projectable acc=0/1 try=1 disc=0] v1  est_net=1.0s\n"
          "wrote docs/reef_sample_run.log and docs/variants_category.txt\n")

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.t0 = time.time() - 10
        self.docs = os.path.join(self.tmp.name, "reef.log")
        self._docs("timed_out: 0 of 6 samples\n")

    def _docs(self, text):
        with open(self.docs, "w") as f:
            f.write(text)

    def _log(self, text):
        p = os.path.join(self.tmp.name, "run.log")
        with open(p, "w") as f:
            f.write(text)
        return p

    def test_healthy_run_passes(self):
        """A sweep that reached its final write with samples is a PASS."""
        self.assertEqual(
            reef_missing_success(self._log(self.OK), self.docs, self.t0),
            (None, None))

    def test_projectability_stop_fails(self):
        """GATE-1 STOP aborts the sweep yet still exits 0."""
        lg = self._log("  STOP: projectability mismatch for v1 "
                       "(real=True, est=False)\n" + self.OK)
        self.assertIn("projectability",
                       reef_missing_success(lg, self.docs, self.t0)[0])

    def test_timeout_stop_fails(self):
        """A fast-predicted sample timing out is a model failure."""
        lg = self._log("  STOP: v1 timed out but est_net=5.0s <= "
                       "timeout=2000s\n" + self.OK)
        self.assertIn("timed out",
                       reef_missing_success(lg, self.docs, self.t0)[0])

    def test_max_discard_stop_fails(self):
        """Exceeding max_discard is the third hard-STOP exit."""
        lg = self._log("  STOP: proj_4M exceeded max_discard=30 "
                       "outliers\n" + self.OK)
        self.assertIn("max_discard",
                       reef_missing_success(lg, self.docs, self.t0)[0])

    def test_missing_wrote_line_fails(self):
        """No terminal 'wrote' line means write_log never completed."""
        self.assertIn(
            "no terminal",
            reef_missing_success(self._log("[proj_4M acc=0/1]\n"),
                                  self.docs, self.t0)[0])

    def test_zero_samples_fails(self):
        """An empty assessment writes a log with no executed samples."""
        self._docs("timed_out: 0 of 0 samples\n")
        self.assertIn(
            "0 samples",
            reef_missing_success(self._log(self.OK), self.docs,
                                  self.t0)[0])

    def test_stale_docs_log_fails(self):
        """A docs log older than the job is a leftover, not this run's."""
        os.utime(self.docs, (self.t0 - 100, self.t0 - 100))
        self.assertIn(
            "stale",
            reef_missing_success(self._log(self.OK), self.docs,
                                  self.t0)[0])

    def test_pool_exhausted_passes_with_note(self):
        """Pool exhaustion is degraded-but-usable: note, not fail."""
        lg = self._log("  WARN: proj_512k pool exhausted with only 3/10 "
                       "accepted (2 discarded)\n" + self.OK)
        reason, note = reef_missing_success(lg, self.docs, self.t0)
        self.assertIsNone(reason)
        self.assertIn("proj_512k", note)


class LkupMissingSuccessTest(unittest.TestCase):
    # Shaped after the real emitters: clam_db.rs fmt_lkup_dist,
    # zkp_driver.rs fmt_cross_rollup, and the driver's closing banner.
    FULL = ("------ Lookup Composition: Mal --------\n"
            "------ Lookup Composition: Dna --------\n"
            "------ Lookup Composition: Dlp --------\n"
            "===== Cross-Dataset Roll-up (% of populated) =====\n"
            "##### END LOOKUP COMPOSITION REPORT #####\n")

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.path = os.path.join(self.tmp.name, "lookup_stats.dat")

    def _write(self, text):
        with open(self.path, "w") as f:
            f.write(text)

    def test_complete_and_fresh_passes(self):
        self._write(self.FULL)
        self.assertIsNone(lkup_missing_success(self.path, 0))

    def test_absent_report(self):
        self.assertIn("no report", lkup_missing_success(self.path, 0))

    def test_stale_report_from_a_prior_run(self):
        self._write(self.FULL)
        os.utime(self.path, (1, 1))
        self.assertIn("stale",
                       lkup_missing_success(self.path, time.time()))

    def test_missing_dataset_section(self):
        self._write(self.FULL.replace("Lookup Composition: Dna", "x"))
        self.assertIn("Dna", lkup_missing_success(self.path, 0))

    def test_truncated_before_end_banner(self):
        self._write(self.FULL.replace("END LOOKUP", "x"))
        self.assertIn("END banner", lkup_missing_success(self.path, 0))


class RunLeafAnalyzeLkupTest(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        for name, sub in (("JOB_LOG_DIR", "logs"),
                           ("FAILED_TGZ_DIR", "failed_tgz"),
                           ("LOGS_DIR", "job_logs"),
                           ("RAW_DATA_ROOT", "raw_data")):
            p = mock.patch.object(_MOD, name,
                                   os.path.join(self.tmp.name, sub))
            p.start()
            self.addCleanup(p.stop)
        os.makedirs(os.path.join(self.tmp.name, "job_logs"))

    def _run(self, mode, rc, report):
        """Stand-in bora_cli: echoes panic-looking text into run.log the
        way the real one echoes the report, then writes `report`."""
        ctx = JobHandle("lkup", mode)
        seen = {}

        def fake(c, name, args, env, log_name="run"):
            seen["args"] = args
            with open(c.log_path(log_name), "w") as f:
                f.write("thread 'main' panicked at echoed.rs:1:1:\n")
            if report is not None:
                with open(args[2], "w") as f:
                    f.write(report)
            return rc

        with mock.patch.object(_MOD, "run_rust_example", fake):
            return ctx, seen, run_leaf_analyze_lkup(mode, ctx)

    def test_dry_perc_and_report_destination(self):
        _, seen, res = self._run("dry", 0, LkupMissingSuccessTest.FULL)
        self.assertEqual(seen["args"][:2], ["lkup", str(LKUP_DRY_PERC)])
        self.assertTrue(seen["args"][2].endswith("lookup_stats.dat"))
        self.assertEqual(res.rc, 0)
        self.assertFalse(res.failed)

    def test_echoed_report_text_cannot_fail_the_leaf(self):
        """A2016: the Rust side println!s the whole report before writing
        it, so run.log carries the report's own words no matter what."""
        _, _, res = self._run("full", 0, LkupMissingSuccessTest.FULL)
        self.assertEqual(res.rc, 0)
        self.assertFalse(res.failed)

    def test_truncated_report_fails_and_places_nothing(self):
        with mock.patch.object(_MOD, "place_raw_data") as pl:
            ctx, _, res = self._run("dry", 0, "half a report\n")
        self.assertEqual(res.rc, 6)
        self.assertTrue(res.failed)
        pl.assert_not_called()
        self.assertTrue(any("lkup:" in n for n in ctx._notes))


class RunLeafScaleDlpTest(unittest.TestCase):
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
            _sandbox_aborted(),
        ]
        for p in patches:
            p.start()
            self.addCleanup(p.stop)
        os.makedirs(os.path.join(self.tmp.name, "job_logs"))

    @staticmethod
    def _round(cnt, extra=""):
        return ("==== SCALE ROUND BEGIN count=%d rules=%d/9861 "
                "corpus=x ====\n%s"
                "==== SCALE ROUND END count=%d ====\n"
                % (cnt, cnt, extra, cnt))

    @staticmethod
    def _all_rounds(extra=""):
        """A complete sweep log for whatever dry counts are configured
        (derived, so retuning the counts cannot rot these tests)."""
        return "".join(
            RunLeafScaleDlpTest._round(c, extra if i == 0 else "")
            for i, c in enumerate(SCALE_DLP_COUNTS["dry"]))

    def _fake_run(self, rcs, bodies):
        """Stand-in run_rust_example: writes the per-call log body,
        returns the per-call rc, records (example, args, log_name)."""
        calls = []

        def fake(ctx, name, args, env, log_name="run"):
            i = len(calls)
            calls.append((name, args, log_name))
            with open(ctx.log_path(log_name), "w") as f:
                f.write(bodies[i])
            return rcs[i]
        return calls, fake

    def test_signal_skips_the_second_sweep(self):
        """A2014: a kill during sweep 1 must not start sweep 2."""
        ctx = JobHandle("scale_dlp", "dry")
        body = self._all_rounds()
        calls, fake = self._fake_run([0, 0], [body, body])

        def abort_after_first(c, name, args, env, log_name="run"):
            rc = fake(c, name, args, env, log_name=log_name)
            _MOD._ABORTED = True
            return rc

        with mock.patch.object(_MOD, "run_rust_example", abort_after_first):
            result = run_leaf_scale_dlp("dry", ctx)
        self.assertEqual(len(calls), 1)
        self.assertEqual(result.rc, ABORT_RC)
        self.assertTrue(any("signal before" in n for n in ctx._notes))

    def test_signal_after_a_failed_sweep_still_records_the_abort(self):
        """`rc = rc or _abort_leaf(...)` would short-circuit the recorder
        in exactly this case, losing the reason the sweep stopped."""
        ctx = JobHandle("scale_dlp", "dry")
        calls, fake = self._fake_run([5], ["broken\n"])

        def abort_after_first(c, name, args, env, log_name="run"):
            rc = fake(c, name, args, env, log_name=log_name)
            _MOD._ABORTED = True
            return rc

        with mock.patch.object(_MOD, "run_rust_example", abort_after_first):
            result = run_leaf_scale_dlp("dry", ctx)
        self.assertEqual(result.rc, 5)          # the real failure wins
        self.assertTrue(any("signal before" in n for n in ctx._notes))

    def test_argv_bundles_and_order(self):
        """Both sweeps run in order with the locked argv/log names;
        each bundle lands in any_server with one member per round."""
        ctx = JobHandle("scale_dlp", "dry")
        body = self._all_rounds()
        csv = ",".join(str(c) for c in SCALE_DLP_COUNTS["dry"])
        calls, fake = self._fake_run([0, 0], [body, body])
        with mock.patch.object(_MOD, "run_rust_example", fake):
            result = run_leaf_scale_dlp("dry", ctx)
        self.assertEqual(result.rc, 0)
        self.assertFalse(result.failed)
        # dry passes the dry token; full passes "0" (see the mode test)
        self.assertEqual(
            calls,
            [("bora_cli", ["scale_dlp", "0", csv, "1"], "scale_2"),
             ("bora_cli", ["scale_dlp", "1", csv, "1"], "scale_6")])
        members = sorted("log_%d.txt.tgz" % c
                          for c in SCALE_DLP_COUNTS["dry"])
        for bundle in ("scale_data_dlp_2.tgz", "scale_data_dlp_6.tgz"):
            dest = raw_data_path(bundle, server_specific=False)
            self.assertTrue(os.path.isfile(dest))
            with tarfile.open(dest) as t:
                self.assertEqual(sorted(t.getnames()), members)
        self.assertEqual(len(ctx.raw_data), 2)

    def test_first_failure_does_not_skip_second(self):
        """Failing first sweep still runs the second; its rc wins and
        only the second's bundle is placed (0 rounds -> untouched)."""
        ctx = JobHandle("scale_dlp", "dry")
        calls, fake = self._fake_run(
            [3, 0], ["no rounds\n", self._all_rounds()])
        with mock.patch.object(_MOD, "run_rust_example", fake):
            result = run_leaf_scale_dlp("dry", ctx)
        self.assertEqual(len(calls), 2)          # second still ran
        self.assertEqual(result.rc, 3)
        self.assertTrue(result.failed)
        self.assertFalse(os.path.isfile(raw_data_path(
            "scale_data_dlp_2.tgz", server_specific=False)))
        self.assertTrue(os.path.isfile(raw_data_path(
            "scale_data_dlp_6.tgz", server_specific=False)))

    def test_missing_round_end_is_rc7(self):
        """rc=0 but one count lacks its ROUND END marker -> rc=7 with
        a note; the partial round is still packed into the bundle."""
        ctx = JobHandle("scale_dlp", "dry")
        top = SCALE_DLP_COUNTS["dry"][-1]
        partial = self._round(SCALE_DLP_COUNTS["dry"][0]) + \
            "==== SCALE ROUND BEGIN count=%d rules=%d/9861 " \
            "corpus=x ====\n" % (top, top)
        _, fake = self._fake_run([0, 0], [partial, self._all_rounds()])
        with mock.patch.object(_MOD, "run_rust_example", fake):
            result = run_leaf_scale_dlp("dry", ctx)
        self.assertEqual(result.rc, 7)
        self.assertIn("scale_2: no ROUND END for counts [%d]" % top,
                       result.note)
        # the partial round is still packed (legacy crash tolerance)
        self.assertTrue(os.path.isfile(raw_data_path(
            "scale_data_dlp_2.tgz", server_specific=False)))

    def test_expected_caperr_noise_not_a_fail(self):
        """Expected bump-retry panic/CapErr text in a SUCCESSFUL log
        must not counterfeit a FAIL verdict (the fail-scan is off)."""
        ctx = JobHandle("scale_dlp", "dry")
        noise = "thread 'main' panicked at 'CapErr: StepFwdPrf'\n"
        body = self._all_rounds(noise)
        _, fake = self._fake_run([0, 0], [body, body])
        with mock.patch.object(_MOD, "run_rust_example", fake):
            result = run_leaf_scale_dlp("dry", ctx)
        self.assertEqual(result.rc, 0)
        self.assertFalse(result.failed)          # fail-scan is off

    def test_pack_runs_even_if_launch_raises(self):
        """A Python-level launch exception still packs the completed
        rounds (the finally block), then propagates to the caller."""
        ctx = JobHandle("scale_dlp", "dry")
        rounds = self._round(2)

        def boom(ctx2, name, args, env, log_name="run"):
            with open(ctx2.log_path(log_name), "w") as f:
                f.write(rounds)
            raise RuntimeError("launch died")
        with mock.patch.object(_MOD, "run_rust_example", boom):
            with self.assertRaises(RuntimeError):
                run_leaf_scale_dlp("dry", ctx)
        self.assertTrue(os.path.isfile(raw_data_path(
            "scale_data_dlp_2.tgz", server_specific=False)))

    def test_full_mode_passes_dry_token_zero(self):
        """full sweeps must send dry=0 -- the real range table and the
        whole corpus, whatever the dry shape is tuned to."""
        ctx = JobHandle("scale_dlp", "full")
        csv = ",".join(str(c) for c in SCALE_DLP_COUNTS["full"])
        body = "".join(self._round(c)
                        for c in SCALE_DLP_COUNTS["full"])
        calls, fake = self._fake_run([0, 0], [body, body])
        with mock.patch.object(_MOD, "run_rust_example", fake):
            result = run_leaf_scale_dlp("full", ctx)
        self.assertEqual(result.rc, 0)
        self.assertEqual([c[1] for c in calls],
                          [["scale_dlp", "0", csv, "0"],
                           ["scale_dlp", "1", csv, "0"]])

    def test_counts_pin_inclusive(self):
        """Count constants are pin-INCLUSIVE (spec 8.10c: legacy +1
        each; top 9861 = the complete rule set)."""
        # dry top = half the full step (986/2 = 493) + the pin.
        self.assertEqual(SCALE_DLP_COUNTS["dry"], [2, 494])
        self.assertEqual(SCALE_DLP_COUNTS["full"],
                          [2, 987, 1973, 2959, 3945, 4931, 5917, 6903,
                           7889, 8875, 9861])

    def test_finish_fail_scan_toggle(self):
        """finish(0, b_fail_scan=False) ignores FAIL_RE log text;
        True (the default for every other leaf) still flags it."""
        for b_scan, want_failed in ((True, True), (False, False)):
            ctx = JobHandle("scale_dlp", "dry")
            with open(ctx.log_path("run"), "w") as f:
                f.write("FATAL: boom\n")
            res = ctx.finish(0, b_fail_scan=b_scan)
            self.assertEqual(res.failed, want_failed)


class RunLeafScaleClamTest(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        patches = [
            mock.patch.object(_MOD, "JOB_LOG_DIR",
                               os.path.join(self.tmp.name, "logs")),
            mock.patch.object(_MOD, "FAILED_TGZ_DIR",
                               os.path.join(self.tmp.name,
                                             "failed_tgz")),
            mock.patch.object(_MOD, "LOGS_DIR",
                               os.path.join(self.tmp.name,
                                             "job_logs")),
            mock.patch.object(_MOD, "RAW_DATA_ROOT",
                               os.path.join(self.tmp.name,
                                             "raw_data")),
            _sandbox_aborted(),
        ]
        for p in patches:
            p.start()
            self.addCleanup(p.stop)
        os.makedirs(os.path.join(self.tmp.name, "job_logs"))

    @staticmethod
    def _round(cnt):
        return ("==== SCALE ROUND BEGIN count=%d rules=%d/38875 "
                "corpus=x ====\n"
                "==== SCALE ROUND END count=%d ====\n"
                % (cnt, cnt, cnt))

    def test_signal_skips_the_second_sweep(self):
        """A2014: same gate as scale_dlp, on the clam sweep loop."""
        ctx = JobHandle("scale_clam", "dry")
        body = "".join(self._round(c) for c in SCALE_CLAM_COUNTS["dry"])
        calls = []

        def fake(c, name, args, env, log_name="run"):
            calls.append(log_name)
            with open(c.log_path(log_name), "w") as f:
                f.write(body)
            _MOD._ABORTED = True
            return 0

        with mock.patch.object(_MOD, "run_rust_example", fake):
            result = run_leaf_scale_clamav("dry", ctx)
        self.assertEqual(len(calls), 1)
        self.assertEqual(result.rc, ABORT_RC)
        self.assertTrue(any("signal before" in n for n in ctx._notes))

    def test_argv_light_bundles_and_scan_free(self):
        """Dry sweeps pass light=1, run readelf then gdb, place the
        legacy bundle names, and verdict scan-free."""
        ctx = JobHandle("scale_clam", "dry")
        body = self._round(1) + self._round(300)
        calls = []

        def fake(c, name, args, env, log_name="run"):
            calls.append((name, args, log_name))
            with open(c.log_path(log_name), "w") as f:
                f.write(body)
            return 0
        with mock.patch.object(_MOD, "run_rust_example", fake):
            result = run_leaf_scale_clamav("dry", ctx)
        self.assertEqual(result.rc, 0)
        self.assertFalse(result.failed)
        self.assertEqual(calls, [
            ("bora_cli", ["scale_clam", "0", "1,300", "1"],
             "scale_readelf"),
            ("bora_cli", ["scale_clam", "1", "1,300", "1"],
             "scale_gdb")])
        for bundle in ("scale_data_readelf.tgz",
                        "scale_data_gdb.tgz"):
            self.assertTrue(os.path.isfile(raw_data_path(
                bundle, server_specific=False)))
        self.assertEqual(len(ctx.raw_data), 2)

    def test_counts_and_full_is_heavy(self):
        """Counts keep legacy cardinality (CLAM pins nothing);
        full passes light=0 and a failing rc wins."""
        self.assertEqual(SCALE_CLAM_COUNTS["dry"], [1, 300])
        self.assertEqual(SCALE_CLAM_COUNTS["full"],
                          [1, 3888, 7775, 11663, 15550, 19438,
                           23325, 27213, 31100, 34988, 38875])
        ctx = JobHandle("scale_clam", "full")
        calls = []

        def fake(c, name, args, env, log_name="run"):
            calls.append(args)
            with open(c.log_path(log_name), "w") as f:
                f.write("")
            return 3
        with mock.patch.object(_MOD, "run_rust_example", fake):
            result = run_leaf_scale_clamav("full", ctx)
        self.assertEqual(result.rc, 3)
        self.assertEqual(calls[0][3], "0")   # light=0 at full
        self.assertEqual(len(calls), 2)      # second still ran


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


def _write_regex_pool(root, sizes):
    """Materialize {name: byte_size} as <root>/<name>.regex files so the
    size cap can be exercised against a real filesystem."""
    for name, n in sizes.items():
        path = os.path.join(root, name + ".regex")
        os.makedirs(os.path.dirname(path), exist_ok=True)
        with open(path, "w") as fh:
            fh.write("x" * n)


class UnderSizeCapTest(unittest.TestCase):
    def setUp(self):
        self.drz = _load_dry_run_zombie()

    def test_regex_bytes_reads_the_real_file_size(self):
        """A resolvable name reports its .regex byte count."""
        with tempfile.TemporaryDirectory() as tmp:
            _write_regex_pool(tmp, {"slug/comb00": 123})
            self.assertEqual(
                self.drz.regex_bytes(tmp, "slug/comb00"), 123)

    def test_regex_bytes_is_zero_for_an_unresolvable_name(self):
        """A synthetic name stats to 0, so it is never cap-dropped."""
        with tempfile.TemporaryDirectory() as tmp:
            self.assertEqual(self.drz.regex_bytes(tmp, "nope"), 0)

    def test_drops_only_names_strictly_over_the_cap(self):
        """The cap is inclusive: == max_bytes survives, +1 does not."""
        with tempfile.TemporaryDirectory() as tmp:
            _write_regex_pool(tmp, {"a": 99, "b": 100, "c": 101})
            self.assertEqual(
                self.drz.under_size_cap(tmp, ["a", "b", "c"], 100),
                ["a", "b"])

    def test_preserves_input_order(self):
        """Filtering keeps corpus order, so spacing stays deterministic."""
        with tempfile.TemporaryDirectory() as tmp:
            _write_regex_pool(tmp, {"a": 1, "b": 999, "c": 2})
            self.assertEqual(
                self.drz.under_size_cap(tmp, ["c", "b", "a"], 10),
                ["c", "a"])

    def test_cap_constant_admits_the_measured_heavy_policy(self):
        """7100 keeps the 7032 B policy measured at 22.5 GB peak RSS."""
        self.assertGreaterEqual(self.drz.DRY_MAX_REGEX_BYTES, 7032)
        self.assertLess(self.drz.DRY_MAX_REGEX_BYTES, 7526)


class MakeDryListPolicyNamesTest(unittest.TestCase):
    def test_subsets_whatever_the_original_fn_returns(self):
        drz = _load_dry_run_zombie()
        original = mock.Mock(return_value=["a", "b", "c", "d"])
        patched = drz._make_dry_list_policy_names(50, original)
        got = patched("regex_zombie_international")
        original.assert_called_once_with("regex_zombie_international")
        self.assertEqual(got, drz.evenly_spaced_subset(
            ["a", "b", "c", "d"], 50))

    def test_size_cap_runs_before_the_spacing(self):
        """Oversized policies leave the pool first, so perc spaces over
        the survivors -- not over holes punched in the corpus."""
        drz = _load_dry_run_zombie()
        with tempfile.TemporaryDirectory() as tmp:
            _write_regex_pool(tmp, {"a": 1, "big": 10 ** 5, "c": 1,
                                     "d": 1})
            original = mock.Mock(return_value=["a", "big", "c", "d"])
            patched = drz._make_dry_list_policy_names(50, original)
            got = patched(tmp)
        self.assertNotIn("big", got)
        self.assertEqual(got, drz.evenly_spaced_subset(["a", "c", "d"],
                                                        50))


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

    def test_scan_free_crash_still_bundles_signatures(self):
        """A scan-free leaf that CRASHES must still ship its failure
        lines: the scan loses its vote, not its triage value."""
        ctx = JobHandle("dlp", "full")
        with open(ctx.log_path("run"), "w") as f:
            f.write("thread 'main' panicked at foo.rs:1:1:\n")
        result = ctx.finish(4, b_fail_scan=False)
        self.assertTrue(result.failed)
        with tarfile.open(result.triage_tgz, "r:gz") as t:
            summ = t.extractfile("SUMMARY.txt").read().decode()
        self.assertIn("panicked", summ)

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

    def test_advisory_lines_do_not_fail(self):
        ctx = JobHandle("dlp", "dry")
        with open(ctx.log_path("run"), "w") as f:
            f.write("CAVEAT: ... finalize via dryrun CapErr or scale"
                    " up.\nWARN big job ... aborts with ... SIGABRT"
                    " while RAM is free\n")
        self.assertFalse(ctx.finish(0).failed)
        ctx2 = JobHandle("dlp", "dry")
        with open(ctx2.log_path("run"), "w") as f:
            f.write("CapErr: word 3 over cap\n")
        self.assertTrue(ctx2.finish(0).failed)

    def test_peak_rss_and_raw_data_pass_through(self):
        ctx = JobHandle("reef", "dry")
        ctx.peak_rss_gb = 12.3
        ctx.raw_data.append("/x/out.dat")
        result = ctx.finish(0)
        self.assertEqual(result.peak_rss_gb, 12.3)
        self.assertEqual(result.raw_data_written, ["/x/out.dat"])


class JobHandleLogHygieneTest(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        for name, sub in (("JOB_LOG_DIR", "jobs"),
                           ("LOGS_DIR", "job_logs")):
            p = mock.patch.object(_MOD, name,
                                   os.path.join(self.tmp.name, sub))
            p.start()
            self.addCleanup(p.stop)

    def test_init_never_deletes_job_logs(self):
        """A2017: another run's live per-job logs must survive ours."""
        os.makedirs(_MOD.LOGS_DIR)
        other = os.path.join(_MOD.LOGS_DIR, "log_job_p0_3.txt")
        open(other, "w").close()
        JobHandle("k", "dry")
        self.assertTrue(os.path.exists(other))

    def test_job_logs_excludes_untouched_pre_existing(self):
        """A pre-existing log nobody rewrote is not ours to scan."""
        os.makedirs(_MOD.LOGS_DIR)
        old = os.path.join(_MOD.LOGS_DIR, "log_job_9.txt")
        with open(old, "w") as f:
            f.write("thread 'main' panicked at old.rs\n")
        os.utime(old, (1, 1))         # long before this job's _t0
        h = JobHandle("k", "dry")
        self.assertEqual(h._job_logs(), [])
        self.assertEqual(h._fail_lines(), [])

    def test_job_logs_includes_new_and_rewritten(self):
        """Ours = created after _t0, or a pre-existing name rewritten."""
        os.makedirs(_MOD.LOGS_DIR)
        touched = os.path.join(_MOD.LOGS_DIR, "log_job_1.txt")
        open(touched, "w").close()
        os.utime(touched, (1, 1))
        h = JobHandle("k", "dry")
        fresh = os.path.join(_MOD.LOGS_DIR, "log_job_2.txt")
        open(fresh, "w").close()
        # explicit stamp, not utime(None): the kernel's coarse mtime
        # clock can lag time.time() by a tick, which would make a
        # genuinely-rewritten file look older than _t0.
        os.utime(touched, (h._t0 + 1, h._t0 + 1))
        self.assertEqual(sorted(h._job_logs()), sorted([touched, fresh]))

    def test_log_path_registered_once(self):
        h = JobHandle("k", "dry")
        a = h.log_path("run")
        self.assertEqual(a, h.log_path("run"))
        self.assertEqual(h._log_paths.count(a), 1)

    def test_report_path_is_bundled_not_scanned(self):
        """report_path files ship in the tgz but never vote on failure."""
        h = JobHandle("k", "dry")
        r = h.report_path("lookup_stats")
        self.assertEqual(r, h.report_path("lookup_stats"))
        self.assertEqual(h.reports, [r])
        self.assertEqual(h._log_paths, [])
        with open(r, "w") as f:
            f.write("thread 'main' panicked at x.rs\n")
        self.assertEqual(h._fail_lines(), [])

    def test_compiler_source_echo_is_not_a_failure(self):
        """The 2026-08-14 false FAIL: a rustc warning quoting circ's
        `use std::{.., panic, ..}` failed a leaf that had passed."""
        h = JobHandle("k", "dry")
        with open(h.log_path("run"), "w") as f:
            f.write("32 | use std::{fmt::Write, panic, path::PathBuf};\n")
            f.write("   |     ^^^^^ CapErr in quoted source\n")
            f.write("warning: unused import: `std::panic`\n")
        self.assertEqual(h._fail_lines(), [])

    def test_real_failures_still_scan(self):
        """The narrowed FAIL_RE still catches a genuine panic, and a
        real rustc error, whose header carries no gutter."""
        h = JobHandle("k", "dry")
        with open(h.log_path("run"), "w") as f:
            f.write("thread 'main' panicked at src/x.rs:1:1:\n")
            f.write("error[E0308]: mismatched types\n")
        self.assertEqual(len(h._fail_lines()), 2)


class _WatchProbe:
    """Drives _watch_child deterministically: each entry is one poll's
    (pids, cpu_s, mtime, rss_gb); the child exits when they run out."""

    def __init__(self, samples):
        self.samples = list(samples)
        self.clock = 0.0
        self.proc = _FakeProc(pid=999)
        self.ctx = mock.Mock(peak_rss_gb=0.0, peak_idle_s=0.0)
        self.kills = []
        self.summary = []

    def _next(self):
        if not self.samples:
            self.proc.returncode = 0        # child gone -> loop exits
            return ([], 0.0, 0.0, 0.0)
        return self.samples.pop(0)

    def run(self, stall_s=100, step=10.0):
        cur = [([], 0.0, 0.0, 0.0)]

        def sleep(_s):
            self.clock += step

        def now():
            return self.clock

        def tick(_pid):
            cur[0] = self._next()
            return list(cur[0][0])

        with mock.patch.object(_MOD, "RSS_POLL_S", 0), \
             mock.patch.object(_MOD, "STALL_S", stall_s), \
             mock.patch.object(_MOD, "_tree_pids", side_effect=tick), \
             mock.patch.object(_MOD, "_cpu_s", lambda p: cur[0][1]), \
             mock.patch.object(_MOD, "_log_mtime", lambda p: cur[0][2]), \
             mock.patch.object(_MOD, "_rss_gb", lambda p: cur[0][3]), \
             mock.patch.object(_MOD, "_proc_state", return_value="S"), \
             mock.patch.object(_MOD, "_stall_kill",
                                side_effect=lambda *a: self.kills.append(a)), \
             mock.patch.object(_MOD, "_summary_line",
                                side_effect=self.summary.append), \
             mock.patch("time.time", side_effect=now), \
             mock.patch("time.sleep", side_effect=sleep):
            _watch_child(self.proc, "/tmp/run.log", self.ctx)
        return self


class WatchChildTest(unittest.TestCase):
    def test_keeps_peak_rss(self):
        """peak_rss_gb is the max tree RSS across polls, not the last."""
        pr = _WatchProbe([([1], 1.0, 1.0, 5.0), ([1], 2.0, 1.0, 20.0),
                          ([1], 3.0, 1.0, 3.0)]).run()
        self.assertEqual(pr.ctx.peak_rss_gb, 20.0)
        self.assertEqual(pr.kills, [])

    def test_cpu_progress_with_frozen_log_is_alive(self):
        """The cmF phase: hours of log silence but CPU still burning."""
        pr = _WatchProbe([([1], float(i), 1.0, 1.0)
                          for i in range(40)]).run(stall_s=100)
        self.assertEqual(pr.kills, [])

    def test_log_progress_with_flat_cpu_is_alive(self):
        """part2 blocked on the snark-start flag: no CPU, but it logs."""
        pr = _WatchProbe([([1], 5.0, float(i), 1.0)
                          for i in range(40)]).run(stall_s=100)
        self.assertEqual(pr.kills, [])

    def test_falling_cpu_total_is_progress_not_stall(self):
        """A child exiting DROPS the tree CPU sum.  A high-water-mark
        comparator stays blind while the survivor climbs 100->129,
        because none of that beats the pre-drop 900."""
        pr = _WatchProbe([([1, 2, 3], 900.0, 1.0, 1.0)]
                         + [([1], 100.0 + i, 1.0, 1.0)
                            for i in range(30)]).run(stall_s=100)
        self.assertEqual(pr.kills, [])

    def test_pid_churn_alone_is_progress(self):
        """Same CPU and mtime, different tree: still making progress."""
        pr = _WatchProbe([([1, i], 5.0, 1.0, 1.0)
                          for i in range(2, 40)]).run(stall_s=100)
        self.assertEqual(pr.kills, [])

    def test_frozen_on_all_axes_kills_and_rearms(self):
        """Nothing moves -> kill at STALL_S, and again one window later
        if the tree survived the kill."""
        pr = _WatchProbe([([1], 5.0, 1.0, 1.0)] * 25).run(stall_s=100)
        self.assertEqual(len(pr.kills), 2)
        self.assertGreaterEqual(pr.kills[0][4], 100)   # idle arg

    def test_warns_once_at_half_threshold(self):
        """The warning is one line, not one per poll."""
        pr = _WatchProbe([([1], 5.0, 1.0, 1.0)] * 9).run(stall_s=100)
        warns = [s for s in pr.summary if "no progress" in s]
        self.assertEqual(len(warns), 1)
        self.assertEqual(pr.kills, [])

    def test_records_peak_idle_margin(self):
        """peak_idle_s is the run's measured margin against STALL_S."""
        pr = _WatchProbe([([1], 5.0, 1.0, 1.0)] * 5
                         + [([1], 9.0, 1.0, 1.0)]).run(stall_s=1000)
        self.assertGreaterEqual(pr.ctx.peak_idle_s, 40.0)
        self.assertEqual(pr.kills, [])

    def test_never_reaps_the_child(self):
        """poll()/wait() here would race pid reuse in _kill_proc."""
        pr = _WatchProbe([([1], float(i), 1.0, 1.0) for i in range(3)])
        pr.proc.poll = lambda: self.fail("watcher must not poll()")
        pr.proc.wait = lambda *a, **k: self.fail("watcher must not wait()")
        pr.run()

    def test_exits_on_zombie_leader(self):
        """A child reaped by the main thread ends the watch immediately."""
        proc, ctx = _FakeProc(pid=999), mock.Mock(peak_rss_gb=0.0,
                                                   peak_idle_s=0.0)
        with mock.patch.object(_MOD, "_proc_state", return_value="Z"), \
             mock.patch.object(_MOD, "_tree_pids") as tp, \
             mock.patch("time.sleep"):
            _watch_child(proc, "/tmp/run.log", ctx)
        tp.assert_not_called()


class StallKillTest(unittest.TestCase):
    """Real children: a fake Popen cannot show SIGKILL escalation, and
    _FakeProc's pid would send the runner's own group a signal."""

    def setUp(self):
        _CHILDREN.clear()
        self.addCleanup(_CHILDREN.clear)
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.log = os.path.join(self.tmp.name, "run.log")
        self.ctx = JobHandle("k", "dry")

    def _spawn(self, setup=""):
        """Child that finishes `setup`, touches a ready file, then idles.
        The handshake matters for the SIGKILL test: signalling before the
        child installs SIG_IGN would only measure a SIGTERM.  It is a
        FILE, not a log line -- spawn() echoes the whole cmd into the log
        header, so any in-source marker matches itself."""
        ready = os.path.join(self.tmp.name, "ready")
        code = ("%s\nopen(%r, 'w').close()\nimport time\n"
                "time.sleep(120)\n" % (setup, ready))
        p, t = spawn([sys.executable, "-u", "-c", code], os.environ,
                      self.log, "t")
        self.addCleanup(_reap, p, t)
        for _ in range(400):
            if os.path.exists(ready):
                return p
            time.sleep(0.05)
        self.fail("child never became ready")

    def test_sigterm_path_reaps_and_notes_reason(self):
        p = self._spawn()
        with mock.patch.object(_MOD, "_summary_line") as sl:
            _stall_kill(p, self.ctx, [p.pid], self.log, 999.0, "run.log")
        self.assertIsNotNone(p.returncode)
        self.assertTrue(any("STALL" in n for n in self.ctx._notes))
        self.assertTrue(any("no progress for 999" in c[0][0]
                            for c in sl.call_args_list))

    def test_escalates_to_sigkill(self):
        p = self._spawn("import signal\n"
                        "signal.signal(signal.SIGTERM, signal.SIG_IGN)")
        with mock.patch.object(_MOD, "KILL_GRACE_S", 2), \
             mock.patch.object(_MOD, "_summary_line"):
            _stall_kill(p, self.ctx, [p.pid], self.log, 999.0, "run.log")
        self.assertEqual(p.returncode, -signal.SIGKILL)
        self.assertFalse(any("survived SIGKILL" in n
                             for n in self.ctx._notes))

    def test_evidence_dump_is_registered_for_the_bundle(self):
        p = self._spawn()
        with mock.patch.object(_MOD, "_summary_line"):
            _stall_kill(p, self.ctx, [p.pid], self.log, 999.0, "run.log")
        dumps = [r for r in self.ctx.reports if "stall_" in r]
        self.assertEqual(len(dumps), 1)
        text = open(dumps[0]).read()
        self.assertIn("no progress for 999", text)
        self.assertIn("per-thread", text)

    def test_gone_process_is_a_noop(self):
        p = self._spawn()
        _kill_proc(p, signal.SIGKILL)
        p.wait()
        _stall_kill(p, self.ctx, [p.pid], self.log, 999.0, "run.log")
        self.assertEqual(self.ctx._notes, [])


class JoinPumpTest(unittest.TestCase):
    def test_bounded_join_returns_on_a_hung_pump(self):
        """A pump blocked on a leaked pipe must not wedge the leaf."""
        stop = threading.Event()
        self.addCleanup(stop.set)
        t = threading.Thread(target=stop.wait, daemon=True)
        t.start()
        with mock.patch.object(_MOD, "KILL_GRACE_S", 0.1):
            _join_pump(t)
        self.assertTrue(t.is_alive())

    def test_none_is_a_noop(self):
        _join_pump(None)


class JobHandleWatchTest(unittest.TestCase):
    def test_starts_daemon_thread(self):
        ctx = JobHandle.__new__(JobHandle)
        ctx.peak_rss_gb = 0.0
        ctx.peak_idle_s = 0.0
        p = _FakeProc(pid=123)
        with mock.patch.object(_MOD, "_watch_child") as fake_watch:
            t = ctx.watch(p, "/tmp/run.log")
            t.join(timeout=1)
        fake_watch.assert_called_once_with(p, "/tmp/run.log", ctx)


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


class DryCostRollupTest(unittest.TestCase):
    def test_all_sums_wall_and_maxes_rss(self):
        """All = SUM of wall, MAX of RSS (leaves run in sequence, so
        RAM does not accumulate)."""
        mins, gb = dry_total()
        self.assertAlmostEqual(mins, sum(c[2] for c in DRY_COST))
        self.assertAlmostEqual(gb, max(c[3] for c in DRY_COST
                                        if c[3] is not None))
        self.assertGreater(mins, max(c[2] for c in DRY_COST))

    def test_unmeasured_rss_excluded_not_zeroed(self):
        """A None RSS must not drag the max down to 0 or crash. Uses a
        synthetic table so it survives every leaf being measured."""
        rows = [("a", "A", 1.0, None, ""), ("b", "B", 2.0, 9.5, "")]
        with mock.patch.object(_MOD, "DRY_COST", rows):
            self.assertEqual(dry_total(), (3.0, 9.5))

    def test_unmeasured_rss_omitted_from_the_label(self):
        """gb None renders no RSS at all rather than a bogus 0GB."""
        self.assertEqual(_cost_tag(9.0, None), "[dry ~9min]")

    def test_leaf_labels_derive_from_the_cost_table(self):
        """Labels are rendered, not hand-written, so a re-measure can
        never leave the menu disagreeing with DRY_COST."""
        self.assertEqual(
            dict(LEAF_CHOICES)["clam"], "Clamav [dry ~8.7min, ~17.1GB]")
        self.assertEqual(dict(LEAF_CHOICES)["dlp"],
                          "DLP [dry ~2.4min, ~6.5GB]")
        self.assertEqual(dict(LEAF_CHOICES)["zombie"],
                          "Zombie [dry ~6.8min cold, ~26.4GB]")

    def test_rollup_appears_on_layer_1_and_on_all(self):
        """The same rollup shows on the top menu's dry_run row and on
        the submenu's (A) All."""
        tag = _cost_tag(*dry_total(), lead="")
        self.assertIn(tag, dict(TOP_CHOICES)["dry_run"])
        buf = io.StringIO()
        with mock.patch("sys.stdout", buf):
            _show_submenu("dry_run")
        self.assertIn("(A) All %s" % tag, buf.getvalue())

    def test_full_run_all_has_no_dry_rollup(self):
        """full_run's leaf costs are unmeasured -- its All stays bare
        rather than quoting dry numbers."""
        buf = io.StringIO()
        with mock.patch("sys.stdout", buf):
            _show_submenu("full_run")
        self.assertIn("(A) All\n", buf.getvalue())
        self.assertNotIn("(A) All [", buf.getvalue())

    def test_snark_label_is_measured_not_dry(self):
        """Menu #2 quotes its own run trailer, so its tag must say
        measured and must never read as one of the dry estimates."""
        label = dict(TOP_CHOICES)["small_full_snark"]
        self.assertIn("[measured ~113.4min, ~433.2GB]", label)
        self.assertNotIn("dry", label)

    def test_every_leaf_key_has_a_cost_row(self):
        """DRY_COST is the single source of the leaf order and keys."""
        self.assertEqual([c[0] for c in DRY_COST], _LEAF_KEYS)
        self.assertEqual(sorted(_LEAF_KEYS), sorted(JOB_SPECS))


class RunSmallTest(unittest.TestCase):
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
        self.seen = {}

    def _capture(self, rc):
        """run_rust_single stand-in: records its args, returns rc."""
        def fake(ctx, test_path, env):
            self.seen.update(ctx=ctx, test=test_path, env=env)
            return rc
        return fake

    def test_success_launches_small_test_and_returns_zero(self):
        """rc=0 runs SMALL_TEST through run_rust_single and exits 0."""
        with mock.patch.object(_MOD, "run_rust_single",
                                side_effect=self._capture(0)):
            self.assertEqual(run_small(), 0)
        self.assertEqual(self.seen["test"], SMALL_TEST)
        self.assertEqual(self.seen["ctx"].key, "small")

    def test_env_carries_no_zkr_knobs(self):
        """small spawns via neo_env, so a ZKR_* in the caller's shell
        never reaches the legacy small_data path."""
        with mock.patch.dict(os.environ, {"ZKR_DLP_PCT": "50"}), \
             mock.patch.object(_MOD, "run_rust_single",
                                side_effect=self._capture(0)):
            run_small()
        self.assertFalse([k for k in self.seen["env"]
                           if k.startswith("ZKR_")])

    def test_report_registered_for_the_failure_bundle(self):
        """SMALL_REPORT lands on ctx.reports so a failed run packs it."""
        with mock.patch.object(_MOD, "run_rust_single",
                                side_effect=self._capture(0)):
            run_small()
        self.assertIn(SMALL_REPORT, self.seen["ctx"].reports)

    def test_failure_returns_one_and_packs_triage(self):
        """rc!=0 exits 1 and leaves a triage tgz behind."""
        with mock.patch.object(_MOD, "run_rust_single",
                                side_effect=self._capture(3)):
            self.assertEqual(run_small(), 1)
        self.assertTrue(glob.glob(os.path.join(
            self.tmp.name, "failed_tgz", "*.tgz")))


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


class PreflightTest(unittest.TestCase):
    """_preflight is the launch gate: fail-closed on a missing input
    file, degrade-only when the numactl probe fails."""

    def setUp(self):
        # never touch the real box from a unit test: no sudo sysctl.
        # _preflight no longer raises the VMA ceiling (main() does), but
        # test_main_returns_preflight_rc_without_detaching drives main().
        p = mock.patch.object(_MOD, "ensure_vma")
        self.vma = p.start()
        self.addCleanup(p.stop)

    def _plan(self, keys):
        return _FakePlan("full_run", "full", keys)

    def test_missing_file_aborts_with_rc_2(self):
        """An absent declared input stops the run before any probe or
        spawn."""
        specs = {"a": JobSpec("a", "a", lambda m, c: None,
                              lambda m: ["/nope/missing.py"])}
        with mock.patch.object(_MOD, "JOB_SPECS", specs), \
             mock.patch.object(_MOD, "preflight_numactl") as pn:
            rc = _preflight(self._plan(["a"]))
        self.assertEqual(rc, 2)
        pn.assert_not_called()

    def test_numactl_failure_degrades_instead_of_aborting(self):
        """A failed --preferred-many probe still returns 0, but clears
        the NUMA flag so every leaf runs as one unpinned process."""
        specs = {"a": JobSpec("a", "a", lambda m, c: None)}
        with mock.patch.object(_MOD, "JOB_SPECS", specs), \
             mock.patch.object(_MOD, "_NUMA_PROBE_OK", True), \
             mock.patch.object(_MOD, "preflight_numactl",
                                return_value=(False, ["unsupported"])):
            rc = _preflight(self._plan(["a"]))
            self.assertEqual(rc, 0)
            self.assertFalse(_MOD._NUMA_PROBE_OK)
            self.assertFalse(numa_available())
            self.assertEqual(resolve_process_model().n_parts, 1)

    def test_clean_box_returns_zero(self):
        """The happy path proceeds with rc 0."""
        specs = {"a": JobSpec("a", "a", lambda m, c: None)}
        with mock.patch.object(_MOD, "JOB_SPECS", specs), \
             mock.patch.object(_MOD, "preflight_numactl",
                                return_value=(True, [])):
            rc = _preflight(self._plan(["a"]))
        self.assertEqual(rc, 0)

    def test_required_files_union_is_ordered_and_deduped(self):
        """Leaves sharing a file contribute it once, in plan order; an
        undeclared leaf contributes nothing."""
        specs = {"a": JobSpec("a", "a", None, lambda m: ["/x", "/y"]),
                  "b": JobSpec("b", "b", None, lambda m: ["/y", "/z"]),
                  "c": JobSpec("c", "c", None)}
        with mock.patch.object(_MOD, "JOB_SPECS", specs):
            self.assertEqual(
                plan_required_files(self._plan(["a", "b", "c"])),
                ["/x", "/y", "/z"])

    def test_zombie_and_reef_declare_the_script_they_launch(self):
        """Preflight and launch must name the SAME file in both modes --
        the drift this field exists to prevent."""
        for key, fn in (("zombie", zombie_script),
                         ("reef", reef_script)):
            for mode in ("dry", "full"):
                self.assertEqual(
                    JOB_SPECS[key].required_files(mode), [fn(mode)])
        self.assertTrue(
            zombie_script("dry").endswith("dry_run_zombie.py"))
        self.assertTrue(zombie_script("full").endswith("run_zombie.py"))
        self.assertTrue(
            reef_script("dry").endswith("dry_run_eval_reef.py"))
        self.assertTrue(reef_script("full").endswith("eval_reef.py"))

    def test_main_returns_preflight_rc_without_detaching(self):
        """An abort must land BEFORE go_background(), so the operator
        sees it on the terminal instead of in a log."""
        with mock.patch("sys.argv",
                         ["prog", "--run", "dry_run", "--items", "lkup"]), \
             mock.patch.object(_MOD, "_preflight", return_value=2), \
             mock.patch.object(_MOD, "go_background") as gb, \
             mock.patch.object(_MOD, "Sequencer") as seq:
            rc = main()
        self.assertEqual(rc, 2)
        gb.assert_not_called()
        seq.assert_not_called()


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



class SequencerRunTest(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        patches = [
            mock.patch.object(_MOD, "SUMMARY_LOG",
                               os.path.join(self.tmp.name, "SUMMARY.log")),
            mock.patch.object(_MOD, "JOB_LOG_DIR",
                               os.path.join(self.tmp.name, "logs")),
            _sandbox_aborted(),
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

        def abort_then_ok(mode, ctx):
            _MOD._ABORTED = True
            return ok

        specs = {"a": JobSpec("a", "a", lambda m, c: ok),
                  "b": JobSpec("b", "b", abort_then_ok),
                  "c": JobSpec("c", "c", lambda m, c: ok)}
        with mock.patch.object(_MOD, "JOB_SPECS", specs):
            seq = Sequencer(_FakePlan("full_run", "full", ["a", "b", "c"]))
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

    def test_jobhandle_init_failure_fails_only_that_leaf(self):
        """JobHandle() raising (full disk, bad LOGS_DIR) must not escape
        the sequencer -- it is built INSIDE the try."""
        ok = _leaf_result(False)
        specs = {"a": JobSpec("a", "a", lambda m, c: ok),
                  "b": JobSpec("b", "b", lambda m, c: ok)}
        real = _MOD.JobHandle

        def boom_once(key, mode):
            if key == "a":
                raise OSError("no space left on device")
            return real(key, mode)

        with mock.patch.object(_MOD, "JOB_SPECS", specs), \
             mock.patch.object(_MOD, "JobHandle", boom_once):
            seq = Sequencer(_FakePlan("full_run", "full", ["a", "b"]))
            rc = seq.run()   # must NOT raise
        self.assertEqual(rc, 1)
        with open(_MOD.SUMMARY_LOG) as f:
            text = f.read()
        self.assertIn("JobHandle init failed", text)
        self.assertIn("FAIL   a", text)
        self.assertIn("OK     b", text)

    def test_triage_pack_failure_is_not_a_second_crash(self):
        """When _pack_bundle is what raised, the except handler must not
        re-enter it and kill the sequence."""
        def boom(mode, ctx):
            raise RuntimeError("launch-level bug")
        ok = _leaf_result(False)
        specs = {"a": JobSpec("a", "a", boom),
                  "b": JobSpec("b", "b", lambda m, c: ok)}
        with mock.patch.object(_MOD, "JOB_SPECS", specs), \
             mock.patch.object(_MOD.JobHandle, "_pack_bundle",
                                side_effect=OSError("tgz write failed")):
            seq = Sequencer(_FakePlan("full_run", "full", ["a", "b"]))
            rc = seq.run()   # must NOT raise
        self.assertEqual(rc, 1)
        with open(_MOD.SUMMARY_LOG) as f:
            text = f.read()
        self.assertIn("triage bundle failed", text)
        self.assertIn("FAIL   a", text)
        self.assertIn("OK     b", text)


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
        ab = _sandbox_aborted()
        ab.start()
        self.addCleanup(ab.stop)
        _CHILDREN.clear()
        self.addCleanup(_CHILDREN.clear)
        self.addCleanup(signal.signal, signal.SIGINT,
                         signal.getsignal(signal.SIGINT))
        self.addCleanup(signal.signal, signal.SIGTERM,
                         signal.getsignal(signal.SIGTERM))

    def test_sets_aborted_and_writes_summary(self):
        self.assertFalse(aborted())
        install_signal_handlers()
        signal.getsignal(signal.SIGINT)(signal.SIGINT, None)
        self.assertTrue(aborted())
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
        # Derive the digit from TOP_CHOICES rather than hard-coding it: this
        # test is about "a top entry WITH a submenu prompts for leaves", not
        # about dry_run being second. It used to type "2", which silently
        # became a different entry the moment the menu was reordered.
        n = [k for k, _ in TOP_CHOICES].index("dry_run") + 1
        with mock.patch("builtins.input", side_effect=[str(n), "dlp,clam"]):
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
        # main() raises vm.max_map_count for every top: never let a unit
        # test reach the real sudo sysctl.
        v = mock.patch.object(_MOD, "ensure_vma")
        self.vma = v.start()
        self.addCleanup(v.stop)

    def _seed_summary(self):
        """A stale FAIL line from an earlier run, as SUMMARY.log would
        really hold it."""
        with open(_MOD.SUMMARY_LOG, "w") as f:
            f.write("[11:44:18] FAIL   small_full_snark rc=101\n")

    def test_list_flag_prints_and_returns(self):
        self._seed_summary()
        with mock.patch("sys.argv", ["prog", "--list"]):
            self.assertEqual(main(), 0)
        self.vma.assert_not_called()
        with open(_MOD.SUMMARY_LOG) as f:
            self.assertIn("rc=101", f.read())

    def test_committed_run_wipes_stale_summary(self):
        """A real launch truncates SUMMARY.log and stamps NEW RUN, so an
        earlier run's FAIL cannot be read as the current state."""
        self._seed_summary()
        with mock.patch("sys.argv", ["prog", "--run", "small"]), \
             mock.patch.object(_MOD, "run_small", return_value=0):
            self.assertEqual(main(), 0)
        with open(_MOD.SUMMARY_LOG) as f:
            txt = f.read()
        self.assertNotIn("rc=101", txt)
        self.assertIn("=== NEW RUN", txt)
        self.assertIn("| small |", txt)
        # the banner must not join the per-leaf START scan (:1785).
        self.assertEqual(re.findall(r"START\s+(\S+)", txt), [])

    def test_plan_only_keeps_the_previous_summary(self):
        """--dry-run only prints the plan, so it must not destroy the
        last real run's record."""
        self._seed_summary()
        with mock.patch("sys.argv",
                         ["prog", "--dry-run", "--run", "small"]):
            self.assertEqual(main(), 0)
        with open(_MOD.SUMMARY_LOG) as f:
            self.assertIn("rc=101", f.read())

    def test_every_top_raises_vma_before_dispatch(self):
        """Every menu top asks for VMA_TARGET, including the three that
        return before _preflight()."""
        for top, _ in TOP_CHOICES:
            argv = ["prog", "--dry-run", "--run", top]
            if top not in NO_ITEM_TOPS:
                argv += ["--items", "dlp"]
            with self.subTest(top=top), mock.patch("sys.argv", argv):
                self.vma.reset_mock()
                self.assertEqual(main(), 0)
                self.vma.assert_called_once_with(VMA_TARGET)

    def test_small_dispatch_calls_run_small_no_backgrounding(self):
        """--run small runs in the foreground, like figs."""
        with mock.patch("sys.argv", ["prog", "--run", "small"]), \
             mock.patch.object(_MOD, "go_background") as gb, \
             mock.patch.object(_MOD, "run_small", return_value=0) as rs:
            self.assertEqual(main(), 0)
            gb.assert_not_called()
            rs.assert_called_once()

    def test_small_plan_only_skips_run_small(self):
        """--dry-run --run small prints the plan and spawns nothing."""
        with mock.patch("sys.argv",
                         ["prog", "--dry-run", "--run", "small"]), \
             mock.patch.object(_MOD, "run_small") as rs:
            self.assertEqual(main(), 0)
            rs.assert_not_called()

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
            ish.assert_called_once_with()
            fake_seq.run.assert_called_once()


class EndToEndWiringTest(unittest.TestCase):
    """Proves CLI -> resolve_plan -> Sequencer -> JobHandle wiring across
    all 8 canonical leaf keys, standing in stub_leaf() run_fns for
    EVERY leaf so the plan run spawns no real cargo. CURRENT_JOB.log
    is out of scope here -- only a real leaf's spawn helper calls
    point_current_job()."""

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
        for key in ("lkup", "zombie", "reef", "dlp", "scale_dlp",
                     "dna", "clam", "scale_clam"):
            specs[key] = JobSpec(key, key, stub_leaf(key, "Stage 2"))
        p = mock.patch.object(_MOD, "JOB_SPECS", specs)
        p.start()
        self.addCleanup(p.stop)

    def test_full_8_leaf_plan_runs_end_to_end(self):
        with mock.patch("sys.argv",
                         ["prog", "--run", "dry_run", "--items", "A"]), \
             mock.patch.object(_MOD, "_preflight", return_value=0) as pf, \
             mock.patch.object(_MOD, "go_background") as gb, \
             mock.patch.object(_MOD, "install_signal_handlers") as ish:
            rc = main()
        self.assertEqual(rc, 0)
        pf.assert_called_once()
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
