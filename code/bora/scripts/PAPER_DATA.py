#!/usr/bin/env python3
# ---------------------------------------------------------------------
# PAPER_DATA.py -- paper-data runner for bora.
#
# Interactive (menu) and non-interactive (--run/--items) driver for the
# paper's data-generation runs.  Built up in layers: D (common infra) ->
# C (leaf registry) -> B (sequencer) -> A (CLI/menu), landing shared
# infra first with stub leaves before any leaf gets a real
# implementation.
# Prepared by Opus 5 under guidance of paper authors.
# ---------------------------------------------------------------------

import argparse
import contextlib
import datetime
import fcntl
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


def run_rust_example(ctx, example_name, args, env, log_name="run",
                     max_wall_s=0, max_rss_gb=0):
    """Single-process `cargo run --release --example <name> -- <args>`,
    mirrors run_external_python but for a real bora_cli-style
    binary instead of a cargo test."""
    cmd = example_cmd(example_name, args)
    run_log = ctx.log_path(log_name)
    point_current_job(run_log, None)
    p, t = spawn(cmd, env, run_log, ctx.key)
    ctx.watch(p, run_log, max_wall_s=max_wall_s,
              max_rss_gb=max_rss_gb)
    p.wait()
    _join_pump(t)
    return p.returncode


# =====================================================================
# neo example launch (M102 D101): env scrub + two-half + scale packer
# =====================================================================

RUSTFLAGS_NEO = "-C link-args=-fuse-ld=lld -Awarnings"

PART_TOKEN = "{part_id}"   # substituted by run_example_two_half

KILL_GRACE_S = 60          # SIGTERM -> SIGKILL, and the pump-join bound


# Operator knobs that belong to the NEO arm itself, not legacy leakage:
# they gate neo-side code and must survive the ZKR_* scrub below.
NEO_ENV_PASS = ("ZKR_NEO_LOAD_LADDER", "ZKR_PROBE_DECLINE")


def neo_env(b_show_dropped=False):
    """The one env builder for bora_cli and small's cargo-test spawns:
    os.environ minus every ZKR_* (neo is argv-only; ~90 legacy env
    knobs must not leak in) except NEO_ENV_PASS, RUSTFLAGS forced for
    deterministic builds."""
    dropped = sorted(k for k in os.environ
                     if k.startswith("ZKR_") and k not in NEO_ENV_PASS)
    e = {k: v for k, v in os.environ.items()
         if not k.startswith("ZKR_") or k in NEO_ENV_PASS}
    e["RUSTFLAGS"] = RUSTFLAGS_NEO
    if b_show_dropped and dropped:
        log("neo_env: dropped %s" % " ".join(dropped))
    return e


def scale_env():
    """neo_env() plus ZKR_DB_PHASE when the operator exported it.

    Deliberately NOT added to NEO_ENV_PASS: neo_env() strips the var,
    so a stray export can reach a SCALE sweep (the only caller of
    this) but can never reach full_dlp/full_clam/full_dna, which call
    neo_env() directly.  The probes it unlocks are log-only."""
    e = neo_env()
    v = os.environ.get("ZKR_DB_PHASE")
    if v:
        e["ZKR_DB_PHASE"] = v
    # ZKR_DB_FAST is ON for every sweep and reachable NOWHERE else:
    # it swaps build_store's O(n^2) Vec::contains duplicate check
    # for the O(1) map insert.  Measured output-identical (COST,
    # lkup size, r1cs rows) at counts 494 and 988; gated only
    # because the DB cache is not byte-stable run-to-run, so a
    # byte-diff cannot certify it for the full runs.
    e["ZKR_DB_FAST"] = os.environ.get("ZKR_DB_FAST", "1")
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


def safe_pack_dump(ctx, base, logs, rc):
    """Place <base>.tgz for ANY outcome (R1): the .tgz is the run's
    full stdout/stderr log, so it belongs in the paper folder however
    the run ended.  A pack failure is noted, never raised, so a
    crashed run still gets its triage bundle."""
    try:
        return pack_full_dump(base, logs, ctx._ts)
    except Exception as e:
        # A raise mid-build leaves <base>*.tgz.tmp behind.  The stale
        # dump is unlinked only AFTER every .tmp is built, so the
        # previous dump is intact on this path either way.
        for t in glob.glob(raw_data_path(base + "*.tgz.tmp")):
            try:
                os.unlink(t)
            except OSError:
                pass
        ctx.note("dump not placed (rc=%s): %s" % (rc, e))
        return []


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

# ---- single-instance run lock ----------------------------------------
#
# Two PAPER_DATA.py on one box are mutually destructive regardless of
# any cache wipe: the second truncates the first's SUMMARY.log, repoints
# CURRENT_JOB.log, rmtree()s FLAG_DIR (releasing the first run's part2
# decider gate early -> overlapping RAM peaks), and its per-job logs
# land in the first run's mtime-scoped fail scan.  One flock at startup
# removes all four, and makes clear_db_cache() safe as a byproduct.

RUN_LOCK = "/tmp/bora/PAPER_DATA.lock"

# The lock fd, held open for the invocation's whole life.  None means
# this process does not hold the lock -- which is also what keeps the
# unit suite (it never acquires) off the real data/cache.
_run_lock_fd = None


def acquire_run_lock():
    """One PAPER_DATA.py per box: flock(RUN_LOCK), kernel-released on
    any death so it can never go stale.  go_background()'s double fork
    inherits the fd (it closes nothing); cargo children do not (Popen
    close_fds).  Returns None on success, else the holder's info line."""
    global _run_lock_fd
    # Already ours: flock treats two fds on one file independently even
    # within a process, so a re-entrant call would refuse ITSELF.  Real
    # runs call main() once; the unit suite calls it many times.
    if _run_lock_fd is not None:
        return None
    os.makedirs(os.path.dirname(RUN_LOCK), exist_ok=True)
    fd = os.open(RUN_LOCK, os.O_RDWR | os.O_CREAT, 0o644)
    try:
        fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except OSError:
        holder = os.read(fd, 256).decode(errors="replace").strip()
        os.close(fd)
        return holder or "unknown holder"
    os.ftruncate(fd, 0)
    os.write(fd, ("pid %d since %s\n" % (
        os.getpid(), datetime.datetime.now())).encode())
    _run_lock_fd = fd
    return None


# ---- data/cache wipe before a full leaf ------------------------------

# Every DB cache lands here: clam_db.rs:2434/2479/2567 build each
# save/load/exists path as <proj_root>/data/cache/<dir_name>, for the
# neo dirs (<name>_neo_p*) and the legacy ones (full_data, dlp_corpus_
# aggr, ...) alike.
CACHE_DIR = os.path.join(REPO, "data", "cache")

# Never wiped: logs/ is LOGS_DIR, where the Rust per-job logs land
# (logger.rs:127) and where every leaf's fail scan reads (A2017);
# main/ is ensured-present by INSTALL.py and never repopulated by it.
CACHE_KEEP = {"logs", "main"}


def clear_db_cache():
    """Best-effort wipe of data/cache before a full leaf, so a run
    reclaims the previous DB copies BEFORE writing its own (clam writes
    ~17GB per NUMA part).  Safe: neo always rebuilds its cache
    (build_or_load read=false), and every other consumer falls back to
    rebuild+save on a missing one (clam_db.rs:2596-2606).  NOT protected
    against runs launched outside PAPER_DATA.py (bare cargo test).
    Returns warning lines instead of raising -- a half-wipe must not
    fail the leaf, and rebuild semantics tolerate partial deletion."""
    warns = []
    if not os.path.isdir(CACHE_DIR):
        return warns
    for name in sorted(os.listdir(CACHE_DIR)):
        if name in CACHE_KEEP:
            continue
        p = os.path.join(CACHE_DIR, name)
        try:
            # data/cache holds plain files (run_complete.sentinel,
            # to_remove.pl) and, on server boxes, symlinks (numa_probe);
            # rmtree raises on both.
            if os.path.islink(p) or not os.path.isdir(p):
                os.unlink(p)
            else:
                shutil.rmtree(p)
        except OSError as e:
            warns.append("clear_db_cache: %s: %s" % (name, e))
    return warns

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


def _watch_child(p, log_path, ctx, max_wall_s=0, max_rss_gb=0):
    """Supervisor thread for one spawned child: tracks peak tree-RSS and
    kills a tree that has made no progress on EITHER axis for STALL_S.
    Progress = any change in (pids, tree cpu, log mtime).  The cpu sum
    falls when a child exits, so the test is inequality with a re-based
    key, never a high-water mark: a shrinking tree IS progress."""
    pid, label = p.pid, os.path.basename(log_path)
    key, last, warned = None, time.time(), False
    # WALL cap, distinct from STALL_S.  STALL_S is a NO-PROGRESS
    # watchdog; a diverging tuner logs a round every ~2 h at 100 %% CPU,
    # so it looks perfectly healthy and STALL_S never fires
    # (max_iters is 60 -> up to ~109 h).  0 = no cap, the default for
    # every pre-existing caller.
    t_start = time.time()
    # p.returncode is a plain attribute read: never poll()/wait() here,
    # or this thread reaps the child and every later os.getpgid(p.pid)
    # races pid reuse.  _proc_state covers the child that died while the
    # main thread was blocked on its sibling.
    while p.returncode is None and _proc_state(pid) not in ("", "Z"):
        pids = _tree_pids(pid)
        gb = _rss_gb(pids)
        if gb > ctx.peak_rss_gb:
            ctx.peak_rss_gb = gb
        if max_rss_gb and gb > max_rss_gb:
            # A kernel OOM takes the whole box down with it; a guarded
            # kill costs one step.  V101 dec_big only.
            _summary_line("       %s: RSS CEILING %.0fGB exceeded "
                          "(%.1fGB) -- killing (OOM-GUARD)"
                          % (label, max_rss_gb, gb))
            ctx.rss_ceiling_hit = True
            _stall_kill(p, ctx, pids, log_path, 0, label)
            return
        # WALL CAP -- an UNCONDITIONAL test, deliberately not an elif
        # on the progress branch.  `now` below carries summed CPU
        # time, which advances at every poll for any compute-bound
        # tree, so a progress-gated wall cap can only ever fire on a
        # process that is ALREADY idle: never on the diverging tuner
        # it exists to bound.  MEASURED 2026-08-17 before the fix:
        # busy child, cap 4 s -> still running at 19 s; idle child,
        # same cap -> killed at 4.2 s.  Resolution is one RSS_POLL_S
        # (10 s), so the kill lands at the next poll after the cap,
        # not on it -- immaterial at the real caps (>= 900 s).
        # Pinned by
        # WatchChildTest.test_wall_cap_kills_a_busy_child.
        if max_wall_s and time.time() - t_start >= max_wall_s:
            _summary_line("       %s: WALL CAP %ds reached -- killing "
                          "(TIMEOUT, not a failure)"
                          % (label, max_wall_s))
            _stall_kill(p, ctx, pids, log_path,
                        time.time() - t_start, label)
            return
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
        # Set by _watch_child when max_rss_gb fired.  A guarded OOM
        # kill is a RESOURCE outcome, not a defect in the step.
        self.rss_ceiling_hit = False
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

    def watch(self, p, log_path, max_wall_s=0, max_rss_gb=0):
        t = threading.Thread(target=_watch_child,
                              args=(p, log_path, self, max_wall_s,
                                    max_rss_gb),
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
            # R3: the paper-data dump rides along, so ONE bundle
            # carries every artifact of a failed run.
            for dp in self.raw_data:
                if dp and os.path.isfile(dp):
                    t.add(dp, arcname="raw_data/"
                           + os.path.basename(dp))
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

# vm.max_map_count floor requested at launch, ZKR_VM_MAX_MAP_COUNT
# overridable -- the legacy attic/scripts/PAPER_DATA.py:61 parameters,
# restored verbatim.  Rust re-checks with a data-derived estimate and
# aborts after the DB build (foldpot/driver.rs:2453); the interim 8M
# floor was sized for the 8-job DLP shape (32768 + 8*34071*16) and
# under-covered full_dna, whose single job carries 1,342,862 packed
# fields -> est need 21,518,560 -> PREFLIGHT ABORT on a fresh box.
# The raise is lazy kernel bookkeeping: no memory cost until mapped.
VMA_TARGET = int(os.environ.get("ZKR_VM_MAX_MAP_COUNT", "1073741824"))


def ensure_vma(target):
    """Raise vm.max_map_count via sudo sysctl, then ENFORCE the floor:
    below it we quit here.  No-op if target <= 0; an unreadable
    /proc entry stays non-fatal (we cannot gate on what we cannot
    read).  Bypass with ZKR_SKIP_MAP_COUNT_CHECK=1, the same env var
    Rust honours."""
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
    # The RAISE is best-effort; the FLOOR is not.  Re-read instead of
    # trusting rc -- the file is the authority, and the value may
    # already be high from /etc/sysctl.d or an earlier session, in
    # which case a missing sudo is harmless.
    try:
        cur = int(open(path).read().strip())
    except OSError as e:
        log("vm.max_map_count: cannot re-read (%s); not gating" % e)
        return
    if cur >= target:
        return
    if os.environ.get("ZKR_SKIP_MAP_COUNT_CHECK"):
        log("WARN: vm.max_map_count=%d < %d but "
            "ZKR_SKIP_MAP_COUNT_CHECK is set -- continuing" %
            (cur, target))
        return
    # Quit HERE, not hours in.  Rust re-checks per job with the exact
    # packed-field count (foldpot/driver.rs:2686) but only AFTER the
    # DB build, and it has FALSE-PASSED (52,544 est vs >1M actual on
    # small_full_snark, 512GB box, 2026-08-13) -- so this floor is the
    # gate that has to hold.  One floor covers every menu item;
    # measured needs by `32768 + n_jobs*max_job_fields*16`:
    #   full_dlp  474,624,000   (8 jobs)
    #   full_clam 431,521,792   (8 jobs, max job 3,371,008 fields)
    #   full_dna   21,518,560   (1 job, 1,342,862 fields)
    raise SystemExit(
        "PREFLIGHT ABORT: vm.max_map_count=%d < %d.\n"
        "  mimalloc hits ENOMEM on mmap/munmap once the VMA count\n"
        "  reaches this ceiling, with RAM still free -- every full\n"
        "  run needs it (full_dlp 474,624,000, full_clam\n"
        "  431,521,792, full_dna 21,518,560).\n"
        "  Fix on the server (free, no memory cost):\n"
        "    sudo sysctl -w vm.max_map_count=%d\n"
        "  Persist:\n"
        "    echo 'vm.max_map_count=%d' | sudo tee \\\n"
        "      /etc/sysctl.d/99-zkregplus.conf && sudo sysctl --system\n"
        "  Or bypass: export ZKR_SKIP_MAP_COUNT_CHECK=1"
        % (cur, target, target, target))


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


# effective leaf's dry thinning: collect_assess_tier_data_adv applies
# it to BOTH the signature set and the scan corpus, so the dry DB stays
# small (the aggressive Dlp DB is ~10 GB serialized at full size).
EFFECTIVE_DRY_PERC = 2

# Positive markers the report must carry: one "Data for" block per
# dataset, the two filesize re-bucket groups (fig 9b), and the END
# banner (truncation guard).  These are the exact strings
# scripts/eval/effectiveness.py regexes for.
EFFECT_SECTIONS = ("=== Data for Mal ===", "=== Data for Dna ===",
                   "=== Data for Dlp ===", "Filesize data for Mal",
                   "Filesize data for Dlp")
EFFECT_END = "END EFFECTIVENESS REPORT"


def effective_missing_success(path, t0):
    """None when the tier-discharge report is complete and was written
    by THIS run, else the reason.  Positive predicate (lkup pattern):
    the collector println!s the report, so its text is in run.log
    either way and the fail scan cannot judge it."""
    if not os.path.isfile(path):
        return "no report at %s" % path
    if os.path.getmtime(path) < t0:
        return "stale report, not rewritten this run"
    text = open(path, errors="replace").read()
    missing = [s for s in EFFECT_SECTIONS if s not in text]
    if missing:
        return "report missing: %s" % ", ".join(missing)
    if EFFECT_END not in text:
        return "report has no END banner (truncated)"
    return None


def run_leaf_effective(mode, ctx):
    """S7.3 tier-discharge report (eval_effective.txt) via
    bora_data_driver::collect_assess_tier_data_adv.  Dlp builds
    AGGRESSIVE (its deployed mode); Mal/Dna non-aggressive.  dry thins
    signatures and scan corpus to perc%; full is the real report."""
    perc = EFFECTIVE_DRY_PERC if mode == "dry" else 100
    local_out = ctx.report_path("eval_effective")
    env = neo_env()
    rc = run_rust_example(ctx, "bora_cli",
                           ["effective", str(perc), local_out], env)
    if rc == 0:
        missing = effective_missing_success(local_out, ctx._t0)
        if missing:
            ctx.note("effective: %s" % missing)
            rc = 6
        else:
            dest = place_raw_data(local_out, "eval_effective.txt",
                                   server_specific=False)
            ctx.raw_data.append(dest)
    # b_fail_scan=False as lkup: the report itself is println!'d into
    # run.log, and ClamAV signature NAMES are arbitrary text.
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
    # R1: the .tgz IS this run's full stdout/stderr log, so it is
    # placed for EVERY outcome -- pass, fail, crash, ladder
    # divergence, or a run that stopped at step 100 of 3000.  Whether
    # the run SUCCEEDED is a separate question, answered by rc and the
    # fail scan, which alone drive the failed_tgz bundle and the
    # FAILURE report.  (D1: canonical name, no backup, so a failed run
    # DOES overwrite the last good dump.)
    ctx.raw_data.extend(safe_pack_dump(ctx, base, logs, rc))
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
    # R1: placed for every outcome -- see run_leaf_full_neo.
    ctx.raw_data.extend(safe_pack_dump(ctx, "full_dna", logs, rc))
    # b_fail_scan=False (D103 pattern): the NON-AGGR tuner prints its
    # caught CapErr probe panics into the run log, so FAIL_RE would
    # counterfeit a FAIL on every successful run. Verdict = rc + the
    # positive markers above.
    return ctx.finish(rc, b_fail_scan=False)


# 69801 decider-probe env (2026-08-15, "snark main fails" triage).
# neo_env() scrubs every ZKR_*, so these must be re-added AFTER it.
DNA_DEBUG_ENV = {
    "ZKR_DECIDER_SAT": "1",       # per-step decider UNSAT checkpoints
    "ZKR_MAIN_SNARK_PROBE": "1",  # pass-vs-from_nova diff + self-verify
    "ZKR_LKUP_PROBE": "1",        # lkup dummy-slot zero audit
    "ZKR_STOP_AFTER_MAIN": "1",   # exit(0) before the CyclePair phase
    "ZKR_STEP_BRACKETS": "1",     # per-gadget step-circ row brackets
    # In-fold step-circuit SAT check, LAST step only (pre-increment
    # i, so 328 steps -> i=327; inert on shorter runs). All-steps
    # (FROM=0) costs ~+9h at full shape -- opt-in by hand only.
    "ZKR_GADGET_CHECK": "1",
    "ZKR_GADGET_FROM": "327",
}

# Lines worth echoing back as the diagnosis: the 69801 probe prints
# plus the armed checkpoint verdicts (utils.rs gadget_sat_check).
DNA_DEBUG_MARK_RE = re.compile(
    r"DEBUG USE 69801\.\d+|GADGET-UNSAT|GADGET-SAT")

# ERROR-class markers: any of these mid-run is already a verdict, so
# the watcher thread alerts on FIRST sight instead of waiting hours
# for the leaf to finish.
DNA_DEBUG_ERR_RE = re.compile(
    r"GADGET-UNSAT"
    r"|69801\.1: .*eq=false"
    r"|69801\.6: .*(bad_c1 [1-9]|bad_c2 [1-9])"
    r"|69801\.7: .*(Ok\(false\)|Err)"
    r"|VERIFICATION FAILED")

# One-file verdict drop for the operator (tail -F or just cat).
DNA_DEBUG_VERDICT = "/tmp/bora/DNA_DEBUG_VERDICT.txt"


def _dna_debug_diagnose(lines):
    """Map the probe lines onto the 69801 decision tree. Returns
    (verdict, detail_lines): verdict is one short CLASS-tagged line."""
    unsat = [l for l in lines if "GADGET-UNSAT" in l]
    if unsat:
        detail = list(unsat)
        # p1s7 is the folded-step-circuit check: first-bad minus the
        # p1s6 cumulative count is the ROW WITHIN THE STEP CIRCUIT,
        # which the ZKR_STEP_BRACKETS "gen_step_cs step N" lines
        # bracket per gadget.
        m = re.search(r"@decider::p1s7 first-bad=(\d+)", unsat[0])
        if m:
            for l in lines:
                m6 = re.search(r"@decider::p1s6 \((\d+) cons\)", l)
                if m6:
                    row = int(m.group(1)) - int(m6.group(1))
                    detail.insert(0, "step-circuit row = %d (map via "
                                  "gen_step_cs brackets)" % row)
                    break
        return ("CLASS A (UNSAT): decider constraint system rejected "
                "the honest witness -- %s" % unsat[0].strip(),
                detail)
    bad_hash = [l for l in lines
                if "69801.1" in l and "eq=false" in l]
    if bad_hash:
        fields = [l for l in lines if "69801.3" in l]
        return ("CLASS B (pass divergence): prove-pass result != "
                "from_nova; diverging fields follow", bad_hash + fields)
    bad_dummy = [l for l in lines if "69801.6" in l and
                 re.search(r"bad_c1 [1-9]|bad_c2 [1-9]", l)]
    if bad_dummy:
        return ("CLASS D (lkup dummies): nonzero dummy col share "
                "slots violate the ch^(cfg-act) recovery assumption",
                bad_dummy[:5])
    bad_ver = [l for l in lines if "69801.7" in l
               and "Ok(true)" not in l]
    if bad_ver:
        return ("CLASS C (key divergence): circuit consistent both "
                "passes yet the snark does not verify -- keygen vs "
                "prove synthesis differ", bad_ver)
    if any("69801.9" in l for l in lines) and \
       any("69801.7" in l and "Ok(true)" in l for l in lines):
        return ("GREEN: all checkpoints SAT, passes agree, main "
                "snark verifies Ok(true) at this shape -- bug did "
                "NOT reproduce here", [])
    return ("INCONCLUSIVE: probes missing or run died before the "
            "decider -- read the log tail", [])


def _dna_debug_alert(subject, body_lines):
    """Push the verdict everywhere a headless operator might look:
    SUMMARY.log banner, a one-file verdict drop, and best-effort
    wall(1) to every logged-in tty. Never raises."""
    try:
        _summary_line("DNA_DEBUG >>> %s" % subject)
        for l in body_lines[:10]:
            _summary_line("DNA_DEBUG     %s" % l.strip())
        with open(DNA_DEBUG_VERDICT, "a") as f:
            f.write("[%s] %s\n" % (_ts(), subject))
            for l in body_lines:
                f.write("    %s\n" % l.strip())
        if shutil.which("wall"):
            msg = "PAPER_DATA dna_debug: %s" % subject[:200]
            subprocess.run(["wall", msg], timeout=10,
                           stdout=subprocess.DEVNULL,
                           stderr=subprocess.DEVNULL)
    except Exception as e:
        log("dna_debug: alert delivery failed: %s" % e)


def _dna_debug_watch(log_path, done_ev):
    """Watcher thread: poll the child's log; on the FIRST error-class
    marker, alert immediately (the full run is hours -- the operator
    should not wait for exit to learn the decider rejected)."""
    seen = 0
    while not done_ev.wait(10):
        try:
            if not os.path.exists(log_path):
                continue
            with open(log_path, errors="replace") as f:
                text = f.read()
            m = DNA_DEBUG_ERR_RE.search(text, seen)
            if m:
                line = text[text.rfind("\n", 0, m.start())+1:
                            text.find("\n", m.end())]
                _dna_debug_alert(
                    "ERROR marker mid-run: %s" % line.strip(), [])
                return  # one mid-run alert; the final one recaps
            seen = max(0, len(text) - 4096)  # rescan tail overlap
        except Exception:
            pass


def run_dna_debug(mode):
    """Menu dna_debug leaf: full_dna with the 69801 decider probes
    armed; classifies the probe lines (CLASS A-D / GREEN) and alerts
    via SUMMARY.log + DNA_DEBUG_VERDICT.txt + wall(1) both mid-run on
    the first ERROR marker and at the end. The Rust side exit(0)s
    after the main snark, so proof-success markers are NOT expected."""
    ctx = JobHandle("dna_debug", mode)
    env = neo_env()
    env.update(DNA_DEBUG_ENV)
    # dry mode: 1% DB x 2% sample but NON-light -- the tuner still
    # converges to the full statement width (measured: cs1e 34.63M vs
    # full 34.66M, share 2539 both), so 7 fold steps exercise the
    # SAME full-width decider incl steps 8/9/10 in a fraction of the
    # wall. Step count differs, so the last-step in-fold check index
    # follows the mode (pre-increment i: 7 steps -> 6, 328 -> 327).
    if mode == "dry":
        argv = ["full_dna", "1", "2", "1", "1", "1", "0", "0", "0"]
        env["ZKR_GADGET_FROM"] = "6"
    else:
        argv = dna_argv(mode)
    ctx.note("mode=dna_debug(%s) probes=%s gadget_from=%s" % (
        mode, ",".join(sorted(DNA_DEBUG_ENV)),
        env.get("ZKR_GADGET_FROM")))
    lp = ctx.log_path("run")
    done_ev = threading.Event()
    watcher = threading.Thread(target=_dna_debug_watch,
                               args=(lp, done_ev), daemon=True)
    watcher.start()
    try:
        rc = run_rust_example(ctx, "bora_cli", argv, env)
    finally:
        done_ev.set()
    watcher.join(timeout=2)
    lines = []
    if os.path.exists(lp):
        for ln in open(lp, errors="replace"):
            if DNA_DEBUG_MARK_RE.search(ln):
                lines.append(ln.rstrip())
    for ln in lines:
        log(ln)
    verdict, detail = _dna_debug_diagnose(lines)
    if not lines:
        ctx.note("NO 69801 probe markers in the log -- the probed "
                 "branch never ran (env scrubbed or early failure)")
        rc = rc or 6
    ctx.note("verdict: %s" % verdict)
    res = ctx.finish(rc, b_fail_scan=False)
    # ALWAYS pack a bundle: on a green debug run the probe lines ARE
    # the analysis artifact, and finish() only packs on failure.
    tgz = res.triage_tgz
    if tgz is None:
        try:
            tgz = ctx._pack_bundle(res.rc, res.wall_s, [])
        except Exception as e:
            log("dna_debug: bundle pack failed: %s" % e)
    _dna_debug_alert("FINISHED rc=%d wall=%ds -- %s | bundle: %s" % (
        res.rc, int(res.wall_s), verdict, tgz), detail)
    log("dna_debug: rc=%d wall=%ds probe_lines=%d log=%s" % (
        res.rc, int(res.wall_s), len(lines), lp))
    log("dna_debug: VERDICT: %s" % verdict)
    log("dna_debug: verdict file: %s  bundle: %s" % (
        DNA_DEBUG_VERDICT, tgz))
    return 1 if res.failed else 0


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


def clam_jobs(mode):
    """Job count for the clam leaf.  ZKR_4JOB halves the full shape:
    8 jobs peak ~479 GB and OOM a 512 GB box, 4 fit.  The ladder is
    job-count independent, so a reused ladder stays valid."""
    if mode == "full" and os.environ.get("ZKR_4JOB"):
        return "4"
    return CLAM_LEAF_ARGS[mode][3]


def clam_argv(mode, numa_num, part):
    """The 9-token bora_cli argv for one full_clam part; part is "0"
    (single process) or PART_TOKEN (two-half). ladder_only always 0."""
    pdb, ps, nc, _nj, light = CLAM_LEAF_ARGS[mode]
    return ["full_clam", pdb, ps, nc, clam_jobs(mode), str(numa_num),
            part, light, "0"]


def run_leaf_clamav(mode, ctx):
    """M104 Clamav leaf: bora_cli full_clam (neo, argv-only);
    verdicts scan-free (the non-aggr tuner prints caught CapErr
    probe panics into every successful log, M103 11.4)."""
    return run_leaf_full_neo(mode, ctx, clam_argv, "full_clam",
                              int(clam_jobs(mode)), "clam",
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


# =====================================================================
# Scale per-round telemetry (emitted by bora_data_driver.rs)
# =====================================================================
# STATS carries the round's fold wall and its saturation: the worst
# SINGLE-CHUNK fill/cap per gauge, read after the last SUCCESSFUL fold
# (retry_caperr resets the gauges at the top of every try).  HIGH IS
# GOOD -- a tight capacity is the point; a LOW reading is capacity
# wasted on that axis, and an OVER after a passing fold is an anomaly.
# sat_report_max omits gauges that never fired, so an empty tail is
# legal, not a parse failure.  PERF 1010 carries the pre-fold split;
# together they account for the whole round.
SCALE_STATS_RE = re.compile(
    r"==== SCALE ROUND STATS count=(\d+) fold_ms=(\d+) sat=(.*?)\s*====")
SAT_ITEM_RE = re.compile(
    r"(\w+) (cs|igc)=(\d+)/(\d+) \(([\d.]+)%( OVER)?\)")
SCALE_PERF_RE = re.compile(
    r"PERF 1010 build_and_tune\[\S+\] cnt=(\d+) db_ms=(\d+) "
    r"disch_ms=(\d+) tune_ms=(\d+)")
SCALE_COST_RE = re.compile(
    r"==== COST GRAND TOTAL over \d+ circuits = (\d+) ====")
SCALE_BUMP_RE = re.compile(r"fold CapErr bump try \d+:")

# build_db's own 7-step split and the 69210 probes.  BOTH are
# emitted only under ZKR_DB_PHASE, so an ordinary sweep log yields
# nothing here and every consumer sees the empty defaults.
# "Bluld_DB" is the source's own typo on step 2 (clam_db.rs).
# The lazy .*? before the duration is what keeps step 7's inline
# "Lkup size: N" from being read as the timing.
SCALE_DBSTEP_RE = re.compile(
    r"B[a-z]+_DB:? (Step [0-9][a-z]?)\b.*?(\d+) (ms|us)\s*$")
SCALE_DBSAVE_RE = re.compile(
    r"DEBUG USE 69210\.9: build_or_load: save cache "
    r"(\d+) (ms|us)\s*$")
SCALE_DBSPLIT_RE = re.compile(
    r"DEBUG USE 69210\.10: db split cnt=(\d+) cfg_ms=(\d+) "
    r"build_ms=(\d+)")

_SCALE_EMPTY = {"sat": "", "bumps": 0, "done": False, "db_ms": 0,
                "disch_ms": 0, "tune_ms": 0, "fold_ms": 0, "cost": None}


def _ms_of(val, unit):
    """flog_perf prints us below 1 ms and ms above; normalise."""
    return float(val) / 1000.0 if unit == "us" else float(val)


def _scale_empty():
    """One fresh round record.  `steps` MUST be built here: dict()
    is a shallow copy, so a literal default would alias one dict
    across every round in the sweep."""
    d = dict(_SCALE_EMPTY)
    d["steps"] = {}     # "Step 1b"/"save" -> ms (float), 69210
    d["cfg_ms"] = 0     # thinning, split out of db_ms by 69210.10
    d["build_ms"] = 0   # build_fresh_db + its cache write, ditto
    return d


def scale_rounds(run_log):
    """Per-round telemetry from one sweep log, keyed by rule count.

    Never raises: a truncated or malformed round still yields what was
    parsed, because this feeds a report, not a gate.  `cost` keeps the
    LAST COST block of the round -- a bump retry emits one per fold
    attempt and only the converged one describes what shipped."""
    out, cur = {}, None
    if not os.path.isfile(run_log):
        return out          # arm never ran, or crashed before its first line
    for line in open(run_log, errors="replace"):
        mb = SCALE_BEGIN_RE.search(line)
        if mb:
            cur = int(mb.group(1))
            out.setdefault(cur, _scale_empty())
            continue
        if cur is None:
            continue
        r = out[cur]
        m = SCALE_PERF_RE.search(line)
        if m and int(m.group(1)) == cur:
            r["db_ms"], r["disch_ms"], r["tune_ms"] = (
                int(m.group(2)), int(m.group(3)), int(m.group(4)))
            continue
        m = SCALE_COST_RE.search(line)
        if m:
            r["cost"] = int(m.group(1))
            continue
        m = SCALE_STATS_RE.search(line)
        if m and int(m.group(1)) == cur:
            r["fold_ms"], r["sat"] = int(m.group(2)), m.group(3)
            continue
        m = SCALE_DBSPLIT_RE.search(line)
        if m and int(m.group(1)) == cur:
            r["cfg_ms"], r["build_ms"] = int(m.group(2)), int(m.group(3))
            continue
        m = SCALE_DBSAVE_RE.search(line)
        if m:
            r["steps"]["save"] = _ms_of(m.group(1), m.group(2))
            continue
        m = SCALE_DBSTEP_RE.search(line)
        if m:
            r["steps"][m.group(1)] = _ms_of(m.group(2), m.group(3))
            continue
        if SCALE_BUMP_RE.search(line):
            r["bumps"] += 1
            continue
        me = SCALE_END_RE.search(line)
        if me and int(me.group(1)) == cur:
            r["done"] = True
    return out


# The gauges whose >100% actually means "over budget".  Q_m records
# the two operands CapErr compares and Q_c the quantity the theorem
# bounds (discharge_adv_neo.rs:1993, :3995).  wrap/real/sub are a
# DECOMPOSITION of the jointly-budgeted Q_m total -- the source calls
# them "SPLIT gauges" -- so any one of them can read over 100% while
# the enforced total is comfortably inside its budget.  Flagging those
# would cry wolf on a healthy round: MEASURED 2026-08-20, gdb count
# 300 shipped real cs=6/2 (300%) with Q_m cs=17/90 (18.9%).
SAT_ENFORCED = ("Q_m", "Q_c")


def sat_span(sat):
    """(min_pct, max_pct, n_over) for one round.

    min/max span EVERY gauge -- that is the capacity-utilisation range,
    and a low min is capacity wasted on that axis.  n_over counts only
    SAT_ENFORCED gauges, because only those bound anything."""
    items = SAT_ITEM_RE.findall(sat)
    if not items:
        return None, None, 0
    pcts = [float(p) for _, _, _, _, p, _ in items]
    over = sum(1 for i in items if i[5] and i[0] in SAT_ENFORCED)
    return min(pcts), max(pcts), over


def _scale_s(ms):
    """Milliseconds as seconds, for the report columns."""
    return ms / 1000.0


def scale_round_report(run_log, tag):
    """Per-round telemetry lines plus one SUMMARY, for the run log.

    ADVISORY ONLY -- it never touches a return code: saturation is a
    quality reading, not a pass/fail."""
    rounds = scale_rounds(run_log)
    if not rounds:
        return ["%s: no SCALE ROUND markers parsed from %s"
                % (tag, run_log)]
    lines, lo, hi, overs, n_sat = [], [], [], 0, 0
    for cnt in sorted(rounds):
        r = rounds[cnt]
        a, b, o = sat_span(r["sat"])
        if a is not None:
            lo.append(a)
            hi.append(b)
            n_sat += 1
        overs += o
        lines.append(
            "%s count=%-6d %s db %6.1fs disch %6.1fs tune %7.1fs "
            "fold %7.1fs cost %-11s bumps %d  sat %s"
            % (tag, cnt, "    " if r["done"] else "PART",
               _scale_s(r["db_ms"]), _scale_s(r["disch_ms"]),
               _scale_s(r["tune_ms"]), _scale_s(r["fold_ms"]),
               "-" if r["cost"] is None else "{:,}".format(r["cost"]),
               r["bumps"], r["sat"] or "(no gauge fired)"))
    done = sum(1 for r in rounds.values() if r["done"])
    lines.append(
        "%s SUMMARY rounds %d (%d complete)  sat %s over %d round(s)"
        "  OVER %d  pre-fold %.1fs  fold %.1fs"
        % (tag, len(rounds), done,
           "-" if not lo else "min %.1f%% max %.1f%%" % (min(lo),
                                                         max(hi)),
           n_sat, overs,
           _scale_s(sum(r["db_ms"] + r["disch_ms"] + r["tune_ms"]
                        for r in rounds.values())),
           _scale_s(sum(r["fold_ms"] for r in rounds.values()))))
    return lines


def _scale_n(v):
    return "-" if v is None else "{:,}".format(v)


def _scale_delta(a, b):
    """b vs a as a signed percent; '-' when either side is missing."""
    if not a or b is None:
        return "-"
    return "%+.2f%%" % (100.0 * (b - a) / a)


def _scale_span(sat):
    a, b, o = sat_span(sat)
    return "-" if a is None else "%.0f-%.0f%%%s" % (a, b,
                                                    "!" if o else "")


def scale_ab_report(log_v1, log_v2, tag):
    """v1-vs-v2 per rule count.  Same DB, same corpus, same rule subset
    -- the ONLY difference is which tuner ran, so d_cost is a QUALITY
    reading (cost is exactly what the scale figure plots) and tune is
    the speed claim.  A round either arm left incomplete is marked PART
    and carries no verdict."""
    a, b = scale_rounds(log_v1), scale_rounds(log_v2)
    if not a or not b:
        return ["%s A/B: no comparison -- %s arm produced no rounds"
                % (tag, "v1" if not a else "v2")]
    out = ["%s A/B  count      |    cost v1 |    cost v2 | d_cost  |"
           "  tune v1 |  tune v2 | speedup |   sat v1 |   sat v2"
           % tag]
    for cnt in sorted(set(a) | set(b)):
        ra, rb = a.get(cnt, _SCALE_EMPTY), b.get(cnt, _SCALE_EMPTY)
        ok = ra["done"] and rb["done"]
        ta, tb = _scale_s(ra["tune_ms"]), _scale_s(rb["tune_ms"])
        out.append(
            "%s A/B %6d %-4s | %10s | %10s | %-7s | %7.1fs | %7.1fs |"
            " %7s | %8s | %8s"
            % (tag, cnt, "" if ok else "PART", _scale_n(ra["cost"]),
               _scale_n(rb["cost"]),
               _scale_delta(ra["cost"], rb["cost"]) if ok else "-",
               ta, tb, "%.2fx" % (ta / tb) if ok and ta and tb else "-",
               _scale_span(ra["sat"]), _scale_span(rb["sat"])))
    out.append("%s A/B NOTE: sat is min-max over ALL gauges;"
               " '!' = an ENFORCED gauge (Q_m/Q_c) over budget."
               "  A DRY sweep runs the dry shape (range2_bit 22,"
               " chunk_len 128), so these ratios do NOT transfer to"
               " production." % tag)
    return out


def run_leaf_scale_dlp(mode, ctx):
    """M102 Scale-DLP leaf: two sequential bora_cli scale_dlp sweeps,
    one per fixed corpus, the second running even if the first failed;
    dry passes dry=1 (22-bit range table, corpus left whole). Each log
    is packed into its any_server bundle even on a crash (partial
    rounds kept; 0 rounds leave the bundle untouched)."""
    counts = SCALE_DLP_COUNTS[mode]
    arg = ",".join(str(c) for c in counts)
    dry = "1" if mode == "dry" else "0"
    env = scale_env()
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
        # advisory telemetry, after the verdict so it cannot alter it
        for ln in scale_round_report(lg, tag):
            log(ln)
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


def run_leaf_scale_clamav(mode, ctx, arm=None):
    """M104 Scale-ClamAV leaf: two sequential bora_cli scale_clam
    sweeps (readelf then gdb), the second running even if the first
    failed; dry passes light=1 (dry chunk shape). Bundles pack in a
    finally, partial rounds kept.

    arm None = production: the bare subcommand, the canonical bundle
    the scale figure reads.  "v1"/"v2" = a tuner A/B arm, which takes
    its own subcommand, log tag and bundle -- so an A/B can never
    overwrite the figure's inputs, and (via arm_plan_dir on the Rust
    side) never shares a plan dir or DB cache with the other arm."""
    counts = SCALE_CLAM_COUNTS[mode]
    arg = ",".join(str(c) for c in counts)
    light = "1" if mode == "dry" else "0"
    sub = "scale_clam" if arm is None else "scale_clam_%s" % arm
    env = scale_env()
    rc = 0
    for idx, bundle, tag in SCALE_CLAM_RUNS:
        if arm is not None:
            bundle = bundle[:-len(".tgz")] + "_%s.tgz" % arm
            tag = "%s_%s" % (tag, arm)
        if aborted():        # see run_leaf_scale_dlp for why not `rc or`
            arc = _abort_leaf(ctx, "signal before %s" % tag)
            rc = rc or arc
            break
        lg = ctx.log_path(tag)
        try:
            rc_i = run_rust_example(
                ctx, "bora_cli",
                [sub, str(idx), arg, light], env,
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
        # advisory telemetry, after the verdict so it cannot alter it
        for ln in scale_round_report(lg, tag):
            log(ln)
        rc = rc or rc_i
    return ctx.finish(rc, b_fail_scan=False)


# The tuner arms an A/B sweep compares, in report order.
SCALE_AB_ARMS = ("v1", "v2")


def run_scale_ab():
    """Menu item: the DRY clam scale sweep once per tuner arm, then the
    comparison.  Writes only scale_data_*_v1/_v2.tgz, so the canonical
    bundles gen_scale_all.py reads are untouched.

    BOTH arms always run: a failed v1 must not suppress v2, or there is
    nothing to compare.  run_leaf_scale_clamav returns a LeafResult, so
    the verdict comes off .failed -- `rc or leaf(...)` would short
    circuit the second call the moment the first returned an object."""
    rc, logs = 0, {}
    for arm in SCALE_AB_ARMS:
        ctx = JobHandle("scale_clam_%s" % arm, "dry")
        ctx.note("mode=scale_clam A/B arm %s (dry counts %s)"
                 % (arm, SCALE_CLAM_COUNTS["dry"]))
        res = run_leaf_scale_clamav("dry", ctx, arm=arm)
        logs[arm] = {tag: ctx.log_path("%s_%s" % (tag, arm))
                     for _, _, tag in SCALE_CLAM_RUNS}
        _summary_line("%-4s   scale_ab arm=%s rc=%s wall=%ds "
                      "peak_rss=%.1fGB"
                      % ("FAIL" if res.failed else "OK", arm, res.rc,
                         int(res.wall_s), res.peak_rss_gb))
        if res.failed:
            rc = rc or (res.rc or 1)
    for _, _, tag in SCALE_CLAM_RUNS:
        for ln in scale_ab_report(logs["v1"][tag], logs["v2"][tag],
                                   tag):
            log(ln)
    log("scale_ab: per-round tables -> %s" % CURRENT_JOB_LOG)
    return rc


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
    "effective":  JobSpec("effective",  "Effectiveness", run_leaf_effective),
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
    """Emit one line to both the console (log()) and SUMMARY.log.
    NEVER raises: this is called from inside _watch_child and
    _stall_kill, and a full /tmp there killed the WATCHDOG THREAD --
    measured, a child outlived its 3 s wall cap by 12 s and counting.
    Losing a log line is survivable; losing the only thing that can
    bound a runaway prover is not."""
    try:
        log(line)
        os.makedirs(os.path.dirname(SUMMARY_LOG), exist_ok=True)
        with open(SUMMARY_LOG, "a") as f:
            f.write("[%s] %s\n" % (_ts(), line))
    except OSError:
        pass


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
            # Full leaves only, and only under the run lock: the wipe's
            # whole safety argument IS the single-instance invariant,
            # and requiring the lock also keeps the unit suite -- which
            # drives this with mode="full" and never locks -- off the
            # real data/cache (A2017).  Before JobHandle so its
            # LOGS_DIR snapshot sees the post-wipe state.
            if mode == "full" and _run_lock_fd is not None:
                for w in clear_db_cache():
                    _summary_line("       %s" % w)
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
    # APPENDED, never inserted (leaves 1-8 keep their menu numbers).
    # effective is ESTIMATED, not measured: gb None until its first
    # instrumented dry run replaces this row.
    ("effective",  "Effectiveness", 6.0,  None, ""),
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
    # clean sits at #5 BY REQUEST (2026-08-14), renumbering figs to #6.
    ("clean", "clean generated data (raw_data/*, pdf/*)"),
    ("figs", "generate list of figures"),
    # 69801 debug probes (2026-08-15): appended LAST so items 1-6 keep
    # their numbers.  Both arm the decider instrumentation and stop
    # after the main snark (no CyclePair phase).
    ("dna_debug", "dna DEBUG probes (small fold, FULL-WIDTH non-light "
                  "decider, ~1.5h)"),
    ("dna_debug_full", "dna DEBUG probes (FULL shape 328 steps, stops "
                       "after main snark, ~5h)"),
    # small_full_dlp (2026-08-17): appended LAST so items 1-8 keep
    # their numbers.  Deliberately NOT a JOB_SPECS leaf -- a leaf would
    # be reachable from `full_run --items all`, and this entry must
    # never alter a full_run.  It writes nothing into raw_data/.
    ("small_full_dlp", "small_full_dlp (ENTIRE dlp DB, ~5% corpus + "
                       "hard core, FOLD COST ONLY, ~8.5h/~230GB)"),
    # V101 (2026-08-17): the whole tuner test suite in ONE unattended
    # run.  Appended LAST so items 1-9 keep their numbers.  NOT a
    # JOB_SPECS leaf -- `full_run --items all` must never reach it,
    # it writes nothing into raw_data/.
    ("v101", "V101 tuner test suite (all tests, unattended, self-"
             "sizing to a 16 h budget; watch "
             "/tmp/bora/v101/V101_PROGRESS.txt, verdict + "
             "V101_BUNDLE.tgz beside it)"),
    # scale_ab (2026-08-20): appended LAST so items 1-10 keep their
    # numbers.  NOT a JOB_SPECS leaf -- `full_run --items all` must
    # never reach it -- and it writes only scale_data_*_v1/_v2.tgz,
    # so the bundles the scale figure reads are untouched.
    ("scale_ab", "scale_clam tuner A/B, v1 vs v2 (DRY sweep twice, "
                 "~15-30 min; own bundles, figure inputs untouched)"),
]

LEAF_CHOICES = [(k, "%s %s" % (name, _cost_tag(mins, gb, note)))
                 for k, name, mins, gb, note in DRY_COST]
_LEAF_KEYS = [k for k, _ in LEAF_CHOICES]     # canonical order (2.2)

# Full-run cost per leaf, MEASURED from the paper's production
# artifacts (ZkregPlusPaper .../raw_data, READ-ONLY; extracted
# 2026-08-14): (key, wall_hours, peak_rss_gb, note); None = never
# measured.  SOURCES: dlp/clam the part logs' ALL-JOBS trailers, dna
# its /usr/bin/time -v block (wall 5:22:56, maxrss 559,310,200 kB),
# zombie/reef the docs logs' per-policy sums (582 runs / 60 samples),
# scale the nested per-round trailers summed.  CAVEATS: dlp and clam
# run their two halves CONCURRENTLY -- the leaf wall is the slower
# part, but the box holds BOTH parts at once (dlp 262+260, clam
# 373+531 GB -> the 1 TB box).  dna's 533 GB is a true time -v tree
# peak; the dlp/clam/scale figures are in-log "RAM: N GB" step
# samples, which the 08-14 calibration showed under-report the tree
# peak by up to ~1.3x.  lkup/effective are the only rows the
# runner MEASURED itself rather than harvested: the 2026-08-20
# full_run on zkreglus-small (512 GB), SUMMARY.log wall 8385 s /
# 8555 s, peak_rss 70.8 GB on both.  The identical peak is
# expected, not a meter artifact -- each leaf builds the same
# three DBs (Mal/Dna/Dlp) and that build is the peak.
FULL_COST = [
    ("dlp",        119.2, 262,  " x2 parts"),
    ("dna",        5.4,   533,  ""),
    ("clam",       19.4,  531,  " x2 parts"),
    ("zombie",     5.2,   None, ""),
    ("reef",       5.2,   None, ""),
    ("lkup",       2.3,   71,   ""),
    ("scale_clam", 10.9,  139,  ""),
    ("scale_dlp",  1.3,   149,  ""),
    ("effective",  2.4,   71,   ""),
]


def _full_tag(hours, gb, note=""):
    """'[full ~5.4h, ~533GB]'; days past 48h; '[full: not measured]'
    when the leaf has no production artifact."""
    if hours is None:
        return "[full: not measured]"
    wall = ("~%sd" % _fmt_min(hours / 24.0) if hours >= 48
            else "~%sh" % _fmt_min(hours))
    if gb is None:
        return "[full %s%s]" % (wall, note)
    return "[full %s%s, ~%dGB]" % (wall, note, gb)


def full_total():
    """Rollup of the measured full leaves: wall SUMS (they run in
    sequence), RSS is the MAX.  Returns (hours, gb, n_unmeasured)."""
    hrs = sum(c[1] for c in FULL_COST if c[1] is not None)
    gb = max(c[2] for c in FULL_COST if c[2] is not None)
    n_un = sum(1 for c in FULL_COST if c[1] is None)
    return hrs, gb, n_un


FULL_LEAF_CHOICES = [
    (k, "%s %s" % (name, _full_tag(h, gb, fnote)))
    for (k, name, _m, _g, _n), (_fk, h, gb, fnote)
    in zip(DRY_COST, FULL_COST)]


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


NO_ITEM_TOPS = ("small", "figs", "small_full_snark", "clean",
                "dna_debug", "dna_debug_full", "small_full_dlp",
                "v101", "scale_ab")


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
    # dry shows the DRY measurements, full the production figures
    # harvested from the paper's raw_data (see FULL_COST's caveats).
    choices = FULL_LEAF_CHOICES if top == "full_run" else LEAF_CHOICES
    for i, (_, label) in enumerate(choices, 1):
        print("  (%d) %s" % (i, label))
    if top == "dry_run":
        print("  (A) All %s" % _cost_tag(*dry_total(), lead=""))
    else:
        hrs, gb, n_un = full_total()
        print("  (A) All [measured ~%sd, ~%dGB peak; %d leaves "
              "unmeasured]" % (_fmt_min(hrs / 24.0), gb, n_un))


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
# Layer A -- small_full_dlp (last menu item: DLP fold cost on a small
# corpus with the FULL database)
# =====================================================================

# Isolation from full_run, by construction (2026-08-17):
#   * not in JOB_SPECS/LEAF_CHOICES/DRY_COST, so `--items all` and
#     `--items dlp` cannot reach it;
#   * SMALL_DLP's own db_cache_dir ("dlp_small_neo"), so the tuned
#     ladder.json / warmstart_caps.json never land where full_dlp
#     reads them (T308: a shared warmstart poisons the next cold
#     start);
#   * no safe_pack_dump / place_raw_data call, so raw_data/ -- and the
#     paper's full_dlp.part*.tgz in particular -- is untouched.
#
# argv, positionally identical to full_dlp's 8-arg tail:
#   perc_db=100      the ENTIRE DLP database (the point: real ladder)
#   perc_samples=100 the corpus list IS already the ~5% sample, so
#                    sampling again would re-open the missing-top-rung
#                    hole SMALL_DLP exists to close
#   num_circs=4      k_max=4, production's 4-rung ladder
#   num_jobs=8       matches production; drop to 4 if fold RAM bites
#   numa_num=1 part_id=0   one process on a 1-socket box
#   dry=0            full width: chunk_len 64, range2_bit 25
#   ladder_only=0    fold for real
SMALL_DLP_JOBS = "8"
SMALL_DLP_ARGS = ["small_full_dlp", "100", "100", "4", SMALL_DLP_JOBS,
                  "1", "0", "0", "0"]


def run_small_full_dlp():
    """Last menu item: fold the ~5%-plus-hard-core DLP corpus against
    the entire DLP database and stop before the decider, to price fold
    cost per step at production circuit width."""
    ctx = JobHandle("small_dlp", "full")
    ctx.note("mode=small_full_dlp (single proc; entire DB, pre-cut "
             "corpus, b_folding_only=true -> no snark)")
    run_log = ctx.log_path("run")
    rc = run_rust_example(ctx, "bora_cli", SMALL_DLP_ARGS, neo_env())
    res = ctx.finish(rc)
    # After finish(): the trailer must stay invisible to the fail scan,
    # and res is where peak_rss_gb / wall_s become final.
    append_run_trailer(run_log, res)
    _summary_line("%-4s   small_full_dlp rc=%s wall=%ds "
                  "peak_rss=%.1fGB idle=%ds/%ds" % (
                      "FAIL" if res.failed else "OK", res.rc,
                      int(res.wall_s), res.peak_rss_gb,
                      int(res.peak_idle_s), STALL_S))
    log("small_full_dlp: peak RSS and wall clock -> %s"
        % CURRENT_JOB_LOG)
    if res.failed:
        log("small_full_dlp: FAILED -- triage: %s" % res.triage_tgz)
        return 1
    log("small_full_dlp: ladder + fold stats -> %s" % run_log)
    return 0




# =====================================================================
# Layer A -- V101 tuner test suite (last menu item: every V101 test in
# one unattended run, self-sizing against a fixed run budget)
# =====================================================================
#
# Isolation from full_run, by construction (2026-08-17):
#   * not in JOB_SPECS/LEAF_CHOICES/DRY_COST, so `--items all` cannot
#     reach it;
#   * the v2 arm runs under its OWN spec name ("clam_v2") and db cache
#     ("clam_v2_neo"), so neither arm can wipe the other's plan dir
#     (bora_data_driver.rs reset_part_dir);
#   * no safe_pack_dump / place_raw_data call, so raw_data/ -- and the
#     paper's full_clam.part*.tgz in particular -- is untouched.
#
# Everything the suite learns lands in FOUR places, all stable paths:
#   /tmp/bora/v101/<ts>/detail.log   every number + the line it came
#                                    from (the debug artifact)
#   /tmp/bora/v101/V101_PROGRESS.txt live status, rewritten at every
#                                    step START and END -- `cat` it
#                                    any time to see where the run is
#   /tmp/bora/v101/V101_VERDICT.txt  the succinct final report
#   /tmp/bora/v101/V101_BUNDLE.tgz   downloadable artifact: the whole
#                                    run dir, repacked after ANY
#                                    failing step and again at the end

V101_ROOT = "/tmp/bora/v101"
V101_VERDICT = os.path.join(V101_ROOT, "V101_VERDICT.txt")
V101_PROGRESS = os.path.join(V101_ROOT, "V101_PROGRESS.txt")
V101_BUNDLE = os.path.join(V101_ROOT, "V101_BUNDLE.tgz")

# Per-file truncation inside the bundle: head + tail, with a marker
# between.  A tuner run.log reaches hundreds of MB and the bundle has
# to stay small enough to scp; the head holds the seed/config lines
# and the tail holds the failure.
V101_BUNDLE_KEEP_MB = 20.0     # files at or under this go in whole
V101_BUNDLE_HEAD_MB = 5.0
V101_BUNDLE_TAIL_MB = 15.0

# neo_env() scrubs every ZKR_*, so these must be re-added AFTER it
# (same mechanism as DNA_DEBUG_ENV).
V101_SEED_ENV = {"ZKR_V101_SEED_ONLY": "1"}
V101_METER_ENV = {"ZKR_METER_T9901": "1"}

# How long the suite may RUN, as a duration from launch.  A DURATION,
# not a wall-clock deadline: with a fixed finish time (this was "the
# next local 12:00"), every hour of slipped start silently bought a
# smaller A/B vehicle, and a launch after the hour had passed got a
# whole extra day.  A duration always grants the same budget.
# Override for a short run with ZKR_V101_HOURS=2.
# Enforced twice: a step is not STARTED without room, and every
# step's wall cap is clamped to the time left (run_v101), so a fixed
# cap_s -- dec_big's 5 h in particular -- cannot overrun the budget.
V101_RUN_HOURS = 16.0

# Seconds the picker must LEAVE on the clock for the three decider
# steps that follow the A/B.  dec_v1/dec_v2 measured 7m/8m locally;
# dec_big is priced at its own 5 h cap.  Without this reserve the
# picker spends the entire clock on the A/B and dec_big -- the only
# production-width fold+prove, i.e. R1's strongest evidence -- is
# skipped for "no time".  Unused reserve is not wasted: a fast A/B
# simply hands its slack to dec_big, whose cap is per-step.
V101_DEC_RESERVE_S = 5.5 * 3600

# Cost-model priors, in the units of the model.  Steps 4 and 5 REPLACE
# every one of these with a measurement before the picker runs; they
# exist only so a suite that skipped those steps can still size itself.
#   t_db      s          DB build, corpus-independent
#   r_disch   s per MB   discharge_for_tuning
#   r_probe   s per padded chunk, one probe round (measured anchor:
#             109 min / 6549 chunks on the reference run)
#   k5, km    multiples of one probe round for the v5 walk and the
#             ZKR_METER_T9901 walk; both are SERIAL over words at
#             n_circs=1 against the probe's 8-thread ~3-walk pass,
#             so 1/(3/8) = 2.67 is the derivation, 2.5 the prior
#   r_seed    s per MB   the estimator's own DFA walk
V101_PRIORS = dict(t_db=180.0, r_disch=2.35, r_probe=1.0,
                    k5=2.5, km=2.5, r_seed=0.4)

# v1 = convergence rounds + post-convergence tightening passes; v2 = 1
# pass by design.  The 12.47 h reference run converged at iter 4 (= 5
# rounds) and its four binary searches (zkp_driver.rs:1207,:1249 and
# their igc twins) cost ~7-10 probes, so 10 was the OPTIMISTIC end of
# the range and an under-estimate here becomes a TIMEOUT on ab_v1.
V101_V1_PASSES = 13
V101_V2_PASSES = 1

# C3 (capacity_probe_collect_top) is on the v2 path ONLY:
# bora_data_driver.rs:2248 probes at the widest rung, while v1's
# zkp_driver.rs:1139 still calls capacity_probe_par -> plan_nd_advice
# and walks 2-5 rungs per word.  `calib` is a v2 step, so the r_probe
# it measures is the C3 rate; spending that same rate on v1's passes
# under-prices the v1 arm by this factor and hands ab_v1 a cap it
# cannot make.  MEASURED 2026-08-17 on one vehicle, both ways:
# probe 62,902 ms -> 34,806 ms = 1.81x.  Superseded at run time by
# the calib_v1 step, which measures the v1 rate directly; this is
# only the fallback for a suite where that step did not run.
V101_V1_PROBE_MULT = 1.81

# If calib_v1 does not return, price the v1 arm from the v2 arm rate
# rather than from the analytic model.  Measured shape: r_v1_arm /
# r_v2_arm ~ 1.87 (v1 pays ~13 non-C3 passes against v2's 1 C3 pass,
# and both pay the same two walks).  2.0 is the conservative round
# number.  The analytic fallback over-priced v1 by 3.43x, which
# collapsed the vehicle from perc 20 to perc 5 and idled 6h40m of
# budget -- schedule-safe, but the worst scientific outcome available.
V101_V1_ARM_RATIO = 2.0

# (perc_samples, files, MB, padded chunks, derived lkup share) for the
# deterministic subsets of the clam corpus at chunk_len 4096.  Measured
# 2026-08-17 by replaying subset()/fixed_perm() over the 8 binexec
# manifests.  DESCENDING: the picker takes the first fit.
#
# Rows 25/30/40 added 2026-08-17 for the 16 h clock.  Same replay,
# re-validated first: it reproduces files and MB EXACTLY on all three
# pre-existing anchors (25/12.3, 242/112.2, 1209/765.5), and its raw
# ceil(size/131072) chunk count runs a flat 5.2-5.5% under the logged
# padded count, so chunks here are replay x 1.0555 (which returns
# 989 at perc 20 and 111 vs the logged 110 at perc 2).
#
# `share` is INFORMATIONAL -- it never enters v101_cost (design 11.1a:
# the derived lkup share does not touch per-chunk probe cost, only
# ladder construction and RAM).  It falls as the vehicle grows, so the
# new rows are strictly CHEAPER in RAM than perc 20, not dearer.
# Production's own share is 129; perc 20 (110) remains the closest.
V101_VEHICLES = [
    (40, 484, 272.0, 2357, 45),
    (30, 363, 175.1, 1539, 71),
    (25, 303, 146.1, 1287, 85),
    (20, 242, 112.2, 989, 110),
    (15, 182, 91.6, 800, 135),
    (10, 121, 48.5, 435, 255),
    (7, 85, 39.6, 350, 313),
    (5, 61, 31.3, 275, 395),
    (3, 37, 20.2, 179, 611),
    (2, 25, 12.3, 110, 1011),
]

# The A/B steps' wall cap, as a multiple of the modelled cost.  1.3
# was too tight: the reference run's rounds GREW 113 -> 154 min
# (+36%) as caps grew, and a subset-calibrated model cannot see that.
V101_AB_CAP_MULT = 1.6

# Extra margin on top of the caps.  NOTE this multiplies the CAPS, not
# the model estimate -- the picker's promise and the caps it then
# hands out have to be the same promise.  The old form compared the
# model estimate to 0.85 x room while handing out caps of 1.3 x the
# estimate, i.e. 10% MORE than the whole room, which quietly ate the
# decider reserve.
V101_MODEL_SLACK = 0.95

# F1b.  The seed is a SOUND UPPER BOUND (bora_data_driver.rs:2063) and
# M3 tightens it afterwards, so "above the proven max" is its design.
# The dry leaf measured seed 43 -> tightened 7 = 6.1x on a HEALTHY
# run, so the advisory line sits above that; the hard stop is the
# spec's own RAM alarm (impl spec 15, R-2).
# The ONE place the green sentence is spelled.  run_v101's exit code
# is derived from it, so the rc and the text can never disagree --
# they did: `bad` counted only step FAIL/TIMEOUT, so a run whose every
# step was OK but whose F1 read FAIL (the PRIMARY unsoundness finding)
# exited 0 under a verdict that said NOT shippable.
V101_GREEN_MARK = "-> stage 3 complete; propose the commit."
V101_SEED_LOOSE_X = 8.0
V101_SEED_RAM_ALARM = 1500000
V101_QM_PROVEN_MAX = 36860


@dataclass
class V101Step:
    """One row of the suite.  `parse` pulls that step's numbers out of
    its own log; `needs_v2` steps are skipped when the binary predates
    stage 2."""
    key: str
    label: str
    argv: list          # bora_cli argv, or [] for a cargo step
    env: dict           # ZKR_* re-added AFTER neo_env()
    cap_s: int          # per-step wall cap; 0 = use the deadline
    needs_v2: bool
    kind: str = "bora"  # "bora" | "cargo" | "calc"
    # D5 guards, dec_big only.  min_avail_gb is a PRECONDITION checked
    # at launch; max_rss_gb is a live ceiling the watchdog enforces.
    min_avail_gb: float = 0.0
    max_rss_gb: float = 0.0


@dataclass
class V101Res:
    key: str
    status: str = "PENDING"   # PENDING RUNNING OK FAIL TIMEOUT SKIP
    why: str = ""
    wall_s: float = 0.0
    rss_gb: float = 0.0
    nums: dict = None         # parsed numbers, verbatim into detail.log
    tgz: str = ""             # this step's own JobHandle triage bundle
    t_start: float = 0.0      # epoch; 0 until the step is spawned
    cap_s: int = 0            # the wall cap this step actually got


def _v101_now():
    return time.time()


def _v101_mem_avail_gb():
    """MemAvailable in GB, 0.0 if unreadable.  Used as a PRECONDITION
    for dec_big: a production-width clam decider is priced at hundreds
    of GB (small_full_snark measured 433 GiB and aborted mid-decider
    once at 512 GB), so it must not start on a box that cannot hold
    it."""
    try:
        with open("/proc/meminfo") as f:
            for line in f:
                if line.startswith("MemAvailable:"):
                    return int(line.split()[1]) / (1024.0 * 1024.0)
    except (OSError, ValueError, IndexError):
        pass
    return 0.0


def _v101_run_seconds():
    """The run budget in seconds.  ZKR_V101_HOURS overrides the
    default; a malformed or non-positive value falls back to it
    rather than running forever or finishing instantly."""
    try:
        h = float(os.environ.get("ZKR_V101_HOURS", ""))
    except ValueError:
        h = 0.0
    return (h if h > 0 else V101_RUN_HOURS) * 3600.0


def _v101_deadline(t0):
    """Absolute epoch the suite must be finished by = start + budget.
    Kept absolute so every 'time left' and every cap clamp downstream
    is unchanged; only where the number COMES FROM has changed."""
    return t0 + _v101_run_seconds()


def _v101_model_line(model):
    """The cost model with every coefficient tagged MEASURED or left
    as a prior.  Untagged, the line reads as if all five were
    measured -- and on the four verdicts already on disk, none of
    them was."""
    seen = model.get("_measured") or set()

    def tag(k):
        return "*" if k in seen else ""
    parts = ["t_db=%.0fs%s" % (model["t_db"], tag("t_db")),
             "r_disch=%.2fs/MB%s" % (model["r_disch"],
                                      tag("r_disch")),
             "r_probe=%.3fs/chunk%s" % (model["r_probe"],
                                         tag("r_probe")),
             "k5=%.2f%s" % (model["k5"], tag("k5")),
             "km=%.2f%s" % (model["km"], tag("km"))]
    for k in ("r_v2_arm", "r_v1_arm"):
        if model.get(k):
            parts.append("%s=%.3fs/chunk*" % (k, model[k]))
    return ("model  " + " ".join(parts)
            + "   (* = measured this run, rest = prior)")


def _v101_room(left):
    """Seconds a step may use without crossing the hard deadline; 180 s
    are held back for the verdict and the bundle."""
    return int(max(60, left - 180))


def _v101_cap(cap_s, left):
    """The wall cap a step actually gets.  A fixed cap_s -- dec_big's
    5 h in particular -- is CLAMPED to the room left, so no step can
    run through the clock; a step with no cap of its own takes the
    room."""
    room = _v101_room(left)
    return min(cap_s, room) if cap_s else room


def _v101_hm(s):
    """4271.0 -> '1h11m'; negative and None print as '--'."""
    if s is None or s < 0:
        return "--"
    return "%dh%02dm" % (int(s // 3600), int((s % 3600) // 60))


def _v101_grep(path, pat, group=0, last=True):
    """Last (or first) regex hit in a log.  Returns (value, rawline)
    so the number and the line it came from both reach detail.log --
    the suite never prints a number it cannot source."""
    rx = re.compile(pat)
    hit = None
    try:
        with open(path, errors="replace") as f:
            for line in f:
                m = rx.search(line)
                if m:
                    hit = (m.group(group), line.rstrip())
                    if not last:
                        break
    except OSError:
        return (None, "")
    return hit if hit else (None, "")


def _v101_int(path, pat):
    v, raw = _v101_grep(path, pat, 1)
    try:
        return (int(v.replace(",", "")), raw)
    except (TypeError, ValueError):
        return (None, raw)


def v101_cost(model, veh, passes):
    """Seconds for ONE arm on `veh` = (perc, files, mb, chunks, share).
    setup + N probe rounds + the v5 walk + the meter walk.  Both walks
    are paid by BOTH arms -- that is I5, and it is why the model has
    k5 and km at all."""
    _p, _f, mb, chunks, _sh = veh
    v1 = passes != V101_V2_PASSES
    setup = model["t_db"] + model["r_disch"] * mb
    # PREFERRED: the arm's own end-to-end rate, measured by calib /
    # calib_v1 on the perc-2 vehicle.  One number that already
    # contains the probe rate, the pass count, the tightening passes
    # and both walks -- so none of them has to be modelled, and the
    # v1/v2 asymmetry that C3 introduced cannot be mis-applied.
    arm = model.get("r_v1_arm" if v1 else "r_v2_arm")
    if arm is None and v1 and model.get("r_v2_arm"):
        # calib_v1 did not return, but calib did: scale rather than
        # fall all the way back to the analytic model.
        arm = model["r_v2_arm"] * V101_V1_ARM_RATIO
    if arm:
        return setup + arm * chunks
    # FALLBACK, only if that step did not run: the analytic model.
    # v1 pays the non-C3 probe rate (C3 is v2-only).
    rate = model["r_probe"] * (V101_V1_PROBE_MULT if v1 else 1.0)
    walks = (model["k5"] + model["km"]) * model["r_probe"] * chunks
    seed = 0.0 if v1 else model["r_seed"] * mb
    return setup + seed + passes * rate * chunks + walks


def v101_pick(model, remain_s, log):
    """Largest vehicle whose A/B pair fits `remain_s` -- measured
    against the CAPS the two steps will actually be given, not against
    the bare model estimate.  Returns (veh, predicted_s) or (None,
    None)."""
    budget = remain_s * V101_MODEL_SLACK
    for veh in V101_VEHICLES:
        c1 = v101_cost(model, veh, V101_V1_PASSES)
        c2 = v101_cost(model, veh, V101_V2_PASSES)
        need = (c1 + c2) * V101_AB_CAP_MULT
        log("picker: perc=%-3d chunks=%-5d v1=%s v2=%s pair=%s "
            "caps=%s budget=%s %s"
            % (veh[0], veh[3], _v101_hm(c1), _v101_hm(c2),
               _v101_hm(c1 + c2), _v101_hm(need), _v101_hm(budget),
               "TAKE" if need <= budget else "skip"))
        if need <= budget:
            return veh, c1 + c2
    return None, None


def v101_argv(sub, perc_db, perc_samples, circs, jobs, numa, part,
               dry, ladder_only):
    """bora_cli's 8-arg tail.  numa_num=1/part_id=0 is load-bearing on
    every tuner step: it makes role.b_proves TRUE, hence
    b_light_test FALSE (bora_data_driver apply_spec_config), i.e.
    production's PROVING part at full width.  Production's part 0 runs
    light-test ON; a tuner baseline must not reproduce that."""
    return [sub, str(perc_db), str(perc_samples), str(circs),
            str(jobs), str(numa), str(part), dry, ladder_only]


def v101_steps():
    """The suite, in execution order.  Steps 1-5 are fixed and cheap;
    they MEASURE the cost model.  6-7 are the A/B, sized by the picker.
    9-11 are the decider checks (D5) -- the only steps that fold and
    prove, and so the only ones that can see R1's four residual axes."""
    return [
        # 3600, not 1800: the wall cap was INERT until the D1 fix,
        # so this number had never actually bounded anything.  A cold
        # release build of this workspace can exceed 30 min.
        V101Step("build", "cargo build --release + capability probe",
                 [], {}, 3600, False, kind="cargo"),
        # 3600, matching `build`: this step runs THREE cargo filters
        # off one budget and the first of them may recompile
        # zkregplus in cfg(test) -- a compile `build` does not do.
        V101Step("units", "test_v101_ / m104 parse / fingerprint_",
                 [], {}, 3600, True, kind="cargo"),
        V101Step("smoke_v1", "dry clam leaf, v1 arm",
                 v101_argv("full_clam_v1", 0.5, 0.1, 2, 2, 1, 0,
                           "1", "1"),
                 {}, 900, False),
        V101Step("smoke_v2", "dry clam leaf, v2 arm",
                 v101_argv("full_clam_v2", 0.5, 0.1, 2, 2, 1, 0,
                           "1", "1"), {}, 900, True),
        # 9000, not 5400: this step carries F1, the primary
        # falsifier, and at 5400 it had the tightest headroom in the
        # suite (2.25x over a 40 min local wall, vs 4-20x elsewhere).
        # A box 2.25x slower lost F1 to a TIMEOUT.
        V101Step("seed", "F1: full-corpus seed-only dry fire",
                 v101_argv("full_clam_v2", 100, 100, 2, 8, 1, 0,
                           "0", "1"), V101_SEED_ENV, 9000, True),
        V101Step("calib", "v2 receipt @ perc 2 (+ calibrates k5/km)",
                 v101_argv("full_clam_v2", 100, 2, 2, 1, 1, 0,
                           "0", "1"), V101_METER_ENV, 3600, True),
        # The v1 arm does NOT get C3 (zkp_driver.rs:1139 still walks
        # 2-5 rungs per word), so its per-chunk rate cannot be read
        # off a v2 step.  Measuring one whole v1 tune at perc 2 costs
        # ~25 min out of hours of margin and replaces BOTH guesses --
        # the probe rate and the pass count -- with one number.
        V101Step("calib_v1", "v1 receipt @ perc 2 (measures the v1 "
                 "arm rate; C3 is v2-only)",
                 v101_argv("full_clam_v1", 100, 2, 2, 1, 1, 0,
                           "0", "1"), V101_METER_ENV, 5400, False),
        V101Step("pick", "choose the A/B vehicle", [], {}, 0, False,
                 kind="calc"),
        V101Step("ab_v1", "A/B v1 arm", [], V101_METER_ENV, 0, False),
        V101Step("ab_v2", "A/B v2 arm", [], V101_METER_ENV, 0, True),
        V101Step("dec_v1", "decider check, v1 ladder (dry leaf, FOLD"
                 " + Groth16 + verify)",
                 v101_argv("full_clam_v1", 0.5, 0.1, 2, 2, 1, 0,
                           "1", "0"),
                 {}, 3600, False),
        V101Step("dec_v2", "decider check, v2 ladder (dry leaf, FOLD"
                 " + Groth16 + verify)",
                 v101_argv("full_clam_v2", 0.5, 0.1, 2, 2, 1, 0,
                           "1", "0"), {}, 3600, True),
        V101Step("dec_big", "decider @ PRODUCTION width, perc 2"
                 " (opportunistic; RAM-guarded)",
                 v101_argv("full_clam_v2", 100, 2, 2, 1, 1, 0,
                           "0", "0"), {}, 18000, True,
                 min_avail_gb=460.0, max_rss_gb=460.0),
    ]


def v101_parse(key, path, res):
    """Pull this step's numbers out of its own log.  Every entry keeps
    the RAW LINE beside the value so detail.log can show where each
    number came from -- the suite never prints an unsourced number."""
    n = {}
    def take(name, pat, cast=int):
        v, raw = _v101_grep(path, pat, 1)
        if v is not None:
            try:
                n[name] = cast(v.replace(",", ""))
                n[name + "@"] = raw
            except ValueError:
                pass
    if key == "units":
        # Independent content for R5.  Each of the three cargo
        # filters prints one "test result: ok." into the merged log,
        # so 3 is the healthy count; anything less means a filter
        # failed or never ran.
        n["units_oks"] = _v101_count(path, r"test result: ok\.")
    if key in ("seed",):
        take("seed_cs", r"V2 QM SEED: cs=(\d+)")
        take("seed_igc", r"V2 QM SEED: cs=\d+ igc=(\d+)")
        take("mid_hits", r"mid_hits=(\d+)")
        take("skipped", r"skipped=(\d+)")
        # Printed since :2363 and never read.  Without it F1 cannot
        # tell a 36,860 taken over the whole 1209-word corpus from one
        # taken over a truncated set -- same number, different claim.
        take("seed_words", r"V2 QM SEED:.* words=(\d+)")
        take("seed_ms", r"V2 PHASE seed ms=(\d+)")
        take("db_ms", r"build DB\. (\d+) ms")
        # bora_data_driver.rs:2370 -- the ONE panic that is by design
        # on this step.  Without it, any crash after the seed line was
        # being forgiven as "the expected panic".
        n["seed_marker"] = _v101_count(
            path, r"V101 SEED-ONLY DRY FIRE")
    if key in ("calib", "ab_v2", "smoke_v2", "dec_v2", "dec_big"):
        take("v2_iters", r"V2 CONVERGED @iter (\d+)")
        take("qm_real", r"V2 CONVERGED @iter \d+: qm_real (\d+)")
        take("qm_real_igc", r"V2 CONVERGED @iter \d+: qm_real \d+/(\d+)")
        take("probe_ms", r"V2 PHASE probe ms=(\d+)")
        take("v5_ms", r"V2 PHASE v5 ms=(\d+)")
        take("seed_ms", r"V2 PHASE seed ms=(\d+)")
        # A bump round is emitted in TWO shapes (bora_data_driver.rs
        # :2265 BUILD bump, :2318 "N of M words failed ... bumped").
        # The old regex saw only :2318, so a run that bumped at build
        # time reported bumps=0 -- observed live 2026-08-17, where the
        # log carried "v2 iter 0: BUILD bump" beside "bumps=0".  Note
        # :2306 ("subset clean, promoting") is a ROUND but NOT a bump.
        n["v2_bumps"] = _v101_count(
            path, r"v2 iter \d+: (BUILD bump|\d+ of \d+ words)")
        # The one bump M2 is supposed to make impossible: the qm_real
        # seed under-capping.  Any other bump (dfa, comp_sig) is
        # tolerated once; this one is not tolerated at all.
        n["v2_qm_bumps"] = _v101_count(
            path, r"v2 iter \d+:.*dis_adv::neo_qm_real")
    if key in ("ab_v1", "smoke_v1", "dec_v1", "calib_v1"):
        take("v1_iters", r"determine_config_non_aggr CONVERGED @iter (\d+)")
        n["v1_bumps"] = _v101_count(path,
                                     r"determine_config_non_aggr iter \d+:")
    # gauges + the meter, wherever they appear
    take("meter_demand_cs", r"qm_real max cs=(\d+)/")
    take("meter_demand_igc", r"igc=(\d+)/\d+ \(demand/cap_seen\)")
    take("shipped_qm", r"vs shipped qm_real_rows=(\d+)/")
    take("caperr_units", r"caperr_units=(\d+)")
    # The decider's real self-verify markers.  foldpot does not abort
    # on a verify failure (consts.rs:67-77), so these counters ARE the
    # whole gate, and every token below is quoted from the emit site
    # rather than from a healthy log:
    #   batch_proc.rs:800,1025,1149  ->  if ok {"PASS"} else {"REJECT"}
    # TWICE BURNED HERE.  The first version grepped "VERIFY_FAILS=",
    # a line that does not exist.  The second grepped "verdict=FAIL",
    # a token that does not exist either -- the failure word is
    # REJECT.  A failure regex CANNOT be validated against a healthy
    # log, which is why both survived review; validate it against the
    # Rust emit site.
    n["verify_pass"] = _v101_count(path,
                                    r"VERIFY-FLAGS.*verdict=PASS")
    n["verify_fail"] = _v101_count(path,
                                    r"VERIFY-FLAGS.*verdict=REJECT")
    # A healthy run emits exactly THREE [final] markers -- batch1,
    # batch2 (the Groth16 decider) and ind -- measured on both arms
    # 2026-08-17.  Counting PASS markers alone is not enough: batch1
    # failing early-returns and simply OMITS the batch2 line
    # (batch_proc.rs:1032-1041), so a missing marker is as much a
    # failure as a REJECTed one.
    n["verify_final"] = _v101_count(
        path, r"VERIFY-FLAGS \w+\[final\].*verdict=PASS")
    n["verify_snark"] = _v101_count(
        path, r"VERIFY-FLAGS batch2\[final\].*verdict=PASS")
    res.nums = n
    return n


def _v101_count(path, pat):
    """Occurrences of `pat`, or None if the log could not be read at
    all.  Returning 0 there was fail-OPEN: a truncated or missing log
    made every bump counter read "zero bumps" and F3a/F3b PASS on
    evidence that was never produced."""
    rx = re.compile(pat)
    c = 0
    try:
        with open(path, errors="replace") as f:
            for line in f:
                if rx.search(line):
                    c += 1
    except OSError:
        return None
    return c


def _v101_keep(run_dir, key, ctx_log):
    """Copy this step's artifacts out BEFORE the next step's
    reset_part_dir wipes the plan dir.  Both A/B arms have their own
    plan dir (spec name clam_v1 / clam_v2 -- the BARE `full_clam` is
    production and keeps `clam`), so this is belt-and-braces -- but a
    lost meter.json is a lost A/B, so it stays."""
    dst = os.path.join(run_dir, key)
    os.makedirs(dst, exist_ok=True)
    for pd in ("/tmp/bora/clam_v1_neo_p0",
               "/tmp/bora/clam_v2_neo_p0"):
        for name in ("ladder.json", "meter.json"):
            src = os.path.join(pd, name)
            if os.path.exists(src):
                tag = "v2_" if "clam_v2" in pd else ""
                try:
                    shutil.copy2(src, os.path.join(dst, tag + name))
                except OSError:
                    pass
    if ctx_log and os.path.exists(ctx_log):
        try:
            shutil.copy2(ctx_log, os.path.join(dst, "run.log"))
        except OSError:
            pass
    return dst


def _v101_step_rows(results, now=None):
    """(key, status, wall, rss, note) per step.  ONE renderer, shared
    by the progress file and the verdict, so the two cannot disagree.
    A RUNNING step reports its elapsed time, not a zero."""
    now = _v101_now() if now is None else now
    out = []
    for k, r in results.items():
        wall = r.wall_s
        # A step that has not run has no numbers; _v101_headline would
        # render them as "conv@None bumps=None", which reads like a
        # measurement that came back empty rather than one not taken.
        note = r.why if r.status == "PENDING" \
            else (r.why or _v101_headline(k, r))
        if r.status == "RUNNING" and r.t_start:
            wall = now - r.t_start
            note = "cap %s, kill at %s" % (
                _v101_hm(r.cap_s),
                time.strftime("%H:%M",
                              time.localtime(r.t_start + r.cap_s)))
        out.append((k, r.status, wall, r.rss_gb, note or ""))
    return out


def v101_progress_text(t0, deadline, run_dir, results, veh, model):
    """Live status, renderable at ANY moment -- including mid-step.
    This is what `cat /tmp/bora/v101/V101_PROGRESS.txt` shows."""
    now = _v101_now()
    L = []
    A = L.append
    A("=" * 66)
    A("V101 SUITE PROGRESS  %s" % time.strftime("%Y-%m-%d %H:%M:%S"))
    settled = sum(1 for r in results.values()
                  if r.status not in ("PENDING", "RUNNING"))
    A("elapsed %s of %s budget   left %s   finish by %s   "
      "%d/%d settled"
      % (_v101_hm(now - t0), _v101_hm(_v101_run_seconds()),
         _v101_hm(deadline - now),
         time.strftime("%H:%M", time.localtime(deadline)),
         settled, len(results)))
    if veh:
        A("vehicle perc_samples=%d  %d files  %.1fMB  %d chunks  "
          "share %d (production 129)"
          % (veh[0], veh[1], veh[2], veh[3], veh[4]))
    else:
        A("vehicle not chosen yet (picker runs after calib)")
    A(_v101_model_line(model))
    A("")
    A("STEP        STATUS     WALL    RSS  NOTE")
    for k, status, wall, rss, note in _v101_step_rows(results, now):
        A("  %-10s %-8s %7s %5.1fGB  %s"
          % (k, status, _v101_hm(wall), rss, note[:42]))
    A("")
    bad = [k for k, r in results.items()
           if r.status in ("FAIL", "TIMEOUT")]
    # "FAILURES" would over-claim: this counts STATUSES, and a step
    # can be OK while a falsifier it feeds later fails.
    A("FAILED STEPS SO FAR: %s"
      % (", ".join(bad) if bad else "none"))
    if bad:
        A("  bundle (repacked after each failure): %s" % V101_BUNDLE)
    A("detail: %s/detail.log" % run_dir)
    A("=" * 66)
    return "\n".join(L)


def _v101_write_progress(run_dir, text):
    """tmp + rename, so a `cat` racing the writer never sees a
    half-written file."""
    path = os.path.join(run_dir, "progress.txt")
    tmp = path + ".tmp"
    try:
        with open(tmp, "w") as f:
            f.write(text + "\n")
        os.rename(tmp, path)
        _atomic_symlink(path, V101_PROGRESS)
    except OSError:
        pass
    return path


def _v101_tar_add(t, path, arcname, stage):
    """Add one file, TRUNCATED to head + tail if it is over
    V101_BUNDLE_KEEP_MB.  A tuner run.log reaches hundreds of MB; the
    head carries the seed/config lines and the tail the failure, and
    the bundle has to stay small enough to scp."""
    try:
        sz = os.path.getsize(path)
    except OSError:
        return
    head = int(V101_BUNDLE_HEAD_MB * 1e6)
    tail = int(V101_BUNDLE_TAIL_MB * 1e6)
    # Add whole unless the file is genuinely bigger than head+tail.
    # The shipped constants leave exactly ONE byte of margin at the
    # threshold; testing against head+tail instead of against KEEP
    # removes the edge no matter how the three are later retuned.  A
    # file that is over the limit but under head+tail would otherwise
    # "drop" a negative count and seek backwards into its own head.
    if sz <= max(V101_BUNDLE_KEEP_MB * 1e6, head + tail):
        t.add(path, arcname=arcname)
        return
    cut = os.path.join(stage, arcname.replace(os.sep, "_") + ".cut")
    try:
        with open(path, "rb") as src, open(cut, "wb") as dst:
            dst.write(src.read(head))
            dst.write(b"\n\n===== V101 BUNDLE TRUNCATED: dropped %d "
                      b"bytes from the middle of a %d byte file "
                      b"=====\n\n" % (sz - head - tail, sz))
            src.seek(sz - tail)
            shutil.copyfileobj(src, dst)
        t.add(cut, arcname=arcname + ".TRUNCATED")
    except OSError:
        pass


def _v101_bundle(run_dir, results, reason, dlog):
    """Repack the whole run dir -- plus every per-step JobHandle
    triage tgz -- into ONE tarball at a stable path.  Called after ANY
    failing step, so the artifact survives a kill, and again at the
    end.  Never raises: a broken bundle must not fail the suite."""
    tgz = os.path.join(run_dir, "bundle.tgz")
    tmp = tgz + ".tmp"
    # mkdtemp is INSIDE the try: it raises on a full or unwritable
    # /tmp, which is precisely the state this function runs in after a
    # failure, and an escape from here lands in the step loop.
    stage = None
    try:
        stage = tempfile.mkdtemp(prefix="v101bundle_")
        man = os.path.join(stage, "MANIFEST.txt")
        with open(man, "w") as f:
            f.write("V101 bundle  host=%s  %s\nreason: %s\n"
                    "run_dir: %s\n\n"
                    % (platform.node(),
                       time.strftime("%Y-%m-%d %H:%M:%S"), reason,
                       run_dir))
            for k, status, wall, rss, note in _v101_step_rows(results):
                f.write("%-10s %-8s wall=%-7s rss=%.1fGB  %s\n"
                        % (k, status, _v101_hm(wall), rss, note))
                if results[k].tgz:
                    f.write("%-10s   triage: %s\n"
                            % ("", results[k].tgz))
        with tarfile.open(tmp, "w:gz", compresslevel=6) as t:
            t.add(man, arcname="MANIFEST.txt")
            for dirpath, _d, names in os.walk(run_dir):
                for nm in sorted(names):
                    p = os.path.join(dirpath, nm)
                    if nm.startswith("bundle.tgz") \
                            or os.path.islink(p) \
                            or not os.path.isfile(p):
                        continue
                    _v101_tar_add(t, p,
                                   os.path.relpath(p, run_dir), stage)
            for r in results.values():
                # A triage tgz is already gzipped, so it cannot be
                # head+tail truncated the way a log can -- a cut
                # tarball is simply unreadable.  Over the limit it is
                # NAMED in the manifest and left on the box instead of
                # silently bloating the download.  The `seed` step
                # always produces one (it panics by design), so this
                # is the common case, not the rare one.
                if not (r.tgz and os.path.isfile(r.tgz)):
                    continue
                if os.path.getsize(r.tgz) > V101_BUNDLE_KEEP_MB * 1e6:
                    dlog("bundle: %s triage %.1f MB > %.0f MB limit "
                         "-- left on the box, see MANIFEST"
                         % (r.key, os.path.getsize(r.tgz) / 1e6,
                            V101_BUNDLE_KEEP_MB))
                    continue
                t.add(r.tgz, arcname="triage/"
                       + os.path.basename(r.tgz))
        os.rename(tmp, tgz)
        _atomic_symlink(tgz, V101_BUNDLE)
        dlog("bundle (%s): %s -> %s  %.1f MB"
             % (reason, tgz, V101_BUNDLE,
                os.path.getsize(tgz) / 1e6))
        return tgz
    except (OSError, tarfile.TarError) as e:
        dlog("bundle FAILED (%s): %s" % (reason, e))
        return ""
    finally:
        if stage:
            shutil.rmtree(stage, ignore_errors=True)


def run_v101():
    """Menu item: the whole V101 test suite, unattended, self-sizing
    against a fixed run budget, with its own verdict."""
    t0 = _v101_now()
    deadline = _v101_deadline(t0)
    # DATED, unlike _ts(): the suite spans midnight by construction
    # (a 16 h run), and detail.log is opened "a", so a bare
    # %H:%M:%S would let two runs started at the same second-of-day
    # share a directory and interleave their logs.
    ts = time.strftime("%Y%m%d_%H%M%S")
    run_dir = os.path.join(V101_ROOT, ts)
    os.makedirs(run_dir, exist_ok=True)
    detail_path = os.path.join(run_dir, "detail.log")
    detail = open(detail_path, "a", buffering=1)
    # The stable paths are what the operator polls.  V101_VERDICT.txt
    # was only repointed at the END and V101_BUNDLE.tgz only on a
    # failure, so for up to 16 h `cat V101_VERDICT.txt` returned the
    # PREVIOUS run's verdict -- complete, plausible, and wrong -- and
    # `scp V101_BUNDLE.tgz` fetched last night's evidence.  Claim both
    # now: the placeholder says the run is live, and the stale bundle
    # link is dropped so a fetch fails loudly instead of lying.
    _vpath = os.path.join(run_dir, "verdict.txt")
    try:
        with open(_vpath, "w") as f:
            f.write("V101 RUN IN PROGRESS since %s\n"
                    "No verdict yet.  Live status:\n  %s\n  %s\n"
                    % (time.strftime("%Y-%m-%d %H:%M:%S"),
                       V101_PROGRESS, detail_path))
        _atomic_symlink(_vpath, V101_VERDICT)
        if os.path.lexists(V101_BUNDLE):
            os.unlink(V101_BUNDLE)
    except OSError:
        pass

    def dlog(msg):
        # Defensive: these run OUTSIDE the per-step try/except, and
        # both write files.  A full /tmp here would otherwise escape
        # the step loop and destroy the verdict, the bundle and the
        # traceback together -- the exact failure the guard exists to
        # prevent, one frame out.  Losing a log line is survivable;
        # losing the run is not.
        try:
            detail.write("[%s] %s\n"
                         % (time.strftime("%H:%M:%S"), msg))
        except (OSError, ValueError):
            pass

    def prog(msg):
        """One line per step, to SUMMARY.log and detail.log, so a
        `tail -F` shows progress without opening anything else."""
        dlog(msg)
        try:
            _summary_line("       v101: %s" % msg)
            log("v101: %s" % msg)
        except OSError:
            pass

    dlog("V101 suite start; budget %s -> finish by %s, run dir %s"
         % (_v101_hm(_v101_run_seconds()),
            time.strftime("%Y-%m-%d %H:%M", time.localtime(deadline)),
            run_dir))
    model = dict(V101_PRIORS)
    dlog("cost model priors: %s" % model)

    steps = v101_steps()
    # Debug hook, read by the PYTHON runner and never passed to a
    # child: ZKR_V101_ONLY=build,units restricts the run to those step
    # keys.  Unset = the whole suite.  It exists so run_v101() itself
    # can be exercised in minutes instead of first executing for real
    # on a 14 h server slot.
    only = [x for x in os.environ.get("ZKR_V101_ONLY", "").split(",")
            if x]
    results = {s.key: V101Res(s.key) for s in steps}
    if only:
        dlog("ZKR_V101_ONLY=%s -- every other step reports NOT-SELECTED"
             % ",".join(only))
        # LOUD, and in the artifacts the operator reads.  A stale
        # ZKR_V101_ONLY in the launching shell runs 2 of 13 steps and
        # still exits 0; the banner named the budget but never this.
        prog("RESTRICTED RUN: ZKR_V101_ONLY=%s -- this is NOT the "
             "full suite" % ",".join(only))
    have_v2 = True
    veh = None
    veh_pred = None

    for st in steps:
        r = results[st.key]
        if only and st.key not in only:
            r.status, r.why = "SKIP", "not selected (ZKR_V101_ONLY)"
            continue
        # SIGTERM must actually stop the suite.  install_signal_
        # handlers only kills the CHILD and sets _ABORTED; without
        # this test the suite bundled the killed step and cheerfully
        # started the next one, so the only way to stop it was
        # SIGKILL -- which loses the verdict and the final bundle.
        if aborted():
            r.status, r.why = "SKIP", "aborted (SIGINT/SIGTERM)"
            prog("%-9s SKIP (%s)" % (st.key, r.why))
            continue
        left = deadline - _v101_now()
        if st.needs_v2 and not have_v2:
            r.status, r.why = "SKIP", "binary predates stage 2"
            prog("%-9s SKIP (%s)" % (st.key, r.why))
            continue
        # The A/B steps get their argv from the picker.  If the picker
        # never ran or found nothing, `stx.argv` is still [] and the
        # child would be spawned with no arguments at all -- bora_cli
        # then prints USAGE and exits 0, which reads as a step that
        # ran and produced no markers.  Skip honestly instead.
        if st.cap_s < 0:
            r.status, r.why = "SKIP", ("surrendered so the A/B could "
                                       "fit the budget")
            prog("%-9s SKIP (%s)" % (st.key, r.why))
            continue
        if st.key in ("ab_v1", "ab_v2") and not st.argv:
            r.status, r.why = "SKIP", "picker chose no vehicle"
            prog("%-9s SKIP (%s)" % (st.key, r.why))
            continue
        # `want` is what the step ASKS for; the skip test uses it, so
        # a step is dropped for "no time" on the same terms as before
        # the clock moved.  `cap` is then CLAMPED to the time actually
        # left: the deadline is hard, and dec_big's fixed 5 h used to
        # be able to run straight through it.
        want = st.cap_s if st.cap_s else _v101_room(left)
        if st.kind != "calc" and left < min(want, 300) + 120:
            r.status, r.why = "SKIP", "no time (%s left)" % _v101_hm(left)
            prog("%-9s SKIP (%s)" % (st.key, r.why))
            continue
        cap = _v101_cap(st.cap_s, left)
        r.cap_s = cap

        if st.min_avail_gb:
            avail = _v101_mem_avail_gb()
            if avail < st.min_avail_gb:
                r.status = "SKIP"
                r.why = ("needs %.0fGB free, box has %.0fGB"
                         % (st.min_avail_gb, avail))
                prog("%-9s SKIP (%s)" % (st.key, r.why))
                continue
            dlog("%s: MemAvailable %.0fGB >= %.0fGB required; RSS "
                 "ceiling %.0fGB armed"
                 % (st.key, avail, st.min_avail_gb, st.max_rss_gb))

        if st.kind == "calc":                      # the picker
            # Hand the decider steps their room BEFORE sizing the A/B
            # (V101_DEC_RESERVE_S).  With no v2 binary only dec_v1
            # survives, so the reserve collapses to its cap.
            reserve = V101_DEC_RESERVE_S if have_v2 else 900.0
            veh, veh_pred = v101_pick(model, left - 300 - reserve,
                                       dlog)
            if veh is None:
                # The dec_big part of the reserve is a PREFERENCE:
                # the A/B is the deliverable (R2, R3), so give dec_big
                # up rather than ship a suite with no A/B at all.  The
                # dec_v1 + dec_v2 part is NOT negotiable -- dropping
                # it would leave no fold-and-prove evidence anywhere,
                # so a floor stays behind on the retry.
                floor = 2 * 3600 + 300
                dlog("picker: nothing fits with the %s decider "
                     "reserve -- retrying with the %s floor "
                     "(dec_v1 + dec_v2 only, dec_big surrendered)"
                     % (_v101_hm(reserve), _v101_hm(floor)))
                veh, veh_pred = v101_pick(model, left - 300 - floor,
                                           dlog)
                if veh is not None:
                    # ACTUALLY surrender it.  Saying so in a comment
                    # while leaving it in the list meant dec_big
                    # started with ~47 min against a 5 h ask, timed
                    # out clock-clamped, and burned the 47 min.
                    dbig = next((x for x in steps
                                 if x.key == "dec_big"), None)
                    if dbig is not None:
                        dbig.cap_s = -1        # sentinel: skip it
            if veh is None:
                r.status, r.why = "FAIL", "no vehicle fits the deadline"
                prog("%-9s FAIL (%s)" % (st.key, r.why))
                continue
            r.status = "OK"
            r.nums = {"perc": veh[0], "files": veh[1], "mb": veh[2],
                      "chunks": veh[3], "share": veh[4],
                      "pred_s": veh_pred, "model": dict(model)}
            for k in ("ab_v1", "ab_v2"):
                sub = ("full_clam_v1" if k == "ab_v1"
                       else "full_clam_v2")
                stx = next(x for x in steps if x.key == k)
                stx.argv = v101_argv(sub, 100, veh[0], 2, 1, 1, 0,
                                      "0", "1")
                passes = (V101_V1_PASSES if k == "ab_v1"
                          else V101_V2_PASSES)
                stx.cap_s = int(V101_AB_CAP_MULT
                                 * v101_cost(model, veh, passes))
            prog("%-9s OK   perc=%d (%d files, %d chunks, share %d), "
                 "pair predicted %s" % (st.key, veh[0], veh[1],
                                        veh[3], veh[4],
                                        _v101_hm(veh_pred)))
            continue

        # ---- spawn ----
        # The whole spawn is guarded.  Under go_background() stdio is
        # /dev/null, so an uncaught OSError from point_current_job,
        # spawn's open(), Popen, _summary_line or _pack_bundle would
        # kill the suite leaving no verdict, no bundle and no
        # traceback anywhere.  Every Sequencer leaf is wrapped for
        # exactly this reason; run_v101 is not a Sequencer leaf and
        # so needs its own.  One broken step is recorded and the
        # suite carries on to the next.
        t_s = _v101_now()
        try:
            ctx = JobHandle("v101_%s" % st.key, "full")
            ctx.note("v101 step %s: %s" % (st.key, st.label))
            run_log = ctx.log_path("run")
            env = dict(neo_env())
            env.update(st.env)
            dlog("step %s argv=%s env+=%s cap=%ds"
                 % (st.key, st.argv, sorted(st.env), cap))
            r.status, r.t_start = "RUNNING", t_s
            prog("%-9s RUNNING cap %s -> kill at %s"
                 % (st.key, _v101_hm(cap),
                    time.strftime("%H:%M",
                                  time.localtime(t_s + cap))))
            _v101_write_progress(run_dir, v101_progress_text(
                t0, deadline, run_dir, results, veh, model))
            if st.kind == "cargo":
                rc = _v101_cargo(ctx, st, env, run_log, dlog, cap)
            else:
                rc = run_rust_example(ctx, "bora_cli", st.argv, env,
                                       max_wall_s=cap,
                                       max_rss_gb=st.max_rss_gb)
            # b_fail_scan=False on EVERY step: the non-aggr tuner
            # prints caught CapErr probe panics into every SUCCESSFUL
            # log (M103 11.4 -- run_leaf_clamav passes False for the
            # same reason), so FAIL_RE's "panicked" fires on a healthy
            # run.  The verdict below uses rc plus POSITIVE markers
            # instead, which is a stronger test than a text scan.
            res = ctx.finish(rc, b_fail_scan=False)
            r.wall_s = _v101_now() - t_s
            r.rss_gb = res.peak_rss_gb
            r.tgz = res.triage_tgz or ""
            v101_parse(st.key, run_log, r)
            for k, v in sorted((r.nums or {}).items()):
                if not k.endswith("@"):
                    dlog("  %s.%s = %s   <- %s"
                         % (st.key, k, v,
                            (r.nums or {}).get(k + "@", "")))
            _v101_keep(run_dir, st.key, run_log)
            r.status, r.why = _v101_verdict_step(
                st, r, res, cap, ctx.rss_ceiling_hit)
        except Exception as e:              # noqa: BLE001 -- see above
            r.wall_s = _v101_now() - t_s
            r.status = "FAIL"
            r.why = "suite exception: %s: %s" % (type(e).__name__, e)
            try:
                dlog("STEP %s RAISED:\n%s"
                     % (st.key, traceback.format_exc()))
            except (OSError, ValueError):
                pass
            try:
                _summary_line("       v101: %s RAISED %s"
                              % (st.key, type(e).__name__))
            except OSError:
                pass
        if st.key == "build" and r.status == "OK":
            have_v2 = _v101_has_v2(dlog)
            if not have_v2:
                dlog("capability probe: full_clam_v2 ABSENT -> every "
                     "v2 step will be skipped; the v1 baseline still "
                     "runs")
        if st.key in ("seed", "calib", "calib_v1") \
                and r.status in ("OK", "TIMEOUT"):
            # A TIMEOUT is EVIDENCE: the arm takes at least the cap.
            # Dropping it sent the picker back to a prior that cannot
            # see the box, and it then chose a BIGGER vehicle.
            _v101_recalibrate(model, st.key, r, veh, dlog,
                               partial=(r.status == "TIMEOUT"))
        prog("%-9s %-7s %8s %5.1fGB  %s"
             % (st.key, r.status, _v101_hm(r.wall_s), r.rss_gb,
                r.why or _v101_headline(st.key, r)))
        _v101_write_progress(run_dir, v101_progress_text(
            t0, deadline, run_dir, results, veh, model))
        if r.status in ("FAIL", "TIMEOUT"):
            # Repack NOW, not at the end: a suite that is later killed
            # or that overruns the clock must still leave a
            # downloadable artifact for the failure it already saw.
            _v101_bundle(run_dir, results,
                          "after %s %s" % (st.key, r.status), dlog)
        # A TIMEOUT is a CLOCK outcome, not evidence about the
        # binary, so it must not clear have_v2 -- doing so turned one
        # slow step into a v1-only night (5 of 13 steps skipped).
        # Only an actual failure downgrades the run.
        if r.status == "FAIL" and st.key in (
                "build", "units", "smoke_v1", "smoke_v2", "seed",
                "calib"):
            # a broken v2 must not poison the rest: keep the v1
            # baseline, drop the v2 arm (design 11.6).
            if st.needs_v2:
                have_v2 = False
                dlog("hard v2 gate %s failed -> v2 steps skipped, v1 "
                     "baseline continues" % st.key)
            elif st.key == "build":
                break

    # Every write below is individually guarded.  Under
    # go_background() stdio is /dev/null, so an OSError here (a full
    # /tmp is the realistic one) would otherwise destroy the verdict,
    # the bundle AND the traceback in one go -- the run would simply
    # stop with no artifact and no explanation.
    txt = ""
    try:
        _v101_write_progress(run_dir, v101_progress_text(
            t0, deadline, run_dir, results, veh, model))
        txt = v101_report(t0, deadline, run_dir, results, veh, model)
        vpath = os.path.join(run_dir, "verdict.txt")
        with open(vpath, "w") as f:
            f.write(txt)
        _atomic_symlink(vpath, V101_VERDICT)
        detail.write("\n" + txt)
    except Exception as e:              # noqa: BLE001
        # Deliberately not just OSError.  The point of this guard is
        # that the run must never end with no verdict, no bundle and
        # no traceback; a TypeError out of v101_report would do
        # exactly that, since the final _v101_bundle sits below.
        dlog("VERDICT WRITE FAILED: %s: %s" % (type(e).__name__, e))
        try:
            dlog(traceback.format_exc())
        except Exception:               # noqa: BLE001
            pass
        _summary_line("       v101: VERDICT WRITE FAILED: %s"
                      % type(e).__name__)
    # The bundle runs BEFORE detail.close() -- dlog() writes to that
    # handle.  detail.log is line-buffered, so the tar reads the
    # verdict text that was just appended to it.
    _v101_bundle(run_dir, results, "final", dlog)
    try:
        detail.close()
    except OSError:
        pass
    print(txt)
    for line in txt.splitlines():
        _summary_line("  %s" % line)
    log("v101: verdict -> %s   detail -> %s   bundle -> %s"
        % (V101_VERDICT, detail_path, V101_BUNDLE))
    bad = [k for k, r in results.items()
           if r.status in ("FAIL", "TIMEOUT")
           and not (k in ("dec_big", "calib_v1")
                    and r.status == "TIMEOUT")]
    dlog("blocking steps: %s" % (", ".join(bad) or "none"))
    if aborted():
        return ABORT_RC          # an operator abort is not a pass
    # Derived from the VERDICT, not from step statuses alone: a
    # falsifier FAIL and both INCONCLUSIVE outcomes are "not
    # shippable" too, and an empty txt means the verdict never got
    # written -- none of which is a zero.
    return 0 if V101_GREEN_MARK in txt else 1


def _v101_cargo(ctx, st, env, run_log, dlog, cap_s):
    """The two cargo steps.  build = release build of bora_cli; units =
    the V101 unit filter plus the fingerprint gate, which must run
    --test-threads=1."""
    if st.key == "build":
        cmd = ["cargo", "build", "--release", "--example", "bora_cli"]
        return _v101_spawn(ctx, cmd, env, run_log, cap_s)
    rc = 0
    # `cap_s` is the budget for ALL THREE filters together.  Passing
    # st.cap_s to each invocation gave `units` three times the wall it
    # declares, while _v101_verdict_step compared the TOTAL against
    # the single cap -- so a legitimate finish could read as TIMEOUT.
    budget = float(max(60, cap_s))
    parts = []
    # (filter, minimum tests that MUST run).  A filter that matches
    # NOTHING exits 0 -- a false green, exactly the trap recorded in
    # small_data_par_lkup_coverage_red -- so every filter carries a
    # floor and the count is re-read out of the log.
    for filt, need, extra in (("test_v101_", 8, []),
                              ("test_m104_parse_clam", 1, []),
                              ("fingerprint_", 1,
                               ["--test-threads=1"])):
        # Each filter writes its OWN log.  spawn() opens with "w", so
        # three filters sharing one path leaves only the last one's
        # output -- the failing filter's evidence was being destroyed
        # before the bundle was built.  ctx.log_path registers them,
        # so they ride along in the triage tgz too.
        sub = ctx.log_path("units_%s" % filt.strip("_"))
        cmd = ["cargo", "test", "--release", "-p", "zkregplus",
               "--lib", "--", filt, "--nocapture"] + extra
        dlog("  units: %s" % " ".join(cmd))
        t0 = time.time()
        rc |= _v101_spawn(ctx, cmd, env, sub, int(max(30, budget)))
        budget -= time.time() - t0
        parts.append(sub)
        n, raw = _v101_grep(sub, r"(\d+) passed", 1)
        got = int(n) if n else 0
        dlog("  units: filter %-22s ran %s (need >= %d)  <- %s"
             % (filt, got, need, raw))
        if got < need:
            dlog("  units: FILTER %s MATCHED %d TESTS -- treating as "
                 "FAIL (a 0-match filter exits 0)" % (filt, got))
            rc |= 1
    try:
        with open(run_log, "w") as out:
            for p in parts:
                out.write("\n===== %s =====\n" % os.path.basename(p))
                if os.path.isfile(p):
                    with open(p, errors="replace") as f:
                        shutil.copyfileobj(f, out)
    except OSError as e:
        dlog("  units: could not merge filter logs: %s" % e)
    return rc


def _v101_spawn(ctx, cmd, env, run_log, cap_s):
    point_current_job(run_log, None)
    p, t = spawn(cmd, env, run_log, ctx.key)
    ctx.watch(p, run_log, max_wall_s=cap_s)
    p.wait()
    _join_pump(t)
    return p.returncode


def _v101_has_v2(dlog):
    """One second, right after the build: does this binary know the
    switch?  Cheaper than discovering it 40 minutes into step 5."""
    exe = os.path.join(REPO, "target", "release", "examples",
                        "bora_cli")
    try:
        out = subprocess.run([exe, "--help"], capture_output=True,
                              text=True, timeout=60).stdout
    except Exception as e:
        dlog("capability probe failed: %s" % e)
        return False
    # BOTH A/B tokens: since the 2026-08-18 default flip the bare
    # `full_clam` means v2, so the v1 arm needs its own token and an
    # older binary that only knows `_v2` would fail 4 steps deep.
    missing = [t for t in ("full_clam_v1", "full_clam_v2")
               if t not in out]
    ok = not missing
    dlog("capability probe: A/B tokens %s" % ("present" if ok
                                              else "ABSENT: %s"
                                              % ",".join(missing)))
    return ok


def _v101_recalibrate(model, key, r, veh, dlog, partial=False):
    """Replace priors with what we just measured.  This is the whole
    reason steps 4 and 5 come before the picker.

    `partial` = the step TIMED OUT, so its wall is a LOWER bound on
    the arm rate rather than the rate.  Discarding it made the picker
    NON-MONOTONE: measured, calib at 3000 s picked perc 10, but calib
    at 3590 s (TIMEOUT) picked perc 15 -- the vehicle grew exactly
    when the evidence said the box was slowest, because the fallback
    is an analytic prior that cannot see the box.

    What actually makes it safe is that a TIMEOUT wall is >= 0.98 x
    the cap, so the derived rate is already a lower bound.  `slower()`
    below is belt-and-braces and is INERT today: r_v1_arm / r_v2_arm
    are absent from V101_PRIORS and each is written by exactly one
    step.  It earns its keep only if a second writer ever appears."""

    def slower(field, val):
        model[field] = max(model.get(field) or 0.0, val) if partial \
            else val
    n = r.nums or {}
    old = dict(model)
    if key == "seed":
        # `db_ms` comes from "build DB. N ms", which ONLY the legacy
        # zkp_driver emits (:1686,:2081).  Every V101 step runs
        # bora_data_driver::build_fresh_db, which logs no such line,
        # so this branch is dead on the neo path and t_db keeps its
        # prior.  Left in place because it costs nothing and would
        # start working the day that timer is added -- but the seed
        # step's own arithmetic below no longer DEPENDS on it: the
        # residual goes into r_disch, a per-MB term, rather than
        # into km, which the old code then multiplied by chunk count.
        if n.get("db_ms"):
            model["t_db"] = n["db_ms"] / 1000.0
            model.setdefault("_measured", set()).add("t_db")
        if n.get("seed_ms") is not None:
            model["r_seed"] = n["seed_ms"] / 1000.0 / 765.5
            model.setdefault("_measured", set()).add("r_seed")
            disch = r.wall_s - model["t_db"] - n["seed_ms"] / 1000.0
            if disch > 0:
                model["r_disch"] = disch / 765.5
                model.setdefault("_measured",
                                  set()).add("r_disch")
    if key == "calib":
        # the perc-2 vehicle, read FROM the table rather than copied
        # out of it: the table grew on 2026-08-17 and a duplicated
        # literal is exactly the thing that goes stale silently.
        chunks = float(dict((v[0], v[3])
                            for v in V101_VEHICLES).get(2, 110))
        pr = n.get("probe_ms")
        if pr:
            model["r_probe"] = (pr / 1000.0) / chunks
            model.setdefault("_measured", set()).add("r_probe")
        if n.get("v5_ms") and pr:
            model["k5"] = max(0.2, (n["v5_ms"] / float(pr)))
            model.setdefault("_measured", set()).add("k5")
        # the meter walk is the tail of the step that neither phase
        # line covers; attribute it as km
        acc = sum(n.get(k, 0) for k in ("seed_ms", "probe_ms", "v5_ms"))
        mb2 = float(dict((v[0], v[2])
                          for v in V101_VEHICLES).get(2, 12.3))
        rest = r.wall_s - acc / 1000.0 - model["t_db"] \
            - model["r_disch"] * mb2
        if pr and rest > 0:
            model["km"] = max(0.2, rest / (pr / 1000.0))
            model.setdefault("_measured", set()).add("km")
        # ...and the same end-to-end rate the v1 arm gets, so the two
        # arms are priced by the same method rather than one by
        # measurement and one by model.
        vh2 = dict((v[0], v) for v in V101_VEHICLES).get(2)
        if vh2 and r.wall_s > 0:
            body = r.wall_s - (model["t_db"]
                               + model["r_disch"] * vh2[2])
            if body > 0:
                slower("r_v2_arm", body / float(vh2[3]))
    if key == "calib_v1":
        # ONE number, measured end to end: the whole v1 arm at perc 2,
        # minus the setup the model already prices, divided by chunks.
        # It absorbs the probe rate, the pass count AND the tightening
        # passes at once, so none of the three has to be guessed.
        vh = dict((v[0], v) for v in V101_VEHICLES).get(2)
        if vh and r.wall_s > 0:
            setup = model["t_db"] + model["r_disch"] * vh[2]
            body = r.wall_s - setup
            if body > 0:
                slower("r_v1_arm", body / float(vh[3]))
                model["v1_rounds_seen"] = (n.get("v1_bumps") or 0) + 1
    dlog("recalibrate after %s: %s -> %s" % (key, old, model))


def num_or(v, alt):
    """A missing count prints its reason, never a bare 0."""
    return alt if v is None else v


def _v101_verdict_step(st, r, res, cap, rss_hit=False):
    """OK / FAIL / TIMEOUT / SKIP for one step, plus the reason.  The
    seed step PANICS by design (the dry fire stops after logging), so
    its nonzero rc and its panic marker are expected, not a failure."""
    n = r.nums or {}
    if rss_hit:
        # The OOM guard is a RESOURCE outcome -- the same class as the
        # min_avail_gb precondition that SKIPS the step before it
        # starts.  Left as a FAIL (the kill makes rc nonzero) it read
        # "BLOCKED BY: dec_big" for a box that simply did not have the
        # RAM, on the one step the suite itself calls opportunistic.
        return "SKIP", ("RSS ceiling %.0fGB hit (OOM-GUARD) at %.1fGB "
                        "peak -- box too small for this step"
                        % (st.max_rss_gb, r.rss_gb))
    if r.wall_s >= cap * 0.98:
        # Distinguish "this step hung" from "the clock ran out".  A
        # cap clamped below what the step asked for is a scheduling
        # outcome, not a defect in the step, and conflating them sends
        # the reader hunting a hang that never happened.
        if st.cap_s and cap < st.cap_s:
            return "TIMEOUT", ("clock-clamped: asked %s, got %s "
                               "before the run budget ran out"
                               % (_v101_hm(st.cap_s), _v101_hm(cap)))
        return "TIMEOUT", "hit the %s wall cap" % _v101_hm(cap)
    if st.key == "seed":
        # The dry fire panics BY DESIGN after logging, so rc != 0 is
        # expected -- but only for THAT panic.  Narrow the allowance
        # to the marker the seed-only path prints, so a different
        # crash after the seed line is still a failure.
        if n.get("seed_cs") and n.get("seed_marker"):
            return "OK", ""
        if n.get("seed_cs"):
            return "FAIL", ("seed printed but the SEED-ONLY marker "
                            "is absent: rc=%s is a real crash"
                            % res.rc)
        return "FAIL", "no V2 QM SEED line"
    if res.rc != 0:
        return "FAIL", "rc=%s (%s)" % (res.rc, res.triage_tgz)
    # POSITIVE markers: a tuner step must show that it converged, a
    # decider step that it folded.  Absence is a failure even at rc 0
    # -- foldpot does not abort on a self-verify failure, it reaches
    # only the log while cargo still prints ok (consts.rs:67-77).
    if st.key in ("smoke_v2", "calib", "ab_v2") \
            and n.get("v2_iters") is None:
        return "FAIL", "no V2 CONVERGED line"
    if st.key in ("smoke_v1", "ab_v1") and n.get("v1_iters") is None:
        return "FAIL", "no determine_config_non_aggr CONVERGED line"
    # foldpot does NOT abort on a self-verify failure -- it reaches
    # only the log while cargo still prints ok (consts.rs:67-77), so a
    # decider step must read the COUNTER, never the exit code.
    if st.key.startswith("dec_"):
        if n.get("verify_fail"):
            return "FAIL", "%d VERIFY-FLAGS verdict=REJECT" \
                % n["verify_fail"]
        # POSITIVE, and specific: all THREE [final] markers must be
        # present AND PASS.  "at least one PASS somewhere" was the old
        # test and it let a REJECTed Groth16 decider through -- a
        # healthy run emits 7 PASS markers, so 6 could reject unseen.
        # `or 0`, not a .get default: _v101_count returns None for an
        # UNREADABLE log, and None < 3 raises.  An unreadable decider
        # log must fail CLOSED -- absence of proof is not proof.
        if (n.get("verify_final") or 0) < 3:
            return "FAIL", ("only %s of 3 [final] VERIFY-FLAGS PASS "
                            "markers (batch1/batch2/ind)"
                            % num_or(n.get("verify_final"), "unreadable"))
        if not n.get("verify_snark"):
            return "FAIL", "no batch2[final] PASS (Groth16 decider)"
    return "OK", ""


def _v101_headline(key, r):
    n = r.nums or {}
    if key == "seed":
        return "cs=%s igc=%s mid_hits=%s skipped=%s" % (
            n.get("seed_cs"), n.get("seed_igc"), n.get("mid_hits"),
            n.get("skipped"))
    # The decider test comes FIRST.  It used to sit below the v2
    # branch, which also matches dec_v2 and dec_big -- so the two
    # steps whose entire purpose is to prove showed tuner numbers and
    # no verify evidence at all, and the branch below was dead code.
    if key.startswith("dec_"):
        return "verify final=%s/3 PASS=%s REJECT=%s  %s" % (
            n.get("verify_final"), n.get("verify_pass"),
            n.get("verify_fail"),
            ("v2 iters=%s" % n.get("v2_iters"))
            if key in ("dec_v2", "dec_big")
            else ("v1 conv@%s" % n.get("v1_iters")))
    if key in ("calib", "ab_v2", "smoke_v2"):
        return "v2 iters=%s bumps=%s qm_real=%s" % (
            n.get("v2_iters"), n.get("v2_bumps"), n.get("qm_real"))
    if key in ("ab_v1", "smoke_v1", "calib_v1"):
        return "v1 conv@%s bumps=%s" % (n.get("v1_iters"),
                                         n.get("v1_bumps"))
    return ""


def _fx(cond, ev):
    """A falsifier row: PASS/FAIL, or N/A when it could not be
    computed.  A metric that could not be computed prints its reason;
    it NEVER prints as a zero."""
    if cond is None:
        return ("N/A", ev)
    return ("PASS" if cond else "FAIL", ev)


def _wx(cond, ev):
    """An ADVISORY row.  Never blocks the verdict -- only FAIL and N/A
    do -- for checks whose miss means "eyeball this", not "do not
    ship".  DECIDE still names every WARN it printed."""
    if cond is None:
        return ("NOTE", ev)
    return ("PASS" if cond else "WARN", ev)


def _com(n):
    """Thousands separators: 36860 and 36,860 in the same line read as
    two different numbers."""
    return "{:,}".format(n)


def _v101_loose(seed_cs):
    """F1b: how far the seed sits above the proven corpus max.  Loose
    is BY DESIGN (M3 tightens it); only the spec's RAM alarm stops."""
    if seed_cs is None:
        return ("NOTE", "seed_cs=not measured")
    x = seed_cs / float(V101_QM_PROVEN_MAX)
    ev = ("seed_cs=%s = %.2fx the proven max %s"
          % (_com(seed_cs), x, _com(V101_QM_PROVEN_MAX)))
    if seed_cs > V101_SEED_RAM_ALARM:
        return ("FAIL", ev + "  <- over the %s RAM alarm (spec R-2)"
                % _com(V101_SEED_RAM_ALARM))
    if x > V101_SEED_LOOSE_X:
        return ("WARN", ev + "  <- loose; M3 absorbs it, but check "
                             "the RAM gate before the next pass")
    return ("PASS", ev)


def v101_report(t0, deadline, run_dir, results, veh, model):
    """The verdict.  Every claim carries its number; no adjectives.
    Shaped so a Claude Code session can decide PASS/FAIL from this
    text alone and only open detail.log when something is red."""
    R = results
    g = lambda k, f, d=None: ((R[k].nums or {}).get(f, d)
                              if k in R else d)
    wall = _v101_now() - t0
    L = []
    A = L.append
    A("=" * 66)
    A("V101 SUITE VERDICT   %s" % time.strftime("%Y-%m-%d %H:%M:%S"))
    A("wall %s of %s budget   margin %s   (finish-by was %s)"
      % (_v101_hm(wall), _v101_hm(_v101_run_seconds()),
         _v101_hm(deadline - _v101_now()),
         time.strftime("%H:%M", time.localtime(deadline))))
    if veh:
        A("vehicle perc_samples=%d  %d files  %.1fMB  %d chunks  "
          "share %d (production 129)"
          % (veh[0], veh[1], veh[2], veh[3], veh[4]))
    A(_v101_model_line(model))
    A("")
    A("STEP        STATUS     WALL    RSS  NOTE")
    for k, status, wall, rss, note in _v101_step_rows(R):
        A("  %-10s %-8s %7s %5.1fGB  %s"
          % (k, status, _v101_hm(wall), rss, note[:42]))
    A("")

    # ---- falsifiers ----
    # `src` records WHICH step a number came from.  Several metrics
    # fall back from ab_v2 (the picked vehicle) to calib (perc 2, 25
    # files); without the tag the reader cannot tell a 272 MB result
    # from a 12.3 MB one, and they are not the same evidence.
    def pick2(field, *keys, **kw):
        """First step that measured `field`.  `zero_ok=False` skips a
        step that measured ZERO and keeps looking, because for a
        demand/cap a 0 is not a measurement -- testing for it AFTER
        the pick threw away a good `calib` reading whenever `ab_v2`
        had already won with its 0.  v2_iters keeps zero_ok=True: 0
        rounds is the BEST outcome there, not a missing number."""
        zero_ok = kw.pop("zero_ok", True)
        assert not kw, kw
        for k in keys:
            v = g(k, field)
            if v is not None and (zero_ok or v):
                return v, k
        for k in keys:
            if g(k, field) == 0:
                return None, "%s read 0 -- not a credible value" % k
        # "no step" rather than the bare None, which rendered as the
        # nonsense "(from None)" on every unmeasured row.
        return None, "no step"

    def worst(field, *keys):
        """MAX over EVERY step that measured `field` -- the right
        aggregation for a COUNTER.  first-hit was wrong for these:
        `_v101_count` returns 0, not None, so ab_v2 always won and
        every later step was invisible.  Five production-width
        dis_adv::neo_qm_real bumps in dec_big parsed correctly and
        were then never consulted, and the verdict went green over
        the exact defect M2 exists to eliminate."""
        hits = [(g(k, field), k) for k in keys
                if g(k, field) is not None]
        if not hits:
            return None, "no step"
        v, k = max(hits)
        return v, (k if len(hits) == 1
                   else "%s = max of %d steps" % (k, len(hits)))

    # Every v2 tuner step, widest first.  A qm_real under-seed is a
    # defect wherever it appears, so none of them may be skipped.
    # NOTE the asymmetry: bumps are logged unconditionally, but
    # caperr_units comes from meter_unit_demand, which only runs under
    # ZKR_METER_T9901 -- so in practice only `calib` and `ab_v2` can
    # ever contribute one.  R1 names its source for that reason.
    V2_STEPS = ("dec_big", "ab_v2", "dec_v2", "calib", "smoke_v2")

    seed_cs = g("seed", "seed_cs")
    v2_bumps, src_bump = worst("v2_bumps", *V2_STEPS)
    v2_qm_bumps, src_qm = worst("v2_qm_bumps", *V2_STEPS)
    v2_iters, src_it = pick2("v2_iters", "ab_v2", "calib")
    v1_iters = g("ab_v1", "v1_iters")
    v1_bumps = g("ab_v1", "v1_bumps")
    # zero_ok=False: demand=0 made F2, F5 and R2 all print PASS at
    # once.  num() was built so a MISSING number never prints as 0;
    # a MEASURED 0 sailed straight through.  No clam vehicle demands
    # zero qm_real rows -- the dry leaf measures 7.
    demand, src_dem = pick2("meter_demand_cs", "ab_v2", "calib",
                             zero_ok=False)
    shipped, src_shp = pick2("shipped_qm", "ab_v2", "calib",
                              zero_ok=False)
    seed_words = g("seed", "seed_words")
    mid = g("seed", "mid_hits")
    skipped = g("seed", "skipped")
    seed_ms = g("seed", "seed_ms")
    v5_ms = g("ab_v2", "v5_ms")
    pr_ms = g("ab_v2", "probe_ms")
    caperr, src_cap = worst("caperr_units", *V2_STEPS)
    units_oks = g("units", "units_oks")
    veh_perc = veh[0] if veh else None

    def num(v, unit=""):
        """A missing measurement prints as 'not measured', NEVER as a
        zero -- a printed 0.0s reads as a real, excellent result."""
        return "not measured" if v is None else ("%s%s" % (v, unit))

    rows = [
        # SOUNDNESS ONLY: >=, not a band.  The seed is a declared
        # sound UPPER BOUND (bora_data_driver.rs:2063) that M3 then
        # tightens, so sitting above the proven max is its job -- the
        # design spec defines F1 as ">= 36,860", its own worked
        # example passes at 41,208 (+11.8%), and the dry leaf
        # measured 6.1x on a healthy run.  A +-5% band here would
        # have stamped a healthy 16 h run "NOT shippable".  Looseness
        # is real but it is a DIFFERENT question, so it gets its own
        # row rather than being folded into the soundness gate.
        ("F1 seed >= the proven max 36,860",
         _fx(None if seed_cs is None
             else seed_cs >= V101_QM_PROVEN_MAX,
             "seed_cs=%s over %s words (proven max %s)"
             % (num(seed_cs and _com(seed_cs)), num(seed_words),
                _com(V101_QM_PROVEN_MAX)))),
        ("F1b seed looseness vs the RAM alarm", _v101_loose(seed_cs)),
        # NOT the spec's F2.  Spec sec 10 wants a PER-UNIT join
        # (est_cs[u] >= qm_real_cs[u] for every u), which needs an
        # estimator dump that was never added -- `grep -rn 61101
        # crates/` is empty.  This row compares two MAXIMA from
        # different populations, so a single per-unit miss is
        # invisible to it.  Named for what it is.
        ("F2 corpus-max seed >= subset-max demand",
         _fx(None if (seed_cs is None or demand is None)
             else seed_cs >= demand,
             "seed_cs=%s (perc 100) vs max demand=%s (from %s)"
             " -- NOT the per-unit join (spec F2 not run)"
             % (num(seed_cs), num(demand), src_dem))),
        # CORRECTED 2026-08-17: "zero bumps" was wrong -- one bump
        # from dfa/comp_sig is expected.  What must be zero is the
        # qm_real bump, which is the one M2 exists to remove.
        ("F3a zero dis_adv::neo_qm_real bumps",
         _fx(None if v2_qm_bumps is None else v2_qm_bumps == 0,
             "qm_real bump rounds=%s (from %s)"
             % (num(v2_qm_bumps), src_qm))),
        # The two numbers come from DIFFERENT pickers (bumps from
        # worst() over every v2 step, iters from the A/B pair), so
        # both sources are named.  Printing one source beside two
        # numbers is the N4 defect that was fixed for R1.
        ("F3b <= 1 v2 bump round overall",
         _fx(None if v2_bumps is None else v2_bumps <= 1,
             "v2 bump rounds=%s (from %s), converged @iter %s "
             "(from %s)"
             % (num(v2_bumps), src_bump, num(v2_iters), src_it))),
        ("F5 shipped qm == measured max",
         _fx(None if (shipped is None or demand is None)
             else shipped >= demand and shipped <= demand + 1,
             "shipped=%s measured max=%s (from %s)"
             % (num(shipped), num(demand), src_shp))),
        # ADVISORY, for the same reason the F1 band was wrong: this
        # is a PERFORMANCE bar folded into a ship decision.  Spec I7
        # says outright that with 8 rayon workers "F6's '< 5 min' bar
        # may bind", and F6's own remedy (:1294) is a faster nibble
        # decoder -- an optimisation follow-up, not a soundness stop.
        # The suite's OWN prior says it will bind: r_seed 0.4 s/MB x
        # 765.5 MB = 306 s, 2% OVER the bar.  The only supporting
        # number (2m51s) is from the spec's ILLUSTRATIVE example; the
        # full-corpus seed has never actually run.
        ("F6 seed wall < 5 min (advisory)",
         _wx(None if seed_ms is None else seed_ms < 300000,
             "seed walk=%s%s"
             % (num(seed_ms and seed_ms / 1000.0, "s"),
                "  <- over the bar; I7's fast decoder is the fix, "
                "not fewer words"
                if (seed_ms or 0) >= 300000 else ""))),
        # ADVISORY, not a gate.  b_mid is set only when the
        # CARRY-FREE mid slice STRICTLY exceeds the best aligned
        # chunk, and aligned chunks accumulate acc1
        # (bora_data_driver.rs:2022-2023) while the mid slice
        # restarts at init_state with none -- so it is handicapped,
        # and mid_hits=0 is a healthy outcome, which is what every
        # run on this box has printed.  A genuinely dead I1 branch
        # surfaces as a CapErr, which R1 measures directly.
        ("F7 mid_hits > 0 (advisory)",
         _wx(None if mid is None else mid > 0,
             "mid_hits=%s" % num(mid))),
        # ADVISORY, and the two None branches of v101_word_sigs are
        # NOT alike.  Branch 1 (vec_sed_sigs empty, :2053) is benign:
        # clamav.rs:3631 asserts the two vecs have equal length, so
        # empty implies n_inp = 0 implies ZERO Q_m real rows -- the
        # word is excluded from both the bound and the thing bounded.
        # Branch 2 (len mismatch, :2059) is FATAL but never silent:
        # sed_mapper.rs:557 asserts exactly its negation, unconditional
        # in release, so a production tune ABORTS there rather than
        # under-capping.  (NOT the all-zero pad word: that one is
        # discharged for real at :1081 and every log prints skipped=0
        # with it present.)  Advisory because it cannot hide an
        # under-cap -- but it is the suite's ONLY full-corpus
        # WordInfo-consistency reading, so the text names the stakes.
        ("F8 skipped words == 0 (advisory)",
         _wx(None if skipped is None else skipped == 0,
             "skipped=%s%s"
             % (num(skipped),
                "  <- branch 2 would ABORT a production tune at "
                "sed_mapper.rs:557; branch 1 (empty sig set) is benign"
                if skipped else ""))),
        # ADVISORY by DESIGN: the spec asks this row to REPORT, not to
        # block ("say so in the result rather than quoting the probe
        # phase alone").  As a falsifier it could never FAIL, yet it
        # could go N/A and single-handedly force INCONCLUSIVE.
        ("F9 v5 walk vs probe (advisory)",
         _wx(None if (v5_ms is None or pr_ms is None)
             else v5_ms <= pr_ms,
             "v5=%s probe=%s%s"
             % (num(v5_ms and v5_ms / 1000.0, "s"),
                num(pr_ms and pr_ms / 1000.0, "s"),
                "  <- v5 dominates: V102 (parallel qm_walk_units) "
                "is the next job"
                if (v5_ms or 0) > (pr_ms or 0) else ""))),
    ]
    A("FALSIFIERS                            verdict  evidence")
    for name, (verd, ev) in rows:
        A("  %-36s %-7s  %s" % (name, verd, ev))
    A("")

    # ---- requirements ----
    dec = [k for k in ("dec_v1", "dec_v2", "dec_big")
           if k in R and R[k].status == "OK"]
    A("REQUIREMENTS")
    # Every row goes through _fx, exactly like the falsifiers.  These
    # four used to be hand-rolled if/else expressions and every one of
    # them could print PASS on evidence that did not exist: R1 read a
    # MISSING caperr measurement (None) as "zero cap errors", and R3
    # tested a non-empty STRING, so it could not fail at all.
    ab_ok = bool(R.get("ab_v2") and R["ab_v2"].status == "OK")
    r_rows = [
        ("R1 never under-cap",
         _fx(None if (caperr is None or not ab_ok) else caperr == 0,
             "caperr_units=%s (from %s); decider steps ok: %s"
             % (num(caperr), src_cap, ",".join(dec) or "none"))),
        ("R2 no waste",
         _fx(None if (shipped is None or demand is None)
             else shipped <= demand + 1,
             "qm_real_rows=%s vs max demand=%s (from %s)"
             % (num(shipped), num(demand), src_shp))),
    ]
    # R3 compares ROUNDS, and a round count is v*_iters + 1 -- the
    # bump counters miss the promotion round (bora_data_driver.rs
    # :2306), so they undercount both arms.
    if v1_iters is not None and v2_iters is not None:
        v1r, v2r = v1_iters + 1, v2_iters + 1
        # A strict win, OR parity when v2 is already at the design
        # floor of one round -- you cannot beat 1.  Plain "<=" let a
        # row named "fast" print PASS on "2 -> 2 rounds", certifying
        # a zero speedup.
        r3 = _fx(v2r < v1r or v2r == 1,
                 "%d -> %d rounds%s  (v1 bumps=%s, v2 bumps=%s)"
                 % (v1r, v2r,
                    "" if v2r < v1r else
                    ("  [parity at the 1-round floor]" if v2r == 1
                     else "  [NO SPEEDUP]"),
                    num(v1_bumps), num(v2_bumps)))
    else:
        r3 = _fx(None, "A/B incomplete: v1_iters=%s v2_iters=%s"
                 % (num(v1_iters), num(v2_iters)))
    r_rows.append(("R3 fast (rounds)", r3))
    r_rows.append(
        ("R5 v1 unchanged",
         _fx(None if units_oks is None
             else (R.get("units") is not None
                   and R["units"].status == "OK" and units_oks >= 3),
             "%s/3 cargo filters ok (test_v101_ incl. "
             "test_v101_ab_switch_is_the_only_difference / m104 / "
             "fingerprint_); units=%s"
             % (num(units_oks),
                R["units"].status if R.get("units") else "absent"))))
    for name, (verd, ev) in r_rows:
        A("  %-36s %-7s  %s" % (name, verd, ev))
    A("")

    # ---- headline ----
    A("HEADLINE")
    w1, w2 = (R["ab_v1"].wall_s if "ab_v1" in R else 0,
              R["ab_v2"].wall_s if "ab_v2" in R else 0)
    if w1 and w2:
        A("  tune wall  v1 %s -> v2 %s  = %.2fx   at perc_samples=%s"
          % (_v101_hm(w1), _v101_hm(w2), w1 / max(w2, 1e-9),
             veh[0] if veh else "?"))
    A("  NOT MEASURED: full-corpus v1 (~18-19h, never observed to "
      "complete).")
    A("  Subset wall does NOT transfer; round COUNTS and caps do.")
    A("")
    fails = [k for k, r in R.items() if r.status in ("FAIL",
                                                      "TIMEOUT")]
    skips = [k for k, r in R.items() if r.status == "SKIP"]
    # PENDING fell through BOTH buckets, so a suite that died before
    # reaching a step could print green without mentioning it at all.
    stalled = [k for k, r in R.items()
               if r.status in ("PENDING", "RUNNING")]
    not_ok = [k for k, r in R.items() if r.status != "OK"]
    # THE GREEN LINE IS GATED ON EVIDENCE, NOT ON THE ABSENCE OF
    # FAILURE.  "Nothing failed" is not "it passed": a run where the
    # v2 binary was missing, or where dec_big was skipped for RAM,
    # produces zero FAILs and zero evidence, and the old wording
    # ("ALL RUN STEPS PASS -> propose the commit") was printed over
    # exactly that -- observed 2026-08-17 on a run with 10 of 12
    # steps SKIP and every falsifier N/A.  dec_big stays an explicit
    # opportunistic exception; the other five are mandatory.
    must = ["units", "seed", "calib", "ab_v1", "ab_v2", "dec_v2"]
    missing = [k for k in must
               if not (R.get(k) and R[k].status == "OK")]
    bad_f = [name for name, (verd, _e) in rows + r_rows
             if verd == "FAIL"]
    na_f = [name for name, (verd, _e) in rows + r_rows
            if verd == "N/A"]
    # Two steps are OPPORTUNISTIC, and a TIMEOUT on either is a
    # scheduling outcome rather than evidence about the code:
    # dec_big (RAM-guarded, last, 5 h cap) printed "BLOCKED BY"
    # directly above the NOTE calling it optional; calib_v1 exists
    # only to replace V101_V1_ARM_RATIO with a measurement, and the
    # constant IS the designed fallback for it not returning.  A real
    # FAIL on either still blocks.
    fails = [k for k in fails
             if not (k in ("dec_big", "calib_v1")
                     and R[k].status == "TIMEOUT")]
    warns = [name for name, (verd, _e) in rows + r_rows
             if verd == "WARN"]
    # NOTE = an advisory that could not be computed.  It blocks
    # nothing, but F8 is the suite's only full-corpus consistency
    # reading, so "we never looked" must not be silent either.
    notes = [name for name, (verd, _e) in rows + r_rows
             if verd == "NOTE"]
    A("DECIDE")
    if fails:
        A("  BLOCKED BY: %s   -> %s/detail.log"
          % (", ".join(fails), run_dir))
    elif missing:
        A("  INCONCLUSIVE -- NOT shippable.  These steps did not "
          "reach OK: %s" % ", ".join(missing))
        A("  Nothing FAILED, but the evidence for R1/R2/R3 was never "
          "produced.")
    elif bad_f:
        A("  FALSIFIED BY: %s   -> NOT shippable"
          % ", ".join(bad_f))
    elif na_f:
        A("  INCONCLUSIVE -- every step ran, but these could not be "
          "computed: %s" % ", ".join(na_f))
    else:
        # "ALL STEPS OK" was an overclaim: the gate gets its evidence
        # from the six MANDATORY steps, and dec_v1/smoke_*/calib_v1
        # could each be SKIP underneath it.  Name what did not run in
        # the same sentence rather than in a footnote below it.
        A("  ALL 6 MANDATORY STEPS OK AND EVERY "
          "FALSIFIER/REQUIREMENT PASSED")
        if not_ok:
            A("  (not-OK, none of them mandatory: %s)"
              % ", ".join("%s=%s" % (k, R[k].status) for k in not_ok))
        A("  " + V101_GREEN_MARK)
    if warns:
        # An advisory row cannot block, but it must never be silent
        # under a green line either.
        A("  ADVISORY (does not block, read before shipping): %s"
          % ", ".join(warns))
    if notes:
        A("  NOT MEASURED (advisory rows, no evidence either way): %s"
          % ", ".join(notes))
    if stalled:
        A("  DID NOT RUN (suite ended early): %s" % ", ".join(stalled))
    if "dec_big" in skips:
        A("  NOTE: dec_big (production-width fold+prove, R1's "
          "strongest evidence) was skipped: %s" % R["dec_big"].why)
    if skips:
        A("  SKIPPED: %s" % ", ".join(
            "%s (%s)" % (k, R[k].why) for k in skips))
    A("  detail:   %s/detail.log" % run_dir)
    A("  progress: %s" % V101_PROGRESS)
    A("  bundle:   %s   <- scp THIS for offline analysis"
      % V101_BUNDLE)
    A("=" * 66)
    return "\n".join(L)

# =====================================================================
# Layer A -- clean (menu #5) + figs (menu #6)
# =====================================================================

RUN_DATA_DIR = os.path.join(REPO, "data", "paper_data", "run_data")
EVAL_DIR = os.path.join(RUN_DATA_DIR, "scripts", "eval")
PDF_DIR = os.path.join(REPO, "data", "paper_data", "pdf")
PDF_PATH = os.path.join(PDF_DIR, "list_figures.pdf")


def _wipe_generated(root):
    """Delete every file under root except the tracked .gitkeep /
    .gitignore markers, then prune emptied subdirs.  Returns
    (n_files, n_bytes)."""
    n = b = 0
    for dirpath, _dirs, filenames in os.walk(root, topdown=False):
        for fn in filenames:
            if fn in (".gitkeep", ".gitignore"):
                continue
            p = os.path.join(dirpath, fn)
            try:
                sz = os.lstat(p).st_size
                os.unlink(p)
                n += 1
                b += sz      # only what was actually removed
            except OSError as e:
                log("clean: cannot remove %s (%s)" % (p, e))
        if dirpath != root:
            try:
                os.rmdir(dirpath)     # succeeds only when emptied
            except OSError:
                pass
    return n, b


CLEAN_PROMPTS = 5      # R4: how many confirmations menu #5 demands


def _confirm_clean(ask=input):
    """R4: five confirmations, announced up front.  Returns 0 to
    proceed, non-zero to abort.  `ask` is injected for testing."""
    if not sys.stdin.isatty():
        log("clean: not a TTY -- refusing (needs %d confirmations)"
            % CLEAN_PROMPTS)
        return 7
    log("clean: this DELETES all generated run data under %s and %s."
        % (RAW_DATA_ROOT, PDF_DIR))
    log("clean: you will be asked to confirm %d times; the last one "
        "requires typing DELETE." % CLEAN_PROMPTS)
    for k in range(1, CLEAN_PROMPTS + 1):
        want = "DELETE" if k == CLEAN_PROMPTS else "yes"
        got = ask("clean: confirm %d/%d -- type %s: "
                   % (k, CLEAN_PROMPTS, want)).strip()
        if got != want:
            log("clean: aborted at prompt %d/%d" % (k, CLEAN_PROMPTS))
            return 1
    return 0


def run_clean():
    """Menu item #5: delete the PROJECT's generated run data -- every
    file under raw_data/ (jet1tb, any_server, failed_tgz, ...) and
    pdf/, keeping the git-tracked marker files and their dirs.  Both
    roots derive from REPO, so the paper tree cannot be touched.
    R4: five confirmations are required before anything is removed."""
    total_n, total_b = 0, 0
    # hard guard FIRST, before the user is prompted: only the
    # project's data/paper_data subtree is ever wiped -- a bad edit
    # upstream must fail loudly here.
    for root in (RAW_DATA_ROOT, PDF_DIR):
        assert root.startswith(
            os.path.join(REPO, "data", "paper_data") + os.sep), root
    rc = _confirm_clean()
    if rc:
        return rc
    for root in (RAW_DATA_ROOT, PDF_DIR):
        if not os.path.isdir(root):
            log("clean: %s absent -- skipped" % root)
            continue
        n, b = _wipe_generated(root)
        log("clean: %s -- removed %d file(s), %.2f GB"
            % (root, n, b / 2**30))
        total_n += n
        total_b += b
    log("clean: done -- %d file(s), %.2f GB total"
        % (total_n, total_b / 2**30))
    return 0


# The git-tracked DLP corpus manifest (the ONLY retained copy of the
# pass/fail email lists; see zkp_driver.rs:8342).  datasets.py reads it
# from raw_data/any_server/, which is gitignored, so a fresh box needs
# it staged before every figs run.
CORPUS_TGZ_SRC = os.path.join(REPO, "data", "paper_data", "dlp",
                               "cfg", "corpus.tgz")


def stage_corpus_tgz():
    """Copy the tracked corpus.tgz into raw_data/any_server/ where
    datasets.py (Table 1) reads it.  Missing source is a loud WARN,
    not an abort: RUNALL tolerates the single failing generator."""
    if not os.path.isfile(CORPUS_TGZ_SRC):
        log("figs: WARN missing %s -- datasets.py will fail"
            % CORPUS_TGZ_SRC)
        return False
    dest = raw_data_path("corpus.tgz", server_specific=False)
    os.makedirs(os.path.dirname(dest), exist_ok=True)
    shutil.copy2(CORPUS_TGZ_SRC, dest)
    log("figs: staged corpus.tgz -> %s" % dest)
    return True


def run_figs():
    """Menu item #6: regenerate every figs/*.tex fragment from whatever
    is currently in raw_data/ (RUNALL.sh tolerates per-generator
    failures -- an ungenerated table just keeps its prior content),
    then compile list_figures.pdf. Runs in the foreground: this takes
    seconds, unlike a Sequencer leaf, so no daemonizing."""
    stage_corpus_tgz()
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
    # The lock goes BEFORE reset_summary_log: a refused invocation must
    # not truncate the live run's SUMMARY.log.  It is also past
    # interactive_select() (a Ctrl-C at the menu takes no lock) and
    # before go_background(), so the refusal reaches the operator's tty.
    if not args.plan_only:
        holder = acquire_run_lock()
        if holder is not None:
            print("REFUSED: another PAPER_DATA.py is running on this "
                  "box (%s).  Concurrent runs share /tmp/bora and "
                  "data/cache; wait for it or kill it first." % holder)
            return 7
        reset_summary_log(plan.top)

    if plan.top == "small":
        if args.plan_only:
            return 0
        return run_small()

    if plan.top == "clean":
        if args.plan_only:
            return 0
        return run_clean()

    if plan.top == "figs":
        if args.plan_only:
            return 0
        return run_figs()

    if plan.top in ("dna_debug", "dna_debug_full"):
        if args.plan_only:
            return 0
        mode = "dry" if plan.top == "dna_debug" else "full"
        # Both modes detach like small_full_snark: the leaf dumps
        # everything to SUMMARY.log / DNA_DEBUG_VERDICT.txt / the
        # bundle tgz, so no terminal needs to stay attached.
        ts = _ts()
        print("[paper_data %s] detaching into the background "
              "(survives logout; no nohup needed)." % ts)
        print("[paper_data %s]   summary log:    tail -F %s"
              % (ts, SUMMARY_LOG))
        print("[paper_data %s]   current job:    tail -F %s"
              % (ts, CURRENT_JOB_LOG))
        print("[paper_data %s]   verdict file:   %s"
              % (ts, DNA_DEBUG_VERDICT))
        sys.stdout.flush()
        go_background()
        install_signal_handlers()
        return run_dna_debug(mode)

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

    if plan.top == "v101":
        if args.plan_only:
            return 0
        # Hours long, single process at a time, and the whole point is
        # that nobody watches it: detach like small_full_dlp.
        ts = _ts()
        print("[paper_data %s] detaching into the background "
              "(survives logout; no nohup needed)." % ts)
        print("[paper_data %s]   summary log:    tail -F %s"
              % (ts, SUMMARY_LOG))
        print("[paper_data %s]   current job:    tail -F %s"
              % (ts, CURRENT_JOB_LOG))
        print("[paper_data %s]   budget:         %s from now "
              "(finish by %s; ZKR_V101_HOURS overrides)"
              % (ts, _v101_hm(_v101_run_seconds()),
                 time.strftime("%H:%M", time.localtime(
                     time.time() + _v101_run_seconds()))))
        print("[paper_data %s]   progress:       cat %s"
              % (ts, V101_PROGRESS))
        print("[paper_data %s]   verdict:        %s"
              % (ts, V101_VERDICT))
        print("[paper_data %s]   bundle on fail: %s"
              % (ts, V101_BUNDLE))
        sys.stdout.flush()
        go_background()
        install_signal_handlers()
        return run_v101()

    if plan.top == "scale_ab":
        if args.plan_only:
            return 0
        # Two dry sweeps back to back, same detach shape as
        # small_full_dlp: one CURRENT_JOB.log, no part2.
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
        try:
            return run_scale_ab()
        except Exception:
            # stdio is /dev/null after go_background(): without this the
            # traceback is lost and the run just stops (V101 lesson).
            log("scale_ab CRASHED:\n%s" % traceback.format_exc())
            return 1

    if plan.top == "small_full_dlp":
        if args.plan_only:
            return 0
        # Hours long and single-process, so it detaches exactly like
        # small_full_snark: one CURRENT_JOB.log, no part2.
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
        return run_small_full_dlp()

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
    # so the suite never contends with a LIVE run's lock (its main()
    # tests would otherwise be refused, rc 7) nor leaves one behind.
    "RUN_LOCK": "run.lock",
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

    def test_neo_env_pass_survives_the_scrub(self):
        """NEO_ENV_PASS knobs reach bora_cli; other ZKR_* still don't."""
        with mock.patch.dict(os.environ,
                              {"ZKR_NEO_LOAD_LADDER": "/tmp/l.json",
                               "ZKR_PROBE_DECLINE": "1",
                               "ZKR_FOO": "1"}):
            e = neo_env()
        self.assertEqual(e.get("ZKR_NEO_LOAD_LADDER"), "/tmp/l.json")
        self.assertEqual(e.get("ZKR_PROBE_DECLINE"), "1")
        self.assertNotIn("ZKR_FOO", e)


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


class SafePackDumpTest(unittest.TestCase):
    """R1's wrapper: never raises, so a crashed run keeps its bundle."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        p = mock.patch.object(_MOD, "RAW_DATA_ROOT",
                               os.path.join(self.tmp.name, "raw"))
        p.start()
        self.addCleanup(p.stop)
        self.ctx = mock.Mock()
        self.ctx._ts = "20260810_000000"

    def test_success_passes_dests_through(self):
        """A working pack returns its dests and notes nothing."""
        with mock.patch.object(_MOD, "pack_full_dump",
                                return_value=["/d/a.tgz"]) as pk:
            out = safe_pack_dump(self.ctx, "full_dlp", ["/l/r.log"], 0)
        self.assertEqual(out, ["/d/a.tgz"])
        pk.assert_called_once_with("full_dlp", ["/l/r.log"],
                                    "20260810_000000")
        self.ctx.note.assert_not_called()

    def test_missing_log_is_noted_not_raised(self):
        """A real pack of a non-existent log returns [] and notes."""
        out = safe_pack_dump(self.ctx, "full_dlp",
                              [os.path.join(self.tmp.name, "gone.log")],
                              3)
        self.assertEqual(out, [])
        self.ctx.note.assert_called_once()
        self.assertIn("rc=3", self.ctx.note.call_args[0][0])

    def test_partial_tmp_is_cleaned_up(self):
        """A raise mid-build leaves no *.tgz.tmp behind."""
        dest_dir = os.path.dirname(raw_data_path("full_dlp.tgz"))
        os.makedirs(dest_dir, exist_ok=True)
        stray = os.path.join(dest_dir, "full_dlp.part1.tgz.tmp")
        open(stray, "w").close()
        with mock.patch.object(_MOD, "pack_full_dump",
                                side_effect=OSError("boom")):
            out = safe_pack_dump(self.ctx, "full_dlp", ["/l/r.log"], 9)
        self.assertEqual(out, [])
        self.assertFalse(os.path.exists(stray))


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

    def test_nonzero_rc_still_packs(self):
        """R1: a failed spawn keeps rc=3 AND still places the dump --
        the .tgz is the run log, not a success artifact."""
        with mock.patch.object(_MOD, "resolve_process_model",
                                return_value=ProcessModel(1, [None])), \
             mock.patch.object(_MOD, "neo_env", return_value={}), \
             mock.patch.object(_MOD, "run_rust_example",
                                return_value=3), \
             mock.patch.object(_MOD, "pack_full_dump") as pk:
            rc = run_leaf_dlp("dry", self.ctx)
        self.assertEqual(rc, 3)
        pk.assert_called_once_with("full_dlp", ["/lp/run.log"],
                                    "20260810_000000")

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

    def test_ladder_divergence_still_packs(self):
        """R1: divergence keeps rc=5 and the note, but the log is
        still placed -- rc, not the dump, reports the failure."""
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
        pk.assert_called_once()
        self.ctx.note.assert_called_once()

    def test_missing_success_markers_still_packs(self):
        """R1: rc=6 with the note, and the dump is placed anyway."""
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
        pk.assert_called_once_with("full_dlp", ["/lp/run.log"],
                                    "20260810_000000")
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

    def test_nonzero_rc_still_packs(self):
        """R1: a failed spawn skips the marker check but still places
        the dump -- the .tgz is the run log, not a success artifact."""
        with mock.patch.object(_MOD, "neo_env", return_value={}), \
             mock.patch.object(_MOD, "run_rust_example",
                                return_value=3), \
             mock.patch.object(_MOD, "pack_full_dump") as pk:
            rc = run_leaf_dna("dry", self.ctx)
        self.assertEqual(rc, 3)
        pk.assert_called_once_with("full_dna", ["/lp/run.log"],
                                    "20260810_000000")

    def test_missing_success_markers_still_packs(self):
        """R1: rc=6 and the note when the positive markers are absent,
        and the dump is placed anyway."""
        with mock.patch.object(_MOD, "neo_env", return_value={}), \
             mock.patch.object(_MOD, "run_rust_example",
                                return_value=0), \
             mock.patch.object(_MOD, "dlp_missing_success",
                                return_value="no markers"), \
             mock.patch.object(_MOD, "pack_full_dump") as pk:
            rc = run_leaf_dna("dry", self.ctx)
        self.assertEqual(rc, 6)
        pk.assert_called_once_with("full_dna", ["/lp/run.log"],
                                    "20260810_000000")
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
        pk.assert_called_once()      # R1: placed despite rc=5


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


class EffectiveMissingSuccessTest(unittest.TestCase):
    # Shaped after bora_data_driver::fmt_tier_block's markers -- the
    # same strings effectiveness.py regexes for.
    FULL = ("=== Data for Mal ===\n"
            "=== Data for Dna ===\n"
            "=== Data for Dlp ===\n"
            "######## Filesize data for Mal ########\n"
            "######## Filesize data for Dlp ########\n"
            "#### END EFFECTIVENESS REPORT ####\n")

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.path = os.path.join(self.tmp.name, "eval_effective.txt")

    def _write(self, text):
        with open(self.path, "w") as f:
            f.write(text)

    def test_complete_and_fresh_passes(self):
        self._write(self.FULL)
        self.assertIsNone(effective_missing_success(self.path, 0))

    def test_absent_report(self):
        self.assertIn("no report",
                      effective_missing_success(self.path, 0))

    def test_stale_report_from_a_prior_run(self):
        self._write(self.FULL)
        os.utime(self.path, (1, 1))
        self.assertIn("stale",
                      effective_missing_success(self.path, time.time()))

    def test_missing_dataset_section(self):
        self._write(self.FULL.replace("Data for Dna", "x"))
        self.assertIn("Dna", effective_missing_success(self.path, 0))

    def test_missing_filesize_group(self):
        """Fig 9b's Dlp re-buckets are load-bearing, not decoration."""
        self._write(self.FULL.replace("Filesize data for Dlp", "x"))
        self.assertIn("Filesize data for Dlp",
                      effective_missing_success(self.path, 0))

    def test_truncated_before_end_banner(self):
        self._write(self.FULL.replace("END EFFECTIVENESS", "x"))
        self.assertIn("END banner",
                      effective_missing_success(self.path, 0))


class RunLeafEffectiveTest(unittest.TestCase):
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
        """Stand-in bora_cli, as the lkup twin: echoes panic-looking
        text into run.log, then writes `report` to args[2]."""
        ctx = JobHandle("effective", mode)
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
            return ctx, seen, run_leaf_effective(mode, ctx)

    def test_dry_perc_and_full_perc(self):
        _, seen, res = self._run("dry", 0,
                                  EffectiveMissingSuccessTest.FULL)
        self.assertEqual(seen["args"][:2],
                         ["effective", str(EFFECTIVE_DRY_PERC)])
        self.assertEqual(res.rc, 0)
        _, seen, res = self._run("full", 0,
                                  EffectiveMissingSuccessTest.FULL)
        self.assertEqual(seen["args"][:2], ["effective", "100"])
        self.assertFalse(res.failed)

    def test_places_as_eval_effective_txt_in_any_server(self):
        with mock.patch.object(_MOD, "place_raw_data",
                                return_value="/x") as pl:
            _, _, res = self._run("full", 0,
                                   EffectiveMissingSuccessTest.FULL)
        self.assertEqual(res.rc, 0)
        self.assertEqual(pl.call_args.args[1], "eval_effective.txt")
        self.assertFalse(pl.call_args.kwargs["server_specific"])

    def test_echoed_report_text_cannot_fail_the_leaf(self):
        """The collector println!s the report; sig names are arbitrary
        text, so the fail scan must not vote (b_fail_scan=False)."""
        _, _, res = self._run("full", 0,
                               EffectiveMissingSuccessTest.FULL)
        self.assertFalse(res.failed)

    def test_truncated_report_fails_and_places_nothing(self):
        with mock.patch.object(_MOD, "place_raw_data") as pl:
            ctx, _, res = self._run("dry", 0, "half a report\n")
        self.assertEqual(res.rc, 6)
        self.assertTrue(res.failed)
        pl.assert_not_called()
        self.assertTrue(any("effective:" in n for n in ctx._notes))


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


class RunScaleAbTest(unittest.TestCase):
    """The A/B driver: both arms must ALWAYS run, and a missing arm log
    must not raise.  Both were live defects on 2026-08-20 -- the leaf
    returns a LeafResult, so `rc = rc or leaf(...)` short circuited the
    v2 call the moment v1 returned an object, and the report then
    opened a log that was never written."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        p = mock.patch.object(_MOD, "JOB_LOG_DIR",
                               os.path.join(self.tmp.name, "logs"))
        p.start()
        self.addCleanup(p.stop)

    @staticmethod
    def _ok(rc=0, failed=False):
        return _MOD.LeafResult(rc=rc, wall_s=1.0, raw_data_written=[],
                                failed=failed, triage_tgz=None,
                                peak_rss_gb=1.0, note="")

    def test_runs_every_arm_even_after_a_failure(self):
        seen = []

        def fake(mode, ctx, arm=None):
            seen.append(arm)
            return self._ok(rc=7, failed=True)

        with mock.patch.object(_MOD, "run_leaf_scale_clamav", fake), \
             mock.patch.object(_MOD, "scale_ab_report",
                                return_value=[]), \
             mock.patch.object(_MOD, "_summary_line"), \
             mock.patch.object(_MOD, "log"):
            rc = _MOD.run_scale_ab()
        self.assertEqual(seen, list(_MOD.SCALE_AB_ARMS),
                          "a failing arm must not suppress the next")
        self.assertNotEqual(rc, 0, "a failed arm must be reported")

    def test_rc_zero_when_both_arms_pass(self):
        with mock.patch.object(_MOD, "run_leaf_scale_clamav",
                                lambda m, c, arm=None: self._ok()), \
             mock.patch.object(_MOD, "scale_ab_report",
                                return_value=[]), \
             mock.patch.object(_MOD, "_summary_line"), \
             mock.patch.object(_MOD, "log"):
            self.assertEqual(_MOD.run_scale_ab(), 0)

    def test_missing_arm_log_reports_instead_of_raising(self):
        good = os.path.join(self.tmp.name, "v1.log")
        open(good, "w").write(
            "==== SCALE ROUND BEGIN count=1 rules=1/38875 corpus=x ====\n"
            "==== SCALE ROUND END count=1 ====\n")
        gone = os.path.join(self.tmp.name, "nope.log")
        out = _MOD.scale_ab_report(good, gone, "tag")
        self.assertEqual(len(out), 1)
        self.assertIn("no comparison", out[0])
        self.assertEqual(_MOD.scale_rounds(gone), {})


class ScaleDbProbeTest(unittest.TestCase):
    """69210 probe parsing, and the guarantee that ZKR_DB_PHASE can
    reach a scale leaf but never a full one."""

    ROUND = (
        "==== SCALE ROUND BEGIN count=987 rules=987/9861 corpus=x ====\n"
        "[job 0] LOG1:  PERF 1010 build_and_tune[dlp_scale] cnt=987 "
        "db_ms=205400 disch_ms=0 tune_ms=500\n"
        "[job 0] LOG1:  DEBUG USE 69210.10: db split cnt=987 "
        "cfg_ms=400 build_ms=205000\n"
        "[job 0] LOG2: --  DEBUG USE 69210.3: Build_DB Step 1b: "
        "aggressive gatekeeper 171300 ms\n"
        "[job 0] LOG2: --  Bluld_DB: Step 2: Writing signatures 3 us\n"
        "[job 0] LOG2: --  Build_DB: Step 7: ADD all to lkup. "
        "Lkup size: 13600000 1000 ms\n"
        "[job 0] LOG2: --  DEBUG USE 69210.9: build_or_load: "
        "save cache 6900 ms\n"
        "==== SCALE ROUND END count=987 ====\n")

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)

    def _rounds(self, text):
        p = os.path.join(self.tmp.name, "s.log")
        open(p, "w").write(text)
        return _MOD.scale_rounds(p)

    def test_probe_lines_parse(self):
        """Split, per-step timings, the us unit, and step 7's inline
        "Lkup size" number all read correctly."""
        r = self._rounds(self.ROUND)[987]
        self.assertEqual((r["cfg_ms"], r["build_ms"]), (400, 205000))
        self.assertEqual(r["steps"]["Step 1b"], 171300.0)
        self.assertEqual(r["steps"]["Step 2"], 0.003)
        self.assertEqual(r["steps"]["Step 7"], 1000.0,
                          "step 7's inline size must not be read as ms")
        self.assertEqual(r["steps"]["save"], 6900.0)

    def test_probe_free_log_keeps_empty_defaults(self):
        """A sweep run without ZKR_DB_PHASE parses as it always did."""
        bare = ("==== SCALE ROUND BEGIN count=1 rules=1/9861 corpus=x "
                "====\n==== SCALE ROUND END count=1 ====\n")
        r = self._rounds(bare)[1]
        self.assertEqual((r["steps"], r["cfg_ms"], r["build_ms"]),
                          ({}, 0, 0))

    def test_steps_dict_not_shared_between_rounds(self):
        """dict(_SCALE_EMPTY) is shallow; each round needs its own."""
        rr = self._rounds(self.ROUND
                          + self.ROUND.replace("987", "1973"))
        self.assertIsNot(rr[987]["steps"], rr[1973]["steps"])

    def test_scale_env_passes_db_phase_but_neo_env_strips_it(self):
        """The isolation contract: scale leaves see the probe switch,
        full_dlp/full_clam/full_dna cannot."""
        with mock.patch.dict(os.environ, {"ZKR_DB_PHASE": "1"}):
            self.assertEqual(_MOD.scale_env().get("ZKR_DB_PHASE"), "1")
            self.assertNotIn("ZKR_DB_PHASE", _MOD.neo_env())
        self.assertNotIn("ZKR_DB_PHASE", _MOD.NEO_ENV_PASS,
                          "adding it here would leak into full runs")
        self.assertNotIn("ZKR_DB_FAST", _MOD.NEO_ENV_PASS,
                          "the fast DB arm must stay scale-only")
        self.assertEqual(_MOD.scale_env().get("ZKR_DB_FAST"), "1",
                          "sweeps take the fast arm by default")
        self.assertNotIn("ZKR_DB_FAST", _MOD.neo_env())

    def test_scale_env_absent_when_unset(self):
        """Unset stays unset -- no accidental always-on probes."""
        e = dict(os.environ)
        e.pop("ZKR_DB_PHASE", None)
        with mock.patch.dict(os.environ, e, clear=True):
            self.assertNotIn("ZKR_DB_PHASE", _MOD.scale_env())


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


class BundleCarriesDumpTest(unittest.TestCase):
    """R3: a failed leaf's triage bundle also holds the paper dump."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        for name, sub in (("JOB_LOG_DIR", "jobs"),
                           ("LOGS_DIR", "job_logs"),
                           ("FAILED_TGZ_DIR", "failed_tgz")):
            p = mock.patch.object(_MOD, name,
                                   os.path.join(self.tmp.name, sub))
            p.start()
            self.addCleanup(p.stop)

    def test_bundle_lists_the_placed_dump(self):
        """The dump appears under raw_data/ inside the BUNDLE tgz."""
        dump = os.path.join(self.tmp.name, "full_dlp.tgz")
        with open(dump, "w") as f:
            f.write("dump bytes\n")
        h = JobHandle("dlp", "dry")
        h.raw_data.append(dump)
        res = h.finish(3)
        self.assertTrue(res.failed)
        with tarfile.open(res.triage_tgz) as t:
            names = t.getnames()
        self.assertIn("raw_data/full_dlp.tgz", names)

    def test_absent_dump_is_skipped_not_fatal(self):
        """A raw_data entry that no longer exists is ignored."""
        h = JobHandle("dlp", "dry")
        h.raw_data.append("/nope/full_dlp.tgz")
        res = h.finish(3)
        with tarfile.open(res.triage_tgz) as t:
            names = t.getnames()
        self.assertNotIn("raw_data/full_dlp.tgz", names)


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
        # rss_ceiling_hit is spelled out: a bare Mock auto-creates a
        # TRUTHY attribute, so the negative case could not fail.
        self.ctx = mock.Mock(peak_rss_gb=0.0, peak_idle_s=0.0,
                              rss_ceiling_hit=False)
        self.kills = []
        self.summary = []

    def _next(self):
        if not self.samples:
            self.proc.returncode = 0        # child gone -> loop exits
            return ([], 0.0, 0.0, 0.0)
        return self.samples.pop(0)

    def run(self, stall_s=100, step=10.0, max_wall_s=0,
            max_rss_gb=0):
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
            _watch_child(self.proc, "/tmp/run.log", self.ctx,
                          max_wall_s, max_rss_gb)
        return self


class WatchChildTest(unittest.TestCase):
    def test_wall_cap_kills_a_busy_child(self):
        """THE regression test.  The wall cap used to hang off an
        `elif` on the progress branch, and `now` carries summed CPU
        time -- which advances at every poll for any compute-bound
        tree.  So the cap could only ever fire on an ALREADY IDLE
        process: never on the diverging tuner it exists to bound.
        Measured against the real function before the fix: busy child,
        cap 4 s, still alive at 19 s."""
        pr = _WatchProbe([([1], float(i), float(i), 1.0)
                          for i in range(40)]).run(stall_s=10_000,
                                                    max_wall_s=50)
        self.assertEqual(len(pr.kills), 1)
        self.assertTrue(any("WALL CAP" in s for s in pr.summary))

    def test_wall_cap_of_zero_never_fires(self):
        """Every pre-existing caller passes 0 and must be unaffected."""
        pr = _WatchProbe([([1], float(i), float(i), 1.0)
                          for i in range(40)]).run(stall_s=10_000)
        self.assertEqual(pr.kills, [])

    def test_a_busy_child_inside_its_cap_is_left_alone(self):
        pr = _WatchProbe([([1], float(i), float(i), 1.0)
                          for i in range(10)]).run(stall_s=10_000,
                                                    max_wall_s=10_000)
        self.assertEqual(pr.kills, [])

    def test_rss_ceiling_kills_and_flags_the_handle(self):
        """The flag is what tells the suite this was a RESOURCE
        outcome; without it dec_big's OOM guard read as a FAIL and
        printed BLOCKED BY over the NOTE calling the step optional."""
        pr = _WatchProbe([([1], 1.0, 1.0, 100.0),
                          ([1], 2.0, 2.0, 500.0)]).run(
                              stall_s=10_000, max_rss_gb=460.0)
        self.assertEqual(len(pr.kills), 1)
        self.assertTrue(pr.ctx.rss_ceiling_hit)
        self.assertTrue(any("OOM-GUARD" in s for s in pr.summary))

    def test_rss_under_the_ceiling_is_left_alone(self):
        pr = _WatchProbe([([1], float(i), float(i), 100.0)
                          for i in range(10)]).run(
                              stall_s=10_000, max_rss_gb=460.0)
        self.assertEqual(pr.kills, [])
        self.assertFalse(pr.ctx.rss_ceiling_hit)

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
        # args 4-5 are V101's max_wall_s / max_rss_gb; 0 = no cap,
        # which is what every pre-existing caller passes.
        fake_watch.assert_called_once_with(p, "/tmp/run.log", ctx, 0, 0)


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
        """A successful raise is re-read and passes the floor."""
        pm = {"/proc/sys/vm/max_map_count": "100\n"}
        with mock.patch("builtins.open", _fake_open(pm)), \
             mock.patch("subprocess.run") as run:
            def _raised(*a, **kw):
                pm["/proc/sys/vm/max_map_count"] = "1000\n"
                return mock.Mock(returncode=0)
            run.side_effect = _raised
            ensure_vma(1000)
            run.assert_called_once_with(
                ["sudo", "sysctl", "-w", "vm.max_map_count=1000"])

    def test_still_short_after_raise_aborts(self):
        """A failed sudo must QUIT, not warn: Rust catches it only
        after the DB build, and has false-passed."""
        pm = {"/proc/sys/vm/max_map_count": "65530\n"}
        with mock.patch("builtins.open", _fake_open(pm)), \
             mock.patch("subprocess.run") as run, \
             mock.patch.dict(os.environ, {}, clear=False):
            os.environ.pop("ZKR_SKIP_MAP_COUNT_CHECK", None)
            run.return_value.returncode = 1
            with self.assertRaises(SystemExit) as cm:
                ensure_vma(1073741824)
            self.assertIn("PREFLIGHT ABORT", str(cm.exception))
            self.assertIn("65530", str(cm.exception))

    def test_bypass_env_downgrades_abort_to_warn(self):
        """ZKR_SKIP_MAP_COUNT_CHECK is the SAME escape hatch Rust
        honours, so one bypass covers both gates."""
        pm = {"/proc/sys/vm/max_map_count": "65530\n"}
        with mock.patch("builtins.open", _fake_open(pm)), \
             mock.patch("subprocess.run") as run, \
             mock.patch.dict(os.environ,
                             {"ZKR_SKIP_MAP_COUNT_CHECK": "1"}):
            run.return_value.returncode = 1
            ensure_vma(1073741824)   # must not raise

    def test_already_high_enough_never_reaches_the_gate(self):
        """cur >= target returns BEFORE sudo, so a box already set up
        by sysctl.d never needs a tty."""
        with mock.patch("builtins.open",
                         _fake_open({"/proc/sys/vm/max_map_count":
                                     "2000000000\n"})), \
             mock.patch("subprocess.run") as run:
            ensure_vma(1073741824)
            run.assert_not_called()

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
            # two copies: the corpus.tgz staging, then the PDF placement
            self.assertEqual(copy2.call_count, 2)
            self.assertEqual(
                copy2.call_args_list[0].args,
                (CORPUS_TGZ_SRC,
                 raw_data_path("corpus.tgz", server_specific=False)))
            self.assertEqual(
                copy2.call_args_list[1].args,
                (os.path.join(RUN_DATA_DIR, "list_figures.pdf"),
                 PDF_PATH))

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


class StageCorpusTest(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.src = os.path.join(self.tmp.name, "corpus.tgz")
        for name, val in (("CORPUS_TGZ_SRC", self.src),
                           ("RAW_DATA_ROOT",
                            os.path.join(self.tmp.name, "raw"))):
            p = mock.patch.object(_MOD, name, val)
            p.start()
            self.addCleanup(p.stop)

    def test_stages_into_any_server(self):
        """The tracked manifest lands where datasets.py reads it."""
        with open(self.src, "w") as f:
            f.write("tgz-bytes")
        self.assertTrue(stage_corpus_tgz())
        dest = os.path.join(self.tmp.name, "raw", "any_server",
                            "corpus.tgz")
        self.assertEqual(open(dest).read(), "tgz-bytes")

    def test_missing_source_warns_not_raises(self):
        self.assertFalse(stage_corpus_tgz())


class RunCleanTest(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        # roots must sit under REPO/data/paper_data for the guard
        repo = self.tmp.name
        self.raw = os.path.join(repo, "data", "paper_data", "run_data",
                                "data", "raw_data")
        self.pdf = os.path.join(repo, "data", "paper_data", "pdf")
        for name, val in (("REPO", repo), ("RAW_DATA_ROOT", self.raw),
                           ("PDF_DIR", self.pdf)):
            p = mock.patch.object(_MOD, name, val)
            p.start()
            self.addCleanup(p.stop)

    def _seed(self):
        for d, files in (
                ("any_server", [".gitkeep", "corpus.tgz"]),
                ("jet1tb", [".gitkeep", "full_dna.tgz"]),
                ("jet1tb/extracted", ["inner.log"]),
                ("failed_tgz", [".gitkeep", "b.tgz"])):
            os.makedirs(os.path.join(self.raw, d), exist_ok=True)
            for fn in files:
                open(os.path.join(self.raw, d, fn), "w").write("x")
        os.makedirs(self.pdf)
        for fn in (".gitkeep", ".gitignore", "list_figures.pdf"):
            open(os.path.join(self.pdf, fn), "w").write("x")

    def test_wipes_data_keeps_tracked_markers(self):
        """Generated files go; .gitkeep/.gitignore and their dirs stay,
        so `git status` stays clean after a wipe."""
        self._seed()
        with mock.patch.object(_MOD, "_confirm_clean", return_value=0):
            self.assertEqual(run_clean(), 0)
        kept = []
        for root in (self.raw, self.pdf):
            for dp, _dirs, fns in os.walk(root):
                kept += [os.path.join(dp, f) for f in fns]
        self.assertEqual(
            sorted(os.path.basename(f) for f in kept),
            [".gitignore", ".gitkeep", ".gitkeep", ".gitkeep",
             ".gitkeep"])
        # a subdir with no tracked marker is pruned entirely
        self.assertFalse(
            os.path.isdir(os.path.join(self.raw, "jet1tb",
                                        "extracted")))
        self.assertTrue(os.path.isdir(os.path.join(self.raw,
                                                    "jet1tb")))

    def test_absent_roots_are_skipped(self):
        with mock.patch.object(_MOD, "_confirm_clean", return_value=0):
            self.assertEqual(run_clean(), 0)

    def test_guard_refuses_roots_outside_paper_data(self):
        """A mispatched root must die loudly, never delete -- and
        before the R4 prompts, so _confirm_clean is never reached."""
        with mock.patch.object(_MOD, "RAW_DATA_ROOT",
                                os.path.join(self.tmp.name, "els")), \
             mock.patch.object(_MOD, "_confirm_clean") as cf:
            with self.assertRaises(AssertionError):
                run_clean()
        cf.assert_not_called()


class CleanGateTest(unittest.TestCase):
    """R4: menu #5 announces 5 prompts and needs all of them."""

    def _ask(self, answers):
        it = iter(answers)
        return lambda _p: next(it)

    def test_five_yes_then_delete_proceeds(self):
        """All 5 answers correct -> 0, and the count is announced."""
        said = []
        with mock.patch.object(sys.stdin, "isatty", return_value=True), \
             mock.patch.object(_MOD, "log", side_effect=said.append):
            rc = _confirm_clean(self._ask(
                ["yes", "yes", "yes", "yes", "DELETE"]))
        self.assertEqual(rc, 0)
        self.assertTrue(any("confirm 5 times" in s for s in said))

    def test_a_no_midway_aborts(self):
        """A wrong answer at prompt 3 stops the run at prompt 3."""
        said = []
        with mock.patch.object(sys.stdin, "isatty", return_value=True), \
             mock.patch.object(_MOD, "log", side_effect=said.append):
            rc = _confirm_clean(self._ask(["yes", "yes", "no"]))
        self.assertEqual(rc, 1)
        self.assertTrue(any("aborted at prompt 3/5" in s for s in said))

    def test_last_prompt_demands_the_word_delete(self):
        """"yes" at prompt 5 is not enough -- it must be DELETE."""
        with mock.patch.object(sys.stdin, "isatty", return_value=True), \
             mock.patch.object(_MOD, "log"):
            rc = _confirm_clean(self._ask(
                ["yes", "yes", "yes", "yes", "yes"]))
        self.assertEqual(rc, 1)

    def test_non_tty_refuses_and_wipes_nothing(self):
        """Unattended (cron, pipe) run_clean returns 7, deletes none."""
        with mock.patch.object(sys.stdin, "isatty", return_value=False), \
             mock.patch.object(_MOD, "log"), \
             mock.patch.object(_MOD, "_wipe_generated") as wp:
            rc = run_clean()
        self.assertEqual(rc, 7)
        wp.assert_not_called()


class VerifyReportScannerTest(unittest.TestCase):
    """The new Rust report tokens must not move any leaf verdict."""

    LINES = [
        "[job 0] LOG1: VERIFY-FLAGS batch1[self]: qa=1 fs=0 kzg=1 "
        "verdict=REJECT",
        "[job 0] LOG1: VERIFY-SKIP batch2[self]: part 1 REJECT -- "
        "part 2 not evaluated",
        "[job 0] LOG1: VERIFY-FLAGS batch2[final]: c1=1 c2=1 c3=1 "
        "c4=1 c5=1 mh=7 n_pub=40 verdict=PASS",
        "[job 0] LOG1: VERIFY-FLAGS ind[final] i=3: idx=1 veval=1 "
        "vcom=1 keval=1 kzg=1 verdict=PASS",
    ]

    def test_matches_no_scanner(self):
        """None of the four scanners keys on the new tokens."""
        for ln in self.LINES:
            for name in ("FAIL_RE", "ADVISORY_RE", "VERIFY_FAIL_RE",
                          "DNA_DEBUG_ERR_RE"):
                self.assertIsNone(getattr(_MOD, name).search(ln),
                                   "%s matched %r" % (name, ln))

    def test_does_not_counterfeit_the_verify_markers(self):
        """VERIFY-FLAGS must not pass for the real success marker."""
        for ln in self.LINES:
            self.assertIsNone(VERIFY_IND_RE.search(ln))
            self.assertIsNone(FOLD_OK_RE.search(ln))

    def test_the_real_failure_line_still_matches(self):
        """The untouched driver ERR line still drives both scanners."""
        real = ("[job 0] ERR: Job 0 BATCH PROOF VERIFICATION FAILED "
                "(verify_batch returned false); continuing other jobs.")
        self.assertIsNotNone(VERIFY_FAIL_RE.search(real))
        self.assertIsNotNone(FAIL_RE.search(real))


class VmaTargetTest(unittest.TestCase):
    def test_target_covers_measured_full_dna_need(self):
        """full_dna's Rust preflight measured est 21,518,560 on
        2026-08-14; a floor below that re-breaks the leaf."""
        self.assertGreaterEqual(VMA_TARGET, 21_518_560)


class CleanTopResolutionTest(unittest.TestCase):
    def test_clean_needs_no_items_and_sits_at_5(self):
        """clean resolves top-only, and holds menu slot 5 by request."""
        self.assertEqual(resolve_plan("clean", None),
                          ResolvedPlan("clean", None, []))
        self.assertEqual([k for k, _ in TOP_CHOICES].index("clean") + 1,
                         5)


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

    def test_full_run_shows_measured_production_costs(self):
        """full_run's submenu quotes the measured full figures, never
        the dry tags, and its All carries the measured rollup."""
        buf = io.StringIO()
        with mock.patch("sys.stdout", buf):
            _show_submenu("full_run")
        out = buf.getvalue()
        self.assertIn("Dna [full ~5.4h, ~533GB]", out)
        self.assertIn("DLP [full ~5d x2 parts, ~262GB]", out)
        self.assertIn("Analyze lkup [full ~2.3h, ~71GB]", out)
        self.assertIn("Effectiveness [full ~2.4h, ~71GB]", out)
        self.assertNotIn("dry", out)
        hrs, gb, n_un = full_total()
        self.assertIn("(A) All [measured ~%sd, ~%dGB peak; %d leaves "
                      "unmeasured]" % (_fmt_min(hrs / 24.0), gb, n_un),
                      out)

    def test_full_cost_mirrors_leaf_keys(self):
        """FULL_COST rows pair 1:1 with DRY_COST -- a new leaf must
        land in BOTH tables or the full submenu mislabels it."""
        self.assertEqual([c[0] for c in FULL_COST], _LEAF_KEYS)

    def test_full_tag_forms(self):
        """Hours under 48 print as h, above as d; missing RSS drops
        the GB field; missing wall says not measured."""
        self.assertEqual(_full_tag(5.4, 533), "[full ~5.4h, ~533GB]")
        self.assertEqual(_full_tag(119.2, 262, " x2 parts"),
                          "[full ~5d x2 parts, ~262GB]")
        self.assertEqual(_full_tag(5.2, None), "[full ~5.2h]")
        self.assertEqual(_full_tag(None, None), "[full: not measured]")

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


class RunLockTest(unittest.TestCase):
    """acquire_run_lock: one holder at a time, and never stale (flock
    treats two fds on one file independently, even same-process)."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        patches = [
            mock.patch.object(_MOD, "RUN_LOCK",
                               os.path.join(self.tmp.name, "run.lock")),
            mock.patch.object(_MOD, "_run_lock_fd", None),
        ]
        for p in patches:
            p.start()
            self.addCleanup(p.stop)
        self.addCleanup(self._close_fd)

    def _close_fd(self):
        if _MOD._run_lock_fd is not None:
            os.close(_MOD._run_lock_fd)

    def test_first_acquire_succeeds_and_records_pid(self):
        """A free lock is granted and stamped with the holder's pid."""
        self.assertIsNone(acquire_run_lock())
        self.assertIsNotNone(_MOD._run_lock_fd)
        with open(_MOD.RUN_LOCK) as f:
            self.assertIn("pid %d" % os.getpid(), f.read())

    def test_acquire_refused_while_another_holds_it(self):
        """A lock held elsewhere is refused, naming that holder."""
        # an independent fd == another invocation, as far as flock cares
        other = os.open(_MOD.RUN_LOCK, os.O_RDWR | os.O_CREAT, 0o644)
        self.addCleanup(os.close, other)
        fcntl.flock(other, fcntl.LOCK_EX | fcntl.LOCK_NB)
        os.write(other, b"pid 424242 since earlier\n")
        holder = acquire_run_lock()
        self.assertIsNotNone(holder)
        self.assertIn("424242", holder)
        self.assertIsNone(_MOD._run_lock_fd)

    def test_reacquire_by_same_process_is_idempotent(self):
        """Our own held lock is not refused to us (main() re-entry)."""
        self.assertIsNone(acquire_run_lock())
        held = _MOD._run_lock_fd
        self.assertIsNone(acquire_run_lock())
        self.assertEqual(_MOD._run_lock_fd, held)

    def test_lock_freed_when_holder_fd_closes(self):
        """Closing the fd (as process death does) frees the lock."""
        self.assertIsNone(acquire_run_lock())
        os.close(_MOD._run_lock_fd)
        _MOD._run_lock_fd = None
        self.assertIsNone(acquire_run_lock())


class ClearDbCacheTest(unittest.TestCase):
    """clear_db_cache: wipes DB dirs, keeps logs/ and main/, and never
    raises on the file/symlink entries data/cache legitimately holds."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.cache = os.path.join(self.tmp.name, "cache")
        p = mock.patch.object(_MOD, "CACHE_DIR", self.cache)
        p.start()
        self.addCleanup(p.stop)

    def _seed(self):
        for d in ("dlp_neo_p0", "clam_neo_p1", "full_data", "logs",
                   "main"):
            os.makedirs(os.path.join(self.cache, d))
        open(os.path.join(self.cache, "logs", "log_job_0.txt"),
              "w").close()
        open(os.path.join(self.cache, "run_complete.sentinel"),
              "w").close()
        outside = os.path.join(self.tmp.name, "elsewhere")
        os.makedirs(outside)
        open(os.path.join(outside, "keepme"), "w").close()
        os.symlink(outside, os.path.join(self.cache, "numa_probe"))
        return outside

    def test_wipes_db_dirs_and_keeps_logs_and_main(self):
        """The DB caches go; LOGS_DIR and main/ survive intact."""
        self._seed()
        self.assertEqual(clear_db_cache(), [])
        left = sorted(os.listdir(self.cache))
        self.assertEqual(left, ["logs", "main"])
        self.assertTrue(os.path.isfile(
            os.path.join(self.cache, "logs", "log_job_0.txt")))

    def test_symlink_unlinked_not_followed(self):
        """A symlink entry is removed, its target left untouched."""
        outside = self._seed()
        clear_db_cache()
        self.assertFalse(
            os.path.lexists(os.path.join(self.cache, "numa_probe")))
        self.assertTrue(os.path.isfile(
            os.path.join(outside, "keepme")))

    def test_missing_cache_dir_is_a_noop(self):
        """No data/cache yet (fresh checkout) is not an error."""
        self.assertEqual(clear_db_cache(), [])

    def test_undeletable_entry_warns_and_continues(self):
        """One unremovable entry yields a warning, not an exception,
        and the other entries are still wiped."""
        self._seed()
        with mock.patch.object(_MOD.shutil, "rmtree",
                                side_effect=OSError("busy")):
            warns = clear_db_cache()
        self.assertTrue(any("full_data" in w for w in warns))
        self.assertTrue(os.path.isdir(
            os.path.join(self.cache, "dlp_neo_p0")))
        self.assertFalse(os.path.exists(
            os.path.join(self.cache, "run_complete.sentinel")))


class LeafWipeGateTest(unittest.TestCase):
    """_run_one_leaf wipes only for a full leaf AND only while this
    process holds the run lock (which the unit suite never does)."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.cache = os.path.join(self.tmp.name, "cache")
        os.makedirs(os.path.join(self.cache, "dlp_neo_p0"))
        patches = [
            mock.patch.object(_MOD, "CACHE_DIR", self.cache),
            mock.patch.object(_MOD, "SUMMARY_LOG",
                               os.path.join(self.tmp.name, "SUMMARY.log")),
            mock.patch.object(_MOD, "JOB_LOG_DIR",
                               os.path.join(self.tmp.name, "logs")),
            _sandbox_aborted(),
        ]
        for p in patches:
            p.start()
            self.addCleanup(p.stop)

    def _run(self, mode, lock_fd):
        specs = {"a": JobSpec("a", "a", lambda m, c: _leaf_result(False))}
        with mock.patch.object(_MOD, "JOB_SPECS", specs), \
             mock.patch.object(_MOD, "_run_lock_fd", lock_fd):
            Sequencer(_FakePlan("full_run", mode, ["a"])).run()
        return os.path.isdir(os.path.join(self.cache, "dlp_neo_p0"))

    def test_full_leaf_under_lock_wipes(self):
        """The intended case: full mode, lock held -> cache cleared."""
        self.assertFalse(self._run("full", 3))

    def test_full_leaf_without_lock_does_not_wipe(self):
        """No lock (the unit suite's own state) -> cache untouched."""
        self.assertTrue(self._run("full", None))

    def test_dry_leaf_under_lock_does_not_wipe(self):
        """Dry runs share the box's caches and must never wipe them."""
        self.assertTrue(self._run("dry", 3))


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
        # derived, not literal: "9" became a VALID index when the
        # effective leaf was appended (2026-08-14)
        with self.assertRaises(SystemExit):
            resolve_plan("dry_run", str(len(_LEAF_KEYS) + 1))
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
        """One past the last menu slot exits.  Derived, not hard-coded:
        a literal went stale the moment a top was appended."""
        past_end = str(len(TOP_CHOICES) + 1)
        with mock.patch("builtins.input", side_effect=[past_end]):
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

        # Stub EVERY key, derived from JOB_SPECS -- an explicit list
        # here went stale when the effective leaf was added, and the
        # test cargo-ran the REAL leaf (2026-08-14).
        specs = {key: JobSpec(key, key, stub_leaf(key, "Stage 2"))
                 for key in JOB_SPECS}
        p = mock.patch.object(_MOD, "JOB_SPECS", specs)
        p.start()
        self.addCleanup(p.stop)

    def test_full_leaf_plan_runs_end_to_end(self):
        # ensure_vma is FATAL since 2026-08-18 and a dev box is
        # typically below the floor; this test is about plan wiring,
        # not the kernel.  EnsureVmaTest owns that gate.
        with mock.patch("sys.argv",
                         ["prog", "--run", "dry_run", "--items", "A"]), \
             mock.patch.object(_MOD, "ensure_vma"), \
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


_V101_MANIFESTS = [
    os.path.join(REPO, "data", "debug", "full_clamav", "config",
                 "binexec_p%d.dat" % i) for i in range(8)]


def _v101_replay_corpus():
    """Re-derive (files, MB, raw chunks) per perc straight from the 8
    binexec manifests, transcribing bora_data_driver.rs fixed_perm /
    subset / count_of.  This is the ONLY check that can catch a
    mistyped V101_VEHICLES row."""
    mask = (1 << 64) - 1

    def fixed_perm(n, s):
        v = list(range(n))
        for i in range(n - 1, 0, -1):
            s = (s + 0x9E3779B97F4A7C15) & mask
            z = s
            z = ((z ^ (z >> 30)) * 0xBF58476D1CE4E5B9) & mask
            z = ((z ^ (z >> 27)) * 0x94D049BB133111EB) & mask
            z ^= z >> 31
            j = z % (i + 1)
            v[i], v[j] = v[j], v[i]
        return v

    files = []
    for p in _V101_MANIFESTS:
        with open(p) as f:
            files += [ln.strip() for ln in f if ln.strip()]
    sizes = [os.path.getsize(os.path.join(REPO, f)) for f in files]
    n = len(files)
    perm = fixed_perm(n - 1, 0x5CA15EED0F0F0F0F)

    def row(perc):
        keep = max(1, min(n, -(-n * perc // 100)))
        if keep >= n:
            idx = list(range(n))
        else:
            idx = sorted([0] + [i + 1 for i in perm[:keep - 1]])
        return (len(idx), sum(sizes[i] for i in idx) / 1e6,
                sum(-(-sizes[i] // 131072) for i in idx))
    return row


def _v101_corpus_present():
    if not all(os.path.isfile(p) for p in _V101_MANIFESTS):
        return False
    with open(_V101_MANIFESTS[0]) as f:
        first = f.readline().strip()
    return bool(first) and os.path.isfile(os.path.join(REPO, first))


class V101VehicleTableTest(unittest.TestCase):
    """The picker walks V101_VEHICLES top-down and takes the first
    fit, so the table's order and its numbers are both load-bearing."""

    def test_perc_is_strictly_descending_and_unique(self):
        """A non-descending row would make the picker take a SMALLER
        vehicle than the clock affords."""
        percs = [v[0] for v in _MOD.V101_VEHICLES]
        self.assertEqual(percs, sorted(set(percs), reverse=True))

    def test_every_column_grows_with_perc(self):
        """files/MB/chunks rise and the lkup share falls, monotonically
        -- a typo in one column shows up as a break here."""
        for a, b in zip(_MOD.V101_VEHICLES, _MOD.V101_VEHICLES[1:]):
            self.assertGreater(a[1], b[1], "files at perc %d" % a[0])
            self.assertGreater(a[2], b[2], "MB at perc %d" % a[0])
            self.assertGreater(a[3], b[3], "chunks at perc %d" % a[0])
            self.assertLess(a[4], b[4], "share at perc %d" % a[0])

    def test_perc_2_row_is_the_calib_vehicle(self):
        """_v101_recalibrate divides by this row; losing it silently
        falls back to the old hardcoded 110."""
        self.assertIn(2, [v[0] for v in _MOD.V101_VEHICLES])

    @unittest.skipUnless(_v101_corpus_present(),
                         "clam corpus not extracted (data/DOWNLOAD.py)")
    def test_rows_match_the_rust_subset_replay(self):
        """files and MB must equal subset()/fixed_perm() EXACTLY.
        NOTE the chunk check is weaker BY CONSTRUCTION: the table was
        built as replay x 1.0555, so re-deriving it the same way is
        circular and catches only transcription typos.  The padding
        factor itself is pinned independently below."""
        row = _v101_replay_corpus()
        for perc, files, mb, chunks, _share in _MOD.V101_VEHICLES:
            f, m, c = row(perc)
            self.assertEqual(files, f, "files at perc %d" % perc)
            self.assertAlmostEqual(mb, m, delta=0.05,
                                    msg="MB at perc %d" % perc)
            self.assertAlmostEqual(chunks, c * 1.0555,
                                    delta=max(3, 0.02 * chunks),
                                    msg="chunks at perc %d" % perc)

    @unittest.skipUnless(_v101_corpus_present(),
                         "clam corpus not extracted (data/DOWNLOAD.py)")
    def test_padding_factor_matches_the_logged_full_corpus(self):
        """The ONE independent anchor for the 1.0555 chunk factor: the
        reference run logged 6,549 padded chunks for the whole corpus.
        Without this the chunk column is self-referential."""
        _f, _m, raw = _v101_replay_corpus()(100)
        self.assertAlmostEqual(raw * 1.0555, 6549, delta=0.02 * 6549)


class V101ClockTest(unittest.TestCase):
    """The budget is a DURATION: same window whenever it starts."""

    def test_budget_is_a_duration_from_launch(self):
        """16 h from t0, not a fixed hour of the day."""
        t = time.mktime((2026, 8, 17, 20, 0, 0, 0, 0, -1))
        self.assertAlmostEqual(
            (_MOD._v101_deadline(t) - t) / 3600.0,
            _MOD.V101_RUN_HOURS, delta=0.01)

    def test_a_late_start_gets_the_same_budget(self):
        """The whole point of the change: under the old fixed-clock
        deadline a start at 23:00 got 13 h and one at 12:30 got 23.5,
        so the vehicle silently tracked the launch hour."""
        a = time.mktime((2026, 8, 17, 20, 0, 0, 0, 0, -1))
        b = time.mktime((2026, 8, 18, 12, 30, 0, 0, 0, -1))
        self.assertAlmostEqual(_MOD._v101_deadline(a) - a,
                               _MOD._v101_deadline(b) - b, delta=1.0)

    def test_env_override_is_honoured(self):
        t = 1000.0
        with mock.patch.dict(os.environ, {"ZKR_V101_HOURS": "2.5"}):
            self.assertAlmostEqual(_MOD._v101_deadline(t) - t,
                                   9000.0, delta=1.0)

    def test_a_bad_or_zero_override_falls_back(self):
        """Never run forever, never finish instantly."""
        for bad in ("", "abc", "0", "-3"):
            with mock.patch.dict(os.environ,
                                 {"ZKR_V101_HOURS": bad}):
                self.assertAlmostEqual(
                    _MOD._v101_run_seconds() / 3600.0,
                    _MOD.V101_RUN_HOURS, delta=0.01,
                    msg="override %r" % bad)

    def test_a_fixed_cap_is_clamped_to_the_time_left(self):
        """dec_big asks for 5 h; with 1 h left it gets 1 h minus the
        180 s report reserve, NOT 5 h through the deadline."""
        self.assertEqual(_MOD._v101_cap(18000, 3600), 3420)

    def test_a_fixed_cap_survives_when_there_is_room(self):
        self.assertEqual(_MOD._v101_cap(3600, 36000), 3600)

    def test_no_cap_means_take_the_room(self):
        self.assertEqual(_MOD._v101_cap(0, 3600), 3420)

    def test_cap_never_goes_below_the_floor(self):
        """Even past the deadline the cap stays positive, so a step
        that does start still terminates."""
        self.assertEqual(_MOD._v101_cap(18000, -500), 60)


class V101PickerReserveTest(unittest.TestCase):
    """The picker must leave the decider steps their room."""

    def setUp(self):
        self.model = dict(_MOD.V101_PRIORS)
        self.model["r_probe"] = 0.55        # post-C3

    def test_reserve_shrinks_the_chosen_vehicle(self):
        """assertLess, not assertLessEqual: <= is a property of any
        descending-table picker and passes with the reserve set to 0,
        so it cannot detect the reserve being removed."""
        left = 13 * 3600
        big, _ = _MOD.v101_pick(self.model, left, lambda *_a: None)
        small, _ = _MOD.v101_pick(self.model,
                                   left - _MOD.V101_DEC_RESERVE_S,
                                   lambda *_a: None)
        self.assertIsNotNone(big)
        self.assertIsNotNone(small)
        self.assertLess(small[0], big[0])

    def test_the_caps_handed_out_fit_the_budget_promised(self):
        """The picker must size against the CAPS the A/B steps get,
        not the bare estimate: comparing the estimate to 0.85 x room
        while granting 1.3 x the estimate spent 10% more than the
        whole room, quietly eating the decider reserve."""
        left = 13 * 3600
        veh, _ = _MOD.v101_pick(self.model, left, lambda *_a: None)
        self.assertIsNotNone(veh)
        caps = _MOD.V101_AB_CAP_MULT * sum(
            _MOD.v101_cost(self.model, veh, p)
            for p in (_MOD.V101_V1_PASSES, _MOD.V101_V2_PASSES))
        self.assertLessEqual(caps, left)

    def test_a_full_clock_still_reaches_a_real_vehicle(self):
        """16 h minus the reserve must still afford more than the
        perc-2 calibration vehicle, else the A/B proves nothing."""
        left = 15 * 3600 - _MOD.V101_DEC_RESERVE_S
        veh, _ = _MOD.v101_pick(self.model, left, lambda *_a: None)
        self.assertIsNotNone(veh)
        self.assertGreaterEqual(veh[0], 20)

    def test_no_time_returns_none_not_a_crash(self):
        veh, pred = _MOD.v101_pick(self.model, 10, lambda *_a: None)
        self.assertIsNone(veh)
        self.assertIsNone(pred)


class V101ProgressTest(unittest.TestCase):
    """`cat V101_PROGRESS.txt` has to work mid-step, not just after."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        p = mock.patch.object(
            _MOD, "V101_PROGRESS",
            os.path.join(self.tmp.name, "V101_PROGRESS.txt"))
        p.start()
        self.addCleanup(p.stop)
        self.res = {k: _MOD.V101Res(k)
                    for k in ("build", "units", "seed")}
        self.res["build"].status = "OK"
        self.res["build"].wall_s = 300.0

    def _text(self):
        return _MOD.v101_progress_text(
            time.time() - 600, time.time() + 3600, self.tmp.name,
            self.res, None, dict(_MOD.V101_PRIORS))

    def test_running_step_shows_elapsed_not_zero(self):
        """A RUNNING row reports time-in-flight; r.wall_s is still 0."""
        self.res["units"].status = "RUNNING"
        self.res["units"].t_start = time.time() - 7200
        self.res["units"].cap_s = 10800
        rows = dict((r[0], r) for r in _MOD._v101_step_rows(self.res))
        self.assertEqual(rows["units"][1], "RUNNING")
        self.assertGreater(rows["units"][2], 7000)
        self.assertIn("2h00m", self._text())

    def test_pending_steps_are_listed_before_they_run(self):
        """All 3 rows appear even though only one has finished."""
        t = self._text()
        for k in ("build", "units", "seed"):
            self.assertIn(k, t)
        self.assertIn("PENDING", t)
        self.assertIn("1/3 settled", t)

    def test_failures_line_names_the_bundle(self):
        self.res["seed"].status = "FAIL"
        t = self._text()
        self.assertIn("FAILED STEPS SO FAR: seed", t)
        self.assertIn(_MOD.V101_BUNDLE, t)

    def test_write_is_atomic_and_symlinked(self):
        """The stable path is a symlink and no .tmp is left behind."""
        _MOD._v101_write_progress(self.tmp.name, self._text())
        self.assertTrue(os.path.islink(_MOD.V101_PROGRESS))
        with open(_MOD.V101_PROGRESS) as f:
            self.assertIn("V101 SUITE PROGRESS", f.read())
        self.assertFalse(os.path.exists(
            os.path.join(self.tmp.name, "progress.txt.tmp")))

    def test_verdict_and_progress_share_one_renderer(self):
        """Assert on the step-row TEXT, not on bare words: 'seed' and
        'FAIL' both occur elsewhere in the verdict (falsifier labels,
        the BLOCKED BY line), so matching those would pass even with
        the shared renderer removed."""
        self.res["seed"].status = "FAIL"
        self.res["seed"].why = "no V2 QM SEED line"
        row = [r for r in _MOD._v101_step_rows(self.res)
               if r[0] == "seed"][0]
        rendered = "  %-10s %-8s" % (row[0], row[1])
        verdict = _MOD.v101_report(
            time.time() - 600, time.time() + 3600, self.tmp.name,
            self.res, None, dict(_MOD.V101_PRIORS))
        self.assertIn(rendered, verdict)
        self.assertIn(rendered, self._text())
        self.assertIn("no V2 QM SEED line", verdict)


class V101BundleTest(unittest.TestCase):
    """One downloadable tarball, written after ANY failure."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.run_dir = os.path.join(self.tmp.name, "run")
        os.makedirs(os.path.join(self.run_dir, "seed"))
        with open(os.path.join(self.run_dir, "detail.log"), "w") as f:
            f.write("detail line\n")
        with open(os.path.join(self.run_dir, "seed", "run.log"),
                   "w") as f:
            f.write("seed log\n")
        p = mock.patch.object(
            _MOD, "V101_BUNDLE",
            os.path.join(self.tmp.name, "V101_BUNDLE.tgz"))
        p.start()
        self.addCleanup(p.stop)
        self.res = {"seed": _MOD.V101Res("seed", status="FAIL")}

    def _names(self, path):
        with tarfile.open(path) as t:
            return t.getnames()

    def test_bundle_carries_the_run_dir_and_a_manifest(self):
        out = _MOD._v101_bundle(self.run_dir, self.res, "test",
                                 lambda *_a: None)
        names = self._names(out)
        self.assertIn("MANIFEST.txt", names)
        self.assertIn("detail.log", names)
        self.assertIn(os.path.join("seed", "run.log"), names)
        self.assertTrue(os.path.islink(_MOD.V101_BUNDLE))

    def test_bundle_carries_the_per_step_triage_tgz(self):
        """JobHandle's own bundle rides along, so ONE scp is enough."""
        tri = os.path.join(self.tmp.name, "triage_seed.tgz")
        with tarfile.open(tri, "w:gz") as t:
            t.add(os.path.join(self.run_dir, "detail.log"),
                  arcname="x.log")
        self.res["seed"].tgz = tri
        out = _MOD._v101_bundle(self.run_dir, self.res, "test",
                                 lambda *_a: None)
        self.assertIn("triage/triage_seed.tgz", self._names(out))

    def test_a_huge_log_is_truncated_head_plus_tail(self):
        """A 200 MB run.log must not make the bundle unscp-able."""
        big = os.path.join(self.run_dir, "seed", "big.log")
        with open(big, "wb") as f:
            f.write(b"H" * 1000)
            f.write(b"M" * (30 * 1000 * 1000))
            f.write(b"T" * 1000)
        with mock.patch.object(_MOD, "V101_BUNDLE_KEEP_MB", 1.0), \
             mock.patch.object(_MOD, "V101_BUNDLE_HEAD_MB", 0.2), \
             mock.patch.object(_MOD, "V101_BUNDLE_TAIL_MB", 0.3):
            out = _MOD._v101_bundle(self.run_dir, self.res, "test",
                                     lambda *_a: None)
            names = self._names(out)
            arc = os.path.join("seed", "big.log")
            self.assertIn(arc + ".TRUNCATED", names)
            self.assertNotIn(arc, names)
            with tarfile.open(out) as t:
                body = t.extractfile(arc + ".TRUNCATED").read()
        self.assertTrue(body.startswith(b"H" * 1000))
        self.assertTrue(body.endswith(b"T" * 1000))
        self.assertIn(b"V101 BUNDLE TRUNCATED", body)
        self.assertLess(len(body), 1_000_000)

    def test_rebundling_does_not_nest_the_previous_bundle(self):
        """The bundle lives IN run_dir; a second call must skip it."""
        _MOD._v101_bundle(self.run_dir, self.res, "first",
                           lambda *_a: None)
        out = _MOD._v101_bundle(self.run_dir, self.res, "second",
                                 lambda *_a: None)
        self.assertNotIn("bundle.tgz", self._names(out))

    def test_a_broken_run_dir_never_raises(self):
        """A bundle failure must not take the suite down with it."""
        said = []
        out = _MOD._v101_bundle("/nonexistent/run", self.res, "x",
                                 said.append)
        self.assertEqual(out, "")
        self.assertTrue(any("bundle FAILED" in s for s in said))


class V101RecalibrateTest(unittest.TestCase):
    def test_calib_divides_by_the_table_not_a_literal(self):
        """The perc-2 chunk count comes FROM the table: with the row
        changed, r_probe follows it and not the 110 fallback."""
        model = dict(_MOD.V101_PRIORS)
        table = [(40, 484, 272.0, 2357, 45),
                 (2, 25, 12.3, 500, 1011)]      # 500 != the 110 default
        r = _MOD.V101Res("calib", wall_s=1000.0,
                          nums={"probe_ms": 55000, "v5_ms": 110000})
        with mock.patch.object(_MOD, "V101_VEHICLES", table):
            _MOD._v101_recalibrate(model, "calib", r, None,
                                    lambda *_a: None)
        self.assertAlmostEqual(model["r_probe"], 55.0 / 500, places=6)
        self.assertAlmostEqual(model["k5"], 2.0, places=6)

    def test_measured_coefficients_are_tagged_in_the_model_line(self):
        """A prior must not print like a measurement.  The trailing
        legend also contains a '*', so only the coefficients count."""
        def coeffs(m):
            return _MOD._v101_model_line(m).split("   (*")[0]
        model = dict(_MOD.V101_PRIORS)
        self.assertNotIn("*", coeffs(model))
        r = _MOD.V101Res("calib", wall_s=1000.0,
                          nums={"probe_ms": 55000, "v5_ms": 110000})
        _MOD._v101_recalibrate(model, "calib", r, None,
                                lambda *_a: None)
        line = coeffs(model)
        self.assertIn("r_probe=", line)
        self.assertRegex(line, r"r_probe=[\d.]+s/chunk\*")
        self.assertNotRegex(line, r"t_db=\d+s\*")   # still a prior
        self.assertIn("measured this run",
                      _MOD._v101_model_line(model))

    def test_calib_v1_measures_the_whole_arm_rate(self):
        """calib_v1 yields r_v1_arm, which v101_cost then prefers over
        the C3-contaminated analytic model."""
        model = dict(_MOD.V101_PRIORS)
        vh = dict((v[0], v) for v in _MOD.V101_VEHICLES)[2]
        setup = model["t_db"] + model["r_disch"] * vh[2]
        r = _MOD.V101Res("calib_v1", wall_s=setup + 1100.0,
                          nums={"v1_bumps": 2})
        _MOD._v101_recalibrate(model, "calib_v1", r, None,
                                lambda *_a: None)
        self.assertAlmostEqual(model["r_v1_arm"], 1100.0 / vh[3],
                                places=6)
        big = (30, 363, 175.1, 1539, 71)
        want = (model["t_db"] + model["r_disch"] * 175.1
                + model["r_v1_arm"] * 1539)
        self.assertAlmostEqual(
            _MOD.v101_cost(model, big, _MOD.V101_V1_PASSES), want,
            places=4)

    def test_v1_arm_is_priced_above_v2_without_a_measurement(self):
        """C3 is v2-only, so the fallback model must charge v1 more
        per chunk -- pricing both at the calibrated (C3) rate is what
        made ab_v1 unable to make its cap."""
        model = dict(_MOD.V101_PRIORS)
        veh = (30, 363, 175.1, 1539, 71)
        c1 = _MOD.v101_cost(model, veh, _MOD.V101_V1_PASSES)
        c2 = _MOD.v101_cost(model, veh, _MOD.V101_V2_PASSES)
        self.assertGreater(c1, c2)
        model["r_probe"] *= 2
        self.assertGreater(
            _MOD.v101_cost(model, veh, _MOD.V101_V1_PASSES), c1)


# Real log fragments.  Every marker below is quoted from the emit site
# (batch_proc.rs:800/1025/1149, bora_data_driver.rs:2265/2318/2370),
# not from a healthy log -- the two decider gates that shipped broken
# were both written by reading a log in which nothing had failed.
_V101_DEC_OK = """\
VERIFY-FLAGS batch1[self]: qa=1 fs=1 kzg=1 verdict=PASS
VERIFY-FLAGS ind[self] i=0: idx=1 veval=1 vcom=1 verdict=PASS
VERIFY-FLAGS batch1[final]: qa=1 fs=1 kzg=1 verdict=PASS
VERIFY-FLAGS batch2[final]: c1=1 c2=1 c3=1 c4=1 c5=1 verdict=PASS
VERIFY-FLAGS ind[final] i=0: idx=1 veval=1 kzg=1 verdict=PASS
determine_config_non_aggr CONVERGED @iter 1: steps=10
"""
_V101_DEC_SNARK_REJECT = _V101_DEC_OK.replace(
    "c5=1 verdict=PASS", "c5=0 verdict=REJECT")
# Three [final] PASS markers and NOT ONE of them from the Groth16
# decider: the count gate alone waves this through.
_V101_DEC_NO_SNARK = _V101_DEC_OK.replace(
    "VERIFY-FLAGS batch2[final]", "VERIFY-FLAGS batchX[final]")


class V101ParseTest(unittest.TestCase):
    """v101_parse decides what the verdict can see; it had no tests."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)

    def _parse(self, key, text):
        p = os.path.join(self.tmp.name, "run.log")
        with open(p, "w") as f:
            f.write(text)
        r = _MOD.V101Res(key)
        _MOD.v101_parse(key, p, r)
        return r.nums

    def test_reject_is_the_failure_token_not_fail(self):
        """batch_proc.rs emits REJECT.  Grepping 'verdict=FAIL' made
        this counter permanently 0 -- a vacuous gate, twice shipped."""
        n = self._parse("dec_v2", _V101_DEC_SNARK_REJECT)
        self.assertEqual(n["verify_fail"], 1)
        self.assertEqual(n["verify_pass"], 4)

    def test_three_final_markers_are_counted_separately(self):
        n = self._parse("dec_v2", _V101_DEC_OK)
        self.assertEqual(n["verify_final"], 3)
        self.assertEqual(n["verify_snark"], 1)

    def test_build_bump_counts_as_a_bump_round(self):
        """bora_data_driver.rs:2265.  The old regex saw only :2318, so
        a real bump printed alongside 'bumps=0'."""
        n = self._parse("calib", 'v2 iter 0: BUILD bump '
                        '[("comp_sig::subsigs_igc", 2)], round 0 ms\n')
        self.assertEqual(n["v2_bumps"], 1)

    def test_word_failure_bump_also_counts(self):
        n = self._parse("calib", "v2 iter 1: 7 of 40 words failed, "
                        'round 90 ms, bumped [("x", 2)]\n')
        self.assertEqual(n["v2_bumps"], 1)

    def test_subset_promotion_is_a_round_but_not_a_bump(self):
        """bora_data_driver.rs:2306 is not a CapErr bump."""
        n = self._parse("calib", "v2 iter 2: subset clean, promoting "
                        "to full corpus; round 5 ms\n")
        self.assertEqual(n["v2_bumps"], 0)

    def test_qm_real_bumps_are_counted_apart(self):
        """The one bump M2 must make impossible."""
        n = self._parse("calib", "v2 iter 0: 3 of 9 words failed, "
                        'round 1 ms, bumped '
                        '[("dis_adv::neo_qm_real", 5509)]\n')
        self.assertEqual(n["v2_qm_bumps"], 1)
        self.assertEqual(n["v2_bumps"], 1)


class V101StepVerdictTest(unittest.TestCase):
    """_v101_verdict_step turns a log into OK/FAIL; it had no tests."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)

    def _verdict(self, key, text, rc=0, cap=3600, wall=10.0,
                 cap_s=3600):
        p = os.path.join(self.tmp.name, "run.log")
        with open(p, "w") as f:
            f.write(text)
        st = _MOD.V101Step(key, key, [], {}, cap_s, False)
        r = _MOD.V101Res(key, wall_s=wall)
        _MOD.v101_parse(key, p, r)
        res = mock.Mock(rc=rc, triage_tgz="/tmp/t.tgz")
        return _MOD._v101_verdict_step(st, r, res, cap)

    def test_an_unreadable_log_is_not_zero_hits(self):
        """Fail-OPEN primitive: returning 0 for a missing log made
        every bump counter read "zero bumps"."""
        self.assertIsNone(
            _MOD._v101_count("/nonexistent/nope.log", r"x"))
        # Built at runtime: a literal here would be IN this file,
        # which is the file being searched.
        self.assertEqual(
            _MOD._v101_count(__file__, "q" + "9" * 40), 0)

    def test_an_unreadable_decider_log_fails_closed(self):
        """None < 3 raises; and absence of proof is not proof."""
        st = _MOD.V101Step("dec_v2", "d", [], {}, 3600, True)
        r = _MOD.V101Res("dec_v2", wall_s=10.0,
                          nums={"verify_final": None,
                                "verify_fail": None})
        res = mock.Mock(rc=0, triage_tgz="")
        status, why = _MOD._v101_verdict_step(st, r, res, 3600)
        self.assertEqual(status, "FAIL")
        self.assertIn("unreadable", why)

    def test_healthy_decider_is_ok(self):
        self.assertEqual(self._verdict("dec_v2", _V101_DEC_OK)[0],
                          "OK")

    def test_rejected_groth16_proof_is_a_failure(self):
        """THE regression test: 4 PASS markers and one REJECT used to
        report OK, because the gate only asked for >=1 PASS."""
        status, why = self._verdict("dec_v2", _V101_DEC_SNARK_REJECT)
        self.assertEqual(status, "FAIL")
        self.assertIn("REJECT", why)

    def test_missing_batch2_line_is_a_failure(self):
        """batch1 failing early-returns and OMITS batch2 entirely, so
        counting PASS markers cannot see it."""
        text = _V101_DEC_OK.replace(
            "VERIFY-FLAGS batch2[final]: c1=1 c2=1 c3=1 c4=1 c5=1 "
            "verdict=PASS\n", "")
        status, why = self._verdict("dec_v2", text)
        self.assertEqual(status, "FAIL")
        self.assertIn("2 of 3", why)

    def test_decider_with_no_verify_at_all_is_a_failure(self):
        status, why = self._verdict("dec_v1", "nothing happened\n")
        self.assertEqual(status, "FAIL")
        self.assertIn("of 3", why)

    def test_seed_ok_needs_the_by_design_panic_marker(self):
        text = ("V2 QM SEED: cs=36860 igc=1 floors=(0,0) words=14 "
                "mid_hits=3 skipped=0 elapsed=200 ms\n"
                "V101 SEED-ONLY DRY FIRE: stop after seed\n")
        self.assertEqual(self._verdict("seed", text, rc=101)[0], "OK")

    def test_seed_crash_after_the_seed_line_is_not_forgiven(self):
        """Without narrowing, ANY nonzero rc was excused once the seed
        line existed."""
        text = ("V2 QM SEED: cs=36860 igc=1 mid_hits=3 skipped=0 "
                "elapsed=200 ms\nsegfault somewhere else\n")
        status, why = self._verdict("seed", text, rc=139)
        self.assertEqual(status, "FAIL")
        self.assertIn("SEED-ONLY marker", why)

    def test_a_nonzero_rc_fails_and_names_the_bundle(self):
        """Untested until now: the plainest failure in the suite."""
        text = "V2 CONVERGED @iter 1: qm_real 36860/1\n"
        status, why = self._verdict("calib", text, rc=101)
        self.assertEqual(status, "FAIL")
        self.assertIn("rc=101", why)
        self.assertIn(".tgz", why)

    def test_a_tuner_that_never_converged_fails_at_rc_zero(self):
        """cargo prints ok while foldpot logs the failure, so the
        POSITIVE marker is the only real test (consts.rs:67-77)."""
        for key, want in (("ab_v2", "no V2 CONVERGED line"),
                          ("calib", "no V2 CONVERGED line"),
                          ("smoke_v2", "no V2 CONVERGED line"),
                          ("ab_v1", "CONVERGED line"),
                          ("smoke_v1", "CONVERGED line")):
            with self.subTest(step=key):
                status, why = self._verdict(key, "nothing useful\n")
                self.assertEqual(status, "FAIL")
                self.assertIn(want, why)

    def test_clock_clamped_timeout_says_so(self):
        """A cap cut down by the deadline is a scheduling outcome, not
        a hang, and must not read like one."""
        status, why = self._verdict("dec_v2", _V101_DEC_OK, wall=990.0,
                                     cap=1000, cap_s=18000)
        self.assertEqual(status, "TIMEOUT")
        self.assertIn("clock-clamped", why)

    def test_three_final_markers_without_the_decider_still_fail(self):
        """The count gate is not enough: batch2[final] IS the Groth16
        decider, and three other PASS markers can make the count."""
        status, why = self._verdict("dec_v2", _V101_DEC_NO_SNARK)
        self.assertEqual(status, "FAIL")
        self.assertIn("batch2[final]", why)

    def test_an_oom_guard_kill_is_a_skip_not_a_failure(self):
        """dec_big is opportunistic and RAM-guarded; a box that is too
        small is a resource outcome, not a defect in the decider."""
        r = _MOD.V101Res("dec_big", wall_s=100.0, rss_gb=470.0)
        st = _MOD.V101Step("dec_big", "d", [], {}, 18000, True,
                            max_rss_gb=460.0)
        res = mock.Mock(rc=-9, triage_tgz="")
        status, why = _MOD._v101_verdict_step(st, r, res, 18000,
                                               rss_hit=True)
        self.assertEqual(status, "SKIP")
        self.assertIn("OOM-GUARD", why)

    def test_without_the_flag_the_same_kill_is_a_failure(self):
        """The control: the demotion must hang off the flag, not off
        dec_big's name."""
        r = _MOD.V101Res("dec_big", wall_s=100.0, rss_gb=470.0)
        st = _MOD.V101Step("dec_big", "d", [], {}, 18000, True,
                            max_rss_gb=460.0)
        res = mock.Mock(rc=-9, triage_tgz="")
        self.assertEqual(
            _MOD._v101_verdict_step(st, r, res, 18000)[0], "FAIL")

    def test_the_two_cargo_steps_share_one_wall_cap(self):
        """`units` runs three filters off one budget and the first
        may recompile zkregplus in cfg(test) -- a compile `build`
        does not do -- so it must not be capped tighter."""
        caps = dict((st.key, st.cap_s) for st in _MOD.v101_steps())
        self.assertEqual(caps["units"], 3600)
        self.assertEqual(caps["build"], 3600)

    def test_a_real_hang_is_a_plain_timeout(self):
        status, why = self._verdict("dec_v2", _V101_DEC_OK, wall=3590.0,
                                     cap=3600, cap_s=3600)
        self.assertEqual(status, "TIMEOUT")
        self.assertNotIn("clock-clamped", why)


class V101ReportGateTest(unittest.TestCase):
    """The verdict's DECIDE line is the deliverable a later session
    reads; it must never claim more than was measured."""

    def _report(self, statuses, nums=None):
        keys = [s.key for s in _MOD.v101_steps()]
        R = {}
        for k in keys:
            R[k] = _MOD.V101Res(k, status=statuses.get(k, "OK"),
                                 wall_s=60.0,
                                 nums=dict((nums or {}).get(k, {})))
        return _MOD.v101_report(time.time() - 60, time.time() + 3600,
                                 "/tmp/none", R, None,
                                 dict(_MOD.V101_PRIORS))

    def test_all_skipped_is_inconclusive_not_a_pass(self):
        """THE regression test: 10 of 12 steps SKIP, every falsifier
        N/A, and the old text said 'propose the commit'."""
        txt = self._report(dict((k, "SKIP") for k in
                                ("units", "seed", "calib", "ab_v1",
                                 "ab_v2", "dec_v2", "dec_big")))
        self.assertIn("INCONCLUSIVE", txt)
        self.assertNotIn("propose the commit", txt)

    def test_missing_v2_arm_alone_blocks_the_green_line(self):
        txt = self._report({"ab_v2": "SKIP"})
        self.assertIn("INCONCLUSIVE", txt)
        self.assertIn("ab_v2", txt)
        self.assertNotIn("propose the commit", txt)

    def test_a_failed_step_blocks_and_is_named(self):
        txt = self._report({"calib": "FAIL"})
        self.assertIn("BLOCKED BY: calib", txt)
        self.assertNotIn("propose the commit", txt)

    def test_dec_big_skip_is_called_out_but_not_fatal(self):
        """It is opportunistic -- but silence about it would let a
        reader assume production-width evidence exists."""
        txt = self._report({"dec_big": "SKIP"})
        self.assertIn("dec_big", txt)
        self.assertNotIn("propose the commit", txt)   # falsifiers N/A

    def test_green_needs_every_falsifier_to_pass(self):
        """All steps OK, all evidence present and correct."""
        nums = {
            "units": {"units_oks": 3},
            "seed": {"seed_cs": 36860, "mid_hits": 3, "skipped": 0,
                     "seed_ms": 120000},
            "ab_v1": {"v1_iters": 4, "v1_bumps": 4},
            "ab_v2": {"v2_iters": 0, "v2_bumps": 0, "v2_qm_bumps": 0,
                      "meter_demand_cs": 36860, "shipped_qm": 36860,
                      "caperr_units": 0, "v5_ms": 100, "probe_ms": 90},
        }
        txt = self._report({}, nums)
        self.assertIn("propose the commit", txt)
        self.assertNotIn("N/A", txt)

    def test_a_loose_seed_is_reported_but_does_not_block(self):
        """The seed is a declared UPPER BOUND that M3 tightens, so 10x
        is loose, not unsound: F1 passes, F1b warns."""
        nums = {"seed": {"seed_cs": 368600, "mid_hits": 3,
                          "skipped": 0, "seed_ms": 120000}}
        txt = self._report({}, nums)
        f1 = [l for l in txt.splitlines()
              if l.strip().startswith("F1 seed")][0]
        f1b = [l for l in txt.splitlines()
               if l.strip().startswith("F1b")][0]
        self.assertIn("PASS", f1)
        self.assertIn("WARN", f1b)
        self.assertIn("10.00x", f1b)

    def test_a_seed_over_the_ram_alarm_blocks(self):
        """Loose is absorbed; past the spec's R-2 RAM alarm it is
        not, because the next pass cannot be run at all."""
        nums = {"seed": {"seed_cs": 2000000, "mid_hits": 3,
                          "skipped": 0, "seed_ms": 120000}}
        txt = self._report({}, nums)
        f1b = [l for l in txt.splitlines()
               if l.strip().startswith("F1b")][0]
        self.assertIn("FAIL", f1b)
        self.assertNotIn("propose the commit", txt)

    def test_a_seed_under_the_proven_max_is_unsound_and_blocks(self):
        """F1's real job: below 36,860 the estimator under-caps."""
        nums = {"seed": {"seed_cs": 100, "mid_hits": 3,
                          "skipped": 0, "seed_ms": 120000}}
        txt = self._report({}, nums)
        f1 = [l for l in txt.splitlines()
              if l.strip().startswith("F1 seed")][0]
        self.assertIn("FAIL", f1)
        self.assertNotIn("propose the commit", txt)

    def test_r1_cannot_pass_without_a_caperr_measurement(self):
        """None means 'the meter line was absent', not 'zero'."""
        txt = self._report({}, {"ab_v2": {"v2_iters": 0}})
        r1 = [l for l in txt.splitlines() if "R1 never" in l][0]
        self.assertIn("N/A", r1)
        self.assertNotIn("PASS", r1)

    def test_r3_can_actually_fail(self):
        """It used to test a non-empty string, so it always passed."""
        nums = {"ab_v1": {"v1_iters": 0, "v1_bumps": 0},
                "ab_v2": {"v2_iters": 5, "v2_bumps": 5}}
        txt = self._report({}, nums)
        r3 = [l for l in txt.splitlines() if "R3 fast" in l][0]
        self.assertIn("FAIL", r3)

    def test_a_missing_number_prints_not_measured_not_zero(self):
        """'seed walk=0.0s' reads as a superb result; it was a hole."""
        txt = self._report({})
        self.assertIn("not measured", txt)
        self.assertNotIn("seed walk=0.0s", txt)


# A run in which everything worked.  Numbers are shaped like the real
# ones (36,860 is the proven corpus max; v1 converges @iter 4, v2 @0).
_V101_HEALTHY = {
    "units": {"units_oks": 3},
    "seed": {"seed_cs": 36860, "mid_hits": 3, "skipped": 0,
             "seed_ms": 120000},
    "ab_v1": {"v1_iters": 4, "v1_bumps": 4},
    "ab_v2": {"v2_iters": 0, "v2_bumps": 0, "v2_qm_bumps": 0,
              "meter_demand_cs": 36860, "shipped_qm": 36860,
              "caperr_units": 0, "v5_ms": 100, "probe_ms": 90},
}


class V101RunLoopTest(unittest.TestCase):
    """run_v101's step loop had NO coverage -- it is called only from
    the dispatcher, so every scheduling decision in it was pinned by
    execution alone.  These drive it with fake children."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.rss_hit = False
        # Exposed so a test can assert the bundle survived: patching
        # it again from the test would LOSE, since _env enters last.
        self.bundle = mock.Mock()
        self.model = {}

        class _Ctx:
            def __init__(_s, key, mode):
                _s.rss_ceiling_hit = False
                _s.peak_rss_gb = 0.0
                _s._p = os.path.join(self.tmp.name, "%s.log" % key)
                io.open(_s._p, "w").write("")

            def note(_s, _m):
                pass

            def log_path(_s, _n):
                return _s._p

            def finish(_s, rc, b_fail_scan=True):
                _s.rss_ceiling_hit = self.rss_hit
                return mock.Mock(rc=rc, peak_rss_gb=1.0,
                                  triage_tgz="")

        self.Ctx = _Ctx

    def _env(self, steps):
        """Every external edge run_v101 touches, stubbed."""
        st = contextlib.ExitStack()
        for p in (
                mock.patch.object(_MOD, "V101_ROOT", self.tmp.name),
                mock.patch.object(_MOD, "V101_VERDICT",
                                  os.path.join(self.tmp.name, "V.txt")),
                mock.patch.object(_MOD, "V101_BUNDLE",
                                  os.path.join(self.tmp.name, "B.tgz")),
                mock.patch.object(_MOD, "v101_steps",
                                  return_value=steps),
                mock.patch.object(_MOD, "JobHandle", self.Ctx),
                mock.patch.object(_MOD, "run_rust_example",
                                  return_value=0),
                mock.patch.object(_MOD, "neo_env", return_value={}),
                mock.patch.object(_MOD, "v101_parse"),
                mock.patch.object(_MOD, "_v101_keep"),
                mock.patch.object(_MOD, "_v101_bundle",
                                  self.bundle),
                mock.patch.object(_MOD, "_v101_write_progress"),
                mock.patch.object(_MOD, "_atomic_symlink"),
                mock.patch.object(_MOD, "_summary_line"),
                mock.patch.object(_MOD, "log"),
                mock.patch.object(_MOD, "_v101_mem_avail_gb",
                                  return_value=999.0),
                mock.patch("builtins.print")):
            st.enter_context(p)
        return st

    def _run_raw(self, steps, rss_hit=False):
        """_run without the v101_report spy, so a test can patch it."""
        self.rss_hit = rss_hit
        with self._env(steps):
            return _MOD.run_v101(), None

    def _run(self, steps, rss_hit=False):
        self.rss_hit = rss_hit
        with self._env(steps):
            captured = {}
            real = _MOD.v101_report

            def spy(t0, dl, rd, R, veh, model):
                captured["R"] = R
                self.model = dict(model)
                return real(t0, dl, rd, R, veh, model)

            with mock.patch.object(_MOD, "v101_report", spy):
                rc = _MOD.run_v101()
            return rc, captured["R"]

    def _step(self, key, **kw):
        kw.setdefault("cap_s", 600)
        return _MOD.V101Step(key, key, ["x"], {}, kw.pop("cap_s"),
                              False, **kw)

    def test_a_report_that_raises_still_leaves_a_bundle(self):
        """The guard's whole point: never end with no verdict, no
        bundle AND no traceback.  It caught only OSError, so a
        TypeError out of v101_report lost all three."""
        st = self._step("smoke_v1")
        with mock.patch.object(_MOD, "v101_report",
                               side_effect=TypeError("boom")):
            rc, _R = self._run_raw([st])
        self.assertTrue(self.bundle.called, "the bundle was lost")
        self.assertEqual(rc, 1)

    def test_the_exit_code_agrees_with_the_verdict(self):
        """A falsifier FAIL is "not shippable" too; rc counted only
        step FAIL/TIMEOUT, so that run exited 0."""
        st = self._step("smoke_v1")
        for txt, want in ((_MOD.V101_GREEN_MARK, 0),
                          ("FALSIFIED BY: F1 ...", 1),
                          ("", 1)):
            with self.subTest(verdict=txt[:20]):
                with mock.patch.object(_MOD, "v101_report",
                                       return_value=txt):
                    rc, _R = self._run_raw([st])
                self.assertEqual(rc, want)

    def test_a_timed_out_calibration_still_feeds_the_model(self):
        """Pins the CALL SITE, not the function: the gate used to be
        `status == "OK"`, so a TIMEOUT was thrown away entirely and
        the picker fell back to a prior that cannot see the box."""
        st = self._step("calib", cap_s=600)
        with mock.patch.object(_MOD, "_v101_verdict_step",
                               return_value=("TIMEOUT", "capped")), \
             mock.patch.object(_MOD, "_v101_recalibrate") as rc_:
            self._run([st])
        self.assertTrue(rc_.called,
                        "a TIMEOUT taught the model nothing")
        self.assertTrue(rc_.call_args[1].get("partial"),
                        "a TIMEOUT was taken as an exact rate")

    def test_a_partial_measurement_never_speeds_the_model_up(self):
        """A TIMEOUT is a LOWER bound on the arm rate.  Overwriting
        with it could make the model FASTER than something already
        measured, which is the one direction that overruns."""
        model = dict(_MOD.V101_PRIORS)
        slow = _MOD.V101Res("calib", status="OK", wall_s=3000.0,
                             nums={"probe_ms": 100, "v5_ms": 100})
        _MOD._v101_recalibrate(model, "calib", slow, None,
                                lambda m: None)
        was = model["r_v2_arm"]
        fast = _MOD.V101Res("calib", status="TIMEOUT", wall_s=300.0,
                             nums={"probe_ms": 100, "v5_ms": 100})
        _MOD._v101_recalibrate(model, "calib", fast, None,
                                lambda m: None, partial=True)
        self.assertEqual(model["r_v2_arm"], was)

    def test_a_slower_calibration_never_buys_a_bigger_vehicle(self):
        """The picker was NON-MONOTONE: a calib that TIMED OUT was
        discarded, the model fell back to a prior that cannot see the
        box, and the vehicle grew exactly when the evidence said the
        box was slowest.  Measured: 3000s -> perc 10, 3590s TIMEOUT
        -> perc 15."""
        def pick(wall, status):
            model = dict(_MOD.V101_PRIORS)
            r = _MOD.V101Res("calib", status=status, wall_s=wall,
                              nums={"probe_ms": int(wall * 400),
                                    "v5_ms": int(wall * 500)})
            _MOD._v101_recalibrate(model, "calib", r, None,
                                    lambda m: None,
                                    partial=(status == "TIMEOUT"))
            left = (16 * 3600 - wall - 300
                    - _MOD.V101_DEC_RESERVE_S)
            veh, _c = _MOD.v101_pick(model, left, lambda m: None)
            return veh[0] if veh else 0

        seq = [pick(1000.0, "OK"), pick(2000.0, "OK"),
               pick(3000.0, "OK"), pick(3590.0, "TIMEOUT")]
        self.assertEqual(seq, sorted(seq, reverse=True),
                         "picker is non-monotone in the calib wall: "
                         "%s" % seq)

    def test_an_oom_guard_kill_reaches_the_verdict_as_a_skip(self):
        """Pins the WIRING: the flag has to be passed through, not
        just set.  Dropping the argument made the kill a FAIL again."""
        st = self._step("dec_big", max_rss_gb=460.0)
        _rc, R = self._run([st], rss_hit=True)
        self.assertEqual(R["dec_big"].status, "SKIP")
        self.assertIn("OOM-GUARD", R["dec_big"].why)

    def test_a_surrendered_step_is_skipped_not_run_with_a_stub_cap(self):
        """cap_s = -1 is the picker's sentinel.  Before it, dec_big
        started with ~47 min against a 5 h ask and burned them."""
        st = self._step("dec_big", cap_s=-1)
        _rc, R = self._run([st])
        self.assertEqual(R["dec_big"].status, "SKIP")
        self.assertIn("surrendered", R["dec_big"].why)


class V101FalsifierNegativeTest(unittest.TestCase):
    """One NEGATIVE case per falsifier and requirement.  A measured
    mutation sweep found 17 of 28 verdict-logic mutations escaping the
    suite -- every row could be neutered to `True` undetected, because
    only green-is-REACHABLE was tested.  Reachability is not a gate."""

    def _report(self, nums, statuses=None):
        keys = [st.key for st in _MOD.v101_steps()]
        R = {}
        for k in keys:
            R[k] = _MOD.V101Res(
                k, status=(statuses or {}).get(k, "OK"), wall_s=60.0,
                nums=dict(nums.get(k, {})))
        return _MOD.v101_report(time.time() - 60, time.time() + 3600,
                                 "/tmp/none", R, None,
                                 dict(_MOD.V101_PRIORS))

    def _mutate(self, step, field, value):
        nums = dict((k, dict(v)) for k, v in _V101_HEALTHY.items())
        nums.setdefault(step, {})[field] = value
        return self._report(nums)

    def test_healthy_run_is_green(self):
        """The control: without it every case below passes trivially."""
        self.assertIn("propose the commit",
                      self._report(_V101_HEALTHY))

    def test_each_broken_metric_blocks_green_and_names_its_row(self):
        cases = [
            ("F1", "seed", "seed_cs", 100),      # under the proven max
            ("F1b", "seed", "seed_cs", 2000000), # past the RAM alarm
            ("F2", "ab_v2", "meter_demand_cs", 99999),
            ("F3a", "ab_v2", "v2_qm_bumps", 1),
            ("F3b", "ab_v2", "v2_bumps", 3),
            # BOTH directions of F5.  Over-shipping is waste; UNDER-
            # shipping is an under-cap, and only the second half was
            # ever exercised.
            ("F5", "ab_v2", "shipped_qm", 50000),
            ("F5", "ab_v2", "shipped_qm", 30000),
            ("R1", "ab_v2", "caperr_units", 3),
            ("R2", "ab_v2", "shipped_qm", 40000),
            ("R3", "ab_v2", "v2_iters", 5),
            ("R5", "units", "units_oks", 2),
        ]
        for row, step, field, bad in cases:
            with self.subTest(row=row, field=field, value=bad):
                txt = self._mutate(step, field, bad)
                self.assertNotIn("propose the commit", txt,
                                 "%s did not block green" % row)
                line = [l for l in txt.splitlines()
                        if l.strip().startswith(row + " ")]
                self.assertTrue(line, "no %s row rendered" % row)
                self.assertIn("FAIL", line[0],
                              "%s did not read FAIL" % row)

    def test_advisory_rows_warn_loudly_without_blocking(self):
        """F7/F8/F1b cannot make a healthy v2 unshippable -- but a
        WARN that no one is told about is the same as no check."""
        for row, step, field, bad in (
                ("F7", "seed", "mid_hits", 0),
                ("F8", "seed", "skipped", 2),
                ("F1b", "seed", "seed_cs", 368600),
                ("F6", "seed", "seed_ms", 400000)):   # > 5 min
            with self.subTest(row=row):
                txt = self._mutate(step, field, bad)
                line = [l for l in txt.splitlines()
                        if l.strip().startswith(row + " ")][0]
                self.assertIn("WARN", line)
                self.assertIn("propose the commit", txt)
                adv = [l for l in txt.splitlines()
                       if "ADVISORY" in l]
                self.assertTrue(adv, "%s WARN was silent" % row)
                self.assertIn(row, adv[0])

    def test_an_unmeasured_advisory_is_announced_too(self):
        """F8 is the suite's ONLY full-corpus consistency reading, so
        "we never looked" must not be silent under a green line."""
        nums = dict((k, dict(v)) for k, v in _V101_HEALTHY.items())
        del nums["seed"]["skipped"]
        txt = self._report(nums)
        note = [l for l in txt.splitlines() if "NOT MEASURED (" in l]
        self.assertTrue(note, "an unmeasured advisory was silent")
        self.assertIn("F8", note[0])

    def test_a_skipped_word_names_the_abort_site(self):
        """Advisory, but the reader must learn what branch 2 costs."""
        txt = self._mutate("seed", "skipped", 2)
        f8 = [l for l in txt.splitlines()
              if l.strip().startswith("F8")][0]
        self.assertIn("sed_mapper.rs:557", f8)

    def test_f1_says_how_many_words_the_max_came_from(self):
        """36,860 over 1209 words and over 3 are different claims."""
        nums = dict((k, dict(v)) for k, v in _V101_HEALTHY.items())
        nums["seed"]["seed_words"] = 1209
        txt = self._report(nums)
        f1 = [l for l in txt.splitlines()
              if l.strip().startswith("F1 seed")][0]
        self.assertIn("1209 words", f1)

    def test_a_zero_on_one_step_does_not_discard_a_good_one(self):
        """pick2 committed to ab_v2 BEFORE the zero test ran, so a
        zero meter there threw away a perfectly good calib reading
        and the whole night went INCONCLUSIVE."""
        nums = dict((k, dict(v)) for k, v in _V101_HEALTHY.items())
        nums["ab_v2"]["meter_demand_cs"] = 0
        nums["ab_v2"]["shipped_qm"] = 0
        nums["calib"] = {"meter_demand_cs": 36860, "shipped_qm": 36860}
        txt = self._report(nums)
        r2 = [l for l in txt.splitlines()
              if l.strip().startswith("R2 ")][0]
        self.assertIn("PASS", r2)
        self.assertIn("calib", r2)

    def test_an_uncomputable_advisory_is_a_note_not_a_pass(self):
        """_v101_loose(None) reading PASS would certify a seed that
        was never measured."""
        self.assertEqual(_MOD._v101_loose(None)[0], "NOTE")
        self.assertEqual(_MOD._v101_loose(36860)[0], "PASS")

    def test_f9_warns_when_the_v5_walk_dominates(self):
        """It is advisory, but it still has to be able to say so --
        it used to be `else True`, which could never fire."""
        nums = dict((k, dict(v)) for k, v in _V101_HEALTHY.items())
        nums["ab_v2"].update(v5_ms=5000, probe_ms=100)
        f9 = [l for l in self._report(nums).splitlines()
              if l.strip().startswith("F9")][0]
        self.assertIn("WARN", f9)
        nums["ab_v2"].update(v5_ms=100, probe_ms=5000)
        f9 = [l for l in self._report(nums).splitlines()
              if l.strip().startswith("F9")][0]
        self.assertIn("PASS", f9)

    def test_a_meter_that_read_zero_is_not_a_measurement(self):
        """demand=0 made F2, F5 and R2 all print PASS at once."""
        txt = self._mutate("ab_v2", "meter_demand_cs", 0)
        for row in ("F2", "F5", "R2"):
            line = [l for l in txt.splitlines()
                    if l.strip().startswith(row + " ")][0]
            self.assertIn("N/A", line, "%s passed on a zero" % row)
        # "never measured" and "measured, and it was 0" are different
        # findings; the evidence has to say which one happened.
        f2 = [l for l in txt.splitlines()
              if l.strip().startswith("F2 ")][0]
        self.assertIn("read 0", f2)
        self.assertNotIn("propose the commit", txt)

    def test_a_shipped_cap_of_zero_is_not_a_measurement(self):
        """The mirror of the demand guard: shipped=0 would let F5 and
        R2 certify a cap that cannot exist."""
        txt = self._mutate("ab_v2", "shipped_qm", 0)
        for row in ("F5", "R2"):
            line = [l for l in txt.splitlines()
                    if l.strip().startswith(row + " ")][0]
            self.assertIn("N/A", line, "%s passed on a zero" % row)
        self.assertNotIn("propose the commit", txt)

    def test_the_mandatory_step_list_is_pinned(self):
        """Dropping any one of the six escapes every other test: the
        remaining five still block, so green stays unreachable."""
        for k in ("units", "seed", "calib", "ab_v1", "ab_v2",
                  "dec_v2"):
            with self.subTest(step=k):
                txt = self._report(_V101_HEALTHY, {k: "SKIP"})
                self.assertIn("INCONCLUSIVE", txt)
                self.assertIn(k, txt)
                self.assertNotIn("propose the commit", txt)

    def test_an_opportunistic_timeout_does_not_block(self):
        """dec_big is RAM-guarded and calib_v1 has V101_V1_ARM_RATIO
        as its designed fallback; neither TIMEOUT is evidence."""
        for k in ("dec_big", "calib_v1"):
            with self.subTest(step=k):
                txt = self._report(_V101_HEALTHY, {k: "TIMEOUT"})
                self.assertNotIn("BLOCKED BY", txt)
                self.assertIn("propose the commit", txt)

    def test_a_real_failure_on_those_two_still_blocks(self):
        """The exemption is for TIMEOUT only, not for FAIL."""
        for k in ("dec_big", "calib_v1"):
            with self.subTest(step=k):
                txt = self._report(_V101_HEALTHY, {k: "FAIL"})
                self.assertIn("BLOCKED BY: %s" % k, txt)

    def test_f3b_names_the_source_of_both_of_its_numbers(self):
        """Bumps come from worst(), iters from the A/B pair."""
        txt = self._report(_V101_HEALTHY)
        f3b = [l for l in txt.splitlines()
               if l.strip().startswith("F3b")][0]
        self.assertEqual(f3b.count("from "), 2)

    def test_a_qm_bump_in_dec_big_is_not_invisible(self):
        """N1 regression.  _v101_count returns 0 rather than None, so
        a first-hit lookup let ab_v2's 0 mask five production-width
        dis_adv::neo_qm_real bumps in dec_big -- the exact defect M2
        exists to eliminate -- and the verdict went green."""
        txt = self._mutate("dec_big", "v2_qm_bumps", 5)
        self.assertNotIn("propose the commit", txt)
        f3a = [l for l in txt.splitlines() if "F3a" in l][0]
        self.assertIn("FAIL", f3a)
        self.assertIn("dec_big", f3a)

    def test_a_caperr_in_any_v2_step_blocks_green(self):
        """Same aggregation bug, on R1's counter."""
        for step in ("dec_v2", "calib", "smoke_v2", "dec_big"):
            with self.subTest(step=step):
                txt = self._mutate(step, "caperr_units", 4)
                self.assertNotIn("propose the commit", txt)

    def test_parity_rounds_do_not_certify_speed(self):
        """A row called "fast" must not PASS on 2 -> 2 rounds."""
        nums = dict((k, dict(v)) for k, v in _V101_HEALTHY.items())
        nums["ab_v1"]["v1_iters"] = 1
        nums["ab_v2"]["v2_iters"] = 1
        txt = self._report(nums)
        r3 = [l for l in txt.splitlines() if "R3 fast" in l][0]
        self.assertIn("FAIL", r3)
        self.assertIn("NO SPEEDUP", r3)

    def test_parity_at_the_one_round_floor_is_allowed(self):
        """v2 at 1 round cannot beat v1 at 1 round; that is not a
        failure, and calling it one would be a false RED."""
        nums = dict((k, dict(v)) for k, v in _V101_HEALTHY.items())
        nums["ab_v1"]["v1_iters"] = 0
        nums["ab_v2"]["v2_iters"] = 0
        txt = self._report(nums)
        r3 = [l for l in txt.splitlines() if "R3 fast" in l][0]
        self.assertIn("PASS", r3)

    def test_a_pending_step_is_never_silent(self):
        """PENDING was in neither `fails` nor `skips`, so a suite that
        died early could print green mentioning nothing."""
        txt = self._report(_V101_HEALTHY, {"dec_v1": "PENDING"})
        self.assertIn("DID NOT RUN", txt)
        self.assertIn("dec_v1", txt)

    def test_the_green_sentence_names_non_mandatory_gaps(self):
        """dec_big SKIP is allowed, but must not sit silently under a
        sentence that reads as if everything ran."""
        txt = self._report(_V101_HEALTHY, {"dec_big": "SKIP"})
        self.assertIn("propose the commit", txt)
        self.assertIn("MANDATORY", txt)
        self.assertIn("dec_big=SKIP", txt)


if __name__ == "__main__":
    sys.exit(main())
