#!/usr/bin/env python3
"""
run_checkpoints.py -- CRIU-based periodic checkpoint orchestrator for the
zkregplus ZK proof-generation run.

Context
-------
We run zkregplus on a GCP spot VM for ~32 hours at a time. Spot VMs can be
preempted with short notice. This script periodically snapshots the running
worker process with CRIU so we can resume within minutes of preemption
instead of restarting the 32-hour run from scratch.

Design highlights (see chat log for full discussion):

- Two launch modes:
    Mode 1 ("./compile.sh"): non-interactive `cargo test` run. Python spawns
                              the command itself and pgreps the worker.
    Mode 2 ("cargo run --release --example main"): main.rs uses dialoguer's
                              TUI Select widgets, which cannot be driven via
                              subprocess stdin. USER must launch this mode
                              manually in a separate terminal; Python then
                              pgreps and watches.

- Checkpoint cycle per tick:
    1. Safety: check the worker has no child processes (we assume rayon-only
       parallelism, i.e. single PID). If children exist, abort the whole run.
    2. Skip if VmRSS > user-configured RAM limit.
    3. `criu pre-dump` into a tmpfs scratch dir (zero persistent-disk I/O,
       process keeps running).
    4. `criu dump --prev-images-dir=<tmpfs>` streamed via criu-image-streamer
       through zstd into <slot>/final.tzst. This is the short-freeze phase.
    5. Compress the tmpfs pre-dump into <slot>/pre.tzst (process already
       running again at this point -- no additional freeze).
    6. Atomically promote the slot by updating latest.txt.
    7. Delete rotated-out slots.

- Slots live at: <proj_root>/data/cache/checkpoints/slot_{a,b}/
  A pointer file latest.txt names the current slot.

- Resume mode: read latest.txt, stream-decompress that slot's pre.tzst and
  final.tzst, hand them to `criu restore`. The Rust binary is NOT re-invoked
  -- the process image is resurrected with all in-memory state intact
  (including log handles, `initialized_jobs` HashSet, etc.).

Requirements
------------
- Must run as root (CRIU needs CAP_SYS_ADMIN/CAP_CHECKPOINT_RESTORE).
- `criu`, `criu-image-streamer`, and `zstd` must be on PATH.
- Project layout assumed:
    <proj_root>/zkregplus/src/run_checkpoints.py   (this file)
    <proj_root>/zkregplus/src/compile.sh           (mode 1)
    <proj_root>/zkregplus/examples/main.rs         (mode 2)
    <proj_root>/data/cache/checkpoints/            (created on first run)

Usage
-----
    sudo python3 run_checkpoints.py

The script prompts interactively for every input. All console output is
teed to ./checkrun.log in the invocation CWD (truncated in new mode,
appended in resume mode).
"""

import json
import os
import re
import shutil
import signal
import subprocess
import sys
import time
from datetime import datetime
from pathlib import Path

# ============================================================================
# Constants
# ============================================================================

# pgrep -f regexes for identifying the zkregplus worker process. Cargo appends
# a content-hash suffix to test-binary and example-binary names; these regexes
# match the fingerprinted path that appears in /proc/<pid>/cmdline.
#
# Mode 1 worker is a cargo test binary:
#     target/release/deps/zkregplus-<hash>  <testfilter> ...
# Mode 2 worker is a cargo example binary (post-daemonize):
#     target/release/examples/main-<hash>
WORKER_PATTERNS = {
    1: r"target/release/deps/zkregplus-[0-9a-f]+.*test_zkreg_main",
    2: r"target/release/examples/main-[0-9a-f]+",
}

MODE_DESCRIPTIONS = {
    1: "./compile.sh  (runs cargo test --lib --release -- test_zkreg_main)",
    2: "cargo run --release --example main  (interactive, launch MANUALLY)",
}

# Where checkpoints live, under <proj_root>/data/cache/
CHECKPOINT_SUBDIR = "data/cache/checkpoints"

# Sentinel file the Rust worker writes on successful normal completion.
# Python checks for this when the worker PID vanishes -- if present, the
# run finished cleanly and we can wipe all checkpoint storage. If absent,
# the process died for some other reason (crash, OOM, preemption) and we
# keep the slots so the user can resume.
#
# NOTE: the Rust side must write this file at the end of its successful
# execution path (in main.rs after (opt.func)(true) returns, and in the
# test_zkreg_main test body). Until that edit lands, this sentinel will
# never exist -- and this script will simply never auto-wipe, which is
# the safe behavior.
RUN_COMPLETE_SENTINEL = "data/cache/run_complete.sentinel"

# Slot names. Slot count is user-configured (1 or 2); we rotate between
# slot_a and slot_b if 2, or always overwrite-via-safe-rename slot_a if 1.
SLOT_NAMES = ("slot_a", "slot_b")
LATEST_POINTER = "latest.txt"

# Poll budget for pgrep after a spawn / after user confirms manual launch.
# Cover compile time (cargo compile can take minutes on a cold target dir)
# plus daemonize double-fork settle time.
PID_POLL_TIMEOUT_SEC = 600
PID_POLL_INTERVAL_SEC = 2

# tmpfs scratch for pre-dump imagery. Located under /tmp so it survives the
# checkpoint cycle but not reboots. We size it generously (1.2x RAM cap) so
# criu pre-dump never runs out of space.
TMPFS_SCRATCH_ROOT = "/tmp/zkregplus_cr_scratch"

# criu-image-streamer uses a UNIX socket inside a directory we pass via -D.
# We put the socket dir in /tmp (small, ephemeral) to keep it off the PD.
STREAMER_SOCK_ROOT = "/tmp/zkregplus_cr_sock"


# ============================================================================
# Tee -- mirror stdout/stderr to ./checkrun.log in the invocation CWD.
# ============================================================================

class Tee:
    """File-like wrapper that fan-outs writes to multiple streams.

    Used to duplicate stdout/stderr to both the terminal and checkrun.log.
    We flush on every write so a `tail -f checkrun.log` stays live.
    """

    def __init__(self, *streams):
        self.streams = streams

    def write(self, data):
        for s in self.streams:
            s.write(data)
            s.flush()

    def flush(self):
        for s in self.streams:
            s.flush()


def install_tee(is_new_mode: bool) -> None:
    """Redirect sys.stdout and sys.stderr to also land in ./checkrun.log.

    New mode truncates the file; resume mode appends. Mirrors the b_resume
    semantics we built into the Rust side for per-job logs.
    """
    open_mode = "w" if is_new_mode else "a"
    # Line-buffered so partial lines aren't held mid-pipeline.
    log_fh = open("checkrun.log", open_mode, buffering=1)
    sys.stdout = Tee(sys.__stdout__, log_fh)
    sys.stderr = Tee(sys.__stderr__, log_fh)


# ============================================================================
# Preflight
# ============================================================================

def require_root() -> None:
    """CRIU dump/restore needs root (or an elaborate capabilities setup we
    deliberately didn't take -- see design discussion). Abort early with a
    clear message rather than failing opaquely deep inside the criu call.
    """
    if os.geteuid() != 0:
        sys.exit(
            "ERROR: must run as root (CRIU requires CAP_SYS_ADMIN).\n"
            "       Try: sudo python3 run_checkpoints.py"
        )


def proj_root() -> Path:
    """Absolute path to the new_zkregplus workspace root.

    This script is at <proj_root>/zkregplus/src/run_checkpoints.py, so the
    root is two parents up from its own directory.
    """
    return Path(__file__).resolve().parents[2]


def require_binary(name: str) -> None:
    """Abort if a required external binary isn't on PATH."""
    if shutil.which(name) is None:
        sys.exit(f"ERROR: required binary '{name}' not found on PATH.")


# ============================================================================
# Interactive prompts
# ============================================================================

def prompt_mode() -> int:
    """Pick launch mode 1 or 2."""
    print("Select command mode:")
    for k, desc in MODE_DESCRIPTIONS.items():
        print(f"  {k}: {desc}")
    while True:
        s = input("Mode [1/2]: ").strip()
        if s in ("1", "2"):
            return int(s)
        print("  (invalid -- enter 1 or 2)")


def prompt_int(msg: str, default: int, min_val: int = 1) -> int:
    """Prompt for a positive integer with a default."""
    while True:
        s = input(f"{msg} [default {default}]: ").strip()
        if not s:
            return default
        try:
            v = int(s)
            if v < min_val:
                print(f"  (must be >= {min_val})")
                continue
            return v
        except ValueError:
            print("  (invalid integer)")


def prompt_choice(msg: str, choices: tuple, default) -> str:
    """Prompt for one of a small set of string choices."""
    while True:
        s = input(f"{msg} {choices} [default {default}]: ").strip().lower()
        if not s:
            return default
        if s in choices:
            return s
        print(f"  (must be one of {choices})")


# ============================================================================
# zstd thread sizing -- factor per design Q4.
# ============================================================================

def compute_zstd_threads(vcpus: int) -> int:
    """Pick a zstd thread count that saturates the 1 TB Balanced PD write
    cap (~280 MB/s) without stealing cores from the rayon worker.

    At ~2.5x compression on ZK field-element memory, the pipeline needs to
    ingest raw data at ~700 MB/s to keep the disk full. Each zstd -3 thread
    does ~400 MB/s, so 2-3 threads suffice. We cap at 8 for safety margin
    and floor at 2 to keep compression off the critical path on tiny VMs.

        zstd_threads = max(2, min(8, vcpus // 14))

    Examples: 4 vCPU -> 2, 56 vCPU -> 4, 112 vCPU -> 8, 224 vCPU -> 8.
    """
    return max(2, min(8, vcpus // 14))


# ============================================================================
# Process discovery
# ============================================================================

def find_worker_pid(mode: int, timeout_sec: int = PID_POLL_TIMEOUT_SEC) -> int:
    """Locate the worker PID by pgrep on a mode-specific regex.

    We use `pgrep -nf <regex>`:
      -n : newest matching process (useful after spawn; also deterministic)
      -f : match against full command line, not just comm name

    Polls up to `timeout_sec`. Returns the single PID, or raises on:
      - Timeout (no match appeared).
      - Multiple matches (regex not unique -- stale zombie, concurrent run).

    For mode 1, pgrep will find the test binary once cargo finishes
    compiling and spawns it. For mode 2, the user has already launched the
    command manually and clicked through the dialoguer prompts by the time
    we get called.
    """
    pattern = WORKER_PATTERNS[mode]
    deadline = time.time() + timeout_sec
    last_err = None

    print(f"Polling for worker PID (pattern: {pattern!r}) ...")
    while time.time() < deadline:
        try:
            # pgrep exits 0 on match, 1 on no match, 2/3 on error.
            res = subprocess.run(
                ["pgrep", "-f", pattern],
                capture_output=True, text=True,
            )
        except FileNotFoundError:
            sys.exit("ERROR: pgrep not found. Install procps.")

        if res.returncode == 0:
            pids = [int(x) for x in res.stdout.split() if x]
            if len(pids) == 1:
                print(f"Found worker PID: {pids[0]}")
                return pids[0]
            if len(pids) > 1:
                last_err = (
                    f"ambiguous: pgrep matched {len(pids)} PIDs: {pids}. "
                    f"Refine regex or kill stale processes."
                )
                # Don't retry -- this is a config problem, not a race.
                break
        time.sleep(PID_POLL_INTERVAL_SEC)

    if last_err:
        sys.exit(f"ERROR: {last_err}")
    sys.exit(f"ERROR: timed out after {timeout_sec}s waiting for worker.")


def spawn_mode1(proj: Path) -> None:
    """Launch mode 1 (compile.sh) as a detached subprocess.

    compile.sh runs `cargo test` which is non-interactive. We fire-and-
    forget -- we don't need to track the bash/cargo parent PIDs because
    find_worker_pid will locate the actual test binary directly.
    """
    script_dir = proj / "zkregplus" / "src"
    print(f"Spawning: bash ./compile.sh  (cwd={script_dir})")
    # Detach stdio -- the Rust side logs to data/cache/logs/ on its own, and
    # we don't want cargo's compile output cluttering checkrun.log.
    subprocess.Popen(
        ["bash", "./compile.sh"],
        cwd=str(script_dir),
        stdin=subprocess.DEVNULL,
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
        start_new_session=True,  # detach from our process group
    )


def remind_manual_mode2(proj: Path) -> None:
    """Print the reminder and wait for user confirmation.

    Mode 2's dialoguer::Select widgets need a real TTY so we can't drive
    them from subprocess stdin. Easiest path: user launches the command
    themselves in another terminal.
    """
    cargo_dir = proj / "zkregplus"
    print()
    print("=" * 70)
    print("MODE 2 REMINDER: you must launch this command MANUALLY.")
    print()
    print(f"  cd {cargo_dir}")
    print("  cargo run --release --example main")
    print()
    print("Complete the interactive option + log-level prompts. After the")
    print("banner prints 'Execution is switching to the background.',")
    print("return here and press Enter to start the checkpoint loop.")
    print("=" * 70)
    input("Press Enter once the job is running in the background... ")


# ============================================================================
# Process health checks
# ============================================================================

def check_no_children(pid: int) -> None:
    """Abort the script (and kill the worker) if the worker has any
    children. We assume zkregplus is rayon-parallel and never forks long-
    lived child processes; anything else breaks the single-PID CRIU
    assumption we baked into the design.

    Called once per checkpoint cycle, before dumping.
    """
    try:
        # --ppid <pid> lists only direct children of <pid>. -o pid= suppresses
        # the header, giving us one line per child PID.
        res = subprocess.run(
            ["ps", "--ppid", str(pid), "-o", "pid="],
            capture_output=True, text=True,
        )
    except FileNotFoundError:
        sys.exit("ERROR: ps not found. Install procps.")

    children = [int(x) for x in res.stdout.split() if x.strip().isdigit()]
    if children:
        print(f"FATAL: worker PID {pid} has children: {children}")
        print(f"       Single-PID assumption violated. Killing worker.")
        try:
            os.kill(pid, signal.SIGTERM)
            time.sleep(3)
            if pid_is_alive(pid):
                os.kill(pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        sys.exit("ERROR: aborted due to unexpected child processes.")


def pid_is_alive(pid: int) -> bool:
    """True if /proc/<pid> still exists (race-free enough for our purposes)."""
    return Path(f"/proc/{pid}").exists()


def measure_rss_gb(pid: int) -> float:
    """Return VmRSS of the worker in GB, parsed from /proc/<pid>/status.

    VmRSS is resident set size -- the bytes actually in physical memory,
    matching what CRIU will have to dump. We intentionally do not add
    VmSwap (user's choice; GCP spot VMs don't have swap by default).
    """
    status_path = Path(f"/proc/{pid}/status")
    for line in status_path.read_text().splitlines():
        if line.startswith("VmRSS:"):
            # Format: "VmRSS:\t   12345 kB"
            kb = int(line.split()[1])
            return kb / (1024.0 * 1024.0)  # kB -> GB
    raise RuntimeError(f"VmRSS not found in {status_path}")


# ============================================================================
# Slot / checkpoint directory helpers
# ============================================================================

def checkpoints_dir(proj: Path) -> Path:
    return proj / CHECKPOINT_SUBDIR


def wipe_checkpoints(proj: Path) -> None:
    """Remove all existing slots and the latest pointer. Called in new mode.

    Creates the directory if it doesn't exist.
    """
    d = checkpoints_dir(proj)
    if d.exists():
        shutil.rmtree(d)
    d.mkdir(parents=True, exist_ok=True)
    print(f"New mode: wiped checkpoint dir {d}")


def sentinel_path(proj: Path) -> Path:
    """Absolute path to the run-complete sentinel file."""
    return proj / RUN_COMPLETE_SENTINEL


def clear_completion_sentinel(proj: Path) -> None:
    """Delete any stale sentinel left over from a previous run.

    Called at the start of a new-mode run. Without this, a sentinel
    written by a prior successful run would cause us to immediately wipe
    the fresh checkpoints when the current worker PID is first detected
    as alive (unlikely race) or -- more likely -- on the first exit.
    """
    sp = sentinel_path(proj)
    if sp.exists():
        print(f"  Clearing stale completion sentinel at {sp}")
        sp.unlink()


def run_completed_successfully(proj: Path) -> bool:
    """True iff the Rust worker wrote the completion sentinel.

    Presence means the worker reached the end of its normal execution
    path and chose to signal success. Absence means we cannot confirm
    success -- treat as crash/preemption and preserve checkpoints.
    """
    return sentinel_path(proj).exists()


def wipe_all_checkpoint_storage(proj: Path) -> int:
    """Remove the entire checkpoints dir plus the sentinel file.

    Called after a successful run to reclaim disk. Returns the number of
    bytes freed (approximate -- measured before the rmtree).
    """
    freed = dir_size_bytes(checkpoints_dir(proj))
    shutil.rmtree(checkpoints_dir(proj), ignore_errors=True)
    sp = sentinel_path(proj)
    if sp.exists():
        sp.unlink()
    return freed


def read_latest(proj: Path) -> str:
    """Return the current 'latest' slot name (e.g. 'slot_a') or '' if none."""
    ptr = checkpoints_dir(proj) / LATEST_POINTER
    if not ptr.exists():
        return ""
    return ptr.read_text().strip()


def write_latest(proj: Path, slot_name: str) -> None:
    """Atomically update latest.txt to point at <slot_name>.

    We write to a temp file and os.replace() for atomicity -- a partial
    write must never leave latest.txt pointing at a nonexistent slot.
    """
    d = checkpoints_dir(proj)
    tmp = d / (LATEST_POINTER + ".tmp")
    tmp.write_text(slot_name + "\n")
    os.replace(tmp, d / LATEST_POINTER)


def pick_target_slot(proj: Path, slot_count: int) -> str:
    """Choose which slot to write the next checkpoint into.

    Rule: never overwrite the current latest. If slot_count == 2 we pick
    the "other" slot; if slot_count == 1 we pick slot_a either way (safe-
    rename via a temp suffix makes this OK).
    """
    current = read_latest(proj)
    if slot_count == 2:
        return SLOT_NAMES[1] if current == SLOT_NAMES[0] else SLOT_NAMES[0]
    # slot_count == 1
    return SLOT_NAMES[0]


def cleanup_obsolete_slots(proj: Path, keep: tuple) -> None:
    """Delete any slot_* directories not in `keep`. Called after rotation."""
    d = checkpoints_dir(proj)
    for entry in d.iterdir():
        if (entry.is_dir() and entry.name.startswith("slot_")
                and entry.name not in keep):
            print(f"Cleaning up obsolete slot: {entry.name}")
            shutil.rmtree(entry, ignore_errors=True)


def dir_size_bytes(path: Path) -> int:
    """Recursive sum of all file sizes under `path`. 0 if path doesn't exist."""
    if not path.exists():
        return 0
    total = 0
    for root, _dirs, files in os.walk(path):
        for f in files:
            fp = Path(root) / f
            try:
                total += fp.stat().st_size
            except FileNotFoundError:
                pass  # race: file deleted mid-walk
    return total


def fmt_bytes(n: int) -> str:
    """Human-readable bytes formatter."""
    for unit in ("B", "KB", "MB", "GB", "TB"):
        if n < 1024 or unit == "TB":
            return f"{n:.2f} {unit}"
        n /= 1024.0


# ============================================================================
# Log-file roll-back
#
# When we checkpoint at time T, the log files in data/cache/logs contain
# lines up to T. Between T and a subsequent crash at T+dt, the process
# writes more lines (those bytes land on disk via append_to_file in the
# Rust side). On resume, CRIU restores the process state to T -- but the
# log files on disk are larger than what the restored process "expects".
# Next append goes to the current EOF, leaving a discontinuity.
#
# Fix: at checkpoint time, record the newline count of each log file.
# At resume time, truncate each file so only that many newlines remain.
# The next append from the restored process then lands cleanly right
# after the checkpoint-time content.
#
# Semantic note: per-job logs are written via append_to_file (O_APPEND,
# open-and-close each call) so truncating the file never desyncs a live
# FD. The daemon stdout/stderr log (zkregplus.log) DOES have a persistent
# FD with its write position preserved by CRIU -- but that position also
# equals the checkpoint-time file size, so truncating to the same line
# count keeps EOF and FD position aligned.
# ============================================================================

def logs_dir(proj: Path) -> Path:
    """Absolute path to the per-job/daemon log directory."""
    return proj / "data" / "cache" / "logs"


def record_log_line_counts(logs_d: Path) -> dict:
    """Return {filename: newline_count} for every regular file in logs_d.

    We count raw '\\n' bytes (fast, boundary-exact) rather than running
    readlines() -- the files can be large and we don't care about the
    content, only the line-terminator positions.
    """
    if not logs_d.exists():
        return {}
    counts = {}
    for entry in logs_d.iterdir():
        if not entry.is_file():
            continue
        n = 0
        with open(entry, "rb") as f:
            while True:
                chunk = f.read(65536)
                if not chunk:
                    break
                n += chunk.count(b"\n")
        counts[entry.name] = n
    return counts


def truncate_log_files_to_counts(logs_d: Path, counts: dict) -> None:
    """Truncate each named file so only the first `count` lines remain.

    Walks the file, locates the byte offset immediately after the N-th
    '\\n', and `os.truncate`s there. Files listed in `counts` but absent
    from disk are skipped with a warning; files on disk but not in
    `counts` (new files created post-checkpoint) are left untouched
    (the restored process doesn't know about them -- fine).
    """
    for fname, target_lines in counts.items():
        fpath = logs_d / fname
        if not fpath.exists():
            print(f"  WARN: log file {fname} missing at resume; skipping.")
            continue

        if target_lines == 0:
            os.truncate(fpath, 0)
            continue

        # Scan chunk-by-chunk to find the byte offset after the N-th '\n'.
        offset_after_nth = None
        seen = 0
        base = 0  # absolute byte offset of the start of the current chunk
        with open(fpath, "rb") as f:
            while True:
                chunk = f.read(65536)
                if not chunk:
                    break
                for i in range(len(chunk)):
                    if chunk[i] == 0x0a:  # '\n'
                        seen += 1
                        if seen == target_lines:
                            offset_after_nth = base + i + 1
                            break
                if offset_after_nth is not None:
                    break
                base += len(chunk)

        if offset_after_nth is None:
            # File has fewer than target_lines newlines (e.g., externally
            # truncated). Leave alone -- truncating to a longer length is
            # impossible, and any real content is preserved.
            print(f"  WARN: {fname} has fewer than {target_lines} lines; "
                  f"leaving unchanged.")
            continue
        os.truncate(fpath, offset_after_nth)


# ============================================================================
# tmpfs scratch management (for pre-dump imagery)
# ============================================================================

def mount_tmpfs_scratch(ram_limit_gb: int) -> Path:
    """Mount a fresh tmpfs at TMPFS_SCRATCH_ROOT/<timestamp> for pre-dump.

    tmpfs lives in RAM, so pre-dump incurs zero persistent-disk I/O -- the
    ~100-500 GB of pre-dump imagery stays in memory until we compress it
    into the slot. Sized at 1.2x the configured RAM limit to guarantee
    headroom (tmpfs is lazy-allocated; unused capacity costs nothing).

    Returns the mount path.
    """
    ts = datetime.now().strftime("%Y%m%d_%H%M%S")
    mount_path = Path(TMPFS_SCRATCH_ROOT) / f"scratch_{ts}"
    mount_path.mkdir(parents=True, exist_ok=True)

    size_gb = int(ram_limit_gb * 1.2) + 1
    subprocess.run(
        ["mount", "-t", "tmpfs",
         "-o", f"size={size_gb}G,mode=700",
         "tmpfs", str(mount_path)],
        check=True,
    )
    # Pre-dump writes into a "pre" subdir we create under the mount.
    (mount_path / "pre").mkdir()
    return mount_path


def umount_tmpfs_scratch(mount_path: Path) -> None:
    """Best-effort umount + rmdir. Failures are logged but non-fatal."""
    try:
        subprocess.run(["umount", str(mount_path)], check=True)
    except subprocess.CalledProcessError as e:
        print(f"WARN: umount {mount_path} failed: {e}")
        return
    try:
        mount_path.rmdir()
        # Try to rmdir the parent scratch root too (may fail if other scratch
        # dirs exist from concurrent runs -- that's OK).
        mount_path.parent.rmdir()
    except OSError:
        pass


# ============================================================================
# Checkpoint & restore
# ============================================================================

def take_checkpoint(
    pid: int,
    slot_dir: Path,
    proj: Path,
    ram_limit_gb: int,
    zstd_threads: int,
) -> dict:
    """Execute one full pre-dump + final-dump + compress cycle.

    Returns a dict of timing and size stats. Caller is responsible for
    rotation and latest.txt updates.

    Sequence:
      1. Mount tmpfs scratch, create <slot_dir>.
      2. `criu pre-dump` -> tmpfs/pre  (process keeps running)
      3. Record current log-file line counts for use at resume time.
      4. Spawn criu-image-streamer capture | zstd > <slot>/final.tzst
      5. `criu dump --prev-images-dir=tmpfs/pre -D <sock_dir>` (brief freeze)
      6. Wait for the streamer+zstd pipeline to finish.
      7. Compress tmpfs/pre into <slot>/pre.tzst (no freeze -- already
         running by now).
      8. Write <slot>/meta.json including log_line_counts for resume roll-back.
      9. umount tmpfs scratch.
    """
    slot_dir.mkdir(parents=True, exist_ok=True)
    cycle_start = time.time()

    tmpfs = mount_tmpfs_scratch(ram_limit_gb)
    pre_dir = tmpfs / "pre"

    sock_dir = Path(STREAMER_SOCK_ROOT) / f"sock_{os.getpid()}"
    if sock_dir.exists():
        shutil.rmtree(sock_dir)
    sock_dir.mkdir(parents=True)

    freeze_sec = 0.0
    try:
        # --- Step 2: pre-dump (no freeze) -------------------------------
        pre_start = time.time()
        _run_criu_predump(pid, pre_dir)
        pre_dump_sec = time.time() - pre_start
        print(f"  pre-dump:  {pre_dump_sec:.1f}s (process kept running)")

        # --- Step 3: record log line counts -----------------------------
        # Done AFTER pre-dump but BEFORE the freeze, minimizing the window
        # in which the process can write log lines we won't account for.
        # Any lines written between this record and the actual freeze will
        # be discarded on resume -- acceptable, because the restored
        # process memory image predates them and will re-emit whatever
        # logs it needs from its resumed state.
        log_line_counts = record_log_line_counts(logs_dir(proj))
        print(f"  logs:      recorded line counts for "
              f"{len(log_line_counts)} file(s)")

        # --- Step 4+5: streamed final dump (brief freeze) ---------------
        # The streamer serves a UNIX socket in sock_dir; criu-dump writes
        # imagery to that socket instead of to a local directory, and the
        # streamer pipes the bytes out via stdout into our zstd pipeline
        # that terminates in slot/final.tzst.
        final_tzst = slot_dir / "final.tzst"
        freeze_start = time.time()
        _run_streamed_final_dump(
            pid, pre_dir, sock_dir, final_tzst, zstd_threads,
        )
        freeze_sec = time.time() - freeze_start
        print(f"  final:     {freeze_sec:.1f}s (process FROZEN)")

        # --- Step 7: compress pre-dump imagery --------------------------
        # Process is running again by now; this compression is off the
        # critical path. We still care about wall time only for cycle stats.
        compress_start = time.time()
        pre_tzst = slot_dir / "pre.tzst"
        _compress_dir_to_tzst(pre_dir, pre_tzst, zstd_threads)
        compress_sec = time.time() - compress_start
        print(f"  compress:  {compress_sec:.1f}s (process running)")

        # --- Step 8: meta.json ------------------------------------------
        slot_size = dir_size_bytes(slot_dir)
        meta = {
            "timestamp": datetime.now().isoformat(),
            "worker_pid": pid,
            "pre_dump_sec": pre_dump_sec,
            "freeze_sec": freeze_sec,
            "compress_sec": compress_sec,
            "slot_size_bytes": slot_size,
            "host": os.uname().nodename,
            # Log line counts at checkpoint time; used on resume to roll
            # log files back so the restored process appends cleanly.
            "log_line_counts": log_line_counts,
        }
        (slot_dir / "meta.json").write_text(json.dumps(meta, indent=2))

    finally:
        # Always clean up scratch + socket dir, even on failure.
        umount_tmpfs_scratch(tmpfs)
        shutil.rmtree(sock_dir, ignore_errors=True)

    total_sec = time.time() - cycle_start
    return {
        "total_sec": total_sec,
        "freeze_sec": freeze_sec,
        "slot_size_bytes": dir_size_bytes(slot_dir),
    }


def _run_criu_predump(pid: int, out_dir: Path) -> None:
    """Invoke `criu pre-dump --track-mem -t <pid> -D <out_dir>`.

    --track-mem enables soft-dirty memory tracking so the subsequent
    `criu dump` only needs to copy pages dirtied since the pre-dump,
    dramatically shrinking the freeze window.
    """
    cmd = [
        "criu", "pre-dump",
        "--track-mem",
        "-t", str(pid),
        "-D", str(out_dir),
        "--shell-job",   # tolerates the worker being a daemon without a ctty
    ]
    _run_checked(cmd, "criu pre-dump")


def _run_streamed_final_dump(
    pid: int,
    pre_dir: Path,
    sock_dir: Path,
    out_tzst: Path,
    zstd_threads: int,
) -> None:
    """Run `criu dump` writing imagery through criu-image-streamer | zstd.

    Two cooperating subprocesses form the output pipeline:

        criu-image-streamer -D sock_dir capture
            |  (pipe)
            v
        zstd -T<n> -3
            |  (pipe)
            v
        out_tzst

    Then CRIU is invoked with -D sock_dir so it finds the streamer's
    socket and writes imagery into the stream instead of to a local dir.
    --leave-running thaws the process after the dump is flushed to the
    streamer (NOT after it's committed to disk -- the tail of zstd writes
    continues after the freeze ends).
    """
    # Build pipeline: streamer | zstd > out_tzst
    with open(out_tzst, "wb") as out_fh:
        streamer = subprocess.Popen(
            ["criu-image-streamer", "-D", str(sock_dir), "capture"],
            stdout=subprocess.PIPE,
        )
        zstd = subprocess.Popen(
            ["zstd", f"-T{zstd_threads}", "-3", "-q"],
            stdin=streamer.stdout,
            stdout=out_fh,
        )
        # Close our copy of the streamer->zstd pipe so zstd sees EOF
        # when the streamer exits.
        streamer.stdout.close()

        # Wait for the streamer to create its socket. If it dies early,
        # bail out before criu tries to connect.
        sock_path = sock_dir / "streamer.sock"
        deadline = time.time() + 30
        while not sock_path.exists():
            if streamer.poll() is not None:
                raise RuntimeError(
                    f"criu-image-streamer exited early "
                    f"(rc={streamer.returncode}) before creating socket"
                )
            if time.time() > deadline:
                raise RuntimeError(
                    "timed out waiting for criu-image-streamer socket"
                )
            time.sleep(0.05)

        # Now run criu dump. The process is frozen from when criu seizes
        # it (early in this call) to when --leave-running resumes it.
        _run_checked(
            [
                "criu", "dump",
                "-t", str(pid),
                "--prev-images-dir", str(pre_dir),
                "-D", str(sock_dir),
                "--leave-running",
                "--shell-job",
            ],
            "criu dump",
        )

        # Drain the pipeline.
        streamer_rc = streamer.wait()
        zstd_rc = zstd.wait()
        if streamer_rc != 0:
            raise RuntimeError(
                f"criu-image-streamer exited rc={streamer_rc}"
            )
        if zstd_rc != 0:
            raise RuntimeError(f"zstd exited rc={zstd_rc}")


def _compress_dir_to_tzst(
    src_dir: Path, out_tzst: Path, zstd_threads: int,
) -> None:
    """Tar+zstd a directory into a single compressed archive.

    Used to fold the pre-dump imagery (which lives in tmpfs) into the
    persistent slot directory. We stream tar into zstd so nothing has to
    materialize on disk between the two.
    """
    with open(out_tzst, "wb") as out_fh:
        tar = subprocess.Popen(
            ["tar", "-C", str(src_dir), "-cf", "-", "."],
            stdout=subprocess.PIPE,
        )
        zstd = subprocess.Popen(
            ["zstd", f"-T{zstd_threads}", "-3", "-q"],
            stdin=tar.stdout,
            stdout=out_fh,
        )
        tar.stdout.close()
        tar_rc = tar.wait()
        zstd_rc = zstd.wait()
        if tar_rc != 0:
            raise RuntimeError(f"tar exited rc={tar_rc}")
        if zstd_rc != 0:
            raise RuntimeError(f"zstd exited rc={zstd_rc}")


def _run_checked(cmd: list, label: str) -> None:
    """subprocess.run wrapper that surfaces stderr on failure.

    CRIU's error messages are useful but only on stderr, and
    subprocess.run's default CalledProcessError message omits them.
    """
    res = subprocess.run(cmd, capture_output=True, text=True)
    if res.returncode != 0:
        print(f"--- {label} FAILED (rc={res.returncode}) ---")
        if res.stdout:
            print("stdout:\n" + res.stdout)
        if res.stderr:
            print("stderr:\n" + res.stderr)
        raise RuntimeError(f"{label} failed with rc={res.returncode}")


def restore_from_latest(proj: Path) -> int:
    """Warm-restore the worker from the current latest slot.

    Streams pre.tzst + final.tzst back into a criu-image-streamer in
    "serve" mode, then invokes `criu restore`. The Rust binary is NOT
    re-invoked -- its in-memory state is resurrected verbatim, which is
    why no b_resume flag is needed on this path.

    Returns the restored worker PID.
    """
    latest = read_latest(proj)
    if not latest:
        sys.exit(
            "ERROR: resume mode but no latest.txt in "
            f"{checkpoints_dir(proj)}. Nothing to resume from."
        )
    slot = checkpoints_dir(proj) / latest
    pre_tzst = slot / "pre.tzst"
    final_tzst = slot / "final.tzst"
    meta_path = slot / "meta.json"
    if not pre_tzst.exists() or not final_tzst.exists():
        sys.exit(f"ERROR: slot {slot} is missing pre.tzst or final.tzst.")

    print(f"Restoring from slot: {latest}")

    # --- Roll back log files BEFORE criu restore --------------------------
    # Must happen before the process is resurrected: CRIU reopens the log
    # files on restore, and for the daemon log it seeks to the write
    # position saved at checkpoint time. That position == checkpoint-time
    # file size, so we need the on-disk file to match that size (via line-
    # count truncation) for appends to land cleanly at EOF.
    if meta_path.exists():
        try:
            meta = json.loads(meta_path.read_text())
            line_counts = meta.get("log_line_counts", {}) or {}
            if line_counts:
                print(f"  Rolling back {len(line_counts)} log file(s) "
                      f"to checkpoint-time line counts ...")
                truncate_log_files_to_counts(logs_dir(proj), line_counts)
        except (json.JSONDecodeError, OSError) as e:
            # Don't abort restore over a cosmetic issue -- log and continue.
            # Worst case the logs get a gap, process still runs correctly.
            print(f"  WARN: could not roll back logs "
                  f"(meta.json error: {e}). Proceeding anyway.")
    else:
        print(f"  WARN: {meta_path.name} missing; skipping log roll-back.")

    # --- Prepare tmpfs + streamer for criu restore ------------------------
    # Decompress pre.tzst into a tmpfs scratch dir (so criu can use it as
    # --prev-images-dir), and stream final.tzst through the streamer in
    # serve mode. The process comes up with all original in-memory state.
    tmpfs = mount_tmpfs_scratch(ram_limit_gb=512)  # generous fixed size
    try:
        pre_dir = tmpfs / "pre"
        # Decompress pre.tzst -> tmpfs/pre
        print("  Decompressing pre-dump imagery into tmpfs ...")
        _decompress_tzst_to_dir(pre_tzst, pre_dir)

        # Stream final.tzst via streamer serve mode; criu restore connects
        # via the socket dir.
        sock_dir = Path(STREAMER_SOCK_ROOT) / f"restore_sock_{os.getpid()}"
        if sock_dir.exists():
            shutil.rmtree(sock_dir)
        sock_dir.mkdir(parents=True)

        try:
            print("  Streaming final dump via criu-image-streamer serve ...")
            pid = _streamed_restore(final_tzst, pre_dir, sock_dir)
        finally:
            shutil.rmtree(sock_dir, ignore_errors=True)
    finally:
        umount_tmpfs_scratch(tmpfs)

    print(f"Restored worker PID: {pid}")
    return pid


def _decompress_tzst_to_dir(in_tzst: Path, out_dir: Path) -> None:
    """Inverse of _compress_dir_to_tzst -- extract into out_dir."""
    out_dir.mkdir(parents=True, exist_ok=True)
    with open(in_tzst, "rb") as in_fh:
        zstd = subprocess.Popen(
            ["zstd", "-d", "-q"],
            stdin=in_fh,
            stdout=subprocess.PIPE,
        )
        tar = subprocess.Popen(
            ["tar", "-C", str(out_dir), "-xf", "-"],
            stdin=zstd.stdout,
        )
        zstd.stdout.close()
        zstd_rc = zstd.wait()
        tar_rc = tar.wait()
        if zstd_rc != 0:
            raise RuntimeError(f"zstd -d exited rc={zstd_rc}")
        if tar_rc != 0:
            raise RuntimeError(f"tar -x exited rc={tar_rc}")


def _streamed_restore(
    final_tzst: Path, prev_images: Path, sock_dir: Path,
) -> int:
    """Run `criu restore` with imagery served by criu-image-streamer.

    Returns the restored worker PID (read from criu's --pidfile output).
    """
    pidfile = Path(f"/tmp/zkregplus_cr_restore_{os.getpid()}.pid")
    if pidfile.exists():
        pidfile.unlink()

    with open(final_tzst, "rb") as in_fh:
        zstd = subprocess.Popen(
            ["zstd", "-d", "-c", "-q"],
            stdin=in_fh,
            stdout=subprocess.PIPE,
        )
        streamer = subprocess.Popen(
            ["criu-image-streamer", "-D", str(sock_dir), "serve"],
            stdin=zstd.stdout,
        )
        zstd.stdout.close()

        # Wait for socket to be ready
        sock_path = sock_dir / "streamer.sock"
        deadline = time.time() + 30
        while not sock_path.exists():
            if streamer.poll() is not None:
                raise RuntimeError(
                    "criu-image-streamer (serve) exited early"
                )
            if time.time() > deadline:
                raise RuntimeError("timed out waiting for streamer socket")
            time.sleep(0.05)

        # Invoke criu restore. It reads from the streamer socket and also
        # uses --prev-images-dir to load the pre-dump layer.
        _run_checked(
            [
                "criu", "restore",
                "-D", str(sock_dir),
                "--prev-images-dir", str(prev_images),
                "--pidfile", str(pidfile),
                "--shell-job",
                "--restore-detached",
            ],
            "criu restore",
        )

        zstd.wait()
        streamer.wait()

    if not pidfile.exists():
        raise RuntimeError("criu restore did not write pidfile")
    pid = int(pidfile.read_text().strip())
    pidfile.unlink()
    return pid


# ============================================================================
# Main loop
# ============================================================================

def checkpoint_loop(
    proj: Path,
    pid: int,
    interval_min: int,
    ram_limit_gb: int,
    slot_count: int,
    zstd_threads: int,
) -> None:
    """Run the periodic checkpoint cycle until the worker exits or Ctrl-C.

    Per tick: child-safety check -> RAM check -> dump -> rotate -> report.
    On KeyboardInterrupt we leave the worker alone (user's running job).
    """
    print()
    print("=" * 70)
    print(f"Starting checkpoint loop:")
    print(f"  worker PID      : {pid}")
    print(f"  interval        : {interval_min} min")
    print(f"  RAM skip limit  : {ram_limit_gb} GB")
    print(f"  slots kept      : {slot_count}")
    print(f"  zstd threads    : {zstd_threads}")
    print("=" * 70)
    print()

    interval_sec = interval_min * 60
    cycle_num = 0

    try:
        while True:
            # Sleep first so we don't checkpoint immediately at t=0 --
            # worker needs time to allocate and start real work.
            print(
                f"[{_now()}] Sleeping {interval_min} min "
                f"until next cycle..."
            )
            time.sleep(interval_sec)
            cycle_num += 1

            if not pid_is_alive(pid):
                # Worker is gone. Decide whether this was a clean finish
                # (wipe storage) or an abort (preserve for resume).
                if run_completed_successfully(proj):
                    freed = wipe_all_checkpoint_storage(proj)
                    print(f"[{_now()}] Worker PID {pid} exited "
                          f"SUCCESSFULLY.")
                    print(f"  Reclaimed {fmt_bytes(freed)} of checkpoint "
                          f"storage. Exiting.")
                else:
                    print(f"[{_now()}] Worker PID {pid} exited without "
                          f"completion sentinel.")
                    print(f"  Treating as abort (crash / preemption / "
                          f"manual kill). Checkpoint slots preserved at "
                          f"{checkpoints_dir(proj)}")
                    print(f"  Rerun with 'resume' to continue from the "
                          f"latest slot.")
                return

            print()
            print("-" * 70)
            print(f"[{_now()}] Cycle #{cycle_num}")
            print("-" * 70)

            # 1. Child-safety check (aborts script on violation).
            check_no_children(pid)

            # 2. RAM skip check.
            rss_gb = measure_rss_gb(pid)
            print(
                f"  worker VmRSS = {rss_gb:.2f} GB "
                f"(limit = {ram_limit_gb} GB)"
            )
            if rss_gb > ram_limit_gb:
                print(f"  [SKIP] RSS above limit; skipping this cycle.")
                continue

            # 3. Pick target slot (never the current latest).
            target_slot_name = pick_target_slot(proj, slot_count)
            target_slot = checkpoints_dir(proj) / target_slot_name
            # Defensive: clean any stale leftovers in the target slot from
            # an interrupted previous attempt.
            if target_slot.exists():
                shutil.rmtree(target_slot)

            print(f"  [CHECKPOINT] dumping into {target_slot_name} ...")

            # 4. Do the actual dump cycle.
            try:
                stats = take_checkpoint(
                    pid=pid,
                    slot_dir=target_slot,
                    proj=proj,
                    ram_limit_gb=ram_limit_gb,
                    zstd_threads=zstd_threads,
                )
            except Exception as e:
                print(f"  ERROR during checkpoint: {e}")
                # Don't tear down the script -- one bad cycle shouldn't
                # kill a 32-hour run. Leave the prior slot intact.
                shutil.rmtree(target_slot, ignore_errors=True)
                continue

            # 5. Promote the new slot and clean up rotated-out slots.
            write_latest(proj, target_slot_name)
            if slot_count == 2:
                # Keep the newly-latest + the other slot (if it exists).
                keep = SLOT_NAMES
            else:
                keep = (target_slot_name,)
            cleanup_obsolete_slots(proj, keep)

            # 6. Report.
            total_ckpt_bytes = dir_size_bytes(checkpoints_dir(proj))
            print(f"  [DONE] freeze={stats['freeze_sec']:.1f}s  "
                  f"total_cycle={stats['total_sec']:.1f}s  "
                  f"slot_size={fmt_bytes(stats['slot_size_bytes'])}  "
                  f"total_on_disk={fmt_bytes(total_ckpt_bytes)}")

    except KeyboardInterrupt:
        print()
        print(f"[{_now()}] Interrupted by user. Worker PID {pid} left "
              f"running. Exiting checkpoint loop.")


def _now() -> str:
    return datetime.now().strftime("%Y-%m-%d %H:%M:%S")


# ============================================================================
# Entry point
# ============================================================================

def main() -> None:
    # ---- Phase 1: collect all inputs before we touch anything ----
    # We ask for the mode selection first because it decides whether we
    # truncate or append checkrun.log.
    print("zkregplus CRIU checkpoint orchestrator")
    print()

    mode = prompt_mode()
    run_mode = prompt_choice(
        "Run mode", ("new", "resume"), default="new",
    )
    interval_min = prompt_int(
        "Checkpoint interval in minutes", default=60,
    )
    ram_limit_gb = prompt_int(
        "Skip checkpoint if worker VmRSS exceeds (GB)", default=300,
    )
    slot_count = prompt_int(
        "Slot count (1 or 2)", default=2, min_val=1,
    )
    if slot_count not in (1, 2):
        sys.exit("ERROR: slot count must be 1 or 2.")
    default_vcpus = os.cpu_count() or 8
    vcpus = prompt_int(
        "vCPU count on this machine", default=default_vcpus,
    )
    zstd_threads = compute_zstd_threads(vcpus)

    # ---- Phase 2: install tee, run preflight checks ----
    is_new = (run_mode == "new")
    install_tee(is_new_mode=is_new)

    print()
    print(f"[{_now()}] Starting run")
    print(f"  mode          : {mode}  ({MODE_DESCRIPTIONS[mode]})")
    print(f"  run_mode      : {run_mode}")
    print(f"  interval      : {interval_min} min")
    print(f"  ram_limit     : {ram_limit_gb} GB")
    print(f"  slot_count    : {slot_count}")
    print(f"  vcpus         : {vcpus}")
    print(f"  zstd_threads  : {zstd_threads}")
    print()

    require_root()
    for bin_name in ("criu", "criu-image-streamer", "zstd",
                     "tar", "pgrep", "ps", "mount", "umount"):
        require_binary(bin_name)

    proj = proj_root()
    print(f"  proj_root     : {proj}")

    # ---- Phase 3: new vs resume bootstrap ----
    if is_new:
        wipe_checkpoints(proj)
        # Any leftover sentinel from a previous run would cause the very
        # first "worker gone" detection to wipe our fresh checkpoints.
        clear_completion_sentinel(proj)
        if mode == 1:
            spawn_mode1(proj)
        else:
            remind_manual_mode2(proj)
        pid = find_worker_pid(mode)
    else:
        # Resume: the binary's already absent; we restore it from latest.
        # (Mode parameter is still used by find_worker_pid for the PID we
        #  get back from criu restore -- verify it matches expectation.)
        pid = restore_from_latest(proj)

    # ---- Phase 4: monitor + checkpoint loop ----
    checkpoint_loop(
        proj=proj,
        pid=pid,
        interval_min=interval_min,
        ram_limit_gb=ram_limit_gb,
        slot_count=slot_count,
        zstd_threads=zstd_threads,
    )


if __name__ == "__main__":
    main()
