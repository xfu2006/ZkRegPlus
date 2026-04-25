#!/usr/bin/env python3
"""
test_run_checkpoints.py -- driver to validate run_checkpoints.py end-to-end.

Three interactive phases (you pick at startup):

  [1] baseline -- run ./compile.sh straight (no CRIU). Times the run, saves
                  data/cache/logs/* into /tmp/mylogs/baseline_<ts>/, records
                  T (wall time) + K = T // (interval*60) checkpoint windows.

  [2] simple   -- [a] launch run_checkpoints.py in checkpoint mode, wait for
                      2 [DONE] events, SIGKILL the worker, SIGINT the script.
                  [b] launch run_checkpoints.py in resume mode, wait for
                      natural exit, snapshot logs, compare to baseline.

  [3] full     -- using K from latest baseline, run serial scenarios. For
                  each chosen k, fresh checkpoint-mode run -> wait for the
                  k-th [DONE] -> sleep 30s -> SIGKILL worker -> SIGINT
                  script -> resume to completion -> compare logs.

Comparison checks per log_job_*.txt:
  (a) PERF tag distribution within +/- 10%.
  (b) Final anchor (last SPEED MB/hr or last `prove_step cost for ...`)
      matches verbatim after normalization.
  (c) No new ERROR/FATAL/PANIC lines vs baseline.
  (d) Total line count within +/- 20%.

Normalization (before comparison): durations, ISO timestamps, pids, and
memory amounts are masked. PERF tag numbers, word_id/seg_id/stmt_len, log
levels are kept untouched.

Requirements: root; criu / criu-image-streamer / zstd on PATH for phases
2 and 3. Pre-warms cargo so compile time doesn't eat the test window.
"""

import atexit
import json
import os
import re
import shutil
import signal
import subprocess
import sys
import threading
import time
from datetime import datetime
from pathlib import Path

# ============================================================================
# Constants
# ============================================================================

WORKER_PATTERN = (
    r"target/release/deps/zkregplus-[0-9a-f]+.*test_zkreg_main"
)

MYLOGS_ROOT = Path("/tmp/mylogs")
TMPFS_SCRATCH_ROOT = Path("/tmp/zkregplus_cr_scratch")

# Run config injected into run_checkpoints.py prompts (mode 1, 2 min,
# 40 GB RAM cap, 2 slots).
INTERVAL_MIN = 2
RAM_LIMIT_GB = 40
SLOT_COUNT = 2
KILL_DELAY_SEC = 30

# Wait budgets.
DONE_WAIT_SEC = 30 * 60        # any single [DONE] arrival
RESUME_TIMEOUT_PADDING = 600   # extra seconds on top of 1.5x baseline T
SCRIPT_EXIT_GRACE_SEC = 120    # grace after we SIGINT the script

# Comparison tolerances.
TAG_COUNT_TOLERANCE = 0.10
LINE_COUNT_TOLERANCE = 0.20

# ============================================================================
# Cleanup-tracking state (used by atexit + signal handlers).
# ============================================================================

SPAWNED_PROCS: list = []   # subprocess.Popen we own
WORKER_PIDS: list = []     # pids reported by run_checkpoints.py


# ============================================================================
# Path helpers
# ============================================================================

def src_dir() -> Path:
    return Path(__file__).resolve().parent


def proj_root() -> Path:
    return Path(__file__).resolve().parents[2]


def logs_dir() -> Path:
    return proj_root() / "data" / "cache" / "logs"


def checkpoints_dir() -> Path:
    return proj_root() / "data" / "cache" / "checkpoints"


def sentinel_path() -> Path:
    return proj_root() / "data" / "cache" / "run_complete.sentinel"


# ============================================================================
# Logging (driver-side; not the worker's per-job logs)
# ============================================================================

def log(msg: str) -> None:
    ts = datetime.now().strftime("%H:%M:%S")
    print(f"[{ts}] {msg}", flush=True)


# ============================================================================
# Cleanup
# ============================================================================

def _kill_proc(p: subprocess.Popen) -> None:
    if p.poll() is not None:
        return
    try:
        p.terminate()
    except Exception:
        pass
    try:
        p.wait(timeout=5)
    except subprocess.TimeoutExpired:
        try:
            p.kill()
        except Exception:
            pass


def _kill_pid(pid: int) -> None:
    try:
        os.kill(pid, signal.SIGKILL)
    except ProcessLookupError:
        pass
    except PermissionError:
        pass


def _unmount_stale_scratch() -> None:
    if not TMPFS_SCRATCH_ROOT.exists():
        return
    for entry in TMPFS_SCRATCH_ROOT.iterdir():
        if not entry.is_dir():
            continue
        subprocess.run(
            ["umount", str(entry)],
            capture_output=True,
        )
        try:
            entry.rmdir()
        except OSError:
            pass


def _cleanup() -> None:
    for p in SPAWNED_PROCS:
        _kill_proc(p)
    for pid in WORKER_PIDS:
        _kill_pid(pid)
    _unmount_stale_scratch()


atexit.register(_cleanup)


def _sig_handler(signum, _frame):
    log(f"received signal {signum}; cleaning up and exiting")
    _cleanup()
    sys.exit(1)


for _sig in (signal.SIGINT, signal.SIGTERM, signal.SIGHUP):
    signal.signal(_sig, _sig_handler)


# ============================================================================
# Preflight
# ============================================================================

def require_root() -> None:
    if os.geteuid() != 0:
        sys.exit(
            "ERROR: must run as root.\n"
            "       Try: sudo python3 test_run_checkpoints.py"
        )


def require_binary(name: str) -> None:
    if shutil.which(name) is None:
        sys.exit(f"ERROR: required binary '{name}' not on PATH")


def kill_stale_workers() -> None:
    res = subprocess.run(
        ["pgrep", "-f", WORKER_PATTERN],
        capture_output=True, text=True,
    )
    pids = [int(x) for x in res.stdout.split() if x.strip().isdigit()]
    for pid in pids:
        log(f"  killing stale worker pid={pid}")
        _kill_pid(pid)


def warn_if_tmp_is_tmpfs() -> None:
    res = subprocess.run(
        ["findmnt", "-no", "FSTYPE", "/tmp"],
        capture_output=True, text=True,
    )
    if res.stdout.strip() == "tmpfs":
        log("WARNING: /tmp is tmpfs; large log snapshots eat RAM.")
        log("         Move MYLOGS_ROOT in this script if that matters.")


# ============================================================================
# State reset (between phases / scenarios)
# ============================================================================

def wipe_run_state(wipe_logs: bool = True) -> None:
    """Reset checkpoint dir, sentinel, and (optionally) logs.

    wipe_logs=False is required between phase [a] and phase [b] of a
    resume scenario: run_checkpoints.py rolls the existing logs back to
    checkpoint-time line counts at restore, and our wiping would defeat
    that.
    """
    if checkpoints_dir().exists():
        shutil.rmtree(checkpoints_dir())
    if sentinel_path().exists():
        sentinel_path().unlink()
    if wipe_logs:
        if logs_dir().exists():
            shutil.rmtree(logs_dir())
        logs_dir().mkdir(parents=True, exist_ok=True)


def snapshot_logs(dst: Path) -> None:
    dst.mkdir(parents=True, exist_ok=True)
    if not logs_dir().exists():
        return
    for entry in logs_dir().iterdir():
        if entry.is_file():
            shutil.copy2(entry, dst / entry.name)


# ============================================================================
# Sub-process driver: run_checkpoints.py
# ============================================================================

def spawn_run_checkpoints(
    run_mode: str, work_dir: Path, vcpus: int,
) -> subprocess.Popen:
    """Spawn run_checkpoints.py as a child, feeding interactive prompts
    via stdin. Stdout+stderr come back as one combined text stream.
    """
    work_dir.mkdir(parents=True, exist_ok=True)
    cmd = ["python3", "-u", str(src_dir() / "run_checkpoints.py")]
    proc = subprocess.Popen(
        cmd,
        cwd=str(work_dir),
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        bufsize=1,
    )
    SPAWNED_PROCS.append(proc)
    answers = (
        "1\n"             # mode 1 (compile.sh)
        f"{run_mode}\n"   # 'new' or 'resume'
        f"{INTERVAL_MIN}\n"
        f"{RAM_LIMIT_GB}\n"
        f"{SLOT_COUNT}\n"
        f"{vcpus}\n"
    )
    proc.stdin.write(answers)
    proc.stdin.flush()
    proc.stdin.close()
    return proc


class ScriptWatcher:
    """Reads stdout of run_checkpoints.py line-by-line on a daemon thread.

    Mirrors each line to our console (prefixed) and updates shared state:
    worker pid, [DONE] count, error flag, exit flag. Provides
    wait_for_done(n) to block until N [DONE] events have been seen.
    """

    DONE_RE = re.compile(r"^\s*\[DONE\]")
    PID_RE = re.compile(r"Found worker PID:\s*(\d+)")
    RESTORE_PID_RE = re.compile(r"Restored worker PID:\s*(\d+)")
    ERROR_RE = re.compile(r"\b(ERROR|FATAL|PANIC|panicked)\b")

    def __init__(self, proc: subprocess.Popen, tag: str = "script"):
        self.proc = proc
        self.tag = tag
        self.lock = threading.Lock()
        self.done_count = 0
        self.worker_pid: int = 0
        self.error_seen = False
        self.exited = False
        self._evt = threading.Event()
        self._thr = threading.Thread(target=self._run, daemon=True)

    def start(self) -> None:
        self._thr.start()

    def _run(self) -> None:
        for line in iter(self.proc.stdout.readline, ""):
            line = line.rstrip("\n")
            print(f"  [{self.tag}] {line}", flush=True)
            with self.lock:
                m = self.PID_RE.search(line)
                if m:
                    self.worker_pid = int(m.group(1))
                    WORKER_PIDS.append(self.worker_pid)
                m = self.RESTORE_PID_RE.search(line)
                if m:
                    self.worker_pid = int(m.group(1))
                    WORKER_PIDS.append(self.worker_pid)
                if self.DONE_RE.search(line):
                    self.done_count += 1
                    self._evt.set()
                if self.ERROR_RE.search(line):
                    self.error_seen = True
        with self.lock:
            self.exited = True
        self._evt.set()

    def wait_for_done(self, n: int, timeout: float) -> bool:
        deadline = time.time() + timeout
        while time.time() < deadline:
            with self.lock:
                if self.done_count >= n:
                    return True
                if self.exited:
                    return False
            self._evt.wait(timeout=1.0)
            self._evt.clear()
        return False

    def wait_exit(self, timeout: float) -> bool:
        deadline = time.time() + timeout
        while time.time() < deadline:
            with self.lock:
                if self.exited:
                    return True
            self._evt.wait(timeout=1.0)
            self._evt.clear()
        return False


def kill_worker_then_script(
    watcher: ScriptWatcher, proc: subprocess.Popen,
) -> None:
    """SIGKILL the worker (so the run looks like a hard preemption),
    then SIGINT the script (so we don't wait the full 2 min interval
    for it to notice the worker is gone).
    """
    pid = watcher.worker_pid
    if pid:
        log(f"SIGKILL worker pid={pid}")
        _kill_pid(pid)
    log("SIGINT run_checkpoints.py for clean exit")
    try:
        proc.send_signal(signal.SIGINT)
    except ProcessLookupError:
        pass
    if not watcher.wait_exit(SCRIPT_EXIT_GRACE_SEC):
        log("WARN: script did not exit on SIGINT; SIGTERM")
        try:
            proc.terminate()
        except Exception:
            pass
        watcher.wait_exit(30)
    proc.wait()


# ============================================================================
# Cargo pre-warm
# ============================================================================

def prewarm_cargo() -> None:
    """Build the test binary so the timed phases don't include compile."""
    log("pre-warming cargo build (cargo test --no-run; can take minutes)")
    cargo_dir = src_dir().parent  # .../zkregplus/
    # No --lib filter args because --no-run rejects test name filters.
    res = subprocess.run(
        ["cargo", "test", "--lib", "--release", "--no-run"],
        cwd=str(cargo_dir),
    )
    if res.returncode != 0:
        sys.exit("ERROR: cargo --no-run build failed")
    log("pre-warm done")


# ============================================================================
# Phase 1 -- baseline
# ============================================================================

def phase_baseline(vcpus: int) -> Path:
    log("=" * 60)
    log("PHASE 1: BASELINE (no CRIU)")
    log("=" * 60)

    prewarm_cargo()
    wipe_run_state(wipe_logs=True)

    ts = datetime.now().strftime("%Y%m%d_%H%M%S")
    out_dir = MYLOGS_ROOT / f"baseline_{ts}"
    out_dir.mkdir(parents=True, exist_ok=True)
    log(f"output dir: {out_dir}")

    log("running ./compile.sh ...")
    t0 = time.time()
    res = subprocess.run(
        ["bash", "./compile.sh"],
        cwd=str(src_dir()),
    )
    T = time.time() - t0
    log(f"baseline finished in {T:.1f}s ({T/60:.2f} min) rc={res.returncode}")

    snapshot_logs(out_dir / "logs")
    K = int(T // (INTERVAL_MIN * 60))
    meta = {
        "timestamp": ts,
        "wall_time_sec": T,
        "interval_min": INTERVAL_MIN,
        "K": K,
        "rc": res.returncode,
    }
    (out_dir / "meta.json").write_text(json.dumps(meta, indent=2))
    log(f"snapshot saved; T={T:.1f}s K={K}")

    if res.returncode != 0:
        log("WARN: baseline rc != 0 -- comparison may be meaningless")
    return out_dir


# ============================================================================
# Phase 2 -- simple kill-after-2 + resume
# ============================================================================

def phase_simple(
    baseline_dir: Path, baseline_meta: dict, vcpus: int,
) -> bool:
    log("=" * 60)
    log("PHASE 2: SIMPLE (kill after 2 [DONE], then resume)")
    log("=" * 60)

    ts = datetime.now().strftime("%Y%m%d_%H%M%S")
    out_dir = MYLOGS_ROOT / f"simple_{ts}"
    (out_dir / "phase_a").mkdir(parents=True)
    (out_dir / "phase_b").mkdir(parents=True)
    log(f"output dir: {out_dir}")

    # ---- phase [a] -------------------------------------------------
    log("--- phase [a]: checkpoint mode, kill after 2nd [DONE] ---")
    wipe_run_state(wipe_logs=True)
    proc_a = spawn_run_checkpoints("new", out_dir / "phase_a", vcpus)
    watcher_a = ScriptWatcher(proc_a, tag="ckpt")
    watcher_a.start()

    log("waiting for 2nd [DONE] ...")
    if not watcher_a.wait_for_done(2, DONE_WAIT_SEC):
        log("ERROR: phase [a] did not reach 2 [DONE] events")
        kill_worker_then_script(watcher_a, proc_a)
        snapshot_logs(out_dir / "phase_a" / "logs")
        return False

    log("2 checkpoints made; killing worker now (no 30s delay in simple)")
    kill_worker_then_script(watcher_a, proc_a)
    snapshot_logs(out_dir / "phase_a" / "logs")

    # ---- phase [b] -------------------------------------------------
    log("--- phase [b]: resume mode (logs NOT wiped; script rolls back) ---")
    wipe_run_state(wipe_logs=False)  # keep logs; keep checkpoints
    proc_b = spawn_run_checkpoints("resume", out_dir / "phase_b", vcpus)
    watcher_b = ScriptWatcher(proc_b, tag="resume")
    watcher_b.start()

    timeout = int(baseline_meta["wall_time_sec"] * 1.5) \
        + RESUME_TIMEOUT_PADDING
    log(f"waiting up to {timeout}s for natural exit ...")
    if not watcher_b.wait_exit(timeout):
        log("ERROR: phase [b] timed out")
        kill_worker_then_script(watcher_b, proc_b)
        snapshot_logs(out_dir / "phase_b" / "logs")
        return False
    proc_b.wait()
    snapshot_logs(out_dir / "phase_b" / "logs")
    report_branch()

    # ---- compare ---------------------------------------------------
    log("comparing phase_b/logs to baseline/logs ...")
    cmp_result = compare_logs(
        baseline_dir / "logs",
        out_dir / "phase_b" / "logs",
    )
    (out_dir / "comparison.json").write_text(
        json.dumps(cmp_result, indent=2)
    )
    print_comparison(cmp_result)
    return all_pass(cmp_result) and not watcher_b.error_seen


# ============================================================================
# Phase 3 -- per-cycle serial scenarios
# ============================================================================

def phase_full(
    baseline_dir: Path,
    baseline_meta: dict,
    vcpus: int,
    scenarios: list,
) -> bool:
    K = baseline_meta["K"]
    log("=" * 60)
    log(f"PHASE 3: FULL (K={K}, scenarios={scenarios})")
    log("=" * 60)

    ts = datetime.now().strftime("%Y%m%d_%H%M%S")
    out_dir = MYLOGS_ROOT / f"full_{ts}"
    log(f"output dir: {out_dir}")

    results: dict = {}
    for k in scenarios:
        log("=" * 60)
        log(f"SCENARIO k={k}")
        log("=" * 60)
        sdir = out_dir / f"k={k}"
        (sdir / "phase_a").mkdir(parents=True)
        (sdir / "phase_b").mkdir(parents=True)

        # phase [a]
        wipe_run_state(wipe_logs=True)
        proc_a = spawn_run_checkpoints("new", sdir / "phase_a", vcpus)
        watcher_a = ScriptWatcher(proc_a, tag=f"ckpt-k{k}")
        watcher_a.start()

        log(f"waiting for {k}-th [DONE] ...")
        if not watcher_a.wait_for_done(k, DONE_WAIT_SEC):
            log(f"ERROR: scenario k={k} did not reach {k} [DONE]s")
            results[k] = {
                "pass": False,
                "reason": f"only {watcher_a.done_count} of {k} [DONE]s",
            }
            kill_worker_then_script(watcher_a, proc_a)
            snapshot_logs(sdir / "phase_a" / "logs")
            continue

        log(f"{k} checkpoint(s) made; sleeping {KILL_DELAY_SEC}s then "
            f"SIGKILL")
        time.sleep(KILL_DELAY_SEC)
        kill_worker_then_script(watcher_a, proc_a)
        snapshot_logs(sdir / "phase_a" / "logs")

        # phase [b]
        log("phase [b]: resume mode")
        wipe_run_state(wipe_logs=False)
        proc_b = spawn_run_checkpoints("resume", sdir / "phase_b", vcpus)
        watcher_b = ScriptWatcher(proc_b, tag=f"resume-k{k}")
        watcher_b.start()

        timeout = int(baseline_meta["wall_time_sec"] * 1.5) \
            + RESUME_TIMEOUT_PADDING
        if not watcher_b.wait_exit(timeout):
            log(f"ERROR: scenario k={k} phase [b] timed out")
            results[k] = {"pass": False, "reason": "phase_b timeout"}
            kill_worker_then_script(watcher_b, proc_b)
            snapshot_logs(sdir / "phase_b" / "logs")
            continue
        proc_b.wait()
        snapshot_logs(sdir / "phase_b" / "logs")
        report_branch()

        cmp_result = compare_logs(
            baseline_dir / "logs",
            sdir / "phase_b" / "logs",
        )
        (sdir / "comparison.json").write_text(
            json.dumps(cmp_result, indent=2)
        )
        print_comparison(cmp_result)
        passed = all_pass(cmp_result) and not watcher_b.error_seen
        results[k] = {"pass": passed}
        log(f"scenario k={k}: {'PASS' if passed else 'FAIL'}")

    # ---- summary ---------------------------------------------------
    log("=" * 60)
    log("PHASE 3 SUMMARY")
    log("=" * 60)
    for k in sorted(results.keys()):
        r = results[k]
        verdict = "PASS" if r.get("pass") else "FAIL"
        reason = r.get("reason", "")
        log(f"  k={k}: {verdict} {reason}")
    return all(r.get("pass") for r in results.values())


# ============================================================================
# Sentinel-branch reporter
# ============================================================================

def report_branch() -> None:
    """Print which exit branch the run took. Don't hard-assert -- the
    Rust side may not yet write the completion sentinel.
    """
    has_sentinel = sentinel_path().exists()
    has_slots = checkpoints_dir().exists() and any(
        p.is_dir() and p.name.startswith("slot_")
        for p in checkpoints_dir().iterdir()
    )
    if has_sentinel and not has_slots:
        log("BRANCH: SUCCESS (sentinel present, slots wiped)")
    elif (not has_sentinel) and has_slots:
        log("BRANCH: ABORT-LIKE (slots preserved, sentinel absent)")
        log("        (expected if Rust side does not yet write sentinel)")
    elif has_sentinel and has_slots:
        log("BRANCH: AMBIGUOUS (both sentinel and slots present)")
    else:
        log("BRANCH: AMBIGUOUS (neither sentinel nor slots)")


# ============================================================================
# Log comparison
# ============================================================================

NORM_PATTERNS = [
    # Floating-point durations.
    (re.compile(
        r"\b\d+\.\d+\s*(?:ms|s|sec|secs|seconds)\b",
        re.IGNORECASE,
    ), "<T>"),
    # Integer durations.
    (re.compile(
        r"\b\d+\s*(?:ms|sec|secs|seconds)\b",
        re.IGNORECASE,
    ), "<T>"),
    # ISO timestamps.
    (re.compile(
        r"\d{4}-\d{2}-\d{2}[T ]\d{2}:\d{2}:\d{2}(?:\.\d+)?"
    ), "<TS>"),
    # PIDs.
    (re.compile(
        r"\bpid[=: ]\s*\d+",
        re.IGNORECASE,
    ), "pid=<P>"),
    # Memory amounts.
    (re.compile(
        r"\b\d+(?:\.\d+)?\s*(?:MB|GB|KB|kB|Mb|Gb)\b"
    ), "<M>"),
]

PERF_TAG_RE = re.compile(r"\bPERF\s+(\d+)\b")
SPEED_RE = re.compile(r"SPEED\s+[\d.]+\s*MB/hr")
ANCHOR_RE = re.compile(r"prove_step cost for word_id:\s*\d+")
ERROR_RE = re.compile(r"\b(ERROR|FATAL|PANIC|panicked)\b")


def normalize(line: str) -> str:
    for pat, repl in NORM_PATTERNS:
        line = pat.sub(repl, line)
    return line


def collect_perf_tags(lines: list) -> dict:
    counts: dict = {}
    for line in lines:
        for m in PERF_TAG_RE.finditer(line):
            tag = m.group(1)
            counts[tag] = counts.get(tag, 0) + 1
    return counts


def find_last_anchor(lines: list) -> str:
    last_speed = None
    last_anchor = None
    for line in lines:
        if SPEED_RE.search(line):
            last_speed = line
        if ANCHOR_RE.search(line):
            last_anchor = line
    return last_speed if last_speed is not None else (last_anchor or "")


def find_errors(lines: list) -> list:
    return [l for l in lines if ERROR_RE.search(l)]


def compare_one_file(base_path: Path, test_path: Path) -> dict:
    if not base_path.exists():
        return {"pass": False, "reason": "baseline file missing"}
    if not test_path.exists():
        return {"pass": False, "reason": "test file missing"}

    base_raw = base_path.read_text(errors="replace").splitlines()
    test_raw = test_path.read_text(errors="replace").splitlines()
    base_norm = [normalize(l) for l in base_raw]
    test_norm = [normalize(l) for l in test_raw]

    # (a) tag distribution
    base_tags = collect_perf_tags(base_norm)
    test_tags = collect_perf_tags(test_norm)
    tag_pass = set(base_tags.keys()) == set(test_tags.keys())
    tag_diff: dict = {}
    if tag_pass:
        for tag, b in base_tags.items():
            t = test_tags.get(tag, 0)
            if b == 0:
                continue
            ratio = abs(t - b) / b
            tag_diff[tag] = {
                "baseline": b, "test": t,
                "diff_pct": round(ratio * 100, 1),
            }
            if ratio > TAG_COUNT_TOLERANCE:
                tag_pass = False
    else:
        tag_diff = {
            "baseline_tags": sorted(base_tags.keys()),
            "test_tags": sorted(test_tags.keys()),
        }

    # (b) anchor
    base_anchor = find_last_anchor(base_norm)
    test_anchor = find_last_anchor(test_norm)
    anchor_pass = (
        base_anchor != "" and test_anchor != ""
        and base_anchor == test_anchor
    )

    # (c) errors
    base_errors = set(find_errors(base_norm))
    test_errors = set(find_errors(test_norm))
    new_errors = sorted(test_errors - base_errors)
    error_pass = len(new_errors) == 0

    # (d) length
    bl = len(base_norm)
    tl = len(test_norm)
    if bl == 0:
        length_pass = (tl == 0)
    else:
        length_pass = abs(tl - bl) / bl <= LINE_COUNT_TOLERANCE

    return {
        "pass": tag_pass and anchor_pass and error_pass and length_pass,
        "tag_check": {"pass": tag_pass, "detail": tag_diff},
        "anchor_check": {
            "pass": anchor_pass,
            "baseline": base_anchor,
            "test": test_anchor,
        },
        "error_check": {
            "pass": error_pass,
            "new_errors": new_errors[:10],
        },
        "length_check": {
            "pass": length_pass, "baseline": bl, "test": tl,
        },
    }


def compare_logs(base_dir: Path, test_dir: Path) -> dict:
    if not base_dir.exists():
        return {"_err": f"baseline dir missing: {base_dir}"}
    results: dict = {}
    for entry in sorted(base_dir.iterdir()):
        if not entry.is_file():
            continue
        results[entry.name] = compare_one_file(
            entry, test_dir / entry.name,
        )
    # Flag any test files that don't appear in baseline.
    if test_dir.exists():
        base_names = {p.name for p in base_dir.iterdir() if p.is_file()}
        for entry in sorted(test_dir.iterdir()):
            if entry.is_file() and entry.name not in base_names:
                results[entry.name] = {
                    "pass": True,  # extra files don't fail comparison
                    "note": "present in test, absent in baseline",
                }
    return results


def all_pass(cmp_result: dict) -> bool:
    if "_err" in cmp_result:
        return False
    if not cmp_result:
        return False
    return all(r.get("pass") for r in cmp_result.values())


def print_comparison(cmp_result: dict) -> None:
    log("--- comparison results ---")
    if "_err" in cmp_result:
        log(f"  {cmp_result['_err']}")
        return
    for fname, r in cmp_result.items():
        verdict = "PASS" if r.get("pass") else "FAIL"
        log(f"  {fname}: {verdict}")
        if r.get("pass"):
            continue
        if "reason" in r:
            log(f"    reason: {r['reason']}")
        for check in ("tag_check", "anchor_check",
                      "error_check", "length_check"):
            cr = r.get(check)
            if cr and not cr.get("pass"):
                log(f"    {check}: FAIL")
                if check == "anchor_check":
                    log(f"      baseline: {cr.get('baseline')!r}")
                    log(f"      test    : {cr.get('test')!r}")
                if check == "length_check":
                    log(f"      baseline lines: {cr.get('baseline')}")
                    log(f"      test     lines: {cr.get('test')}")
                if check == "error_check":
                    for e in cr.get("new_errors", []):
                        log(f"      new error: {e}")


# ============================================================================
# Baseline finder
# ============================================================================

def find_latest_baseline() -> Path:
    if not MYLOGS_ROOT.exists():
        return None
    candidates = [
        d for d in MYLOGS_ROOT.iterdir()
        if d.is_dir() and d.name.startswith("baseline_")
        and (d / "meta.json").exists()
    ]
    if not candidates:
        return None
    return max(candidates, key=lambda p: p.name)


# ============================================================================
# Interactive prompts
# ============================================================================

def prompt_phase() -> int:
    print()
    print("Phase to run:")
    print("  [1] baseline   -- run ./compile.sh straight, snapshot logs")
    print("  [2] simple     -- kill after 2 [DONE], resume, compare")
    print("  [3] full       -- per-k serial kill+resume scenarios")
    while True:
        s = input("Choose [1/2/3]: ").strip()
        if s in ("1", "2", "3"):
            return int(s)
        print("  invalid; enter 1, 2, or 3")


def prompt_vcpus() -> int:
    default = os.cpu_count() or 8
    s = input(f"vCPUs on this machine [default {default}]: ").strip()
    if not s:
        return default
    try:
        v = int(s)
        if v < 1:
            print("  must be >= 1; using default")
            return default
        return v
    except ValueError:
        print("  invalid; using default")
        return default


def prompt_scenarios(K: int) -> list:
    print(f"K = {K} possible checkpoint cycles in baseline.")
    print("Which scenarios? Enter 'all' or 'k=<n>' where 1 <= n <= K.")
    while True:
        s = input("Choose: ").strip().lower()
        if s == "all":
            return list(range(1, K + 1))
        m = re.match(r"k\s*=\s*(\d+)\s*$", s)
        if m:
            n = int(m.group(1))
            if 1 <= n <= K:
                return [n]
            print(f"  out of range; need 1 <= n <= {K}")
        else:
            print("  invalid; enter 'all' or 'k=<n>'")


# ============================================================================
# Main
# ============================================================================

def main() -> int:
    require_root()

    print("=" * 60)
    print("test_run_checkpoints.py")
    print(f"  proj_root  : {proj_root()}")
    print(f"  MYLOGS_ROOT: {MYLOGS_ROOT}")
    print("=" * 60)

    phase = prompt_phase()
    vcpus = prompt_vcpus()

    warn_if_tmp_is_tmpfs()
    MYLOGS_ROOT.mkdir(parents=True, exist_ok=True)

    log("preflight: kill stale workers")
    kill_stale_workers()

    if phase != 1:
        log("preflight: check criu binaries")
        for b in ("criu", "criu-image-streamer", "zstd",
                  "tar", "pgrep", "ps", "mount", "umount",
                  "findmnt"):
            require_binary(b)
        log("preflight: criu check --all (warnings non-fatal)")
        res = subprocess.run(
            ["criu", "check", "--all"],
            capture_output=True, text=True,
        )
        if res.returncode != 0:
            log("  WARN: criu check --all reported issues")
            if res.stdout.strip():
                log(f"  stdout: {res.stdout.strip()}")
            if res.stderr.strip():
                log(f"  stderr: {res.stderr.strip()}")
        log("preflight: unmount stale scratch")
        _unmount_stale_scratch()

    if phase == 1:
        out = phase_baseline(vcpus)
        log(f"BASELINE saved at {out}")
        return 0

    base_dir = find_latest_baseline()
    if base_dir is None:
        sys.exit(
            f"ERROR: no baseline found under {MYLOGS_ROOT}. "
            "Run phase 1 first."
        )
    base_meta = json.loads((base_dir / "meta.json").read_text())
    log(f"using baseline {base_dir}")
    log(f"  T={base_meta['wall_time_sec']:.1f}s  K={base_meta['K']}")

    if phase == 2:
        ok = phase_simple(base_dir, base_meta, vcpus)
        log("=" * 60)
        log(f"PHASE 2 RESULT: {'PASS' if ok else 'FAIL'}")
        log("=" * 60)
        return 0 if ok else 1

    # phase == 3
    K = base_meta["K"]
    if K < 1:
        sys.exit(f"ERROR: baseline K={K}; no resume scenarios possible")
    scenarios = prompt_scenarios(K)
    ok = phase_full(base_dir, base_meta, vcpus, scenarios)
    log("=" * 60)
    log(f"PHASE 3 RESULT: {'PASS' if ok else 'FAIL'}")
    log("=" * 60)
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
