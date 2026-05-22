#!/usr/bin/env python3
"""
par_data.py -- parallel-jobs data sweep driver

Sweeps `num_jobs` in `zkp_driver::full_par` over [1, 2, 4, 6, ..., n],
runs ./compile.sh once per value, and records:
  - the SPEED (MB/hour) reported on the LAST `PERF 1006` line in
    data/cache/logs/log_job_0.txt
  - the average + maximum CPU % (top-style: 100% = one core)
  - the average + maximum resident-set RAM (GB)
of the cargo-test worker process, sampled every 10 s starting once
"prove_step cost" first appears in the log.

A single in-place edit is performed on zkregplus/src/zkp_driver.rs to
swap the literal in `let num_jobs:usize = ...;` *inside full_par() only*.
The original file bytes are restored on every exit path (normal end,
exception, Ctrl+C, kill).

Run from anywhere; uses absolute paths. No CLI args -- prompts for n.
"""

import atexit
import hashlib
import os
import re
import signal
import subprocess
import sys
import time
from pathlib import Path
from typing import List, Optional, Tuple

import psutil

# ---------------------------------------------------------------------------
# Paths and constants
# ---------------------------------------------------------------------------

# proj_root = .../code/new_zkregplus  (parents[2] of this file)
PROJ_ROOT = Path(__file__).resolve().parents[2]
ZKP_DRIVER_RS = PROJ_ROOT / "zkregplus" / "src" / "zkp_driver.rs"
COMPILE_SH_DIR = PROJ_ROOT / "zkregplus" / "src"
COMPILE_SH = COMPILE_SH_DIR / "compile.sh"
LOG_JOB_0 = PROJ_ROOT / "data" / "cache" / "logs" / "log_job_0.txt"

# Cmdline regex for the cargo-test worker. Must match what `cargo test
# --lib --release -- test_zkreg_main` actually launches: a binary named
# target/release/deps/zkregplus-<16hex> with `test_zkreg_main` somewhere
# on its argv. Applied to descendants of compile_proc only -- we never
# scan the global process table, so stale workers from prior runs in
# other working directories cannot be matched by accident.
WORKER_REGEX = r"target/release/deps/zkregplus-[0-9a-f]+.*test_zkreg_main"
WORKER_CMDLINE_RE = re.compile(WORKER_REGEX)

# Anchors used to locate full_par() in zkp_driver.rs. The full signature
# (with generic + arg name) is intentionally specific so it cannot collide
# with any other function in the file.
FULL_PAR_HEADER = "fn full_par<F:PrimeField>(b_check_lkup: bool){"

# Pattern for the `let num_jobs:usize = N;` line inside full_par.
# Notes:
#  - `(?m)^` anchors at line start, and the indent group is `[ \t]*`
#    (whitespace only), so commented-out lines like
#        //let num_jobs:usize = 16;
#    are NOT matched. Without this anchor, the regex would match the
#    `let num_jobs:usize = 16` substring inside the comment.
#  - The `:usize` annotation is a secondary safeguard: the other
#    `num_jobs` declaration in this file (line ~1714) has no `:usize`.
NUM_JOBS_RE = re.compile(
    rb"(?m)^(?P<indent>[ \t]*)let\s+num_jobs\s*:\s*usize\s*=\s*(?P<val>\d+)\s*;"
)

# Polling cadence (seconds).
PID_POLL_SEC = 2          # how fast to retry pgrep waiting for worker
SAMPLE_SEC = 10           # CPU + RSS sample cadence after trigger
TRIGGER_TOKEN = b"prove_step cost"

# How long to keep waiting for the worker process to appear after
# compile.sh starts. cargo may need to rebuild on the first iteration,
# so we keep polling until compile.sh itself exits (indicating that
# either the build failed or the test finished without the worker
# being seen, both of which are terminal for this iteration).

# ---------------------------------------------------------------------------
# Source-file edit / restore (scoped to full_par())
# ---------------------------------------------------------------------------

# Module-level state used by the restore handler. Set when we first
# stash the original bytes and cleared after a successful restore.
_ORIG_BYTES: Optional[bytes] = None
_ORIG_SHA256: Optional[str] = None


def _scan_for_full_par_body(text: bytes) -> Tuple[int, int]:
    """
    Return (header_start, body_end_exclusive) byte offsets in `text` that
    delimit the full_par function body.

    `header_start` points at the first byte of FULL_PAR_HEADER.
    `body_end_exclusive` is one past the matching closing `}` of the
    function -- i.e. text[header_start:body_end_exclusive] contains the
    full function definition, header included.

    The brace-balancing scanner skips // line comments, /* */ block
    comments, and "..." / '...' literal contents so braces inside those
    don't perturb the depth counter. Rust raw strings (r#"..."#) are
    handled minimally: they are treated as ordinary "..." strings, which
    is fine for full_par() (it does not contain raw strings as of the
    pinned source). If you ever add raw strings inside full_par,
    extend the state machine.
    """
    header = FULL_PAR_HEADER.encode("utf-8")
    h = text.find(header)
    if h < 0:
        raise RuntimeError(
            f"could not locate full_par header in {ZKP_DRIVER_RS}: "
            f"expected literal {FULL_PAR_HEADER!r}")
    if text.find(header, h + 1) >= 0:
        raise RuntimeError(
            "full_par header literal appears more than once -- aborting "
            "to avoid editing the wrong copy")

    # Find the opening `{` of the body. The header literal already ends
    # in `{`, but to be safe, scan from h forward until we see one.
    i = text.find(b"{", h)
    if i < 0:
        raise RuntimeError("no opening brace after full_par header")
    body_open = i
    i = body_open + 1   # start scanning *after* the opening brace
    depth = 1

    # Tiny state machine over the byte stream.
    # State: NORMAL | LINE_COMMENT | BLOCK_COMMENT | STR | CHR
    NORMAL, LINE_COMMENT, BLOCK_COMMENT, STR, CHR = range(5)
    state = NORMAL
    n = len(text)
    while i < n and depth > 0:
        c = text[i:i+1]
        if state == NORMAL:
            if c == b"/" and i + 1 < n:
                nxt = text[i+1:i+2]
                if nxt == b"/":
                    state = LINE_COMMENT
                    i += 2
                    continue
                if nxt == b"*":
                    state = BLOCK_COMMENT
                    i += 2
                    continue
            if c == b'"':
                state = STR
                i += 1
                continue
            if c == b"'":
                # Could be a char literal OR a Rust lifetime ('a). The
                # heuristic: if the next non-letter byte after a single
                # backtick-free run isn't another `'`, this is a lifetime
                # and we should not enter CHR. We keep it simple: enter
                # CHR only when text matches a typical char-literal shape
                # ('x' or '\n' or '\xNN' or '\u{...}'). Otherwise treat
                # as a normal byte (lifetime).
                rest = text[i+1:i+8]
                # char literal ends with `'` within a few bytes of the
                # opener; lifetime never does.
                close = rest.find(b"'")
                if close >= 0:
                    state = CHR
                    i += 1
                    continue
                # else: lifetime, ignore
                i += 1
                continue
            if c == b"{":
                depth += 1
            elif c == b"}":
                depth -= 1
                if depth == 0:
                    return h, i + 1
            i += 1
            continue
        if state == LINE_COMMENT:
            if c == b"\n":
                state = NORMAL
            i += 1
            continue
        if state == BLOCK_COMMENT:
            if c == b"*" and text[i+1:i+2] == b"/":
                state = NORMAL
                i += 2
                continue
            i += 1
            continue
        if state == STR:
            if c == b"\\":
                # skip escape (handles \", \\, \n, etc.)
                i += 2
                continue
            if c == b'"':
                state = NORMAL
            i += 1
            continue
        if state == CHR:
            if c == b"\\":
                i += 2
                continue
            if c == b"'":
                state = NORMAL
            i += 1
            continue

    raise RuntimeError(
        "reached end of file without closing full_par body -- "
        "brace-balance scanner failed (unbalanced source?)")


def _stash_original_once() -> None:
    """Read zkp_driver.rs once and remember its bytes + sha256 for
    restoration on exit. Idempotent."""
    global _ORIG_BYTES, _ORIG_SHA256
    if _ORIG_BYTES is not None:
        return
    _ORIG_BYTES = ZKP_DRIVER_RS.read_bytes()
    _ORIG_SHA256 = hashlib.sha256(_ORIG_BYTES).hexdigest()


def restore_source_file() -> None:
    """Write original bytes back to zkp_driver.rs and verify hash.
    Safe to call multiple times. Used by atexit and signal handlers."""
    global _ORIG_BYTES
    if _ORIG_BYTES is None:
        return
    try:
        ZKP_DRIVER_RS.write_bytes(_ORIG_BYTES)
        check = hashlib.sha256(ZKP_DRIVER_RS.read_bytes()).hexdigest()
        if check != _ORIG_SHA256:
            sys.stderr.write(
                f"WARNING: restored zkp_driver.rs hash mismatch! "
                f"expected {_ORIG_SHA256}, got {check}\n")
    except Exception as e:
        sys.stderr.write(f"WARNING: failed to restore source: {e}\n")


def _signal_restore_and_exit(signo, _frame):
    """Signal handler: restore source then re-raise default behaviour."""
    restore_source_file()
    # Reset to default and re-raise so we exit with the proper status.
    signal.signal(signo, signal.SIG_DFL)
    os.kill(os.getpid(), signo)


def install_restore_handlers() -> None:
    atexit.register(restore_source_file)
    signal.signal(signal.SIGINT, _signal_restore_and_exit)
    signal.signal(signal.SIGTERM, _signal_restore_and_exit)
    signal.signal(signal.SIGHUP, _signal_restore_and_exit)


def set_num_jobs_in_full_par(new_value: int) -> None:
    """
    Edit zkp_driver.rs in place: rewrite the literal in
        let num_jobs:usize = N;
    *inside the full_par function body only*.

    Performs sanity checks before writing:
      - exactly one match inside the body window;
      - total file-wide count of `let num_jobs:usize = ...;` declarations
        is unchanged after the edit (we only changed the literal);
      - the byte offset of FULL_PAR_HEADER is unchanged after the edit.
    """
    _stash_original_once()
    text = bytes(_ORIG_BYTES)  # always edit from the pristine original
    h, body_end = _scan_for_full_par_body(text)
    body = text[h:body_end]

    matches = list(NUM_JOBS_RE.finditer(body))
    if len(matches) == 0:
        raise RuntimeError(
            "no `let num_jobs:usize = ...;` declaration found inside "
            "full_par() -- did the source change?")
    if len(matches) > 1:
        # Multiple typed declarations would be ambiguous. Bail.
        raise RuntimeError(
            f"found {len(matches)} `let num_jobs:usize = ...;` lines "
            f"inside full_par() -- expected exactly 1")

    m = matches[0]
    new_decl = m.group("indent") + f"let num_jobs:usize = {new_value};".encode()
    new_body = body[:m.start()] + new_decl + body[m.end():]
    new_text = text[:h] + new_body + text[body_end:]

    # Sanity: the count of typed declarations file-wide must match.
    pre_count = len(NUM_JOBS_RE.findall(text))
    post_count = len(NUM_JOBS_RE.findall(new_text))
    if pre_count != post_count:
        raise RuntimeError(
            f"typed-decl count changed during edit: {pre_count} -> "
            f"{post_count} (refusing to write)")

    # Sanity: header offset must be unchanged.
    new_h = new_text.find(FULL_PAR_HEADER.encode("utf-8"))
    if new_h != h:
        raise RuntimeError(
            "full_par header offset shifted after edit (refusing to write)")

    ZKP_DRIVER_RS.write_bytes(new_text)


# ---------------------------------------------------------------------------
# Worker discovery and monitoring
# ---------------------------------------------------------------------------

def find_worker_in_descendants(
        compile_proc: subprocess.Popen) -> Optional[int]:
    """
    Walk the descendant tree of compile_proc and return the PID of the
    first child whose cmdline matches WORKER_CMDLINE_RE, or None.

    Replaces an earlier `pgrep -nf` global scan. The pgrep approach
    could match unrelated test_zkreg_main processes still hanging around
    from prior runs (e.g. a previously-killed cargo test from a stale
    working directory), so we now restrict the search to children of
    the bash subprocess we just spawned.
    """
    try:
        parent = psutil.Process(compile_proc.pid)
        descendants = parent.children(recursive=True)
    except psutil.NoSuchProcess:
        return None
    for child in descendants:
        try:
            cmd = " ".join(child.cmdline())
        except (psutil.NoSuchProcess, psutil.AccessDenied):
            continue
        if WORKER_CMDLINE_RE.search(cmd):
            return child.pid
    return None


def wait_for_worker_pid(
        compile_proc: subprocess.Popen) -> Optional[int]:
    """
    Poll the descendant tree until either (a) the worker PID is found
    and returned, or (b) compile.sh exits before the worker ever
    appears (returns None).
    """
    while True:
        pid = find_worker_in_descendants(compile_proc)
        if pid is not None:
            return pid
        if compile_proc.poll() is not None:
            # compile.sh exited without us seeing a worker; one last
            # look in case it appeared between checks.
            return find_worker_in_descendants(compile_proc)
        time.sleep(PID_POLL_SEC)


def log_contains_trigger(p: Path) -> bool:
    """Cheap O(filesize) scan for TRIGGER_TOKEN. Called at most once per
    SAMPLE_SEC until True; afterwards never re-checked."""
    if not p.exists():
        return False
    try:
        with open(p, "rb") as f:
            for line in f:
                if TRIGGER_TOKEN in line:
                    return True
    except OSError:
        return False
    return False


def _debug_cmdline(pid: int) -> str:
    """Best-effort read of /proc/<pid>/cmdline. Returns a printable string
    with NUL separators replaced by spaces. Used only for DEBUG USE 67321."""
    try:
        raw = Path(f"/proc/{pid}/cmdline").read_bytes()
        return raw.replace(b"\x00", b" ").decode("utf-8", "replace").strip()
    except Exception as e:
        return f"<unreadable: {e}>"


def monitor_worker(
        pid: int,
        log_path: Path,
        compile_proc: subprocess.Popen) -> Tuple[List[float], List[float]]:
    """
    Poll the worker every SAMPLE_SEC. Once TRIGGER_TOKEN appears in
    log_path, start collecting CPU% and RSS samples. Stops when the
    worker process exits.

    Returns (cpu_samples, rss_gb_samples). Either may be empty if the
    trigger never fired or the worker died first.
    """
    cpu_samples: List[float] = []
    rss_samples: List[float] = []

    # DEBUG USE 67321.1: verify the PID we attached to is actually the
    # test binary (vs. a short-lived build subprocess or cargo itself).
    print(f"    DEBUG USE 67321.1: pid={pid} cmdline={_debug_cmdline(pid)!r}",
          flush=True)

    try:
        proc = psutil.Process(pid)
    except psutil.NoSuchProcess:
        print("    DEBUG USE 67321.2: psutil.Process(pid) raised "
              "NoSuchProcess immediately on attach", flush=True)
        return cpu_samples, rss_samples

    # Prime psutil's CPU accounting. After this, every cpu_percent(None)
    # returns the % CPU consumed since the previous call (top-style:
    # 100% = one core fully busy, regardless of core count).
    try:
        prime0 = proc.cpu_percent(None)
        # DEBUG USE 67321.3: priming call should return 0.0 per psutil docs.
        print(f"    DEBUG USE 67321.3: prime cpu_percent={prime0} "
              f"status={proc.status()} nthreads={proc.num_threads()}",
              flush=True)
    except psutil.NoSuchProcess:
        print("    DEBUG USE 67321.4: process vanished during prime",
              flush=True)
        return cpu_samples, rss_samples

    triggered = False
    tick = 0
    while True:
        time.sleep(SAMPLE_SEC)
        tick += 1

        # Liveness check first -- if the worker is gone, stop.
        try:
            if not proc.is_running():
                print(f"    DEBUG USE 67321.5: tick={tick} proc.is_running="
                      f"False -- breaking", flush=True)
                break
            st = proc.status()
            if st == psutil.STATUS_ZOMBIE:
                print(f"    DEBUG USE 67321.6: tick={tick} zombie -- "
                      f"breaking", flush=True)
                break
        except psutil.NoSuchProcess:
            print(f"    DEBUG USE 67321.7: tick={tick} liveness check "
                  f"NoSuchProcess -- breaking", flush=True)
            break

        # Belt-and-braces: also stop if compile.sh itself exited (the
        # worker should be gone before this, but cover the race).
        if compile_proc.poll() is not None:
            # Take one final sample then stop.
            try:
                cpu = proc.cpu_percent(None)
                rss_bytes = proc.memory_info().rss
                rss = rss_bytes / (1024 ** 3)
                print(f"    DEBUG USE 67321.8: tick={tick} compile.sh exited;"
                      f" final cpu={cpu} rss_bytes={rss_bytes} rss_gb={rss}"
                      f" triggered={triggered}", flush=True)
                if triggered:
                    cpu_samples.append(cpu)
                    rss_samples.append(rss)
            except psutil.NoSuchProcess:
                print(f"    DEBUG USE 67321.9: tick={tick} compile.sh exited;"
                      f" NoSuchProcess on final sample", flush=True)
                pass
            break

        if not triggered:
            # Cheap log-scan: only until the trigger fires.
            if log_contains_trigger(log_path):
                triggered = True
                print(f"    DEBUG USE 67321.10: tick={tick} trigger fired; "
                      f"re-priming and continuing", flush=True)
                # Re-prime so the first post-trigger sample reflects a
                # clean SAMPLE_SEC window after the trigger fired.
                try:
                    proc.cpu_percent(None)
                except psutil.NoSuchProcess:
                    print(f"    DEBUG USE 67321.11: tick={tick} re-prime "
                          f"NoSuchProcess -- breaking", flush=True)
                    break
                # Skip taking a sample on this tick.
                continue
            else:
                # Not triggered yet. Don't append any sample.
                print(f"    DEBUG USE 67321.12: tick={tick} trigger not yet "
                      f"in {log_path} (status={st})", flush=True)
                continue

        # Triggered: collect a CPU + RSS sample.
        try:
            cpu = proc.cpu_percent(None)
            rss_bytes = proc.memory_info().rss
            rss = rss_bytes / (1024 ** 3)
            nth = proc.num_threads()
        except psutil.NoSuchProcess:
            print(f"    DEBUG USE 67321.13: tick={tick} sample read "
                  f"NoSuchProcess -- breaking", flush=True)
            break
        print(f"    DEBUG USE 67321.14: tick={tick} cpu={cpu} "
              f"rss_bytes={rss_bytes} rss_gb={rss:.3f} status={st} "
              f"nthreads={nth}", flush=True)
        cpu_samples.append(cpu)
        rss_samples.append(rss)

    return cpu_samples, rss_samples


# ---------------------------------------------------------------------------
# Log-file parsing
# ---------------------------------------------------------------------------

# The Step-1 PERF 1006 line is the only one carrying SPEED. Regex is kept
# loose enough to tolerate other text on the line.
SPEED_RE = re.compile(
    r"PERF\s+1006[^\n]*?SPEED:\s*([0-9.]+)\s*MB/hour",
    re.IGNORECASE,
)


def extract_last_perf_1006_speed(p: Path) -> Optional[float]:
    """Return the SPEED value from the LAST PERF 1006 line in `p` that
    contains a SPEED: ... MB/hour field, or None if not found."""
    if not p.exists():
        return None
    last: Optional[float] = None
    try:
        with open(p, "rb") as f:
            for raw in f:
                line = raw.decode("utf-8", errors="replace")
                m = SPEED_RE.search(line)
                if m:
                    try:
                        last = float(m.group(1))
                    except ValueError:
                        pass
    except OSError:
        return None
    return last


# ---------------------------------------------------------------------------
# Per-iteration driver
# ---------------------------------------------------------------------------

def build_sequence(n: int) -> List[int]:
    """Return [1, 2, 4, 6, ..., n]. n must be even and >= 2."""
    if n < 2 or n % 2 != 0:
        raise ValueError(f"n must be an even integer >= 2, got {n}")
    seq = [1] + list(range(2, n + 1, 2))
    return seq


def fmt_or_na(v, spec: str) -> str:
    if v is None:
        return "N/A"
    return format(v, spec)


def run_one_iteration(num_jobs: int) -> dict:
    """Run a single sweep step with the given num_jobs value. Returns
    a dict with keys: num_jobs, speed, cpu_avg, cpu_max, rss_avg,
    rss_max. Any field may be None on failure."""
    print(f"\n=== iteration: num_jobs = {num_jobs} ===", flush=True)

    # 1. Edit zkp_driver.rs (scoped to full_par body).
    set_num_jobs_in_full_par(num_jobs)
    print(f"  patched zkp_driver.rs: num_jobs = {num_jobs}", flush=True)

    # 2. Wipe the log so we never read stale data from a prior run if
    #    the worker dies before writing anything. (The Rust logger
    #    overwrites on first touch when b_resume=false anyway, but
    #    deleting up-front is a defensive belt.)
    try:
        LOG_JOB_0.unlink()
    except FileNotFoundError:
        pass

    # 3. Spawn ./compile.sh in its own process group so we can clean it
    #    up wholesale on Ctrl+C (the signal handler for SIGINT will
    #    re-raise after restoring the source; before re-raising, the
    #    process-group teardown happens via the OS once the script
    #    exits).
    print(f"  launching {COMPILE_SH}...", flush=True)
    compile_proc = subprocess.Popen(
        ["bash", str(COMPILE_SH)],
        cwd=str(COMPILE_SH_DIR),
        start_new_session=True,
    )

    # 4. Wait for the worker PID to appear.
    pid = wait_for_worker_pid(compile_proc)
    if pid is None:
        print("  ERROR: worker PID never appeared (compile.sh exited "
              "before worker spawned). Recording N/A.", flush=True)
        compile_proc.wait()
        return {
            "num_jobs": num_jobs,
            "speed": None, "cpu_avg": None, "cpu_max": None,
            "rss_avg": None, "rss_max": None,
        }
    print(f"  worker PID = {pid}", flush=True)
    # DEBUG USE 67321.0: print the process we captured so we can see if
    # pgrep found the test binary or some other matching subprocess.
    print(f"  DEBUG USE 67321.0: captured cmdline="
          f"{_debug_cmdline(pid)!r}", flush=True)

    # 5. Monitor until worker exits.
    cpu_samples, rss_samples = monitor_worker(pid, LOG_JOB_0, compile_proc)
    print(f"  collected {len(cpu_samples)} CPU samples, "
          f"{len(rss_samples)} RSS samples", flush=True)

    # 6. Wait for compile.sh to fully exit (cargo prints summary).
    compile_proc.wait()
    print(f"  compile.sh exited (rc = {compile_proc.returncode})",
          flush=True)

    # 7. Parse the last PERF 1006 SPEED line.
    speed = extract_last_perf_1006_speed(LOG_JOB_0)
    if speed is None:
        print("  WARNING: no PERF 1006 SPEED line in log_job_0.txt",
              flush=True)
    else:
        print(f"  PERF 1006 SPEED = {speed} MB/hour", flush=True)

    cpu_avg = sum(cpu_samples) / len(cpu_samples) if cpu_samples else None
    cpu_max = max(cpu_samples) if cpu_samples else None
    rss_avg = sum(rss_samples) / len(rss_samples) if rss_samples else None
    rss_max = max(rss_samples) if rss_samples else None

    return {
        "num_jobs": num_jobs,
        "speed": speed,
        "cpu_avg": cpu_avg, "cpu_max": cpu_max,
        "rss_avg": rss_avg, "rss_max": rss_max,
    }


# ---------------------------------------------------------------------------
# Output table
# ---------------------------------------------------------------------------

def print_results_table(rows: List[dict]) -> None:
    headers = [
        "num_jobs", "speed (MB/hr)",
        "avg_cpu%", "max_cpu%",
        "avg_rss_gb", "max_rss_gb",
    ]
    body = []
    for r in rows:
        body.append([
            str(r["num_jobs"]),
            fmt_or_na(r["speed"], ".4f"),
            fmt_or_na(r["cpu_avg"], ".1f"),
            fmt_or_na(r["cpu_max"], ".1f"),
            fmt_or_na(r["rss_avg"], ".2f"),
            fmt_or_na(r["rss_max"], ".2f"),
        ])
    widths = [max(len(h), *(len(row[i]) for row in body))
              for i, h in enumerate(headers)]

    def fmt_row(cells):
        return " | ".join(c.ljust(w) for c, w in zip(cells, widths))

    sep = "-+-".join("-" * w for w in widths)
    print()
    print("=" * (sum(widths) + 3 * (len(widths) - 1)))
    print("FINAL RESULTS")
    print("=" * (sum(widths) + 3 * (len(widths) - 1)))
    print(fmt_row(headers))
    print(sep)
    for cells in body:
        print(fmt_row(cells))


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main() -> None:
    # Phase 0: install restore handlers FIRST so any failure below is
    # caught and the source file is restored.
    install_restore_handlers()

    # Phase 1: prompt for n.
    raw = input("Enter even number n (sweep is [1, 2, 4, 6, ..., n]): ")
    try:
        n = int(raw.strip())
    except ValueError:
        print(f"ERROR: '{raw}' is not an integer.", file=sys.stderr)
        sys.exit(1)
    try:
        sequence = build_sequence(n)
    except ValueError as e:
        print(f"ERROR: {e}", file=sys.stderr)
        sys.exit(1)
    print(f"sweep sequence: {sequence}", flush=True)

    # Sanity preflight: required files exist.
    for p in (ZKP_DRIVER_RS, COMPILE_SH):
        if not p.exists():
            print(f"ERROR: required file missing: {p}", file=sys.stderr)
            sys.exit(1)

    # Stash original bytes once up front (also done lazily inside
    # set_num_jobs_in_full_par, but doing it here means even if the very
    # first edit fails for a parsing reason we still have the stash for
    # the restore handler -- which is a no-op since we never wrote, but
    # the symmetry is cleaner).
    _stash_original_once()

    # Phase 2: sweep.
    rows: List[dict] = []
    for i in sequence:
        try:
            row = run_one_iteration(i)
        except Exception as e:
            print(f"  ERROR in iteration num_jobs={i}: {e}",
                  file=sys.stderr, flush=True)
            row = {
                "num_jobs": i,
                "speed": None, "cpu_avg": None, "cpu_max": None,
                "rss_avg": None, "rss_max": None,
            }
        rows.append(row)
        # Restore source between iterations so a Ctrl+C mid-sweep
        # always leaves a clean tree (atexit also fires, but earlier
        # is better).
        restore_source_file()
        # Re-stash for next iteration (no-op if bytes unchanged).
        _stash_original_once()

    # Phase 3: report.
    print_results_table(rows)


if __name__ == "__main__":
    main()
