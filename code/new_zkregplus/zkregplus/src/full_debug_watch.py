#!/usr/bin/env python3
"""
full_debug_watch.py — minimal watcher for the full_debug test.

Runs `cargo test ... test_full_debug_main` from zkregplus/src/, waits
for it to exit, and bundles dump.txt + per-job logs + extracted
77317.x probe lines + env/git info into a single .tgz for offline
analysis.

Designed for the post-fail-fast world: install_fail_fast_panic_hook()
in foldpot_main calls process::abort() within milliseconds of any
panic in a rayon worker (e.g. the check_logup assertion), so this
script just needs to launch + wait + collect. NO silence-detection
loop, NO gdb attach, NO source patching — full_debug is a dedicated
test function.

Usage:
    cd zkregplus/src
    python3 full_debug_watch.py              # foreground (default)
    python3 full_debug_watch.py --daemon     # detach, log to file

Env passthrough (set in the parent shell or by this script):
    ZKR_PROBE_77317=1       enable the 77317.x probes (set by us)
    ZKR_ALLOW_PTRACE_ANY=1  no effect under fail-fast; harmless
    RUST_BACKTRACE=1        full backtrace in panic output (set by us)
"""

import argparse
import json
import os
import re
import shutil
import signal
import subprocess
import sys
import tarfile
import time
from datetime import datetime
from pathlib import Path

# ---- python version gate ----------------------------------------
_PY_MIN = (3, 6)
if sys.version_info < _PY_MIN:
    sys.exit(f"ERR: full_debug_watch.py needs Python >= {_PY_MIN[0]}."
             f"{_PY_MIN[1]}; got {sys.version_info[:3]}")

# ---- paths ------------------------------------------------------
SRC_DIR = Path(__file__).resolve().parent             # zkregplus/src
ZKREGPLUS_DIR = SRC_DIR.parent                         # zkregplus
REPO_ROOT = ZKREGPLUS_DIR.parent                       # new_zkregplus
PER_JOB_LOG_DIR = REPO_ROOT / "data/cache/logs"
DAEMON_LOG_DEST = PER_JOB_LOG_DIR / "zkregplus.log"
SENTINEL = REPO_ROOT / "data/cache/run_complete.sentinel"
ANALYZE_LOG = SRC_DIR / "full_debug_watch_log.txt"

# Hard cap so a runaway prover doesn't hold the bundler forever.
# full_debug is single-job, 4 small files; even a clean success
# should fit well under this. fail-fast abort fires in ms.
MAX_RUNTIME_S = 4 * 3600  # 4 hours

# ============================================================
# Logging
# ============================================================
def _ts():
    return datetime.now().strftime("%Y-%m-%dT%H:%M:%S")

def log(level, msg, **kw):
    line = f"{_ts()} {level} {msg}"
    if kw:
        line += " " + json.dumps(kw, default=str)
    print(line, flush=True)
    try:
        with open(ANALYZE_LOG, "a") as f:
            f.write(line + "\n")
    except OSError:
        pass

# ============================================================
# Preflight
# ============================================================
REQUIRED_CACHE = [
    "data/cache/full_data/vec_sigs.txt",
    "data/cache/full_clamav/g16_main.key",
    "data/cache/full_clamav/g16_cp.key",
]
REQUIRED_DATA = [
    "data/debug/full_debug/config/binexec_debug.dat",
    "data/debug/full_clamav/config/main.dat",
    "data/debug/full_clamav/config/main_dfa.dat",
    "data/debug/full_clamav/config/needs_ised.dat",
    "data/debug/full_clamav/config/needs_ised_igc.dat",
]

def preflight():
    if not shutil.which("cargo"):
        log("ERROR", "cargo not on PATH")
        sys.exit(1)
    missing_cache = [p for p in REQUIRED_CACHE
                     if not (REPO_ROOT / p).exists()]
    if missing_cache:
        log("ERROR",
            "Required cache files missing — run "
            "full_clamav_setup first",
            missing=missing_cache)
        sys.exit(1)
    missing_data = [p for p in REQUIRED_DATA
                    if not (REPO_ROOT / p).exists()]
    if missing_data:
        log("ERROR", "Required data files missing",
            missing=missing_data)
        sys.exit(1)
    log("INFO", "preflight OK",
        cwd_is_src=(Path.cwd() == SRC_DIR))

# ============================================================
# Launch
# ============================================================
def launch_prover(dump_path: Path) -> subprocess.Popen:
    """Run cargo test test_full_debug_main, tee stdout/stderr to
    dump_path. Returns the Popen handle.

    We do NOT use compile2.sh — that wrapper is for the multi-rung
    deadlock_detect.py flow. Here, plain cargo + fail-fast abort is
    enough; if the prover panics check_logup, abort() fires within
    milliseconds and cargo test exits non-zero.
    """
    env = os.environ.copy()
    env["ZKR_PROBE_77317"]      = "1"
    env["RUST_BACKTRACE"]       = "1"
    # Belt-and-suspenders: ptrace-any is harmless under fail-fast,
    # leave it in case a non-panic stall ever sneaks back.
    env["ZKR_ALLOW_PTRACE_ANY"] = "1"
    # Allow core dumps from the abort()-style fail-fast path. We can
    # only ulimit -c the parent we exec; the cargo child inherits.
    # If the user already has a higher limit set, this is a no-op.
    try:
        import resource
        resource.setrlimit(resource.RLIMIT_CORE,
                           (resource.RLIM_INFINITY,
                            resource.RLIM_INFINITY))
    except (ImportError, ValueError, OSError) as e:
        log("WARN", f"could not raise core dump limit: {e}")
    cmd = [
        "cargo", "test", "--lib", "--release", "--",
        "test_full_debug_main",
        "--show-output", "--nocapture",
    ]
    log("INFO", "launching prover",
        cmd=" ".join(cmd), dump=str(dump_path))
    with open(dump_path, "wb") as f:
        proc = subprocess.Popen(
            cmd, cwd=str(SRC_DIR), env=env,
            stdout=f, stderr=subprocess.STDOUT,
            start_new_session=True)
    log("INFO", f"prover pid={proc.pid}")
    return proc

def wait_for_exit(proc: subprocess.Popen) -> int:
    """Block until proc exits or MAX_RUNTIME_S, whichever first.
    Returns the exit code (or -signal on timeout-kill)."""
    start = time.monotonic()
    deadline = start + MAX_RUNTIME_S
    while True:
        rc = proc.poll()
        if rc is not None:
            log("INFO", f"prover exited rc={rc} "
                f"elapsed_s={int(time.monotonic() - start)}")
            return rc
        if time.monotonic() > deadline:
            log("ERROR", "MAX_RUNTIME exceeded, killing prover")
            try:
                os.killpg(os.getpgid(proc.pid), signal.SIGTERM)
            except ProcessLookupError:
                pass
            try:
                proc.wait(timeout=30)
            except subprocess.TimeoutExpired:
                try:
                    os.killpg(os.getpgid(proc.pid),
                              signal.SIGKILL)
                except ProcessLookupError:
                    pass
                proc.wait()
            return -1
        time.sleep(2)

# ============================================================
# Classify + extract
# ============================================================
PANIC_RE      = re.compile(r"^FAIL-FAST: prover panic", re.M)
PANIC_AT_RE   = re.compile(
    r"panicked at ([^\n]+):\s*\n([^\n]+)", re.M)
PROBE_LINE_RE = re.compile(r"^DEBUG USE 77317\.[\w.]+:?", re.M)

def classify(rc: int, dump_path: Path) -> str:
    text = ""
    try:
        text = dump_path.read_text(errors="replace")
    except OSError:
        pass
    if rc == 0 and SENTINEL.exists():
        return "SUCCESS"
    if PANIC_RE.search(text):
        return "PANIC_FAILFAST"
    if "panicked at" in text:
        return "PANIC"
    if rc < 0:
        return "TIMEOUT"
    return "OTHER"

def parse_panic_site(dump_path: Path) -> str:
    try:
        text = dump_path.read_text(errors="replace")
    except OSError:
        return ""
    m = PANIC_AT_RE.search(text)
    if not m:
        return ""
    return f"{m.group(1).strip()} -- {m.group(2).strip()}"

def first_probe_mismatch(text: str) -> str:
    """Find the first MULTISET_MISMATCH line. The tag (e.g. 6, 5, 4,
    3, 2.raw, 1) localizes which call-site noticed it FIRST. That
    answers 'host-side vs circuit-side bug'."""
    for line in text.splitlines():
        if "MULTISET_MISMATCH" in line:
            return line.strip()
    return "(none — multisets all agreed; bug is downstream of "\
           "checks, e.g. inside check_logup's inverse step)"

# ============================================================
# Bundle
# ============================================================
def setup_bundle_dir() -> Path:
    ts = datetime.now().strftime("%Y%m%d_%H%M%S")
    d = SRC_DIR / f"full_debug_{ts}"
    d.mkdir(parents=True, exist_ok=False)
    return d

def package(bundle_dir: Path, rc: int, dump_path: Path):
    outcome = classify(rc, dump_path)
    panic_site = parse_panic_site(dump_path)

    log("INFO", "packaging",
        bundle=str(bundle_dir), outcome=outcome, rc=rc)

    # 1. dump.txt (move into bundle)
    bundle_dump = bundle_dir / "dump.txt"
    try:
        shutil.copy(dump_path, bundle_dump)
    except OSError as e:
        log("WARN", f"copy dump.txt failed: {e}")

    # 2. per-job logs
    for p in PER_JOB_LOG_DIR.glob("log_job_*.txt"):
        try:
            shutil.copy(p, bundle_dir / p.name)
        except OSError as e:
            log("WARN", f"copy {p.name} failed: {e}")

    # 3. daemon log
    if DAEMON_LOG_DEST.exists():
        try:
            shutil.copy(DAEMON_LOG_DEST,
                        bundle_dir / "zkregplus.log")
        except OSError as e:
            log("WARN", f"copy zkregplus.log failed: {e}")

    # 4. probe extraction
    probes_path = bundle_dir / "probes_77317.txt"
    sources = [bundle_dir / "dump.txt"]
    sources += sorted(bundle_dir.glob("log_job_*.txt"))
    if (bundle_dir / "zkregplus.log").exists():
        sources.append(bundle_dir / "zkregplus.log")
    with open(probes_path, "w") as out:
        for src in sources:
            try:
                txt = src.read_text(errors="replace")
            except OSError:
                continue
            for line in txt.splitlines():
                if PROBE_LINE_RE.match(line):
                    out.write(f"[{src.name}] {line}\n")
    probe_text = probes_path.read_text(errors="replace")
    first_mismatch = first_probe_mismatch(probe_text)

    # 5. env / git
    write_env(bundle_dir)
    write_git(bundle_dir)

    # 6. core dump if present
    for c in REPO_ROOT.glob("core*"):
        try:
            shutil.copy(c, bundle_dir / c.name)
            log("INFO", f"bundled core dump {c.name}")
        except OSError:
            pass

    # 7. summary.txt — the headline you read first
    write_summary(bundle_dir, outcome, rc, panic_site,
                  first_mismatch)

    # 8. tar-gz
    tgz_path = SRC_DIR / f"{bundle_dir.name}.tgz"
    with tarfile.open(tgz_path, "w:gz") as t:
        t.add(bundle_dir, arcname=bundle_dir.name)
    size = tgz_path.stat().st_size
    log("INFO", "package_tgz",
        path=str(tgz_path), size_bytes=size)
    # Echo the path so the user can scp it without ls-hunting.
    print()
    print("=" * 60)
    print(f"  bundle directory: {bundle_dir}")
    print(f"  tgz for download: {tgz_path}  ({size:,} B)")
    print("=" * 60)
    return tgz_path

def write_env(bundle_dir: Path):
    lines = [f"hostname: {os.uname().nodename}",
             f"date: {_ts()}",
             f"user: {os.environ.get('USER', '?')}"]
    for cmd in (["cargo", "--version"], ["rustc", "--version"],
                ["uname", "-a"]):
        try:
            out = subprocess.check_output(
                cmd, stderr=subprocess.STDOUT, timeout=5)
            lines.append(
                f"{cmd[0]} {cmd[1]} -> {out.decode().strip()}")
        except (FileNotFoundError, subprocess.TimeoutExpired,
                subprocess.CalledProcessError) as e:
            lines.append(f"{cmd[0]} {cmd[1]} -> ERR: {e}")
    (bundle_dir / "env.txt").write_text("\n".join(lines) + "\n")

def write_git(bundle_dir: Path):
    if not shutil.which("git"):
        return
    try:
        log_out = subprocess.check_output(
            ["git", "log", "-10", "--oneline"],
            cwd=str(REPO_ROOT), timeout=10).decode()
        (bundle_dir / "git_log.txt").write_text(log_out)
    except Exception as e:
        log("WARN", f"git log failed: {e}")
    try:
        diff_out = subprocess.check_output(
            ["git", "diff"], cwd=str(REPO_ROOT),
            timeout=30).decode(errors="replace")
        # Cap at 5 MB; if larger, just keep the stat.
        if len(diff_out) > 5_000_000:
            stat_out = subprocess.check_output(
                ["git", "diff", "--stat"],
                cwd=str(REPO_ROOT), timeout=10).decode()
            (bundle_dir / "git_diff.txt").write_text(
                "DIFF >5MB, showing --stat instead:\n\n"
                + stat_out)
        else:
            (bundle_dir / "git_diff.txt").write_text(diff_out)
    except Exception as e:
        log("WARN", f"git diff failed: {e}")

def write_summary(bundle_dir, outcome, rc, panic_site,
                  first_mismatch):
    summary = [
        f"timestamp: {_ts()}",
        f"outcome:   {outcome}",
        f"rc:        {rc}",
        f"panic_at:  {panic_site or '(no panic detected)'}",
        f"first_77317_mismatch:",
        f"  {first_mismatch}",
        "",
        "interpretation hints:",
        "  77317.6 mismatch -> bug in build_statement / gen_m_table",
        "                      (host-side construction is wrong)",
        "  77317.5 mismatch -> bug in stmt vector layout indices",
        "                      between StatementInst and stmt vec",
        "  77317.4/3 mismatch -> bug in to_vec_fp_var / from_vec",
        "                       (slicing into wtns_var.statement)",
        "  only 77317.1 fires -> bug inside check_logup's inverse",
        "                        step (look at 77317.2 r_u64)",
        "  (no MULTISET_MISMATCH but assert fired) -> r_val may",
        "    be pathological; check 77317.2 r_u64",
        "",
        "files:",
        "  probes_77317.txt  -- start here (sorted probe lines)",
        "  dump.txt          -- cargo stdout/stderr (panic + bt)",
        "  log_job_0.txt     -- per-job log (single job in full_debug)",
        "  zkregplus.log     -- daemon log (if any)",
    ]
    (bundle_dir / "summary.txt").write_text(
        "\n".join(summary) + "\n")

# ============================================================
# Main
# ============================================================
def main():
    ap = argparse.ArgumentParser(
        description="full_debug watcher")
    ap.add_argument("--no-clear-sentinel", action="store_true",
                    help="don't remove run_complete.sentinel "
                         "before launch")
    args = ap.parse_args()

    # Sentinel reset so SUCCESS detection isn't a stale signal.
    if not args.no_clear_sentinel and SENTINEL.exists():
        try:
            SENTINEL.unlink()
            log("INFO", f"cleared stale sentinel: {SENTINEL}")
        except OSError as e:
            log("WARN", f"could not clear sentinel: {e}")

    preflight()
    bundle_dir = setup_bundle_dir()
    dump_path = bundle_dir / "dump.txt.live"
    proc = launch_prover(dump_path)
    rc = wait_for_exit(proc)
    package(bundle_dir, rc, dump_path)
    # The live dump was copied into the bundle; remove the work
    # file so the next invocation starts clean.
    try:
        dump_path.unlink()
    except OSError:
        pass

if __name__ == "__main__":
    main()
