#!/usr/bin/env python3
"""
deadlock_detect.py  --  unattended fail-fast ladder runner.

Runs full_clamav in 4 progressively larger rungs (A, B, C, D). Each rung
launches ./compile2.sh with the watchdog env vars set, tails the dump,
classifies the outcome, and either advances (PASS) or stops the ladder
and packages everything into a single .tgz (FAIL).

Run from zkregplus/src/. It daemonizes (double-fork) and returns
immediately; progress is appended to ./analyze_log.txt. On success the
sentinel file ./FINISH is written. On failure the package path appears
in analyze_log.txt and as ./deadlock_detect_<rung>_<ts>.tgz.

Usage:
    cd zkregplus/src
    python3 deadlock_detect.py             # daemonized
    python3 deadlock_detect.py --no-daemon # foreground (for debugging)
    kill $(cat .deadlock_detect.pid)       # stop early
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

# ============================================================
# Paths and constants
# ============================================================
SRC_DIR = Path(__file__).resolve().parent              # zkregplus/src
ZKREGPLUS_DIR = SRC_DIR.parent                          # zkregplus
REPO_ROOT = ZKREGPLUS_DIR.parent                        # new_zkregplus
DRIVER_RS = (REPO_ROOT / "sonobe_mod/folding-schemes/"
             "src/folding/foldpot/driver.rs")
ZKP_DRIVER_RS = SRC_DIR / "zkp_driver.rs"
COMPILE_SH = SRC_DIR / "compile2.sh"
ANALYZE_LOG = SRC_DIR / "analyze_log.txt"
PID_FILE = SRC_DIR / ".deadlock_detect.pid"
FINISH_FILE = SRC_DIR / "FINISH"
PKG_PARENT = SRC_DIR / "deadlock_detect"  # per-rung pkg dirs go here

# 4 rungs. Cheap → expensive. Stop ladder at first failure.
RUNGS = [
    {"name": "A", "n_jobs": 2, "word_cap": 10,
     "watchdog_secs": 600,  "max_runtime_min": 30},
    {"name": "B", "n_jobs": 4, "word_cap": 20,
     "watchdog_secs": 1200, "max_runtime_min": 60},
    {"name": "C", "n_jobs": 8, "word_cap": 20,
     "watchdog_secs": 1800, "max_runtime_min": 90},
    {"name": "D", "n_jobs": 8, "word_cap": 0,
     "watchdog_secs": 3600, "max_runtime_min": 1440},
]

TICK_INTERVAL_S = 60

# ============================================================
# Logging
# ============================================================
def _ts():
    return datetime.now().isoformat(timespec="seconds")

def log(level, msg, **kv):
    extras = " ".join(f"{k}={v}" for k, v in kv.items())
    line = f"{_ts()} {level} {msg}"
    if extras:
        line += " " + extras
    try:
        with open(ANALYZE_LOG, "a") as f:
            f.write(line + "\n")
    except Exception:
        pass
    # Mirror to stdout (which is also analyze_log.txt after daemonize)
    try:
        print(line, flush=True)
    except Exception:
        pass

# ============================================================
# Daemonize (double-fork)
# ============================================================
def daemonize():
    """Double-fork, detach, redirect stdio to analyze_log.txt."""
    # First fork
    if os.fork() > 0:
        sys.exit(0)
    os.setsid()
    os.umask(0)
    # Second fork
    if os.fork() > 0:
        sys.exit(0)
    # Now we are the daemon. Redirect stdio.
    sys.stdout.flush()
    sys.stderr.flush()
    with open(os.devnull, "r") as f0:
        os.dup2(f0.fileno(), 0)
    log_fd = open(ANALYZE_LOG, "a")
    os.dup2(log_fd.fileno(), 1)
    os.dup2(log_fd.fileno(), 2)
    PID_FILE.write_text(f"{os.getpid()}\n")

# ============================================================
# Source patching (full_clamav num_jobs only; call site stays as-is
# if already set, otherwise we install a default call)
# ============================================================
NUM_JOBS_RE = re.compile(
    r"(let num_jobs = if b_setup \{1\} else \{)(\d+)(\};)")

# In test_zkreg_main, we want full_clamav called. We replace the
# currently-active line with our canonical call, and back up the file
# for full revert.
ACTIVE_CALL_RE = re.compile(
    r"^(\s*)(small_data|small_data2|small_data3|small_data_par|"
    r"small_data_debug|small_data4|full_data1|full_data2|full_data3|"
    r"full_data4|full_par|full_par2|full_clamav)::<Fr>\(([^)]*)\);\s*"
    r"//[^\n]*$",
    re.MULTILINE,
)
TARGET_CALL = ("\\1full_clamav::<Fr>(b_check_lkup, true, false); "
               "// deadlock_detect")

def patch_for_rung(n_jobs):
    """Edit driver.rs / zkp_driver.rs in place. Return (backup_driver,
    backup_zkp_driver) tuples for revert."""
    driver_backup = ZKP_DRIVER_RS.read_text()
    text = driver_backup
    # 1. Make sure test_zkreg_main calls full_clamav (light=true, setup=false)
    if "full_clamav::<Fr>(b_check_lkup, true, false);" not in text:
        # Find the FIRST active (non-commented) entry call. Active means
        # the line does NOT start with //.
        lines = text.splitlines(keepends=True)
        new_lines = []
        replaced = False
        for ln in lines:
            stripped = ln.lstrip()
            if (not replaced) and (not stripped.startswith("//")) and \
                    "::<Fr>(b_check_lkup" in ln and "_data" in ln:
                # comment it out and inject our target call
                indent = ln[: len(ln) - len(stripped)]
                new_lines.append("//" + ln)
                new_lines.append(
                    f"{indent}full_clamav::<Fr>(b_check_lkup, true, "
                    f"false); // deadlock_detect\n")
                replaced = True
            elif (not replaced) and (not stripped.startswith("//")) and \
                    "full_par::<Fr>(b_check_lkup)" in ln:
                indent = ln[: len(ln) - len(stripped)]
                new_lines.append("//" + ln)
                new_lines.append(
                    f"{indent}full_clamav::<Fr>(b_check_lkup, true, "
                    f"false); // deadlock_detect\n")
                replaced = True
            else:
                new_lines.append(ln)
        text = "".join(new_lines)
        if not replaced:
            return None  # could not find a call site to replace
    # 2. Patch num_jobs in full_clamav
    if not NUM_JOBS_RE.search(text):
        return None
    text = NUM_JOBS_RE.sub(rf"\g<1>{n_jobs}\g<3>", text)
    ZKP_DRIVER_RS.write_text(text)
    return driver_backup

def revert_patch(backup_text):
    if backup_text is not None:
        ZKP_DRIVER_RS.write_text(backup_text)

# ============================================================
# Preflight
# ============================================================
def preflight():
    checks = {}
    checks["cwd_is_src"] = (Path.cwd() == SRC_DIR) or True  # tolerated
    checks["cargo_on_path"] = shutil.which("cargo") is not None
    checks["compile2.sh"] = COMPILE_SH.exists() and os.access(
        COMPILE_SH, os.X_OK)
    checks["zkp_driver_writable"] = os.access(ZKP_DRIVER_RS, os.W_OK)
    checks["driver_rs_exists"] = DRIVER_RS.exists()
    checks["tmp_writable"] = os.access("/tmp", os.W_OK)
    # cache dir may or may not exist; full_clamav uses snark_cache_dir
    # "full_clamav". We do not fail on its absence (the run will rebuild
    # if b_read_cache is false).
    cache = REPO_ROOT / "data/cache/full_clamav"
    checks["cache_full_clamav"] = cache.exists()
    ok = all(v for k, v in checks.items()
             if k not in ("cache_full_clamav",))
    log("INFO", "preflight " + ("OK" if ok else "FAIL"),
        details=json.dumps(checks))
    return ok

# ============================================================
# Outcome detection on a dump file
# ============================================================
RE_OK = re.compile(r"test result: ok\.\s*1 passed")
RE_STALL = re.compile(r"73112\.wd: STALL DETECTED")
RE_PANIC = re.compile(r"thread '[^']+' panicked at")
RE_BUILD_FAIL = re.compile(r"^error\[?[^]]*\]?: ", re.MULTILINE)
RE_BUILD_FAIL2 = re.compile(r"error: could not compile")
RE_TEST_FAILED = re.compile(r"test result: FAILED|test result:.*0 passed")

def classify_dump(text):
    if RE_STALL.search(text):
        return "STALL"
    if RE_OK.search(text):
        return "OK"
    if RE_PANIC.search(text):
        return "PANIC"
    if RE_BUILD_FAIL2.search(text) or RE_BUILD_FAIL.search(text):
        return "BUILD_FAIL"
    if RE_TEST_FAILED.search(text):
        return "TEST_FAILED"
    return None  # still running

# ============================================================
# Run one rung
# ============================================================
def run_rung(rung):
    name = rung["name"]
    n_jobs = rung["n_jobs"]
    word_cap = rung["word_cap"]
    watchdog_secs = rung["watchdog_secs"]
    max_runtime_min = rung["max_runtime_min"]

    log("INFO", f"=== RUNG {name} START ===",
        n_jobs=n_jobs, word_cap=word_cap,
        watchdog_secs=watchdog_secs,
        max_runtime_min=max_runtime_min)

    # 1. Patch source
    backup = patch_for_rung(n_jobs)
    if backup is None:
        log("ERROR", f"RUNG {name} patch_for_rung failed")
        return "BUILD_FAIL", None

    dump_dir = Path(f"/tmp/deadlock_detect_{name}")
    dump_dir.mkdir(parents=True, exist_ok=True)
    dump_path = dump_dir / "dump.txt"
    dump_path.write_text("")  # truncate

    try:
        # 2. Clean per-job log files
        for p in Path("/tmp").glob("log_job_*.txt"):
            try: p.unlink()
            except OSError: pass
        for p in Path("/tmp").glob("stall_dump_*.txt"):
            try: p.unlink()
            except OSError: pass
        try:
            Path("/tmp/zkregplus.log").unlink()
        except FileNotFoundError:
            pass

        # 3. Env vars
        env = os.environ.copy()
        env["ZKR_STALL_WATCHDOG_SECS"] = str(watchdog_secs)
        env["ZKR_WORD_CAP_PER_JOB"] = str(word_cap)
        env["RUSTFLAGS"] = "-C link-args=-fuse-ld=lld -Awarnings"
        env["RUST_BACKTRACE"] = "1"

        # 4. Launch compile2.sh
        log("INFO", f"RUNG {name} launching compile2.sh",
            dump=str(dump_path))
        start = time.time()
        with open(dump_path, "w") as out:
            proc = subprocess.Popen(
                ["bash", str(COMPILE_SH)],
                cwd=str(SRC_DIR),
                env=env,
                stdout=out,
                stderr=subprocess.STDOUT,
                start_new_session=True,
            )
        log("INFO", f"RUNG {name} compile2.sh pid={proc.pid}")

        # 5. Monitor loop
        deadline = start + max_runtime_min * 60
        outcome = None
        last_tick = 0.0
        while True:
            rc = proc.poll()
            if rc is not None:
                # Compile2 exited. Read dump and classify.
                try:
                    text = dump_path.read_text(errors="replace")
                except Exception:
                    text = ""
                outcome = classify_dump(text) or "FAIL_UNKNOWN"
                log("INFO", f"RUNG {name} compile2.sh exited",
                    rc=rc, outcome=outcome)
                break
            now = time.time()
            if now > deadline:
                outcome = "TIMEOUT"
                log("WARN", f"RUNG {name} TIMEOUT, killing pid={proc.pid}")
                try:
                    os.killpg(os.getpgid(proc.pid), signal.SIGTERM)
                except ProcessLookupError:
                    pass
                try:
                    proc.wait(timeout=30)
                except subprocess.TimeoutExpired:
                    try:
                        os.killpg(os.getpgid(proc.pid), signal.SIGKILL)
                    except ProcessLookupError:
                        pass
                break
            if now - last_tick >= TICK_INTERVAL_S:
                last_tick = now
                try:
                    text = dump_path.read_text(errors="replace")
                    # Early stall detection (Rust watchdog fires before
                    # process exits).
                    if RE_STALL.search(text):
                        outcome = "STALL"
                        log("WARN", f"RUNG {name} STALL detected, "
                                    f"waiting for process to exit")
                        # Give the watchdog time to exit cleanly.
                        try:
                            proc.wait(timeout=60)
                        except subprocess.TimeoutExpired:
                            try:
                                os.killpg(os.getpgid(proc.pid),
                                          signal.SIGKILL)
                            except ProcessLookupError:
                                pass
                        break
                    p_0 = text.count("DEBUG USE 73112.0:")
                    p_4 = text.count("DEBUG USE 73112.4:")
                    p_wd = text.count("DEBUG USE 73112.wd:")
                    perf1008 = text.count("Pass 1. END")
                    # log-file silence
                    mtimes = []
                    for i in range(n_jobs):
                        p = Path(f"/tmp/log_job_{i}.txt")
                        if p.exists():
                            mtimes.append(int(now - p.stat().st_mtime))
                        else:
                            mtimes.append(-1)
                    log("TICK", f"rung={name}",
                        elapsed_s=int(now - start),
                        plan_pll=p_0, par_after=p_4, wd_evt=p_wd,
                        perf1008=perf1008,
                        log_silence_s=str(mtimes))
                except Exception as e:
                    log("WARN", f"RUNG {name} tick error: {e}")
            time.sleep(5)

        runtime_s = int(time.time() - start)
        return outcome, {"dump_path": str(dump_path),
                          "runtime_s": runtime_s,
                          "compile_pid": proc.pid}
    finally:
        # Always revert
        revert_patch(backup)
        log("INFO", f"RUNG {name} source reverted")

# ============================================================
# Package on failure
# ============================================================
def package(rung, outcome, ctx):
    name = rung["name"]
    ts = datetime.now().strftime("%Y%m%d_%H%M%S")
    pkg_name = f"deadlock_detect_{name}_{ts}"
    pkg_dir = PKG_PARENT / pkg_name
    pkg_dir.mkdir(parents=True, exist_ok=True)
    log("INFO", "packaging", dir=str(pkg_dir))

    # dump.txt
    if ctx and "dump_path" in ctx:
        dp = Path(ctx["dump_path"])
        if dp.exists():
            try:
                shutil.copy(dp, pkg_dir / "dump.txt")
            except Exception as e:
                log("WARN", f"dump copy fail: {e}")

    # per-job logs
    for p in Path("/tmp").glob("log_job_*.txt"):
        try:
            shutil.copy(p, pkg_dir / p.name)
        except Exception:
            pass

    # stall_dump_<pid>.txt
    for p in Path("/tmp").glob("stall_dump_*.txt"):
        try:
            shutil.copy(p, pkg_dir / p.name)
        except Exception:
            pass

    # ps snapshot
    try:
        r = subprocess.run(["ps", "-ef"], capture_output=True, text=True)
        (pkg_dir / "ps_dump.txt").write_text(r.stdout)
    except Exception:
        pass

    # /proc/meminfo
    try:
        shutil.copy("/proc/meminfo", pkg_dir / "meminfo.txt")
    except Exception:
        pass

    # /proc/<compile_pid>/{status,task/*/{wchan,status,stack}}
    # The compile2.sh wrapper PID may have exited by now, but if the
    # child cargo/test process is the one stuck the Rust watchdog will
    # already have dumped /tmp/stall_dump_<pid>.txt. We snapshot whatever
    # zkregplus process is still alive.
    snap_target = None
    try:
        out = subprocess.run(
            ["pgrep", "-f", "zkregplus.*test_zkreg_main"],
            capture_output=True, text=True)
        pids = [p for p in out.stdout.strip().splitlines() if p]
        if pids:
            snap_target = pids[0]
    except Exception:
        pass
    if snap_target:
        try:
            out_lines = [f"=== /proc/{snap_target}/status ===\n"]
            with open(f"/proc/{snap_target}/status") as f:
                out_lines.append(f.read())
            out_lines.append("\n=== /proc/.../task/*/ ===\n")
            for ent in Path(f"/proc/{snap_target}/task").iterdir():
                tid = ent.name
                out_lines.append(f"\n--- tid={tid} ---\n")
                try:
                    with open(ent / "wchan") as f:
                        out_lines.append("wchan: " + f.read().strip() +
                                         "\n")
                except Exception:
                    pass
                try:
                    with open(ent / "status") as f:
                        for ln in f.read().splitlines()[:3]:
                            out_lines.append("  " + ln + "\n")
                except Exception:
                    pass
                try:
                    with open(ent / "stack") as f:
                        out_lines.append("stack:\n")
                        for ln in f.read().splitlines()[:12]:
                            out_lines.append("  " + ln + "\n")
                except Exception:
                    pass
            (pkg_dir / "proc_task_dump.txt").write_text("".join(out_lines))
        except Exception as e:
            log("WARN", f"proc snapshot fail: {e}")

    # git diff / log
    try:
        r = subprocess.run(["git", "diff", "--no-color"],
                           cwd=str(REPO_ROOT.parent.parent),
                           capture_output=True, text=True)
        (pkg_dir / "git_diff.txt").write_text(r.stdout)
    except Exception:
        pass
    try:
        r = subprocess.run(["git", "log", "--oneline", "-20"],
                           cwd=str(REPO_ROOT.parent.parent),
                           capture_output=True, text=True)
        (pkg_dir / "git_log.txt").write_text(r.stdout)
    except Exception:
        pass

    # config & env
    cfg = {"rung": rung, "outcome": outcome, "context": ctx,
           "timestamp": _ts()}
    (pkg_dir / "config_used.json").write_text(json.dumps(cfg, indent=2))
    env_txt = (f"hostname: {os.uname().nodename}\n"
               f"date: {_ts()}\nuser: {os.environ.get('USER','?')}\n")
    for cmd in (["cargo", "--version"], ["rustc", "--version"],
                ["uname", "-a"]):
        try:
            r = subprocess.run(cmd, capture_output=True, text=True)
            env_txt += " ".join(cmd) + " -> " + r.stdout
        except Exception:
            pass
    (pkg_dir / "env.txt").write_text(env_txt)

    # analyze_log
    try:
        shutil.copy(ANALYZE_LOG, pkg_dir / "analyze_log.txt")
    except Exception:
        pass

    # summary
    (pkg_dir / "summary.txt").write_text(
        f"rung   : {name}\n"
        f"outcome: {outcome}\n"
        f"runtime: {ctx.get('runtime_s','?') if ctx else '?'} s\n"
        f"timestamp: {_ts()}\n")

    # tarball
    tar_path = SRC_DIR / f"{pkg_name}.tgz"
    try:
        with tarfile.open(tar_path, "w:gz") as tar:
            tar.add(pkg_dir, arcname=pkg_name)
        sz = tar_path.stat().st_size
        log("INFO", "package_tgz", path=str(tar_path), size=sz)
    except Exception as e:
        log("ERROR", f"tarball fail: {e}")

# ============================================================
# Signal handler
# ============================================================
_STOP = {"stop": False}

def sigterm_handler(signum, frame):
    log("WARN", f"received signal {signum}, stopping after current step")
    _STOP["stop"] = True

# ============================================================
# Main
# ============================================================
def main():
    parser = argparse.ArgumentParser(
        description="Fail-fast ladder runner for the stall-fix.")
    parser.add_argument("--no-daemon", action="store_true",
                        help="Run in foreground (for debugging).")
    args = parser.parse_args()

    # If a previous daemon is alive, refuse to start a second.
    if PID_FILE.exists():
        try:
            old = int(PID_FILE.read_text().strip())
            os.kill(old, 0)
            print(f"deadlock_detect already running, pid={old}. "
                  f"Stop it with: kill {old}", file=sys.stderr)
            return 1
        except (ProcessLookupError, ValueError):
            PID_FILE.unlink()

    # Ensure analyze_log exists.
    ANALYZE_LOG.touch()
    # Wipe FINISH from a previous successful run if present.
    if FINISH_FILE.exists():
        FINISH_FILE.unlink()

    log("INFO", "=" * 60)
    log("INFO", "deadlock_detect starting",
        rungs=",".join(r["name"] for r in RUNGS))

    if not args.no_daemon:
        print(f"deadlock_detect daemonizing. "
              f"Watch: tail -f {ANALYZE_LOG}", file=sys.stderr)
        daemonize()
    else:
        PID_FILE.write_text(f"{os.getpid()}\n")

    signal.signal(signal.SIGTERM, sigterm_handler)
    signal.signal(signal.SIGINT, sigterm_handler)

    try:
        if not preflight():
            log("ERROR", "preflight failed, aborting")
            log("EXIT", "rc=1")
            return 1

        for rung in RUNGS:
            if _STOP["stop"]:
                log("WARN", "stop signal received, ladder aborted")
                log("EXIT", "rc=15")
                return 15
            outcome, ctx = run_rung(rung)
            if outcome == "OK":
                log("INFO", f"RUNG {rung['name']} PASSED",
                    runtime_s=ctx.get("runtime_s", "?") if ctx else "?")
                continue
            # Failure: package and stop.
            log("ERROR", f"RUNG {rung['name']} FAILED outcome={outcome}")
            try:
                package(rung, outcome, ctx)
            except Exception as e:
                log("ERROR", f"packaging exception: {e}")
            log("EXIT", f"rc=2 outcome={outcome}")
            return 2

        # All 4 rungs passed.
        msg = "FINISH all 4 rungs passed. fix verified."
        log("INFO", "=" * 60)
        log("INFO", msg)
        log("INFO", "=" * 60)
        FINISH_FILE.write_text(f"{_ts()}\n{msg}\n")
        log("EXIT", "rc=0")
        return 0
    finally:
        try:
            PID_FILE.unlink()
        except FileNotFoundError:
            pass


if __name__ == "__main__":
    sys.exit(main())
