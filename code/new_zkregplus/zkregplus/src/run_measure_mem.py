#!/usr/bin/env python3
"""
run_measure_mem.py -- start ./compile.sh in background and periodically
sample the zkregplus binary's RAM usage. Exit when that binary is gone.

Outputs (cwd):
  dump.txt        compile.sh stdout+stderr
  mem_log.txt     timestamp pid vmrss_gb vmhwm_gb (one line per sample)
  .run_measure_mem.pid

Usage:
  python3 run_measure_mem.py                # daemonize, 30s sampling
  python3 run_measure_mem.py -i 15          # 15s sampling
  python3 run_measure_mem.py --no-daemon    # foreground
  python3 run_measure_mem.py -p 'examples/main'   # custom pgrep pattern
  kill $(cat .run_measure_mem.pid)          # stop early
"""

import argparse
import os
import shutil
import subprocess
import sys
import time
from datetime import datetime
from pathlib import Path

CWD = Path.cwd()
COMPILE_SH = CWD / "compile.sh"
DUMP_FILE  = CWD / "dump.txt"
MEM_LOG    = CWD / "mem_log.txt"
PID_FILE   = CWD / ".run_measure_mem.pid"
DEFAULT_PATTERN = "target/release/deps/zkregplus"
FIND_TIMEOUT_S = 7200   # allow up to 2h for cargo to finish building

def ts():
    return datetime.now().isoformat(timespec="seconds")

def mlog(line):
    with open(MEM_LOG, "a") as f:
        f.write(line + "\n")

def daemonize():
    if os.fork() > 0: sys.exit(0)
    os.setsid(); os.umask(0)
    if os.fork() > 0: sys.exit(0)
    sys.stdout.flush(); sys.stderr.flush()
    with open(os.devnull, "r") as f0:
        os.dup2(f0.fileno(), 0)
    log_fd = open(MEM_LOG, "a")
    os.dup2(log_fd.fileno(), 1)
    os.dup2(log_fd.fileno(), 2)
    PID_FILE.write_text(f"{os.getpid()}\n")

def find_pid(pattern):
    try:
        r = subprocess.run(["pgrep", "-f", pattern],
                           capture_output=True, text=True)
        pids = [int(p) for p in r.stdout.strip().splitlines() if p.strip()]
        return pids[0] if pids else None
    except Exception:
        return None

def read_mem_kb(pid):
    """Returns {VmRSS, VmHWM} kB or None if pid gone."""
    try:
        out = {}
        with open(f"/proc/{pid}/status") as f:
            for ln in f:
                if ln.startswith(("VmRSS:", "VmHWM:")):
                    k, v = ln.split(":", 1)
                    out[k] = int(v.strip().split()[0])
        return out or None
    except FileNotFoundError:
        return None

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("-i", "--interval", type=int, default=30,
                    help="sample interval seconds (default 30)")
    ap.add_argument("-p", "--pattern", default=DEFAULT_PATTERN,
                    help=f"pgrep -f pattern (default {DEFAULT_PATTERN!r})")
    ap.add_argument("--no-daemon", action="store_true")
    args = ap.parse_args()

    if not COMPILE_SH.exists():
        sys.exit(f"ERR: {COMPILE_SH} not found.")
    if not shutil.which("pgrep"):
        sys.exit("ERR: pgrep not on PATH.")
    if PID_FILE.exists():
        try:
            old = int(PID_FILE.read_text().strip())
            os.kill(old, 0)
            sys.exit(f"ERR: already running pid={old}. "
                     f"Stop: kill {old}")
        except (ProcessLookupError, ValueError):
            PID_FILE.unlink()

    DUMP_FILE.write_text("")
    MEM_LOG.write_text(
        f"# run_measure_mem.py started {ts()}\n"
        f"# pattern={args.pattern!r} interval={args.interval}s\n"
        f"# columns: timestamp pid vmrss_gb vmhwm_gb\n")
    print(f"compile.sh stdout/stderr -> {DUMP_FILE}", file=sys.stderr)
    print(f"memory samples           -> {MEM_LOG}",   file=sys.stderr)

    if not args.no_daemon:
        print(f"daemonizing. stop: kill $(cat {PID_FILE})",
              file=sys.stderr)
        daemonize()
    else:
        PID_FILE.write_text(f"{os.getpid()}\n")

    try:
        out_fd = open(DUMP_FILE, "w")
        proc = subprocess.Popen(
            ["bash", str(COMPILE_SH)],
            cwd=str(CWD),
            stdout=out_fd, stderr=subprocess.STDOUT,
            start_new_session=True,
        )
        mlog(f"{ts()} started compile.sh pid={proc.pid}")

        # Wait for the zkregplus binary to appear.
        deadline = time.time() + FIND_TIMEOUT_S
        target_pid = None
        while time.time() < deadline:
            target_pid = find_pid(args.pattern)
            if target_pid:
                break
            if proc.poll() is not None:
                mlog(f"{ts()} compile.sh exited rc={proc.returncode} "
                     f"before zkregplus binary appeared; exiting")
                return 1
            time.sleep(min(args.interval, 10))

        if not target_pid:
            mlog(f"{ts()} zkregplus pattern {args.pattern!r} not found "
                 f"within {FIND_TIMEOUT_S}s; exiting")
            return 1

        mlog(f"{ts()} sampling pid={target_pid} every {args.interval}s")
        peak_rss = 0.0
        peak_hwm = 0.0
        while True:
            st = read_mem_kb(target_pid)
            if st is None:
                mlog(f"{ts()} pid={target_pid} gone. "
                     f"peak_rss_gb={peak_rss:.2f} "
                     f"peak_hwm_gb={peak_hwm:.2f}")
                break
            rss = st.get("VmRSS", 0) / (1024 * 1024)
            hwm = st.get("VmHWM", 0) / (1024 * 1024)
            peak_rss = max(peak_rss, rss)
            peak_hwm = max(peak_hwm, hwm)
            mlog(f"{ts()} {target_pid} {rss:.2f} {hwm:.2f}")
            time.sleep(args.interval)
    finally:
        try: PID_FILE.unlink()
        except FileNotFoundError: pass
    return 0


if __name__ == "__main__":
    sys.exit(main())
