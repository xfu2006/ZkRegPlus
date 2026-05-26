#!/usr/bin/env python3
"""
run_measure_mem.py -- start ./compile.sh in background and periodically
sample the zkregplus binary's RAM usage. Exit when that binary is gone.

Outputs (cwd):
  dump.txt             everything: compile.sh stdout+stderr AND memory
                       samples (prefixed with '[mem]') interleaved.
  .run_measure_mem.pid

Filter just the memory samples:  grep '^\\[mem\\]' dump.txt

Usage:
  python3 run_measure_mem.py                # daemonize, 15s sampling
  python3 run_measure_mem.py -i 30          # 30s sampling
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
PID_FILE   = CWD / ".run_measure_mem.pid"
DEFAULT_PATTERN = "target/release/deps/zkregplus"
FIND_TIMEOUT_S = 7200   # allow up to 2h for cargo to finish building
# DEBUG USE 60010.5: dump full maps once when VMA count crosses this.
MAPS_HI_FILE = CWD / "maps_hi.txt"
VMA_DUMP_THRESHOLD = 500_000

def ts():
    return datetime.now().isoformat(timespec="seconds")

def mlog(line):
    with open(DUMP_FILE, "a") as f:
        f.write(f"[mem] {line}\n")

def daemonize():
    if os.fork() > 0: sys.exit(0)
    os.setsid(); os.umask(0)
    if os.fork() > 0: sys.exit(0)
    sys.stdout.flush(); sys.stderr.flush()
    with open(os.devnull, "r") as f0:
        os.dup2(f0.fileno(), 0)
    log_fd = open(DUMP_FILE, "a")
    os.dup2(log_fd.fileno(), 1)
    os.dup2(log_fd.fileno(), 2)
    PID_FILE.write_text(f"{os.getpid()}\n")

def find_pid(pattern):
    """Return the matching pid with the largest RSS (the real heavy
    prover), or None. Picking max-RSS instead of the first match keeps
    us from locking onto a transient helper that also matches the
    pattern (e.g. a short-lived cargo/test spawn that dies in seconds)."""
    try:
        r = subprocess.run(["pgrep", "-f", pattern],
                           capture_output=True, text=True)
        pids = [int(p) for p in r.stdout.split() if p.strip()]
    except Exception:
        return None
    best, best_rss = None, -1
    for p in pids:
        st = read_mem_kb(p)
        rss = st.get("VmRSS", 0) if st else -1
        if rss > best_rss:
            best, best_rss = p, rss
    return best

def read_mem_kb(pid):
    """Returns {VmRSS, VmHWM} kB or None if pid gone."""
    try:
        out = {}
        with open(f"/proc/{pid}/status") as f:
            for ln in f:
                if ln.startswith(("VmRSS:", "VmHWM:", "VmSize:",
                                  "VmData:", "VmPTE:", "Threads:")):
                    k, v = ln.split(":", 1)
                    out[k] = int(v.strip().split()[0])
        return out or None
    except FileNotFoundError:
        return None

# ===== DEBUG USE 60010: VMA / ENOMEM crash diagnosis helpers =====
def scan_maps(pid):
    """Single read of /proc/<pid>/maps -> (total, perms_hist, n_anon,
    n_file), or None if gone. perms_hist tallies the 4-char permission
    field so we can see which mappings dominate (rw-p committed anon,
    ---p PROT_NONE reserved/guard, r-xp code). Reading maps briefly
    holds mmap_lock; fine at the sample cadence."""
    try:
        total = anon = filed = 0
        hist = {}
        with open(f"/proc/{pid}/maps") as f:
            for ln in f:
                total += 1
                parts = ln.split()
                if len(parts) >= 2:
                    hist[parts[1]] = hist.get(parts[1], 0) + 1
                if len(parts) >= 6 and parts[5].startswith("/"):
                    filed += 1
                else:
                    anon += 1
        return total, hist, anon, filed
    except FileNotFoundError:
        return None

def dump_maps_full(pid, path, vma, when):
    """Write the full maps once to a side file at peak fragmentation
    (kept out of the main dump to avoid bloating it)."""
    try:
        with open(f"/proc/{pid}/maps") as src, open(path, "w") as dst:
            dst.write(f"# DEBUG USE 60010.5 full maps pid={pid} "
                      f"vma={vma} at {when}\n")
            dst.write(src.read())
        return True
    except Exception:
        return False

def read_meminfo_kb(keys):
    """Return {key: kB} for the requested /proc/meminfo keys."""
    want = {k + ":" for k in keys}
    out = {}
    try:
        with open("/proc/meminfo") as f:
            for ln in f:
                head = ln.split(":", 1)[0] + ":"
                if head in want:
                    out[head[:-1]] = int(
                        ln.split(":", 1)[1].strip().split()[0])
    except Exception:
        pass
    return out

def log_proc_limits(pid):
    """Per-process rlimits as the kernel sees them (authoritative;
    beats the launcher's ulimit). Logged once."""
    try:
        with open(f"/proc/{pid}/limits") as f:
            for ln in f:
                mlog(f"DEBUG USE 60010.4: {ln.rstrip()}")
    except Exception as e:
        mlog(f"DEBUG USE 60010.4: limits unavailable: {e}")

def log_dmesg_tail(n=40):
    """Best-effort kernel ring tail at exit: catches page-alloc / vmap
    / OOM messages that explain an mmap ENOMEM (may need privileges)."""
    try:
        r = subprocess.run(["dmesg", "--ctime"], capture_output=True,
                           text=True, timeout=10)
        if r.returncode == 0 and r.stdout:
            mlog("DEBUG USE 60010.6: ==== dmesg tail ====")
            for ln in r.stdout.strip().splitlines()[-n:]:
                mlog(f"DEBUG USE 60010.6: {ln}")
        else:
            mlog(f"DEBUG USE 60010.6: dmesg rc={r.returncode} "
                 f"(restricted? run once with sudo)")
    except Exception as e:
        mlog(f"DEBUG USE 60010.6: dmesg unavailable: {e}")

def log_os_snapshot():
    """One-time OS/mem limits so the dump self-identifies the ceiling."""
    def rd(p):
        try:
            return Path(p).read_text().strip()
        except Exception:
            return "?"
    mlog("DEBUG USE 60010.1: ==== OS/mem snapshot ====")
    mlog(f"DEBUG USE 60010.1: max_map_count="
         f"{rd('/proc/sys/vm/max_map_count')}")
    mlog(f"DEBUG USE 60010.1: overcommit_memory="
         f"{rd('/proc/sys/vm/overcommit_memory')} "
         f"ratio={rd('/proc/sys/vm/overcommit_ratio')}")
    try:
        import resource
        s, h = resource.getrlimit(resource.RLIMIT_AS)
        mlog(f"DEBUG USE 60010.1: rlimit_as_soft={s} hard={h}")
    except Exception:
        pass
    mi = read_meminfo_kb(["MemTotal", "SwapTotal", "CommitLimit"])
    for k in ("MemTotal", "SwapTotal", "CommitLimit"):
        if k in mi:
            mlog(f"DEBUG USE 60010.1: {k}={mi[k]} kB")
    cg = "/sys/fs/cgroup/memory.max"
    if os.path.exists(cg):
        mlog(f"DEBUG USE 60010.1: cgroup_memory_max={rd(cg)}")
    else:
        mlog("DEBUG USE 60010.1: no cgroup v2 memory.max")
# ===== end DEBUG USE 60010 helpers =====

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("-i", "--interval", type=int, default=15,
                    help="sample interval seconds (default 15)")
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

    DUMP_FILE.write_text(
        f"[mem] # run_measure_mem.py started {ts()}\n"
        f"[mem] # pattern={args.pattern!r} interval={args.interval}s\n"
        f"[mem] # columns: timestamp pid vmrss_gb vmhwm_gb\n"
        f"[mem] # DEBUG USE 60010: .1 OS snapshot  .2/.2b per-sample "
        f"VMA count+perms / Committed_AS / threads / page-table  "
        f".4 proc limits  .5 full maps -> maps_hi.txt  .6 dmesg tail\n"
        f"[mem] # (compile.sh stdout/stderr follows, interleaved)\n")
    print(f"all output -> {DUMP_FILE}", file=sys.stderr)
    print(f"  grep '^\\[mem\\]' {DUMP_FILE.name}  "
          f"# to see only mem samples", file=sys.stderr)

    if not args.no_daemon:
        print(f"daemonizing. stop: kill $(cat {PID_FILE})",
              file=sys.stderr)
        daemonize()
    else:
        PID_FILE.write_text(f"{os.getpid()}\n")

    try:
        out_fd = open(DUMP_FILE, "a")
        # DEBUG USE 60010.3: mimalloc names the failing OS op + (Linux
        # ENOMEM) a vm.max_map_count hint, and prints options/version.
        child_env = os.environ.copy()
        child_env.setdefault("MIMALLOC_VERBOSE", "1")
        child_env.setdefault("MIMALLOC_SHOW_ERRORS", "1")
        proc = subprocess.Popen(
            ["bash", str(COMPILE_SH)],
            cwd=str(CWD),
            stdout=out_fd, stderr=subprocess.STDOUT,
            start_new_session=True,
            env=child_env,
        )
        mlog(f"{ts()} started compile.sh pid={proc.pid}")
        log_os_snapshot()   # DEBUG USE 60010.1

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

        mlog(f"{ts()} sampling largest match of {args.pattern!r} "
             f"every {args.interval}s")
        peak_rss = 0.0
        peak_hwm = 0.0
        maps_dumped = False           # DEBUG USE 60010.5 one-shot
        limits_logged = False         # DEBUG USE 60010.4 one-shot
        while True:
            # Re-acquire the largest-RSS match each tick: follow the
            # real prover, ignore transient matches; stop only once
            # nothing matches and compile.sh has exited.
            target_pid = find_pid(args.pattern)
            if target_pid is None:
                if proc.poll() is not None:
                    mlog(f"{ts()} no match for {args.pattern!r} and "
                         f"compile.sh exited rc={proc.returncode}. "
                         f"peak_rss_gb={peak_rss:.2f} "
                         f"peak_hwm_gb={peak_hwm:.2f}")
                    break
                time.sleep(args.interval)
                continue
            st = read_mem_kb(target_pid)
            if st is None:        # raced with exit; retry next tick
                time.sleep(args.interval)
                continue
            if not limits_logged:
                log_proc_limits(target_pid)   # DEBUG USE 60010.4
                limits_logged = True
            rss = st.get("VmRSS", 0) / (1024 * 1024)
            hwm = st.get("VmHWM", 0) / (1024 * 1024)
            peak_rss = max(peak_rss, rss)
            peak_hwm = max(peak_hwm, hwm)
            mlog(f"{ts()} {target_pid} {rss:.2f} {hwm:.2f}")
            # DEBUG USE 60010.2: which ceiling is approached as RSS
            # falls on the descent -- VMA count vs max_map_count, and
            # Committed_AS vs CommitLimit; plus virtual size, page
            # tables, threads, and free memory (rule in/out true OOM).
            scan = scan_maps(target_pid)
            vma = scan[0] if scan else None
            vsz = st.get("VmSize", 0) / (1024 * 1024)
            dat = st.get("VmData", 0) / (1024 * 1024)
            pte = st.get("VmPTE", 0) / 1024            # MB
            thr = st.get("Threads", 0)
            mi = read_meminfo_kb(["Committed_AS", "MemAvailable",
                                  "MemFree"])
            com_gb = mi.get("Committed_AS", 0) / (1024 * 1024)
            avail_gb = mi.get("MemAvailable", 0) / (1024 * 1024)
            free_gb = mi.get("MemFree", 0) / (1024 * 1024)
            mlog(f"DEBUG USE 60010.2: {ts()} pid={target_pid} "
                 f"vma={vma} threads={thr} vsize_gb={vsz:.2f} "
                 f"data_gb={dat:.2f} pte_mb={pte:.1f} "
                 f"committed_gb={com_gb:.2f} "
                 f"memavail_gb={avail_gb:.2f} memfree_gb={free_gb:.2f}")
            if scan:
                hist = ",".join(f"{p}:{n}" for p, n in sorted(
                    scan[1].items(), key=lambda kv: -kv[1]))
                mlog(f"DEBUG USE 60010.2b: {ts()} perms{{{hist}}} "
                     f"anon={scan[2]} file={scan[3]}")
                if (vma and vma >= VMA_DUMP_THRESHOLD
                        and not maps_dumped):
                    if dump_maps_full(target_pid, MAPS_HI_FILE, vma,
                                      ts()):
                        maps_dumped = True
                        mlog(f"DEBUG USE 60010.5: wrote full maps "
                             f"(vma={vma}) to {MAPS_HI_FILE}")
            time.sleep(args.interval)
        # process gone (likely crashed): grab the kernel ring tail.
        log_dmesg_tail()              # DEBUG USE 60010.6
    finally:
        try: PID_FILE.unlink()
        except FileNotFoundError: pass
    return 0


if __name__ == "__main__":
    sys.exit(main())
