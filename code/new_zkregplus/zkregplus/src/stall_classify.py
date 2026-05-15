#!/usr/bin/env python3
# stall_classify.py -- triage a deadlock_detect bundle for which of the
# three suspected stall causes is most likely.
#
# Usage:
#     python3 stall_classify.py [--bundle-dir DIR]
#
# Reads (best-effort, missing files are tolerated):
#   - proc_task_dump.txt          : per-thread wchan + State + kernel
#                                   stack (12 lines), produced by
#                                   deadlock_detect.py::package()
#   - stall_dump_<pid>.txt        : same shape, produced by the
#                                   Rust watchdog
#   - userspace_stacks_<pid>.txt  : full userspace bt of every
#                                   thread, produced by
#                                   `gdb -batch thread apply all bt 20`
#                                   (added 2026-05-15 to package()).
#                                   gdb walks parked-thread stacks
#                                   reliably; the brief ptrace-stop
#                                   is harmless on an already-
#                                   stalled prover.
#   - proc_extra_<pid>.txt        : per-thread comm/state/utime/stime/
#                                   syscall snapshot (also new)
#
# Output (stdout): a human-readable report. Exit code mirrors the
# verdict so deadlock_detect.py can branch on it.
#
# Categories
# ----------
# RAYON-IDLE     : parked rayon worker (sleep / Stealer / Latch)
# MALLOC-BLOCKED : parked on a libc malloc-internal Mutex (arena)
# MUTEX-BLOCKED  : parked on a user-code Mutex (Rust std / parking_lot)
# PRODUCTIVE     : R state, not in any park/lock code
# OTHER          : everything we couldn't slot

import argparse
import re
import sys
from collections import defaultdict
from pathlib import Path

# ---- dependency check -------------------------------------------
# stall_classify.py is stdlib-only. It only reads files from the
# bundle dir; no external CLI tools, no pip packages. The QUALITY
# of the verdict depends on which files are present in the bundle:
#   proc_task_dump.txt        : produced by deadlock_detect.py
#                               (kernel wchan + State + kernel stack)
#   stall_dump_<pid>.txt      : produced by the Rust watchdog
#   proc_extra_<pid>.txt      : per-thread comm/stat/syscall snapshot
#                               (NEW 2026-05-15)
#   userspace_stacks_<pid>.txt: perf-script rendering of 5s of
#                               perf record samples (NEW 2026-05-15)
# If any are missing, the classifier degrades gracefully but the
# verdict is more likely to land on INCONCLUSIVE. main() prints a
# heads-up listing which input families were found.
_PY_MIN = (3, 6)
if sys.version_info < _PY_MIN:
    sys.exit(f"ERR: stall_classify.py needs Python >= {_PY_MIN[0]}."
             f"{_PY_MIN[1]}; got {sys.version_info[:3]}")

# ---- patterns for classification --------------------------------
RAYON_IDLE_RE = re.compile(
    r"rayon_core::sleep|crossbeam_deque::Stealer|"
    r"Latch::wait|SleepData::sleep|"
    r"WorkerThread::wait_until|main_loop"
)
MALLOC_FRAME_RE = re.compile(
    r"\b(_int_malloc|_int_free|arena_get|arena_get2|"
    r"malloc_consolidate|tcache_init|__libc_calloc|"
    r"__libc_malloc|__libc_free|__GI___libc_malloc|"
    r"sysmalloc|munmap_chunk)\b"
)
USER_MUTEX_RE = re.compile(
    r"std::sync::mutex::Mutex|parking_lot|"
    r"__pthread_mutex_lock|pthread_rwlock_wrlock|"
    r"pthread_rwlock_rdlock"
)
PARK_WCHAN_RE = re.compile(r"futex_do_wait|do_futex|hrtimer_nanosleep")
RUN_STATE_RE  = re.compile(r"State:\s*R")
SLP_STATE_RE  = re.compile(r"State:\s*S")

# ---- block parser -----------------------------------------------
TID_HDR_RE  = re.compile(r"(?:===\s*tid=|---\s*tid=)(\d+)")
WCHAN_RE    = re.compile(r"wchan\s*:\s*(\S+)")
SYSCALL_RE  = re.compile(r"syscall\s*:\s*(.+)")
COMM_RE     = re.compile(r"comm\s*:\s*(.+)")
# gdb 'thread apply all bt' header line. Examples:
#   "Thread 1 (Thread 0x7fff77ffd1c0 (LWP 12487) \"main\"):"
#   "Thread 23 (LWP 12509):"     (older gdb / no thread name)
# We pull the LWP number (= kernel TID) so blocks line up with
# proc_task_dump.txt entries keyed by the same TID.
GDB_HDR_RE = re.compile(r"^Thread\s+\d+\s+\(.*LWP\s+(\d+)\)")

def parse_thread_blocks(text):
    """Split text into per-tid blocks. Returns list of (tid, block_text).

    Handles three formats:
      (a) deadlock_detect proc_task_dump.txt / proc_extra_<pid>.txt
          with '=== tid=N ===' or '--- tid=N ---' separators.
      (b) Rust stall_dump_<pid>.txt with '=== tid=N ==='.
      (c) gdb 'thread apply all bt' output where each thread block
          starts with 'Thread N (... LWP TID ...):' followed by
          frame lines '#0 <addr> in <func> at <file>:<line>'.
    """
    if not text:
        return []
    out = []
    cur_tid = None
    cur_buf = []
    for line in text.splitlines():
        m = TID_HDR_RE.search(line)
        if m:
            if cur_tid is not None:
                out.append((cur_tid, "\n".join(cur_buf)))
            cur_tid = int(m.group(1))
            cur_buf = [line]
            continue
        mg = GDB_HDR_RE.match(line)
        if mg:
            if cur_tid is not None:
                out.append((cur_tid, "\n".join(cur_buf)))
            cur_tid = int(mg.group(1))
            cur_buf = [line]
            continue
        if cur_tid is not None:
            cur_buf.append(line)
    if cur_tid is not None:
        out.append((cur_tid, "\n".join(cur_buf)))
    return out

def classify_block(block):
    """Return (category, details_dict). details has 'futex' if found."""
    d = {}
    is_running = bool(RUN_STATE_RE.search(block))
    is_sleep   = bool(SLP_STATE_RE.search(block))
    park       = bool(PARK_WCHAN_RE.search(block))
    has_malloc = bool(MALLOC_FRAME_RE.search(block))
    has_rayon  = bool(RAYON_IDLE_RE.search(block))
    has_mutex  = bool(USER_MUTEX_RE.search(block))

    # capture futex address if present (syscall-line pattern from
    # /proc/PID/task/TID/syscall: '202 0xADDR ...' is futex syscall)
    msc = SYSCALL_RE.search(block)
    if msc:
        toks = msc.group(1).split()
        if toks and toks[0] == "202" and len(toks) >= 2:
            d["futex"] = toks[1]

    # 2026-05-15: when we have a gdb stack the lock-related frame
    # itself is sufficient evidence -- we don't insist on a kernel
    # wchan match too. The wchan check still helps when ONLY proc
    # data is present (no userspace_stacks_*.txt).
    if is_running:
        return ("PRODUCTIVE", d)
    if has_malloc and (park or has_mutex):
        # malloc-blocked usually means the libc arena lock is held;
        # the stack will show __pthread_mutex_lock under _int_malloc
        # or wchan will be futex_do_wait.
        return ("MALLOC-BLOCKED", d)
    if has_rayon:
        return ("RAYON-IDLE", d)
    if has_mutex and (park or is_sleep):
        return ("MUTEX-BLOCKED", d)
    if has_mutex:
        # gdb-only bundle: no State line nearby, but the stack does
        # show a Mutex lock call. Trust the frame.
        return ("MUTEX-BLOCKED", d)
    if park and is_sleep:
        # parked on a futex but we couldn't see why -- still a soft
        # mutex-blocked signal but mark it so it doesn't crowd out
        # cleaner findings.
        return ("PARKED-OTHER", d)
    return ("OTHER", d)

# ---- main -------------------------------------------------------
def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--bundle-dir", default=".",
        help="path to deadlock_detect_<rung>_<ts>/ bundle")
    ap.add_argument("--top-locks", type=int, default=5)
    ap.add_argument("--per-cat-sample", type=int, default=3)
    args = ap.parse_args()

    bdir = Path(args.bundle_dir).resolve()
    if not bdir.is_dir():
        print(f"ERR: bundle dir not found: {bdir}", file=sys.stderr)
        return 2

    # Gather all source texts we know about.
    sources = []
    for name in ("proc_task_dump.txt",):
        p = bdir / name
        if p.exists():
            sources.append((name, p.read_text(errors="replace")))
    for p in sorted(bdir.glob("stall_dump_*.txt")):
        sources.append((p.name, p.read_text(errors="replace")))
    for p in sorted(bdir.glob("userspace_stacks_*.txt")):
        sources.append((p.name, p.read_text(errors="replace")))
    for p in sorted(bdir.glob("proc_extra_*.txt")):
        sources.append((p.name, p.read_text(errors="replace")))

    if not sources:
        print(f"ERR: no stall-state files in {bdir}", file=sys.stderr)
        print("  expected at least one of: proc_task_dump.txt, "
              "stall_dump_<pid>.txt, userspace_stacks_<pid>.txt, "
              "proc_extra_<pid>.txt", file=sys.stderr)
        return 2

    # Heads-up: tell caller which input families were available so an
    # INCONCLUSIVE verdict can be traced to a missing input rather
    # than misclassification.
    print("== Inputs found ==")
    have = {n.split("_")[0]: False for n in
            ("proc_task_dump", "stall_dump", "userspace_stacks",
             "proc_extra")}
    for name, _ in sources:
        for k in have:
            if name.startswith(k):
                have[k] = True
    for k, v in have.items():
        print(f"  {k:18s} {'yes' if v else 'NO  (degrades verdict)'}")
    print()

    # Merge per-tid blocks across all sources -- a richer block wins.
    merged = {}  # tid -> block text (concatenated)
    for _, text in sources:
        for tid, blk in parse_thread_blocks(text):
            merged.setdefault(tid, "")
            merged[tid] += "\n" + blk

    if not merged:
        print(f"ERR: no per-thread blocks found in {bdir}",
              file=sys.stderr)
        return 2

    print(f"== stall_classify ({len(merged)} threads, bundle={bdir.name}) ==")
    print()

    # Classify.
    counts = defaultdict(int)
    samples = defaultdict(list)
    futex_groups = defaultdict(list)  # futex addr -> [tid]
    for tid, blk in merged.items():
        cat, d = classify_block(blk)
        counts[cat] += 1
        if len(samples[cat]) < args.per_cat_sample:
            # store the first ~15 lines of the block for the sample
            samples[cat].append(
                (tid, "\n".join(blk.splitlines()[:15])))
        if cat in ("MUTEX-BLOCKED", "MALLOC-BLOCKED", "PARKED-OTHER"):
            fx = d.get("futex")
            if fx:
                futex_groups[fx].append(tid)

    print("== Category histogram ==")
    total = sum(counts.values())
    for k in ("PRODUCTIVE", "RAYON-IDLE", "MALLOC-BLOCKED",
              "MUTEX-BLOCKED", "PARKED-OTHER", "OTHER"):
        n = counts.get(k, 0)
        pct = (n / total * 100) if total else 0
        print(f"  {k:18s} {n:5d}  ({pct:5.1f}%)")
    print()

    print("== Top contended futex addresses (>=2 waiters) ==")
    ordered = sorted(futex_groups.items(),
                     key=lambda kv: -len(kv[1]))
    shown = 0
    for fx, tids in ordered[: args.top_locks]:
        if len(tids) < 2:
            continue
        print(f"  {fx}: {len(tids)} waiters  tids={tids[:10]}")
        shown += 1
    if shown == 0:
        print("  (no futex address shared by >=2 threads in the dump,")
        print("   or the bundle has no proc_extra_<pid>.txt -- the")
        print("   syscall field requires elevated /proc permissions)")
    print()

    print("== Sample stacks per category ==")
    for k in ("MUTEX-BLOCKED", "MALLOC-BLOCKED", "RAYON-IDLE",
              "PARKED-OTHER", "OTHER"):
        if not samples[k]:
            continue
        print(f"  -- {k} --")
        for tid, snippet in samples[k]:
            print(f"  [tid={tid}]")
            for ln in snippet.splitlines():
                print("    " + ln[:160])
            print()

    # Verdict heuristic.
    print("== Verdict ==")
    n_prod   = counts.get("PRODUCTIVE", 0)
    n_rayon  = counts.get("RAYON-IDLE", 0)
    n_malloc = counts.get("MALLOC-BLOCKED", 0)
    n_mutex  = counts.get("MUTEX-BLOCKED", 0)
    n_park   = counts.get("PARKED-OTHER", 0)
    n_block  = n_malloc + n_mutex + n_park

    big_lock = max((len(v) for v in futex_groups.values()), default=0)

    verdict = "INCONCLUSIVE"
    rationale = []
    if n_malloc >= max(3, n_block * 0.4):
        verdict = "GUESS_2_MALLOC_ARENA"
        rationale.append(
            f"{n_malloc} threads parked inside libc malloc internals")
    elif big_lock >= 3 and (n_mutex + n_park) >= big_lock:
        verdict = "GUESS_3_USER_MUTEX"
        rationale.append(
            f"{big_lock} threads share one futex address; "
            f"non-libc lock pattern")
    elif n_rayon > 0 and n_prod < n_rayon * 0.2:
        verdict = "GUESS_1_RAYON_STARVATION"
        rationale.append(
            f"{n_rayon} rayon-idle vs {n_prod} productive -- "
            f"pool starved")
    else:
        rationale.append(
            "no single category dominates -- richer capture needed")
        rationale.append(
            "  hints: ensure gdb userspace bt and /proc syscall")
        rationale.append(
            "         snapshots are in the bundle. gdb needs the")
        rationale.append(
            "         binary on PATH and same-uid ptrace (the")
        rationale.append(
            "         default on most distros). /proc syscall needs")
        rationale.append(
            "         same-uid + kernel.yama.ptrace_scope <= 1.")

    print(f"  {verdict}")
    for r in rationale:
        print(f"  - {r}")

    code_map = {
        "GUESS_1_RAYON_STARVATION": 11,
        "GUESS_2_MALLOC_ARENA":     12,
        "GUESS_3_USER_MUTEX":       13,
        "INCONCLUSIVE":             10,
    }
    return code_map.get(verdict, 10)

if __name__ == "__main__":
    sys.exit(main())
