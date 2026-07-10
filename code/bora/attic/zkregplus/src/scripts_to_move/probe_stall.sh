#!/usr/bin/env bash
# probe_stall.sh — dump per-thread kernel state for a running prover
# process. Tells you whether stalled prover threads are parked on a
# futex (likely deadlock) or actively running (just slow).
#
# Usage:
#   ./probe_stall.sh                   # auto-detect zkregplus process
#   ./probe_stall.sh <pid>             # use the given PID
#
# Writes a full per-thread dump to /tmp/probe_stall_<pid>_<ts>.txt and
# prints a histogram of (State, wchan) grouping to stdout.

set -u

PID="${1:-}"

if [[ -z "$PID" ]]; then
    # Pick the longest-running process whose name matches the prover.
    # ps -eo etimes sorts by elapsed seconds.
    PID=$(ps -eo pid,etimes,comm --no-headers \
        | awk '$3 ~ /main|zkregplus/ {print $1, $2}' \
        | sort -k2 -n -r \
        | head -1 | awk '{print $1}')
    if [[ -z "$PID" ]]; then
        echo "ERROR: could not auto-detect a zkregplus PID." >&2
        echo "       Pass it explicitly: ./probe_stall.sh <pid>" >&2
        exit 1
    fi
    echo "[probe_stall] auto-detected PID=$PID"
fi

if [[ ! -d "/proc/$PID/task" ]]; then
    echo "ERROR: /proc/$PID/task not found (no such process?)." >&2
    exit 1
fi

TS=$(date +%Y%m%d_%H%M%S)
OUT="/tmp/probe_stall_${PID}_${TS}.txt"

{
    echo "==== probe_stall.sh PID=$PID at $(date) ===="
    echo "--- /proc/$PID/status (summary) ---"
    grep -E '^(Name|State|VmRSS|VmHWM|Threads):' "/proc/$PID/status" \
        2>/dev/null
    echo
    echo "--- per-thread dump ---"
    for tid in /proc/$PID/task/*/; do
        tid_num=$(basename "$tid")
        echo
        echo "=== tid=$tid_num ==="
        wchan=$(cat "$tid/wchan" 2>/dev/null || echo "?")
        echo "wchan : $wchan"
        grep -E '^(Name|State):' "$tid/status" 2>/dev/null \
            | sed 's/^/  /'
        if [[ -r "$tid/stack" ]]; then
            echo "stack :"
            sed 's/^/  /' "$tid/stack" 2>/dev/null | head -15
        else
            echo "stack : (not readable — set kernel.kptr_restrict=0)"
        fi
    done
} > "$OUT" 2>&1

echo "[probe_stall] full dump -> $OUT"

# Quick histogram: (State, wchan) -> count.
echo
echo "==== histogram: thread count by (State, wchan) ===="
for tid in /proc/$PID/task/*/; do
    state=$(awk '/^State:/ {print $2}' "$tid/status" 2>/dev/null)
    wchan=$(cat "$tid/wchan" 2>/dev/null)
    [[ -z "$state" ]] && continue
    echo "${state}  ${wchan}"
done | sort | uniq -c | sort -rn

echo
echo "Interpretation hints:"
echo "  many threads parked on  futex_*  -> likely lock deadlock"
echo "  threads in State=R, wchan=0      -> CPU-bound, just slow"
echo "  threads on  do_epoll_wait        -> idle (drainer / rayon)"
