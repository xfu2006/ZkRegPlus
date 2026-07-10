#!/usr/bin/env bash
# gen_tgz.sh -- one-shot manual stall-state collector.
#
# Run from zkregplus/src/. Bundles everything useful for diagnosing a
# live or just-killed run into a single .tgz next to this script. Safe
# to run while the prover is still alive; does not modify anything.
#
# Collected:
#   - all per-job logs  data/cache/logs/log_job_*.txt
#   - /tmp/zkregplus.log (daemon stdout/stderr)
#   - any /tmp/stall_dump_*.txt produced by the Rust watchdog
#   - live /proc/<pid>/{status,task/*/{wchan,status,stack}} for every
#     running zkregplus prover process found via pgrep
#   - ps -ef snapshot, /proc/meminfo, env (uname, cargo --version,
#     rustc --version, hostname, date)
#   - git diff & git log (from bora root)
#   - analyze_log.txt (deadlock_detect.py log, if present)
#   - .deadlock_detect.pid (if present)
#
# Outputs:
#   ./manual_stall_<YYYYmmdd_HHMMSS>.tgz
# Usage:
#   bash gen_tgz.sh                       # default name
#   bash gen_tgz.sh my_label              # ./manual_stall_my_label_<ts>.tgz

set -u  # NOTE: do NOT use -e; we want partial collection on missing
        # files / unreadable /proc entries.

SRC_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ZKREGPLUS_DIR="$(dirname "$SRC_DIR")"
REPO_ROOT="$(dirname "$ZKREGPLUS_DIR")"   # bora
GIT_ROOT="$(dirname "$(dirname "$REPO_ROOT")")"  # ZkRegPlus

LABEL="${1:-}"
TS="$(date +%Y%m%d_%H%M%S)"
if [ -n "$LABEL" ]; then
    PKG_NAME="manual_stall_${LABEL}_${TS}"
else
    PKG_NAME="manual_stall_${TS}"
fi

STAGE="$(mktemp -d -t "${PKG_NAME}.XXXXXX")"
PKG_DIR="$STAGE/$PKG_NAME"
mkdir -p "$PKG_DIR"

echo "gen_tgz.sh: staging at $PKG_DIR"

# ---- summary header (written last; we collect facts here) ----------
SUMMARY="$PKG_DIR/summary.txt"
{
    echo "package : $PKG_NAME"
    echo "ts      : $(date --iso-8601=seconds)"
    echo "host    : $(hostname)"
    echo "user    : ${USER:-?}"
    echo "src_dir : $SRC_DIR"
    echo "repo    : $REPO_ROOT"
} > "$SUMMARY"

# ---- per-job logs -------------------------------------------------
LOGS_DIR="$REPO_ROOT/data/cache/logs"
if [ -d "$LOGS_DIR" ]; then
    cnt=0
    for f in "$LOGS_DIR"/log_job_*.txt; do
        [ -e "$f" ] || continue
        cp -p "$f" "$PKG_DIR/" 2>/dev/null && cnt=$((cnt+1))
    done
    echo "per_job_logs: $cnt copied from $LOGS_DIR" >> "$SUMMARY"
else
    echo "per_job_logs: MISSING dir $LOGS_DIR" >> "$SUMMARY"
fi

# ---- /tmp side files ----------------------------------------------
for f in /tmp/zkregplus.log /tmp/stall_dump_*.txt; do
    [ -e "$f" ] || continue
    cp -p "$f" "$PKG_DIR/" 2>/dev/null
done

# ---- analyze_log + daemon pid -------------------------------------
[ -f "$SRC_DIR/analyze_log.txt" ] && \
    cp -p "$SRC_DIR/analyze_log.txt" "$PKG_DIR/"
[ -f "$SRC_DIR/.deadlock_detect.pid" ] && \
    cp -p "$SRC_DIR/.deadlock_detect.pid" "$PKG_DIR/"

# ---- live /proc snapshot of running zkregplus processes -----------
# pgrep can match the daemonized example binary name.
PROC_DUMP="$PKG_DIR/proc_dump.txt"
: > "$PROC_DUMP"
PIDS="$(pgrep -f 'zkregplus|test_zkreg_main' 2>/dev/null | sort -u)"
if [ -z "$PIDS" ]; then
    echo "(no zkregplus/test_zkreg_main pid found by pgrep)" \
        >> "$PROC_DUMP"
    echo "live_pids: none" >> "$SUMMARY"
else
    n_pids=$(echo "$PIDS" | wc -l)
    echo "live_pids: $n_pids ($(echo $PIDS | tr '\n' ' '))" >> "$SUMMARY"
fi
for pid in $PIDS; do
    {
        echo "==================================================="
        echo "PID=$pid"
        echo "==================================================="
        echo
        echo "--- /proc/$pid/status (first 15 lines) ---"
        head -15 "/proc/$pid/status" 2>/dev/null || echo "(unreadable)"
        echo
        echo "--- /proc/$pid/cmdline ---"
        tr '\0' ' ' < "/proc/$pid/cmdline" 2>/dev/null
        echo
        echo
        echo "--- /proc/$pid/task/* (per-thread wchan/state/stack) ---"
        tdir="/proc/$pid/task"
        if [ -d "$tdir" ]; then
            for t in "$tdir"/*; do
                tid="$(basename "$t")"
                echo
                echo "=== tid=$tid ==="
                printf '  wchan : '
                cat "$t/wchan" 2>/dev/null; echo
                printf '  state : '
                grep -E '^State:' "$t/status" 2>/dev/null \
                    | head -1
                echo "  stack :"
                head -12 "$t/stack" 2>/dev/null \
                    | sed 's/^/    /'
            done
        else
            echo "(no $tdir)"
        fi
        echo
    } >> "$PROC_DUMP"
    # 2026-05-15: stall_classify.py wants comm/stat/syscall and a
    # gdb-bt per pid. Best-effort; permission failures are fine.
    EXTRA="$PKG_DIR/proc_extra_${pid}.txt"
    : > "$EXTRA"
    tdir="/proc/$pid/task"
    if [ -d "$tdir" ]; then
        for t in "$tdir"/*; do
            tid="$(basename "$t")"
            {
                echo
                echo "--- tid=$tid ---"
                grep -E '^(State|Name):' "$t/status" 2>/dev/null \
                    | sed 's/^/  /'
                printf '  comm: '; cat "$t/comm" 2>/dev/null
                printf '  stat: '; cat "$t/stat" 2>/dev/null
                printf '  syscall: '; cat "$t/syscall" 2>/dev/null
                echo
            } >> "$EXTRA"
        done
    fi
    # 2026-05-15: userspace bt via gdb (30s hard timeout). gdb is
    # the best fit at stall time -- it walks parked-thread stacks
    # directly, which is what fails under perf record. The prover
    # is already stuck so the brief ptrace-stop is free.
    if command -v gdb >/dev/null 2>&1; then
        USOUT="$PKG_DIR/userspace_stacks_${pid}.txt"
        timeout 30 gdb -p "$pid" -batch -nx \
            -ex "set pagination off" \
            -ex "set confirm off" \
            -ex "thread apply all bt 20" \
            -ex "detach" -ex "quit" \
            > "$USOUT" 2>&1 || \
            echo "(gdb attach failed or timed out)" >> "$USOUT"
    fi
done

# ---- ps & meminfo -------------------------------------------------
ps -ef > "$PKG_DIR/ps_dump.txt" 2>/dev/null
cp -p /proc/meminfo "$PKG_DIR/meminfo.txt" 2>/dev/null
{
    echo "load: $(cat /proc/loadavg 2>/dev/null)"
    echo "uptime: $(cat /proc/uptime 2>/dev/null)"
} > "$PKG_DIR/host_snap.txt"

# ---- env / versions -----------------------------------------------
ENV_TXT="$PKG_DIR/env.txt"
{
    echo "host    : $(hostname)"
    echo "kernel  : $(uname -a)"
    echo "date    : $(date --iso-8601=seconds)"
    echo "user    : ${USER:-?}"
    printf 'cargo   : '; cargo --version 2>/dev/null
    printf 'rustc   : '; rustc --version 2>/dev/null
    printf 'python3 : '; python3 --version 2>/dev/null
} > "$ENV_TXT"

# ---- git state ----------------------------------------------------
if [ -d "$GIT_ROOT/.git" ] || \
   git -C "$GIT_ROOT" rev-parse 2>/dev/null > /dev/null; then
    git -C "$GIT_ROOT" log --oneline -30 \
        > "$PKG_DIR/git_log.txt" 2>/dev/null
    git -C "$GIT_ROOT" diff --no-color \
        > "$PKG_DIR/git_diff.txt" 2>/dev/null
    git -C "$GIT_ROOT" status -s \
        > "$PKG_DIR/git_status.txt" 2>/dev/null
fi

# ---- per-job log silence column (quick eyeball) -------------------
if [ -d "$LOGS_DIR" ]; then
    {
        echo "now=$(date +%s)"
        for f in "$LOGS_DIR"/log_job_*.txt; do
            [ -e "$f" ] || continue
            m=$(stat -c %Y "$f")
            now=$(date +%s)
            echo "$(basename "$f"): mtime=$m silence_s=$((now - m))"
        done
    } > "$PKG_DIR/log_silence.txt"
fi

# ---- run analyzer scripts (2026-05-15) ----------------------------
# verify_logs.py: routing-health check on the per-job logs we copied.
# stall_classify.py: triage among the three stall hypotheses using
# the proc_extra_*.txt and userspace_stacks_*.txt captured above.
if [ -f "$SRC_DIR/verify_logs.py" ]; then
    python3 "$SRC_DIR/verify_logs.py" --logs-dir "$PKG_DIR" \
        > "$PKG_DIR/log_routing_check.txt" 2>&1 \
        || echo "(verify_logs.py rc=$?)" >> "$PKG_DIR/log_routing_check.txt"
fi
if [ -f "$SRC_DIR/stall_classify.py" ]; then
    python3 "$SRC_DIR/stall_classify.py" --bundle-dir "$PKG_DIR" \
        > "$PKG_DIR/stall_classify.txt" 2>&1 \
        || echo "(stall_classify.py rc=$?)" >> "$PKG_DIR/stall_classify.txt"
fi

# ---- finalize tarball ---------------------------------------------
OUT="$SRC_DIR/${PKG_NAME}.tgz"
( cd "$STAGE" && tar czf "$OUT" "$PKG_NAME" )
SZ=$(stat -c %s "$OUT" 2>/dev/null || echo '?')
echo "gen_tgz.sh: wrote $OUT ($SZ bytes)"

# Leave staging dir for inspection if the tarball failed; otherwise
# clean it up.
if [ -s "$OUT" ]; then
    rm -rf "$STAGE"
fi

echo "Done."
