#!/usr/bin/env bash
# compile2.sh — wraps ./compile.sh with exit-signal + OOM detection.
#
# Usage:
#   ./compile2.sh > dump.txt 2>&1 &
#
# At the end of dump.txt you will see:
#   - A banner with the exit code, OR
#     "TERMINATED by signal N (NAME), exit=128+N" if killed by a signal.
#   - Any kernel "oom / killed process / out of memory" lines that
#     fired during the run, prefixed with [KMSG] (streamed live) or
#     [KMSG-FINAL] (authoritative end-of-run sweep).
#
# Why this exists:
#   SIGKILL (signal 9, used by the kernel OOM-killer) leaves no
#   in-process trace. The wrapping shell DOES see the wait-status,
#   so we record it ourselves. We also stream dmesg into the same
#   log so the kernel side of the story is captured inline.

set -u
HERE="$(cd "$(dirname "$0")" && pwd)"
INNER="${HERE}/compile.sh"

# =================================================================
# PREFLIGHT — runs FIRST so any setup problem is loud and you can
# Ctrl-C before kicking off a multi-hour job that might lose its
# kernel-side evidence.
# =================================================================
echo "===== compile2.sh PREFLIGHT ====="

# 1) inner script must exist and be executable
if [ ! -x "${INNER}" ]; then
    echo "[preflight] FAIL: ${INNER} missing or not executable" >&2
    exit 2
fi
echo "[preflight] OK   inner=${INNER}"

# 2) dmesg readability — try plain, then sudo -n, then auto-fix
DMESG=""
probe_dmesg() {
    dmesg -T 2>/dev/null | head -1 >/dev/null 2>&1
}
probe_sudo_dmesg() {
    sudo -n true 2>/dev/null \
        && sudo -n dmesg -T >/dev/null 2>&1
}

if probe_dmesg; then
    DMESG="dmesg"
elif probe_sudo_dmesg; then
    DMESG="sudo -n dmesg"
else
    # try a one-shot self-fix via passwordless sudo
    if sudo -n true 2>/dev/null; then
        echo "[preflight] dmesg restricted; trying" \
            "sudo -n sysctl -w kernel.dmesg_restrict=0"
        sudo -n sysctl -w kernel.dmesg_restrict=0 \
            >/dev/null 2>&1 || true
        if probe_dmesg; then DMESG="dmesg"
        elif probe_sudo_dmesg; then DMESG="sudo -n dmesg"
        fi
    fi
fi

if [ -n "${DMESG}" ]; then
    echo "[preflight] OK   dmesg=${DMESG}"
else
    echo "[preflight] WARN dmesg unreadable — kernel-side OOM" \
        "evidence will NOT be captured."
    echo "[preflight] WARN to fix: sudo sysctl -w" \
        "kernel.dmesg_restrict=0  (or run this script as root)"
    echo "[preflight] WARN sleeping 5s — Ctrl-C now if you want" \
        "to fix it before the long run starts."
    sleep 5
fi

# 3) /tmp tmpfs warning (the dump itself can vanish on reboot)
if mount | grep -qE ' /tmp .* (tmpfs|ramfs)'; then
    echo "[preflight] WARN /tmp is tmpfs; if dump.txt is on /tmp" \
        "it will be lost on reboot. Prefer \$HOME or /var/log."
fi

echo "===== compile2.sh PREFLIGHT done ====="
echo

# =================================================================
# RUN
# =================================================================

# background watcher: stream kernel OOM/kill lines live
WATCH_PID=""
if [ -n "${DMESG}" ]; then
    {
        ${DMESG} -wT 2>/dev/null \
        | grep --line-buffered -iE \
            "oom|killed process|out of memory|invoked oom-killer" \
        | sed -u 's/^/[KMSG] /'
    } &
    WATCH_PID=$!
fi

START_TS="$(date -Is)"
echo "===== compile2.sh START ts=${START_TS} pid=$$" \
    "inner=${INNER} watcher=${WATCH_PID:-none} ====="

# run the inner script in foreground; its stdout/stderr inherit ours
"${INNER}"
EC=$?
END_TS="$(date -Is)"

# let any final kernel message drain into the watcher's pipeline
sleep 1

# stop the streaming watcher (and its pipeline children)
if [ -n "${WATCH_PID}" ]; then
    pkill -P "${WATCH_PID}" 2>/dev/null || true
    kill    "${WATCH_PID}"  2>/dev/null || true
    wait    "${WATCH_PID}"  2>/dev/null || true
fi

# exit-reason banner
echo
echo "===== compile2.sh END ts=${END_TS} ====="
if [ "${EC}" -gt 128 ]; then
    SIG=$((EC - 128))
    SIG_NAME="$(kill -l "${SIG}" 2>/dev/null || echo '?')"
    echo "===== TERMINATED by signal ${SIG} (${SIG_NAME})," \
        "exit=${EC} ====="
    if [ "${SIG}" -eq 9 ]; then
        echo "===== signal 9 = SIGKILL: almost certainly the" \
            "OOM-killer or an external kill -9. See [KMSG] /" \
            "[KMSG-FINAL] lines for confirmation. ====="
    fi
elif [ "${EC}" -ne 0 ]; then
    echo "===== EXITED non-zero: code=${EC} ====="
else
    echo "===== EXITED cleanly ====="
fi

# final authoritative dmesg sweep over the run window
if [ -n "${DMESG}" ]; then
    echo "===== final dmesg sweep [since ${START_TS}] ====="
    ${DMESG} -T --since "${START_TS}" 2>/dev/null \
      | grep -iE \
        "oom|killed process|out of memory|invoked oom-killer" \
      | sed 's/^/[KMSG-FINAL] /' \
      | head -50 || true
fi

exit "${EC}"
