#!/usr/bin/env bash
# DLP twin of run_collect_scale_data.sh: sequential scale + SDE-saturation sweep
# over TWO short NON-MATCHING emails (easy runs FIRST so its data lands before
# the heavier hard run):
#   1) continental/2 (EASY, ~0% SDE)  -> /tmp/bora/scale_data_dlp_2.tgz
#   2) donohoe/6     (HARD, ~91% SDE) -> /tmp/bora/scale_data_dlp_6.tgz
# Both sweep the counts owned by the Rust test_collect_scale_dlp
# (1, 10%..100% of the 9,860 sweepable MS-DLP rules). They share the
# /tmp/bora/scale_dlp scratch, so they MUST run sequentially.
#
# Run from zkregplus/src (anywhere works, paths are derived from this file):
#   nohup ./run_collect_scale_dlp.sh &
#   tail -f nohup.out
#
# NOTE: no `set -e` -- we want the easy run to complete even if the hard run
# exits non-zero (the Python packs its bundle even on crash).

# repo root = two levels up from this script (zkregplus/src/ -> repo root)
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO="$(cd "$SCRIPT_DIR/../.." && pwd)"
cd "$REPO" || { echo "FATAL: cannot cd to repo root: $REPO"; exit 1; }
echo "[run_scale_dlp_sh] repo root: $REPO"

RUNNER="zkregplus/src/run_collect_scale_dlp.py"
EASY="$REPO/data/samples/email/src/maildir/griffith-j/continental/2."   # ~0% SDE
HARD="$REPO/data/samples/email/src/maildir/donohoe-t/sent/6."           # ~91% SDE (.py default)

mkdir -p /tmp/bora

echo "=== [1/2] EASY continental/2 (~0% SDE) START $(date) ==="
ZKR_SCALE_WORD="$EASY" python3 "$RUNNER"
echo "=== [1/2] EASY DONE rc=$? $(date) ==="

echo "=== [2/2] HARD donohoe/6 (~91% SDE) START $(date) ==="
ZKR_SCALE_WORD="$HARD" python3 "$RUNNER"
echo "=== [2/2] HARD DONE rc=$? $(date) ==="

echo "=== ALL DONE $(date) ==="
echo "bundles: /tmp/bora/scale_data_dlp_2.tgz  /tmp/bora/scale_data_dlp_6.tgz"
