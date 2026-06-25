#!/usr/bin/env bash
# Sequential scale + forward-fill diagnostic over TWO SEPARATE words
# (readelf runs FIRST so its data lands before the slow gdb run):
#   1) readelf (easy, ~512KB)     -> /tmp/bora/scale_data_readelf.tgz
#   2) gdb     (difficult, 6.6M)  -> /tmp/bora/scale_data_gdb.tgz
# Both sweep the counts in the Rust const SCALE_COUNTS (test_collect_scale_data);
# the per-step forward-queue dump is gated by the SCALE_DUMP_FWD global, no env.
# They share the /tmp/bora/scale scratch, so they MUST run sequentially.
#
# Run from zkregplus/src (anywhere works, paths are derived from this file):
#   nohup ./run_collect_scale_data.sh &
#   tail -f nohup.out
#
# NOTE: do NOT use `set -e` -- we want readelf to run even if gdb exits
# non-zero (the Python packs its bundle even on crash).

# repo root = two levels up from this script (zkregplus/src/ -> repo root)
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO="$(cd "$SCRIPT_DIR/../.." && pwd)"
cd "$REPO" || { echo "FATAL: cannot cd to repo root: $REPO"; exit 1; }
echo "[run_scale_sh] repo root: $REPO"

RUNNER="zkregplus/src/run_collect_scale_data.py"
WORD2="$REPO/data/samples/binexec_merged128k/readelf"

mkdir -p /tmp/bora

echo "=== [1/2] readelf (easy ~512KB) START $(date) ==="
ZKR_SCALE_WORD="$WORD2" python3 "$RUNNER"
echo "=== [1/2] readelf DONE rc=$? $(date) ==="

echo "=== [2/2] gdb (difficult) START $(date) ==="
python3 "$RUNNER"
echo "=== [2/2] gdb DONE rc=$? $(date) ==="

echo "=== ALL DONE $(date) ==="
echo "bundles: /tmp/bora/scale_data_gdb.tgz  /tmp/bora/scale_data_readelf.tgz"
