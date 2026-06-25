#!/usr/bin/env bash
# Sequential scale + forward-fill diagnostic over TWO SEPARATE words:
#   1) gdb     (difficult, 6.6M)  -> /tmp/bora/scale_data_gdb.tgz
#   2) readelf (easy, ~512KB)     -> /tmp/bora/scale_data_readelf.tgz
# Both sweep VEC_PERC=[2,4] with ZKR_DUMP_FWD=1 (per-chunk forward-fill profile).
# They share the /tmp/bora/scale scratch, so they MUST run sequentially.
#
# Run from zkregplus/src (anywhere works, paths are derived from this file):
#   nohup ./run_me.sh &
#   tail -f nohup.out
#
# NOTE: do NOT use `set -e` -- we want readelf to run even if gdb exits
# non-zero (the Python packs its bundle even on crash).

# repo root = two levels up from this script (zkregplus/src/ -> repo root)
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO="$(cd "$SCRIPT_DIR/../.." && pwd)"
cd "$REPO" || { echo "FATAL: cannot cd to repo root: $REPO"; exit 1; }
echo "[run_me] repo root: $REPO"

RUNNER="zkregplus/src/run_collect_scale_data.py"
WORD2="$REPO/data/samples/binexec_merged128k/readelf"

mkdir -p /tmp/bora

echo "=== [1/2] gdb (difficult) START $(date) ==="
ZKR_DUMP_FWD=1 python3 "$RUNNER"
echo "=== [1/2] gdb DONE rc=$? $(date) ==="

echo "=== [2/2] readelf (easy ~512KB) START $(date) ==="
ZKR_SCALE_WORD="$WORD2" ZKR_DUMP_FWD=1 python3 "$RUNNER"
echo "=== [2/2] readelf DONE rc=$? $(date) ==="

echo "=== ALL DONE $(date) ==="
echo "bundles: /tmp/bora/scale_data_gdb.tgz  /tmp/bora/scale_data_readelf.tgz"
