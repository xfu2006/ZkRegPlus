#!/usr/bin/env bash
# one_bisec_job3.sh -- FAST PATH for the full_clam job-3 MainDecider failure.
#
# Instead of file-bisection (which starves the lookup-coverage assert), this
# runs job 3 WHOLE as a single valid job (151 files -> ~1704 chunks -> the
# assert passes -> it folds + proves), with the ZKR_CS_CHECK probe ON. The
# probe fires inside MainDecider proving and names the FIRST unsatisfied
# constraint block, so you learn the failing gadget directly.
#
# Usage (from anywhere):  bash zkregplus/src/one_bisec_job3.sh
#   long run (hours). To detach:  nohup bash .../one_bisec_job3.sh &
#
# Output: prints the first "CS UNSAT @<block>" and packs a small bundle to
# /tmp/one_bisec_job3.tgz for download.
set -euo pipefail

# ---- locate repo root (this script lives in zkregplus/src/) ----------------
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJ_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
cd "$PROJ_ROOT"
echo "[one_bisec] proj_root = $PROJ_ROOT"

# ---- paths -----------------------------------------------------------------
SRC_LIST="data/debug/full_clamav/config/binexec_p3.dat"   # job 3's file list
SLICE_DIR="data/debug/full_clam_bisect/config"
REPORT_DIR="data/debug/full_clam_bisect/reports"
KEYDIR="data/cache/full_data"
JOBLOG="data/cache/logs/log_job_0.txt"                     # single job -> id 0
STDOUT_LOG="/tmp/one_bisec_job3_stdout.txt"
PACK_TGZ="/tmp/one_bisec_job3.tgz"

# ---- preflight: keys (bisect reuses them READ-ONLY, never writes) ----------
missing=""
for k in g16_main.key g16_main.key.meta g16_cp.key g16_cp.key.meta \
         g16_main.sidecar.cf g16_cp.sidecar.cf g16_cp.sidecar.cp; do
	[ -f "$KEYDIR/$k" ] || missing="$missing $k"
done
if [ -n "$missing" ]; then
	echo "############################################################"
	echo "## SNARK KEYS MISSING under $KEYDIR"
	echo "## missing:$missing"
	echo "## Stage them from a prior full_clamav run before proceeding;"
	echo "## this run reads keys read-only and will fail at the decider"
	echo "## without them. Aborting."
	echo "############################################################"
	exit 1
fi
[ -f "$SRC_LIST" ] || { echo "[one_bisec] MISSING $SRC_LIST"; exit 1; }

# ---- build the single-job slice = all of job 3 -----------------------------
mkdir -p "$SLICE_DIR" "$REPORT_DIR"
rm -f "$SLICE_DIR"/slice_*.dat
cp "$SRC_LIST" "$SLICE_DIR/slice_0.dat"
n_files="$(grep -cve '^[[:space:]]*$' "$SRC_LIST" || true)"
echo "[one_bisec] slice_0.dat = $n_files files (whole job 3)"
rm -f "$JOBLOG" "$PROJ_ROOT/data/cache/run_complete.sentinel" 2>/dev/null || true

# ---- run: NJOBS=1 keeps chunks high; ZKR_CS_CHECK=1 arms the probe ---------
echo "[one_bisec] running (full fold + Groth16, hours). stdout -> $STDOUT_LOG"
set +e
RUSTFLAGS="-C link-args=-fuse-ld=lld -Awarnings" \
ZKR_CS_CHECK=1 ZKR_BISECT_NJOBS=1 \
ZKR_BISECT_DIR="$PROJ_ROOT/$SLICE_DIR" \
cargo test -p zkregplus --release -- \
	test_full_clam_bisect --exact --nocapture --test-threads=1 \
	2>&1 | tee "$STDOUT_LOG"
rc="${PIPESTATUS[0]}"
set -e
echo "[one_bisec] cargo test exit = $rc"

# ---- report: first UNSAT block is the culprit gadget -----------------------
echo "======================================================================"
if grep -q "62001.2" "$JOBLOG" 2>/dev/null; then
	echo "PROBE: constraint blocks checked (OK then first UNSAT) ->"
	grep -E "62001\.[123]" "$JOBLOG" | sed 's/^.*DEBUG USE /  /'
	echo "----------------------------------------------------------------------"
	echo "FIRST UNSAT block (the failing gadget):"
	grep "62001.2" "$JOBLOG" | head -1 | sed 's/^.*DEBUG USE /  /'
elif grep -q "62001.1" "$JOBLOG" 2>/dev/null; then
	echo "PROBE: all checked blocks SATISFIED (no UNSAT seen). Either the"
	echo "failure is past the probed blocks, or it did not reproduce here."
	grep -E "62001\.[13]" "$JOBLOG" | tail -5 | sed 's/^.*DEBUG USE /  /'
else
	echo "PROBE: no 62001.* lines in $JOBLOG -- proving likely never reached"
	echo "(check $STDOUT_LOG for a panic, e.g. a capacity assert)."
	grep -i "panicked at\|ERROR: lk_share" "$STDOUT_LOG" | head -5 || true
fi
echo "======================================================================"

# ---- pack for download (stage both files, tar once) ------------------------
STAGE="$(mktemp -d)"
[ -f "$JOBLOG" ]     && cp "$JOBLOG"     "$STAGE/log_job_0.txt"
[ -f "$STDOUT_LOG" ] && cp "$STDOUT_LOG" "$STAGE/stdout.txt"
tar czf "$PACK_TGZ" -C "$STAGE" .
rm -rf "$STAGE"
echo "[one_bisec] packed -> $PACK_TGZ  (log_job_0.txt + stdout.txt)"
