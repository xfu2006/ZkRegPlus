#!/usr/bin/env bash
# job3_decider_probe.sh -- DECIDER-ONLY probe for the full_clam job-3 failure.
#
# Runs job 3 WHOLE as a single valid job (151 files -> ~1704 chunks -> the
# lookup-coverage assert passes -> it folds + proves) with ONLY the decider
# probe (ZKR_CS_CHECK). NO per-step probing -> the fold is prod-faithful. The
# probe fires at MainDecider assembly and names the FIRST unsatisfied
# constraint block (62001.2), so you learn the failing decider block directly.
#
# This is the minimal-interference variant. For per-step localization (which
# fold step / file / gadget fails, with early abort) use job3_step_probe.sh.
#
# Usage (from anywhere):  bash zkregplus/src/job3_decider_probe.sh
#   long run (~16h). To detach:  nohup bash .../job3_decider_probe.sh &
#
# Output: prints the first "CS UNSAT @<block>" and packs a small bundle to
# /tmp/job3_decider_probe.tgz for download.
set -euo pipefail

# ---- locate repo root (this script lives in zkregplus/src/) ----------------
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJ_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
cd "$PROJ_ROOT"
echo "[decider_probe] proj_root = $PROJ_ROOT"

# ---- paths -----------------------------------------------------------------
SRC_LIST="data/debug/full_clamav/config/binexec_p3.dat"   # job 3's file list
SLICE_DIR="data/debug/full_clam_bisect/config"
REPORT_DIR="data/debug/full_clam_bisect/reports"
KEYDIR="data/cache/full_data"
JOBLOG="data/cache/logs/log_job_0.txt"                     # single job -> id 0
STDOUT_LOG="/tmp/job3_decider_probe_stdout.txt"
PACK_TGZ="/tmp/job3_decider_probe.tgz"

# ---- preflight: keys. Missing is NOT fatal -- the runner auto-builds ------
# a cold/partial snark cache this run (driver.rs:2815-2831 flips to write-mode
# and persists g16_* keys). Warm cache = fast reuse; cold = +multi-hour keygen.
missing=""
for k in g16_main.key g16_main.key.meta g16_cp.key g16_cp.key.meta \
         g16_main.sidecar.cf g16_cp.sidecar.cf g16_cp.sidecar.cp; do
	[ -f "$KEYDIR/$k" ] || missing="$missing $k"
done
if [ -n "$missing" ]; then
	echo "############################################################"
	echo "## SNARK KEYS COLD under $KEYDIR"
	echo "## missing:$missing"
	echo "## NOT fatal -- this run will BUILD + PERSIST them (multi-hour"
	echo "## keygen), then prove. Later runs reuse them. To skip the"
	echo "## keygen, stage keys from a prior full_clamav run first."
	echo "############################################################"
else
	echo "[decider_probe] snark keys warm -> reused read-only"
fi
[ -f "$SRC_LIST" ] || { echo "[decider_probe] MISSING $SRC_LIST"; exit 1; }

# ---- build the single-job slice = all of job 3 -----------------------------
mkdir -p "$SLICE_DIR" "$REPORT_DIR"
rm -f "$SLICE_DIR"/slice_*.dat
cp "$SRC_LIST" "$SLICE_DIR/slice_0.dat"
n_files="$(grep -cve '^[[:space:]]*$' "$SRC_LIST" || true)"
echo "[decider_probe] slice_0.dat = $n_files files (whole job 3)"
rm -f "$JOBLOG" "$PROJ_ROOT/data/cache/run_complete.sentinel" 2>/dev/null || true

# ---- run: NJOBS=1 keeps chunks high; ZKR_CS_CHECK=1 arms the probe ---------
echo "[decider_probe] running (full fold + Groth16, hours). stdout -> $STDOUT_LOG"
set +e
# NOTE: --lib restricts to the lib test binary (skips doctests); the filter
# is the FULL module path because --exact matches the whole test name.
RUSTFLAGS="-C link-args=-fuse-ld=lld -Awarnings" \
ZKR_CS_CHECK=1 ZKR_BISECT_NJOBS=1 \
ZKR_BISECT_DIR="$PROJ_ROOT/$SLICE_DIR" \
cargo test -p zkregplus --release --lib -- \
	zkp_driver::tests_zkp_driver::test_full_clam_bisect \
	--exact --nocapture --test-threads=1 \
	2>&1 | tee "$STDOUT_LOG"
rc="${PIPESTATUS[0]}"
set -e
echo "[decider_probe] cargo test exit = $rc"

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
echo "[decider_probe] packed -> $PACK_TGZ  (log_job_0.txt + stdout.txt)"
