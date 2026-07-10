#!/usr/bin/env bash
# doxygen_dfa_probe.sh -- FAST fold-only confirmation of the DFA discharge-
# combo fix on the REAL doxygen chunk that broke full_clam job-3.
#
# Background: the bug was a per-step UNSAT in DfaAdvGadget's discharge-combo
# well-formedness check (validate_discharge_sig_combo step-2.1), triggered by
# a count>=2 discharge disjunct (sig-35591). It is Branch A (self-contained),
# so it reproduces from a FRESH fold of doxygen ALONE. This script folds
# doxygen (1 file) with:
#   ZKR_BISECT_FOLD_ONLY=1 -> b_folding_only (DEBUG 62731.0): stop AFTER
#     folding, no decider/keys -> fast (~15-20 min) + modest RAM. The bug (if
#     present) fires DURING folding, so the decider is not needed to see it.
#   ZKR_GADGET_CHECK=1 ZKR_GADGET_FROM=0 -> per-gadget SAT check every step.
#     PRE-fix: the doxygen bad chunk prints 62730.2 GADGET-UNSAT + panics.
#     POST-fix: every step prints 62730.1 GADGET-SAT OK; no 62730.2.
#   ZKR_BISECT_CHECK_LKUP=0 -> doxygen (~67 chunks) < the ~678-chunk lk_share
#     coverage floor, so a 1-file run would panic; false skips that check.
#   Same full_data DB + full_clamav caps/config as job3 (full_clam_bisect) ->
#     doxygen routes to the SAME circ=1 DFA gadget that failed.
#   ZKR_DFA_DUMP=1 -> the 62731.x DFA diagnostic probes fire (note 62731.9
#     recomputes the OLD buggy formula, so it still prints res_bad>=0 even
#     when FIXED -- that line is diagnostic only; the VERDICT is 62730.2).
#
# VERDICT: PASS = fold completes ("b_folding_only set, no snark generated")
# AND zero 62730.2 GADGET-UNSAT. FAIL = any 62730.2 / prover panic.
#
# Usage:  nohup bash zkregplus/src/doxygen_dfa_probe.sh > /tmp/dox.out 2>&1 &
# Output: prints the verdict, packs /tmp/doxygen_dfa_probe.tgz.
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJ_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
cd "$PROJ_ROOT"
echo "[dox_probe] proj_root = $PROJ_ROOT"

REPRO_FILE="${ZKR_DOX_FILE:-data/samples/binexec_merged128k/doxygen}"
SLICE_DIR="data/debug/full_clam_bisect/config"
REPORT_DIR="data/debug/full_clam_bisect/reports"
JOBLOG="data/cache/logs/log_job_0.txt"
STDOUT_LOG="/tmp/doxygen_dfa_probe_stdout.txt"
PACK_TGZ="/tmp/doxygen_dfa_probe.tgz"

[ -f "$REPRO_FILE" ] || { echo "[dox_probe] MISSING $REPRO_FILE"; exit 1; }

# ---- single-file slice = just doxygen ---------------------------------------
mkdir -p "$SLICE_DIR" "$REPORT_DIR"
rm -f "$SLICE_DIR"/slice_*.dat
printf '%s\n' "$REPRO_FILE" > "$SLICE_DIR/slice_0.dat"
echo "[dox_probe] slice_0.dat = 1 file: $REPRO_FILE"
rm -f "$JOBLOG" "$PROJ_ROOT/data/cache/run_complete.sentinel" 2>/dev/null || true

echo "[dox_probe] running single-file fold-only DFA repro. stdout -> $STDOUT_LOG"
set +e
RUSTFLAGS="-C link-args=-fuse-ld=lld -Awarnings" \
RUST_MIN_STACK=4000000000 \
ZKR_BISECT_FOLD_ONLY=1 \
ZKR_BISECT_CHECK_LKUP=0 \
ZKR_BISECT_NJOBS=1 \
ZKR_BISECT_DIR="$PROJ_ROOT/$SLICE_DIR" \
ZKR_GADGET_CHECK=1 ZKR_GADGET_FROM=0 \
ZKR_STEP_CHECK=1 ZKR_CS_CHECK=1 \
ZKR_DFA_DUMP=1 \
cargo test -p zkregplus --release --lib -- \
	zkp_driver::tests_zkp_driver::test_full_clam_bisect \
	--exact --nocapture --test-threads=1 \
	2>&1 | tee "$STDOUT_LOG"
rc="${PIPESTATUS[0]}"
set -e
echo "[dox_probe] cargo test exit = $rc"

# ---- verdict ----------------------------------------------------------------
echo "======================================================================"
UNSAT=$(grep -h -c "62730.2\|GADGET-UNSAT" "$STDOUT_LOG" "$JOBLOG" 2>/dev/null \
	| paste -sd+ | bc 2>/dev/null || echo 0)
FOLD_DONE=$(grep -h -c "b_folding_only set, no snark generated" \
	"$STDOUT_LOG" "$JOBLOG" 2>/dev/null | paste -sd+ | bc 2>/dev/null || echo 0)
DFA_SAT=$(grep -h -c "62730.1.*DfaAdvGadget" "$STDOUT_LOG" "$JOBLOG" \
	2>/dev/null | paste -sd+ | bc 2>/dev/null || echo 0)
echo "62730.2 GADGET-UNSAT count : $UNSAT   (expect 0 when FIXED)"
echo "DfaAdvGadget GADGET-SAT OK  : $DFA_SAT  (per-step, >0 when FIXED)"
echo "fold-only completed markers : $FOLD_DONE (>0 = folded all chunks)"
if [ "$rc" = "0" ] && [ "${UNSAT:-1}" = "0" ] && [ "${FOLD_DONE:-0}" != "0" ]; then
	echo "VERDICT: PASS  (doxygen folded, DFA gadget SAT, no UNSAT) -- FIX CONFIRMED"
else
	echo "VERDICT: FAIL  (see 62730.2 below) -- BUG STILL PRESENT"
	grep -h "62730.2\|GADGET-UNSAT" "$STDOUT_LOG" "$JOBLOG" 2>/dev/null \
		| head -4 | sed 's/^.*DEBUG USE /  /' || true
fi
echo "----------------------------------------------------------------------"
echo "context -- last fold step (62727.0):"
grep -h "62727.0" "$STDOUT_LOG" 2>/dev/null | tail -1 \
	| sed 's/^.*DEBUG USE /  /' || true
echo "context -- step-2.1 recheck (62731.9; OLD-formula probe, res_bad>=0"
echo "           is EXPECTED even when fixed -- diagnostic only):"
grep -h "62731.9:" "$STDOUT_LOG" "$JOBLOG" 2>/dev/null | tail -2 \
	| sed 's/^.*DEBUG USE /  /' || true
echo "======================================================================"

# ---- pack -------------------------------------------------------------------
STAGE="$(mktemp -d)"
[ -f "$JOBLOG" ]     && cp "$JOBLOG"     "$STAGE/log_job_0.txt"
[ -f "$STDOUT_LOG" ] && cp "$STDOUT_LOG" "$STAGE/stdout.txt"
tar czf "$PACK_TGZ" -C "$STAGE" .
rm -rf "$STAGE"
echo "[dox_probe] packed -> $PACK_TGZ"
