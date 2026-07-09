#!/usr/bin/env bash
# doxygen_dfa_probe.sh -- MINIMAL DFA-failure repro for the full_clam job-3 bug.
#
# The 07-08i server run localized the failure to a PER-STEP gadget UNSAT in
# DfaAdvGadget for ONE file (doxygen, seg 1) -- Branch A, self-contained, so it
# reproduces from a FRESH fold. This script folds doxygen ALONE (1 file) with:
#   ZKR_BISECT_CHECK_LKUP=0 -> b_check_lkup=false (DEBUG 62731.0). doxygen is
#     ~67 chunks < the ~678 lk_share coverage floor, so a 1-file run would panic
#     with b_check_lkup=true; false skips that. The DFA gadget's step-3 logup is
#     emitted during synthesis regardless, so the bug still reproduces.
#   Same full_data DB + same full_clamav caps/config as job3 (full_clam_bisect)
#     -> doxygen routes to the SAME circ=1 DFA gadget that failed.
#   ZKR_GADGET_CHECK=1 ZKR_GADGET_FROM=0 -> per-gadget SAT checks from step 0;
#     at doxygen's bad chunk the DFA gadget prints 62730.2 GADGET-UNSAT + panics.
#   ZKR_DFA_DUMP=1 -> the 62731.x DFA diagnostic probes (uncovered sig + DNF
#     shape + per-subsig FSM result + pattern/carry) fire so we can infer the
#     root cause (empty-DNF vs SDE-vs-DFA discharge disagreement vs carry).
#
# Cost: ~15-20 min (Pass-1 discharge doxygen ~6 min + build + a couple of fold
# steps -> panic). No decider, no keys (aborts before them).
#
# Usage:  nohup bash zkregplus/src/doxygen_dfa_probe.sh > /tmp/dox.out 2>&1 &
# Output: prints the named sig + gadget, packs /tmp/doxygen_dfa_probe.tgz.
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

echo "[dox_probe] running single-file DFA repro. stdout -> $STDOUT_LOG"
set +e
RUSTFLAGS="-C link-args=-fuse-ld=lld -Awarnings" \
RUST_MIN_STACK=4000000000 \
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

# ---- report -----------------------------------------------------------------
echo "======================================================================"
echo "GADGET named (62730.2):"
grep -h "62730.2" "$STDOUT_LOG" "$JOBLOG" 2>/dev/null | head -2 \
	| sed 's/^.*DEBUG USE /  /' || echo "  (none)"
echo "UNCOVERED SIG + DNF shape (62731.1):"
grep -h "62731.1" "$STDOUT_LOG" "$JOBLOG" 2>/dev/null | head -8 \
	| sed 's/^.*DEBUG USE /  /' || true
echo "disjunct subsig FSM results (62731.2) -- non-False => SDE/DFA disagree:"
grep -h "62731.2" "$STDOUT_LOG" "$JOBLOG" 2>/dev/null | head -20 \
	| sed 's/^.*DEBUG USE /  /' || true
echo "committed-column miss (62731.4) -- fires only if advice was consistent:"
grep -h "62731.4" "$STDOUT_LOG" "$JOBLOG" 2>/dev/null | head -8 \
	| sed 's/^.*DEBUG USE /  /' || true
echo "LOGUP DIAG (62731.6) -- sum_ok=false names the failing logup:"
grep -h "62731.6:" "$STDOUT_LOG" "$JOBLOG" 2>/dev/null \
	| grep -v "sum_ok=true" | head -20 | sed 's/^.*DEBUG USE /  /' || true
echo "  (membership misses 62731.6a):"
grep -h "62731.6a" "$STDOUT_LOG" "$JOBLOG" 2>/dev/null | head -20 \
	| sed 's/^.*DEBUG USE /  /' || true
echo "  (multiplicity mismatches 62731.6b):"
grep -h "62731.6b" "$STDOUT_LOG" "$JOBLOG" 2>/dev/null | head -20 \
	| sed 's/^.*DEBUG USE /  /' || true
echo "fold step / file at abort (62727.0):"
grep -h "62727.0" "$STDOUT_LOG" 2>/dev/null | tail -1 \
	| sed 's/^.*DEBUG USE /  /' || true
echo "======================================================================"

# ---- pack -------------------------------------------------------------------
STAGE="$(mktemp -d)"
[ -f "$JOBLOG" ]     && cp "$JOBLOG"     "$STAGE/log_job_0.txt"
[ -f "$STDOUT_LOG" ] && cp "$STDOUT_LOG" "$STAGE/stdout.txt"
tar czf "$PACK_TGZ" -C "$STAGE" .
rm -rf "$STAGE"
echo "[dox_probe] packed -> $PACK_TGZ"
