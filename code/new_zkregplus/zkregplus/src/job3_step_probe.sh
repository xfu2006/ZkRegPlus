#!/usr/bin/env bash
# job3_step_probe.sh -- PER-STEP diagnostic for the full_clam job-3 failure.
#
# Runs job 3 WHOLE as a single valid job (151 files -> ~1704 chunks) with BOTH
# probes armed:
#   ZKR_STEP_CHECK=1 -> per fold step, check the fresh witness against its tight
#                       step-R1CS (62727.1). On the FIRST bad step it prints the
#                       step, circ, first-bad constraint row, then PANICS (early
#                       abort -- you do NOT pay for the rest of the fold or the
#                       decider). 62727.0 (printed just before each step) names
#                       the file; 62729.1 names the finite cross-chunk subsig.
#   ZKR_CS_CHECK=1   -> if NO step fails, the fold completes and the decider
#                       probe names the failing decider block (62001.2).
# Overhead ~1% (tight-only; the redundant relaxed check 62727.2 stays OFF unless
# ZKR_STEP_CHECK_RELAXED is also exported).
#
# Decision tree captured in ONE run:
#   branch A (62727.1 panic) -> a fold step's gadget is UNSAT: step + file +
#     constraint row (+ subsig). Localized, early abort.
#   branch B (no 62727.1, 62001.2) -> fold-carry: which decider block is UNSAT.
#
# For a prod-faithful fold with the decider block only (no per-step probing),
# use job3_decider_probe.sh instead.
#
# Usage (from anywhere):  bash zkregplus/src/job3_step_probe.sh
#   long run (up to ~16h; far less if it aborts early). Detach:
#   nohup bash .../job3_step_probe.sh &
#
# Output: prints the localized culprit and packs a bundle to
# /tmp/job3_step_probe.tgz for download.
set -euo pipefail

# ---- locate repo root (this script lives in zkregplus/src/) ----------------
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJ_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
cd "$PROJ_ROOT"
echo "[step_probe] proj_root = $PROJ_ROOT"

# ---- paths -----------------------------------------------------------------
SRC_LIST="data/debug/full_clamav/config/binexec_p3.dat"   # job 3's file list
SLICE_DIR="data/debug/full_clam_bisect/config"
REPORT_DIR="data/debug/full_clam_bisect/reports"
KEYDIR="data/cache/full_data"
JOBLOG="data/cache/logs/log_job_0.txt"                     # single job -> id 0
STDOUT_LOG="/tmp/job3_step_probe_stdout.txt"
PACK_TGZ="/tmp/job3_step_probe.tgz"

# ---- preflight: keys. Missing is NOT fatal -- the runner auto-builds -------
# a cold/partial snark cache this run (driver.rs:2815-2831 flips to write-mode
# and persists g16_* keys). Warm cache = fast reuse; cold = +multi-hour keygen.
# NOTE: if 62727.1 fires (branch A) the run aborts BEFORE the decider, so no
# g16 keys are needed at all in that case.
missing=""
for k in g16_main.key g16_main.key.meta g16_cp.key g16_cp.key.meta \
         g16_main.sidecar.cf g16_cp.sidecar.cf g16_cp.sidecar.cp; do
	[ -f "$KEYDIR/$k" ] || missing="$missing $k"
done
if [ -n "$missing" ]; then
	echo "############################################################"
	echo "## SNARK KEYS COLD under $KEYDIR"
	echo "## missing:$missing"
	echo "## NOT fatal -- only needed if the fold COMPLETES (branch B);"
	echo "## a branch-A per-step abort never reaches the decider."
	echo "############################################################"
else
	echo "[step_probe] snark keys warm -> reused read-only"
fi
[ -f "$SRC_LIST" ] || { echo "[step_probe] MISSING $SRC_LIST"; exit 1; }

# ---- build the single-job slice = all of job 3 -----------------------------
mkdir -p "$SLICE_DIR" "$REPORT_DIR"
rm -f "$SLICE_DIR"/slice_*.dat
cp "$SRC_LIST" "$SLICE_DIR/slice_0.dat"
n_files="$(grep -cve '^[[:space:]]*$' "$SRC_LIST" || true)"
echo "[step_probe] slice_0.dat = $n_files files (whole job 3)"
rm -f "$JOBLOG" "$PROJ_ROOT/data/cache/run_complete.sentinel" 2>/dev/null || true

# ---- run: NJOBS=1 keeps chunks high; STEP+CS+GADGET checks armed -----------
# DEBUG USE 62730 (REMOVE LATER): ZKR_GADGET_CHECK=1 + ZKR_GADGET_FROM arms the
# per-gadget SAT checkpoints ONLY from that fold step onward (mod_super forces
# construct_matrices:true there). At the culprit step the FIRST failing
# sub-gadget prints 62730.2 GADGET-UNSAT @<gadget> and panics DURING synthesis
# -- finer than 62727.1's whole-step row, and it fires BEFORE 62727.1. Default
# FROM=567 arms probe-steps 568/569 (the observed 62727.1 was step 569), a +-1
# margin; override via ZKR_GADGET_FROM=<n>. RUST_MIN_STACK=4GB keeps the
# mid-synthesis is_satisfied() off the 2MB test stack (sigma_ir1cs.rs:3433
# warns eval_lc can overflow on ~20M-constraint circuits).
ZKR_GADGET_FROM="${ZKR_GADGET_FROM:-567}"
echo "[step_probe] running (per-step tight R1CS + per-gadget SAT + decider probe). stdout -> $STDOUT_LOG"
echo "[step_probe] gadget SAT checkpoints armed from fold step >= $ZKR_GADGET_FROM"
set +e
# NOTE: --lib restricts to the lib test binary (skips doctests); the filter
# is the FULL module path because --exact matches the whole test name.
RUSTFLAGS="-C link-args=-fuse-ld=lld -Awarnings" \
RUST_MIN_STACK=4000000000 \
ZKR_CS_CHECK=1 ZKR_STEP_CHECK=1 ZKR_BISECT_NJOBS=1 \
ZKR_GADGET_CHECK=1 ZKR_GADGET_FROM="$ZKR_GADGET_FROM" \
ZKR_BISECT_DIR="$PROJ_ROOT/$SLICE_DIR" \
cargo test -p zkregplus --release --lib -- \
	zkp_driver::tests_zkp_driver::test_full_clam_bisect \
	--exact --nocapture --test-threads=1 \
	2>&1 | tee "$STDOUT_LOG"
rc="${PIPESTATUS[0]}"
set -e
echo "[step_probe] cargo test exit = $rc"

# ---- report: walk the decision tree ----------------------------------------
# 62727.x/62729.x go to stdout (emit_stdout); 62001.x go to the per-job log.
echo "======================================================================"
if grep -hq "62730.2" "$STDOUT_LOG" "$JOBLOG" 2>/dev/null; then
	echo "RESULT: PER-GADGET BUG NAMED (branch A+) -- a sub-gadget's SAT check"
	echo "  fired during synthesis of the culprit step and named the gadget:"
	grep -h "62730.2" "$STDOUT_LOG" "$JOBLOG" | head -3 | sed 's/^.*DEBUG USE /    /'
	echo "  file being folded at that step (last FOLD-STEP before the abort):"
	grep -h "62727.0" "$STDOUT_LOG" "$JOBLOG" | tail -1 | sed 's/^.*DEBUG USE /    /'
	echo "  gadget SAT checkpoints that PASSED before it (bracketing context):"
	grep -h "62730.1" "$STDOUT_LOG" "$JOBLOG" 2>/dev/null | tail -8 | sed 's/^.*DEBUG USE /    /'
	echo "  finite cross-chunk prune values near that step (subsig id):"
	grep -h "62729.1" "$STDOUT_LOG" "$JOBLOG" 2>/dev/null | tail -6 | sed 's/^.*DEBUG USE /    /'
	echo "  NEXT: the label @<gadget> is the culprit -- read that validator's"
	echo "        constraint against the finite cross-chunk carry and fix."
elif grep -hq "62727.1" "$STDOUT_LOG" "$JOBLOG" 2>/dev/null; then
	echo "RESULT: PER-STEP GADGET BUG (branch A) -- fold aborted at the culprit step."
	echo "  (No 62730.2 -- the violated constraint is OUTSIDE the labeled gadget"
	echo "   checkpoints; see the mod_super::augmented_F_circuit backstop / row.)"
	echo "  failing step (step / circ / first-bad constraint row):"
	grep -h "62727.1" "$STDOUT_LOG" "$JOBLOG" | head -2 | sed 's/^.*DEBUG USE /    /'
	echo "  whole-augmented-cs backstop (if it fired):"
	grep -h "62730.2\|62730.3" "$STDOUT_LOG" "$JOBLOG" 2>/dev/null | grep "augmented_F_circuit" | tail -2 | sed 's/^.*DEBUG USE /    /'
	echo "  file being folded at that step (last FOLD-STEP before the abort):"
	grep -h "62727.0" "$STDOUT_LOG" "$JOBLOG" | tail -1 | sed 's/^.*DEBUG USE /    /'
	echo "  finite cross-chunk prune values near that step (subsig id):"
	grep -h "62729.1" "$STDOUT_LOG" "$JOBLOG" 2>/dev/null | tail -6 | sed 's/^.*DEBUG USE /    /'
	echo "  NEXT: map first_bad_row -> gadget; feed fname to a local discharge-"
	echo "        only run (full_clam_find_file) to name the signature."
elif grep -q "62001.2" "$JOBLOG" 2>/dev/null; then
	echo "RESULT: FOLD-CARRY / DECIDER BUG (branch B) -- all fold steps were SAT;"
	echo "  the decider block is UNSAT:"
	grep -E "62001\.[123]" "$JOBLOG" | sed 's/^.*DEBUG USE /    /'
	echo "  first UNSAT decider block:"
	grep "62001.2" "$JOBLOG" | head -1 | sed 's/^.*DEBUG USE /    /'
elif grep -hq "62727.3" "$STDOUT_LOG" 2>/dev/null; then
	echo "RESULT: all fold steps SAT and no decider UNSAT seen -- either it did"
	echo "  not reproduce here, or the failure is past the probed decider blocks."
	grep -h "62727.3" "$STDOUT_LOG" | tail -2 | sed 's/^.*DEBUG USE /    /'
else
	echo "RESULT: no probe lines -- proving likely never reached. Check for a panic:"
	grep -i "panicked at\|ERROR: lk_share" "$STDOUT_LOG" | head -5 || true
fi
echo "======================================================================"

# ---- pack for download (stage both files, tar once) ------------------------
STAGE="$(mktemp -d)"
[ -f "$JOBLOG" ]     && cp "$JOBLOG"     "$STAGE/log_job_0.txt"
[ -f "$STDOUT_LOG" ] && cp "$STDOUT_LOG" "$STAGE/stdout.txt"
tar czf "$PACK_TGZ" -C "$STAGE" .
rm -rf "$STAGE"
echo "[step_probe] packed -> $PACK_TGZ  (log_job_0.txt + stdout.txt)"
