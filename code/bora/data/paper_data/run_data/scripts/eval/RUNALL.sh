#!/usr/bin/env bash
# ----------------------------------------------------------------------------
# Run every evaluation script in data/scripts/eval, then the data-provenance
# check last. Each generator reads the raw run logs (server-specific ones via
# common.SERVER_TO_USE) and writes a LaTeX fragment under ../../../figs/.
#
# Usage:  bash RUNALL.sh        (run from anywhere; it cd's to its own folder)
#
# A generator that fails (e.g. a dataset whose real dump is still regenerating
# on the server) does NOT stop the run -- it is reported and the rest continue.
# The final exit code is the number of generators that failed; the closing
# check_data_server.py is informational and never counted.
# ----------------------------------------------------------------------------
set -u
cd "$(dirname "$0")"

# Generators, grouped by the table/figure they emit.
GENERATORS=(
  datasets.py            # Table 1  : dataset sizes (Mal/Dna/Dlp)
  effectiveness.py       # §7.3     : approximation-effectiveness tables
  gen_lkup_info.py       # §7.4     : lookup-table composition
  gen_component_cost.py  # §7.4     : per-circuit cost profile
  gen_overall_perf.py    # §7.5     : stage-level performance breakdown
  gen_scale_all.py       # §7.5     : regex-set scalability figure
  dna_reef_bora.py       # Table 3  : Reef per-bucket vs BORA (chr17)
  gen_zombie_table.py    # §7.7     : Zombie measured totals + projection
  gen_compare_all.py     # tab:compare-all : Zombie/Reef/BORA comparison
  count_loc.py           # impl/eval: author-owned Rust line counts
)

fail=0
for s in "${GENERATORS[@]}"; do
  echo "==================== $s ===================="
  if python3 "$s"; then
    echo "[ok]   $s"
  else
    echo "[FAIL] $s"
    fail=$((fail + 1))
  fi
done

# Data-provenance check runs LAST. It audits raw_data/{gcpm1,jet1tb} and exits
# non-zero when it finds a violation, so it is allowed to fail without counting.
echo "==================== check_data_server.py ===================="
python3 check_data_server.py || true

echo
echo "RUNALL done: ${fail} generator(s) failed."
exit "${fail}"
