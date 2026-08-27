#!/usr/bin/env bash
# ----------------------------------------------------------------------------
# Run every evaluation script in data/scripts/eval, then the data-provenance
# check last. Each generator reads the raw run logs (server-specific ones via
# common.SERVER_TO_USE) and writes a LaTeX fragment under ../../../figs/ --
# except count_loc.py and the closing check_data_server.py, which write no
# fragment and only print.
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
  datasets.py            # Table 1      : dataset sizes (Mal/Dna/Dlp), §6.2
  effectiveness.py       # Tables 2/5/6 : approximation effectiveness, §6.3 + App. C.2
  gen_lkup_info.py       # Table 7      : lookup-table composition, App. C.3 (§6.4)
  gen_component_cost.py  # Table 8      : per-circuit cost profile, App. C.3 (§6.4)
  gen_overall_perf.py    # Table 3      : stage-level performance breakdown, §6.5
  gen_scale_all.py       # Figure 8     : regex-set scalability, App. C.3 (§6.5)
  dna_reef_bora.py       # Table 9      : Reef per-bucket vs BORA (chr17), App. C.4
  gen_zombie_table.py    # Tables 10/11 : Zombie measured totals + projection, App. C.4
  gen_compare_all.py     # Table 4      : Zombie/Reef/BORA comparison (tab:compare-all), §6.5
  count_loc.py           # §6.1 "99k LOC": author-owned Rust line counts
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
