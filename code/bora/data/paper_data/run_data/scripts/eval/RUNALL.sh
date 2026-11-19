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

# Generators, grouped by the table/figure they emit (numbers: 11/18 build).
GENERATORS=(
  datasets.py            # Table 1      : dataset sizes (Mal/Dna/Dlp), Sec. 6.2
  effectiveness.py       # Tables 2/5/6 : tier discharge + per-circuit steps (T2)
  gen_lkup_info.py       # Table 7      : lookup-table composition, App. D
  gen_component_cost.py  # Table 8      : per-circuit cost profile, App. D
  gen_overall_perf.py    # Table 3      : stage-level performance breakdown, Sec. 6.5
  gen_scale_all.py       # Figure 12    : regex-set scalability (Sec. 6.5 after WA08)
  dna_reef_bora.py       # Table 9      : Reef per-bucket vs BORA (chr17), App. D.4
  gen_zombie_table.py    # Table 10     : Zombie same-sample per arm, App. D.4
  gen_compare_measured.py # W203 table  : measured Reef/Zombie vs BORA, Sec. 6.5
  count_loc.py           # Sec. 6.1 "99k LOC": author-owned Rust line counts
)

# ALL_T1020: drop every old fragment first, so a failed generator leaves
# no fragment (list_figures shows MISSING) instead of an older one.
python3 -c 'import sys; sys.path.insert(0, ".."); import common; common.reset_fig_dir()'

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
