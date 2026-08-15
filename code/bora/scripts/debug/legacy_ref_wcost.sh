#!/usr/bin/env bash
# Companion to circ_sel_ratio.sh: replay the legacy (paper) full_dlp run
# over the SAME words the live neo run has finished, and print legacy's
# step count, pci mix, and wcost.  Feed the wcost back in as LEG_REF to
# turn the coarse ratio into the honest apples-to-apples one.
#
# Runs on the machine that holds the paper log, not on the prod server.
# The legacy log is ~741 MB, so one pass takes a couple of minutes.
#
# Usage:  bash scripts/debug/legacy_ref_wcost.sh W0 W1 .. W7
#   where W0..W7 are the per-job completed prefixes printed by
#   circ_sel_ratio.sh (a -1 skips that job, e.g. it had not started).
# Env:
#   LEG_LOG    path to the legacy combined log
#   LEG_COSTS  4 legacy per-rung step costs in ms, low rung first.
#              Defaults are the measured full_dlp prove_step averages.
set -u

if [ $# -eq 0 ]; then
  echo "usage: $0 W0 W1 .. W7   (per-job prefixes from circ_sel_ratio.sh)"
  exit 1
fi

PAPER=/home/xiang/Desktop/NewResearch/Projects/ZkregPlusAll/ZkregPlusPaper
LEG_LOG=${LEG_LOG:-"$PAPER/usenix27/data/raw_data/jet1tb/extracted/full_dlp.combined.log"}
LEG_COSTS=${LEG_COSTS:-"1985 2522 8059 42156"}

if [ ! -f "$LEG_LOG" ]; then
  echo "legacy log not found: $LEG_LOG"; exit 1
fi

LC_ALL=C grep -a "per-chunk circ sel" "$LEG_LOG" \
| LC_ALL=C awk -v WJ="$*" -v LC="$LEG_COSTS" '
BEGIN{ split(WJ, wj, " "); split(LC, c, " ") }  # wj[1..8], c[1..4]
{ match($0,/\[job [0-9]+\]/);    j=substr($0,RSTART+5,RLENGTH-6)+0
  match($0,/word_id: [0-9]+/);   w=substr($0,RSTART+9,RLENGTH-9)+0
  match($0,/pci: [0-9]+/);       p=substr($0,RSTART+5,RLENGTH-5)+0
  lim = wj[j+1]
  if(lim == "" || lim+0 < 0) next               # job skipped
  if(w <= lim+0){ n[p]++; t++; nj[j]++ } }
END{
  if(t==0){ print "no legacy steps in that prefix -- check the W list"
            exit 1 }
  printf "legacy on the SAME words: steps=%d  per-job:", t
  for(j=0;j<8;j++) printf " %d", nj[j]+0
  print ""
  s=0
  for(p=0;p<4;p++){ printf "  pci%d = %6.2f%%   n=%d\n",
                           p, 100*n[p]/t, n[p]+0
                    s += n[p]/t * c[p+1] }
  printf "legacy wcost = %.0f ms\n", s
  printf "\nnow rerun on the server:  LEG_REF=%.0f bash \\\n", s
  printf "  scripts/debug/circ_sel_ratio.sh\n"
  printf "(its step count must match %d, else the words differ)\n", t }'
