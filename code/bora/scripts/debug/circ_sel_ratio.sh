#!/usr/bin/env bash
# Tabulate the Phase-1 per-chunk circuit-selection mix of a live neo run
# and score its predicted step cost against the legacy (paper) full_dlp
# run, so a fold can be called GREEN/RED hours after Pass 1 starts.
#
# Marker parsed (foldpot/driver.rs:1947, emitted once per chunk inside
# the Pass-1 "decide circ alloc" loop, needs log_level >= LOG3):
#   [job J] LOG3: ... PERF 1001: per-chunk circ sel. Phase 1
#   word_id: W, subseg_id: S, fname: F, pci: P, seg_len: L
# pci is the FINAL rung the chunk was routed to, so the pci histogram
# IS the prove_step circ_id histogram (verified on the legacy log:
# job 0 pci hist == its real prove_step hist, exactly).
#
# Only words a job has FINISHED are counted (word_id < that job's max
# seen), so a half-emitted word cannot skew the shares.  Lines are
# deduped on (job, word_id, subseg_id), so re-runs appending to the
# same log do not double-count.
#
# Usage:   bash scripts/debug/circ_sel_ratio.sh [log ...]
#          default log: /tmp/bora/CURRENT_JOB.log
# Env:
#   NEO_COSTS  4 neo per-rung step costs in ms, low rung first.
#              Default is the full_dlp v5 ladder.
#   LEG_REF    legacy same-words reference wcost in ms.  Overrides the
#              built-in coarse table, which is only a 3-bucket
#              approximation -- the honest number comes from replaying
#              the printed per-job prefixes against the paper log.
#   LEG_DAYS   legacy full-run fold wall in days, for the projection.
set -u

LOGS=("$@")
if [ ${#LOGS[@]} -eq 0 ]; then LOGS=(/tmp/bora/CURRENT_JOB.log); fi

NEO_COSTS=${NEO_COSTS:-"1898 4287 12954 31128"}
LEG_REF=${LEG_REF:-0}
LEG_DAYS=${LEG_DAYS:-5.05}

LC_ALL=C grep -ah "per-chunk circ sel. Phase 1" "${LOGS[@]}" 2>/dev/null \
| LC_ALL=C awk -v NC="$NEO_COSTS" -v LEGREF="$LEG_REF" \
              -v LEGDAYS="$LEG_DAYS" '
BEGIN{ split(NC, c, " ") }          # c[1..4] = neo cost of pci 0..3
{ match($0,/\[job [0-9]+\]/);    j=substr($0,RSTART+5,RLENGTH-6)+0
  match($0,/word_id: [0-9]+/);   w=substr($0,RSTART+9,RLENGTH-9)+0
  match($0,/subseg_id: [0-9]+/); b=substr($0,RSTART+11,RLENGTH-11)+0
  match($0,/pci: [0-9]+/);       p=substr($0,RSTART+5,RLENGTH-5)+0
  k=j","w","b; if(kk[k]++) next   # dedup: one line per chunk
  if(w>mx[j]) mx[j]=w             # per-job high-water word_id
  cnt[j","w","p]++; seen[j]=1 }
END{
  ns=0; for(j in seen) ns++
  if(ns==0){ print "no Phase-1 circ-sel lines found -- log_level < LOG3,"
             print "wrong log path, or Pass 1 has not started yet."; exit 1 }
  print "per-job progress (max word_id seen):"
  pb=""
  for(j=0;j<8;j++){
    if(j in seen){ printf "  job %d: word %d\n", j, mx[j]
                   pb = pb (pb==""?"":" ") (mx[j]-1) }
    else           pb = pb (pb==""?"":" ") "-1" }
  minW=1000000000
  for(j in seen) if(mx[j]-1 < minW) minW=mx[j]-1
  for(k in cnt){ split(k,a,",")
    if(a[2]+0 < mx[a[1]+0]){ n[a[3]]+=cnt[k]; t+=cnt[k] } }
  if(t==0){ print "no completed words yet -- rerun in a few minutes"
            exit 1 }
  printf "\npooled steps over completed words: %d", t
  printf "  (min common prefix word_id <= %d)\n", minW
  s=0
  for(p=0;p<4;p++){ printf "  pci%d = %6.2f%%   n=%d\n",
                           p, 100*n[p]/t, n[p]+0
                    s += n[p]/t * c[p+1] }
  ref=LEGREF+0
  src="exact (LEG_REF)"
  if(ref<=0){ ref=2934; if(minW<200) ref=2888; else if(minW<650) ref=3005
              src="coarse table" }
  r=s/ref
  v=(r<=0.95) ? "GREEN" : ((r>=1.15) ? "RED" : "WAIT-AND-RERUN")
  printf "\nneo wcost  = %.0f ms\n", s
  printf "legacy ref = %d ms   [%s]\n", ref, src
  printf "RATIO      = %.2f  ->  %s", r, v
  printf "   (<=0.95 GREEN | >=1.15 RED)\n"
  printf "projected fold wall ~= %.2f days (%.2f x RATIO)\n",
         LEGDAYS*r, LEGDAYS
  printf "\nper-job completed prefixes, for the exact legacy replay:\n"
  printf "  %s\n", pb }'
