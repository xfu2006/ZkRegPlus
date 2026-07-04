#!/usr/bin/env bash
# one_time_numa_test_dlp.sh  --  run from zkregplus/src:
#   nohup ./one_time_numa_test_dlp.sh &   ; then: tail -f nohup.out
# NUMA timing for full_dlp fold-only (PCT_CMP% sample, default 1%):
#   optionally HARVEST the real pct=100 ladder (PINNED to half the box ->
#   512GB-equiv ~7h for circuit selection, vs ~14h unpinned on 1TB); when
#   SKIP_HARVEST=1 that step is skipped and the existing DB+ladder are REUSED
#   (preflight hard-fails if either is missing). Then baseline J8, numa J8,
#   numa J16 at PCT_CMP.
# Greppable: "ONETIME_DLP PHASE START/END", "ONETIME_DLP ESTIMATE/ACTUAL/
#   REMAINING", "ONETIME_DLP TIMING <name> <s>", plus the driver's own
#   "PERF WORKFLOW Step N time" / "DLP SPLIT VERIFY: PASS|FAIL".
# ALWAYS (success/error/Ctrl-C/TERM) an EXIT trap packs everything into ONE
#   download file: ./one_time_numa_test_dlp_BUNDLE_<ts>.tgz (with SUMMARY.txt +
#   failure reasons). Only kill -9 can skip it.
set -u
TAG="ONETIME_DLP"

# ---------------- knobs ----------------
SKIP_HARVEST=1      # 1=HARVEST already done on this box: REUSE the existing DB +
                    # ladder, do NOT wipe or rebuild (STEP 0/1 skipped). Preflight
                    # HARD-FAILS if the DB or ladder is missing. 0=fresh harvest.
WIPE_DB=0           # 1=full cold wipe of dlp_corpus_aggr (rebuilds 40GB DB, +~2h).
                    # Forced 0 when SKIP_HARVEST=1 (never wipe reused artifacts).
PCT_CMP=1            # sample % for the 3 comparison runs (~1.2h max fold wall)
HARVEST_PIN=1        # 1=pin HARVEST to one NUMA half (512GB-equiv ~7h, not ~14h)
PART2_DELAY=0        # numa: 0 => halves OVERLAP now (real timing). Raise at pct>=25.
PART2_RAM=700        # numa: only delay part2 START if part1 tree-RSS >= this (GB)
DC_THREADS=8         # ZKR_DC_THREADS for circuit selection (HARVEST only). 8 is
                     # proven; higher MAY cut the ~7h on a many-core half-box but
                     # is unmeasured and can change NUMA behavior.
export ZKR_DC_THREADS="$DC_THREADS"   # driver base_env honors a pre-set value
# Lock RUSTFLAGS to the driver's default so the preflight build and the real
# runs SHARE one build cache (different flags would force a full rebuild).
export RUSTFLAGS="${RUSTFLAGS:--C link-args=-fuse-ld=lld -Awarnings}"

# ---------------- per-task estimates (seconds) -- priors; recalibrate as you go
EST_HARVEST=36000    # ~10h: DB build ~2h + discharge ~0.5h + circuit-sel ~7h (pinned)
EST_BASELINE_J8=1800 # ~30m (pct=1, baseline = all-8-nodes, the slow case)
EST_NUMA_J8=1200     # ~20m (pct=1, pinned halves, overlapping)
EST_NUMA_J16=1200    # ~20m (pct=1)
# SKIP_HARVEST reuses the harvested DB+ladder, so never wipe them and drop the
# HARVEST task from the ETA ladder.
[ "$SKIP_HARVEST" = "1" ] && WIPE_DB=0
if [ "$SKIP_HARVEST" = "1" ]; then
  TASKS=( "RUN_BASELINE_J8:$EST_BASELINE_J8" \
          "RUN_NUMA_J8:$EST_NUMA_J8" "RUN_NUMA_J16:$EST_NUMA_J16" )
else
  TASKS=( "HARVEST_LADDER:$EST_HARVEST" "RUN_BASELINE_J8:$EST_BASELINE_J8" \
          "RUN_NUMA_J8:$EST_NUMA_J8" "RUN_NUMA_J16:$EST_NUMA_J16" )
fi

# ---------------- paths (relative to zkregplus/src) ----------------
DRV=./run_full_dlp_numa.py
REPO=../..                                   # new_zkregplus (cargo workspace root)
RUST_SRC=./zkp_driver.rs                      # holds the ZKR_DLP_LADDER_ONLY gate
RUNCFG=../../data/paper_data/dlp/cfg/config/runcfg_full.json
MASTER=../../data/paper_data/dlp/cfg/jobs/final_enron_list.txt.tgz
SIG=../../data/paper_data/dlp/cfg/regex_pat/main_data_dlp_internationl.dat
CACHE=../../data/cache/dlp_corpus_aggr
LADDER=../../data/paper_data/dlp/cfg/config/dlp_ladder.json
JOBSDIR=../../data/paper_data/dlp/cfg/jobs
LOGS=../../data/cache/logs
TGZ_SRC=/tmp/full_dlp_numa_run               # driver's hardcoded OUT
TS=$(date +%Y%m%d_%H%M%S)
RESULTS=./one_time_numa_test_dlp_out_${TS}   # tgz + timings land here (relative)
BUNDLE=./one_time_numa_test_dlp_BUNDLE_${TS}.tgz   # the ONE file to download
mkdir -p "$RESULTS"

say(){ local m="===== [$TAG] $* ====="; echo "$m"
  echo "$m" >> "$RESULTS/run.log" 2>/dev/null; }   # also kept in the bundle
fmt(){ local s=$1; printf '%dh%02dm%02ds' $((s/3600)) $(((s%3600)/60)) $((s%60)); }
remaining_from(){ local i=$1 sum=0
  while [ "$i" -lt "${#TASKS[@]}" ]; do sum=$((sum + ${TASKS[$i]##*:})); i=$((i+1));
  done; echo "$sum"; }

# half-box pin for HARVEST (circuit selection is NUMA-sensitive: all 8 nodes is
# ~2x slower than one half on the 1TB box).
NNODES=$(numactl -H 2>/dev/null | grep -cE '^node [0-9]+ cpus:')  # grep -c => int
NNODES=${NNODES:-0}
HALF=""
if [ "$HARVEST_PIN" = "1" ] && [ "$NNODES" -ge 2 ] && command -v numactl >/dev/null
then HALF="0-$(( NNODES/2 - 1 ))"; fi

TOTAL_ELAPSED=0
TASK_IDX=0
STAGE="(init)"          # updated as we go; shown in the summary on any exit
PHASE_PREFIX=()
CHILD=""                # PID of the running phase child (for signal cleanup)

kill_tree(){            # kill_tree <pid>: TERM pid and ALL descendants
  local pid="$1" c
  for c in $(pgrep -P "$pid" 2>/dev/null); do kill_tree "$c"; done
  kill -TERM "$pid" 2>/dev/null
}
run_phase(){            # run_phase <NAME> <python-args...>
  local name="$1"; shift
  local est=${TASKS[$TASK_IDX]##*:}
  STAGE="$name (running)"
  say "PHASE START $name ($(date '+%F %T'))"
  say "ESTIMATE $name ~$(fmt "$est")  |  REMAINING incl. this ~$(fmt "$(remaining_from "$TASK_IDX")")"
  rm -f "$TGZ_SRC"/*.tgz "$LOGS"/log_job_*.txt 2>/dev/null   # isolate this run
  local t0=$SECONDS
  # background + wait so an INT/TERM is honored mid-run (a foreground child
  # would defer the trap until it exits -- useless for a 10h phase).
  ${PHASE_PREFIX[@]+"${PHASE_PREFIX[@]}"} python3 -u "$DRV" "$@" &
  CHILD=$!
  wait "$CHILD"; local rc=$?
  CHILD=""
  local dt=$((SECONDS - t0))
  TOTAL_ELAPSED=$((TOTAL_ELAPSED + dt))
  STAGE="$name (done rc=$rc)"
  TASK_IDX=$((TASK_IDX + 1))
  local rem=$(remaining_from "$TASK_IDX")
  local n=0
  for f in "$TGZ_SRC"/*.tgz; do [ -e "$f" ] || continue
    cp -f "$f" "$RESULTS/${name}__$(basename "$f")"; n=$((n+1)); done
  say "PHASE END $name rc=$rc"
  say "ACTUAL $name $(fmt "$dt")  (est $(fmt "$est"))  |  total $(fmt "$TOTAL_ELAPSED")  |  REMAINING ~$(fmt "$rem")"
  printf '%s TIMING %-16s actual=%ss est=%ss rc=%s tgz=%s\n' \
    "$TAG" "$name" "$dt" "$est" "$rc" "$n" | tee -a "$RESULTS/timings.txt"
}

# ---- ALWAYS bundle into ONE tgz on exit (success, error, or signal) ----
write_summary(){          # write_summary <exit-code> -> RESULTS/SUMMARY.txt
  local code="$1" sf="$RESULTS/SUMMARY.txt" fails
  {
    echo "ONE-TIME NUMA DLP TEST -- SUMMARY"
    echo "host=$(hostname)  start_ts=$TS  end=$(date '+%F %T')"
    echo "exit_code=$code   last_stage=$STAGE"
    echo "knobs: WIPE_DB=$WIPE_DB PCT_CMP=$PCT_CMP HARVEST_PIN=$HARVEST_PIN(${HALF:-none}) DC_THREADS=$DC_THREADS"
    echo "total_elapsed=$(fmt "$TOTAL_ELAPSED")"
    echo
    echo "== per-phase timings (actual vs est, rc) =="
    [ -f "$RESULTS/timings.txt" ] && cat "$RESULTS/timings.txt" || echo "(no phase completed)"
    echo
    fails=$(grep -E 'rc=[1-9]' "$RESULTS/timings.txt" 2>/dev/null)
    if [ "$code" = "0" ] && [ -z "$fails" ]; then
      echo "OVERALL: SUCCESS (all phases rc=0)"
    else
      echo "OVERALL: FAILURE / INCOMPLETE (exit=$code, last_stage=$STAGE)"
      echo
      echo "== failure reasons (scanned driver logs + nohup.out) =="
      grep -nE "PREFLIGHT FAIL|ABORT|panic|panicked|error\[|CapErr|SIGABRT|Killed|out of memory|cannot allocate|DLP SPLIT VERIFY: FAIL|FATAL|VERIFICATION FAILED" \
        "$TGZ_SRC"/*.log ./nohup.out "$RESULTS"/run.log "$RESULTS"/preflight_build.log 2>/dev/null | tail -n 40 \
        || echo "(no obvious signature; read the .log/.tgz in this bundle)"
    fi
    echo
    echo "== bundle contents =="
    echo "SUMMARY.txt, timings.txt, *__*.tgz (per-phase), *.log (raw driver), nohup_tail.txt"
  } > "$sf" 2>&1
}

on_sig(){                 # INT/TERM handler: stop the child tree, then bundle
  say "SIGNAL caught (exit $1) -> stopping child tree + bundling"
  [ -n "${CHILD:-}" ] && kill_tree "$CHILD"
  exit "$1"
}

finish(){                 # EXIT trap: build the single download bundle, always
  local code=$?
  [ -n "${CHILD:-}" ] && kill_tree "$CHILD"   # belt: never orphan the prover
  # surface a phase failure (rc!=0) as a non-zero script exit, even if we
  # ran every phase to the end (we never set -e, so a crash doesn't stop us).
  if [ "$code" = "0" ] && grep -qE 'rc=[1-9]' "$RESULTS/timings.txt" 2>/dev/null
  then code=1; fi
  say "FINALIZE: building ONE download bundle (exit=$code, stage=$STAGE)"
  write_summary "$code"
  cp -f "$TGZ_SRC"/*.log "$RESULTS"/ 2>/dev/null          # raw driver logs
  [ -f ./nohup.out ] && tail -n 1000 ./nohup.out > "$RESULTS/nohup_tail.txt" 2>/dev/null
  tar -czf "$BUNDLE" -C "$(dirname "$RESULTS")" "$(basename "$RESULTS")" 2>/dev/null
  say "BUNDLE READY (download this ONE file): $BUNDLE"
  ls -la "$BUNDLE" 2>/dev/null
  say "SUMMARY (also inside the bundle):"
  sed -n '1,14p' "$RESULTS/SUMMARY.txt" 2>/dev/null
  exit "$code"
}
trap finish EXIT
trap 'on_sig 130' INT
trap 'on_sig 143' TERM

say "BEGIN host=$(hostname) ts=$TS  WIPE_DB=$WIPE_DB PCT_CMP=$PCT_CMP nodes=$NNODES"
say "harvest pin: ${HALF:-none}  dc_threads: $DC_THREADS  results dir (relative): $RESULTS"
say "PLAN  HARVEST ~$(fmt "$EST_HARVEST") | BASELINE_J8 ~$(fmt "$EST_BASELINE_J8") | NUMA_J8 ~$(fmt "$EST_NUMA_J8") | NUMA_J16 ~$(fmt "$EST_NUMA_J16")"
say "PLAN  GRAND TOTAL ~$(fmt "$(remaining_from 0)")"

# STEP -1: PREFLIGHT -- fail BEFORE the wipe so a broken setup never destroys
# the 40GB DB (and a missing Rust gate never turns --ladder-only into a full
# pct=100 fold). Cheap checks first; the slow build only if those pass.
STAGE="PREFLIGHT"
say "STEP -1/5 PREFLIGHT (verify before any wipe)"
pf=0
grep -q "ladder-only" "$DRV" || { say "PREFLIGHT FAIL: $DRV lacks --ladder-only"; pf=1; }
grep -q "ZKR_DLP_LADDER_ONLY" "$RUST_SRC" || { say "PREFLIGHT FAIL: $RUST_SRC lacks ZKR_DLP_LADDER_ONLY gate (would full-fold!)"; pf=1; }
[ -f "$RUNCFG" ] || { say "PREFLIGHT FAIL: missing runcfg $RUNCFG"; pf=1; }
[ -f "$MASTER" ] || { say "PREFLIGHT FAIL: missing master list $MASTER"; pf=1; }
[ -f "$SIG" ]    || { say "PREFLIGHT FAIL: missing sig file $SIG"; pf=1; }
if [ -n "$HALF" ]; then
  numactl "--cpunodebind=$HALF" "--preferred-many=$HALF" true 2>/dev/null \
    || { say "PREFLIGHT FAIL: numactl --preferred-many=$HALF unsupported (driver numa mode needs it too)"; pf=1; }
fi
# SKIP_HARVEST reuses harvested artifacts -- FAIL LOUD if either is missing so
# we never silently fall into a ~7h ladder rebuild or a 40GB DB rebuild.
if [ "$SKIP_HARVEST" = "1" ]; then
  [ -s "$LADDER" ] \
    || { say "PREFLIGHT FAIL: SKIP_HARVEST=1 but ladder missing/empty: $LADDER (set SKIP_HARVEST=0 to harvest it)"; pf=1; }
  { [ -d "$CACHE" ] && [ -f "$CACHE/lkup.txt" ]; } \
    || { say "PREFLIGHT FAIL: SKIP_HARVEST=1 but DB cache missing: $CACHE (need lkup.txt; set SKIP_HARVEST=0)"; pf=1; }
fi
if [ "$pf" = "0" ]; then
  say "PREFLIGHT: cargo test --no-run (build the test binary; cold build may be slow)"
  if ( cd "$REPO" && cargo test -p zkregplus --release --no-run ) \
       > "$RESULTS/preflight_build.log" 2>&1
  then say "PREFLIGHT: build OK"
  else say "PREFLIGHT FAIL: cargo test --no-run failed (see preflight_build.log)"; pf=1; fi
fi
if [ "$pf" = "1" ]; then
  say "ABORT before wipe -- preflight failed; DB/ladder untouched. Fix and rerun."
  exit 3
fi
say "PREFLIGHT OK"

# STEP 0/5: wipe to a known fresh state (skipped entirely when reusing artifacts)
STAGE="STEP0 WIPE"
if [ "$SKIP_HARVEST" = "1" ]; then
  say "STEP 0/5 SKIP WIPE (SKIP_HARVEST=1: keep DB + ladder + splits intact)"
else
  say "STEP 0/5 WIPE"
  rm -f  "$LADDER"            && echo "$TAG removed ladder"
  rm -rf "$JOBSDIR"/jobs8 "$JOBSDIR"/jobs16 \
         "$JOBSDIR"/jobs8_pct* "$JOBSDIR"/jobs16_pct* && echo "$TAG removed splits"
  if [ "$WIPE_DB" = "1" ]; then
    rm -rf "$CACHE" && echo "$TAG removed FULL DB (will rebuild in HARVEST)"
  else
    rm -rf "$CACHE/discharge" && echo "$TAG removed discharge cache (kept DB)"
  fi
fi

# STEP 1/5: harvest the REAL pct=100 ladder, PINNED to half the box, stop pre-fold
if [ "$SKIP_HARVEST" = "1" ]; then
  say "STEP 1/5 SKIP HARVEST (reuse ladder $LADDER + DB $CACHE)"
else
  say "STEP 1/5 HARVEST (build DB + discharge + circuit selection)"
  if [ -n "$HALF" ]; then
    PHASE_PREFIX=(numactl "--cpunodebind=$HALF" "--preferred-many=$HALF")
  fi
  run_phase HARVEST_LADDER --ladder-only
  PHASE_PREFIX=()
fi
[ -s "$LADDER" ] || { say "FATAL: ladder missing; abort"; exit 2; }
say "ladder ready: $LADDER"

# STEP 2/5: baseline, 8 jobs
say "STEP 2/5 BASELINE J8"
run_phase RUN_BASELINE_J8 --mode=baseline --jobs=8 --pct=$PCT_CMP

# STEP 3/5: numa, 8 jobs (overlapping halves)
say "STEP 3/5 NUMA J8"
run_phase RUN_NUMA_J8 --mode=numa --jobs=8 --pct=$PCT_CMP \
  --part2-delay=$PART2_DELAY --part2-ram-gb=$PART2_RAM

# STEP 4/5: numa, 16 jobs (overlapping halves)
say "STEP 4/5 NUMA J16"
run_phase RUN_NUMA_J16 --mode=numa --jobs=16 --pct=$PCT_CMP \
  --part2-delay=$PART2_DELAY --part2-ram-gb=$PART2_RAM

# STEP 5/5: summary
say "STEP 5/5 SUMMARY  (total elapsed $(fmt "$TOTAL_ELAPSED"))"
cat "$RESULTS/timings.txt"
say "tgz outputs (relative $RESULTS):"; ls -la "$RESULTS"/*.tgz 2>/dev/null
say "per-step: grep 'PERF WORKFLOW Step' nohup.out ; verify: grep 'DLP SPLIT VERIFY' nohup.out"
say "DONE"
