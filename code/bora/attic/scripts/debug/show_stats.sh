#!/usr/bin/env bash
# Read-only CPU/thread snapshot of a live bora run, to settle ONE
# question about Phase-1 Pass 1: is the box saturated, or is neo running
# about one thread per job?
#
# Why it matters: the aggressive Pass-1 router (foldpot/driver.rs:937
# gen_nd_advice_per_seg_pll) is a serial segment loop inside a serial
# word loop (driver.rs:1947), so a job's only parallelism is whatever
# the mapper does internally.  Legacy discharge_adv.rs has 66 rayon
# sites (31 of them in to_container); discharge_adv_neo.rs has none.
# If that asymmetry is live, this script shows ~1 busy thread per job
# in a pool sized to the box.  A pre-fix perf run saw exactly that:
# "8 threads at 6.70% in a 64-wide pool".
#
# %CPU is computed from /proc/<pid>/stat utime+stime deltas over the
# sample interval, NOT from `ps -o %cpu` (which reports the average
# since process start and would be diluted by the setup phase).  No
# sysstat dependency.  Nothing is written outside stdout.
#
# Also harvests the 69120 Pass-1 probes from the run log:
#   69120.5/.6  shared_core fn vs per-subsig loop span
#   69120.7     partA router: halo / ok-try / failed-try
#   69120.8     partB: halo / advice / stmt / lkup
#
# Usage:   bash scripts/debug/show_stats.sh [interval_secs]
#          default interval: 5
# Env:
#   PAT   process match pattern for pgrep -f.  Default bora_cli.
#   LOG   run log to scan for probes.
#         Default /tmp/bora/neo_run/speed/v1_probe.log
#   TOPN  how many hot threads to list.  Default 12.

set -u

IVAL=${1:-5}
PAT=${PAT:-bora_cli}
LOG=${LOG:-/tmp/bora/neo_run/speed/v1_probe.log}
TOPN=${TOPN:-12}
HZ=$(getconf CLK_TCK 2>/dev/null || echo 100)
NCPU=$(nproc)

# utime+stime (ticks) for a /proc/<pid> or /proc/<pid>/task/<tid> dir.
# Strips "pid (comm) " first so a comm containing spaces cannot shift
# the field numbering; utime/stime are then fields 12/13.
read_ticks() {
	local f="$1/stat" line rest
	[ -r "$f" ] || { echo 0; return; }
	line=$(cat "$f" 2>/dev/null) || { echo 0; return; }
	rest=${line#*') '}
	# shellcheck disable=SC2086
	set -- $rest
	echo $(( ${12:-0} + ${13:-0} ))
}

pct() { # ticks_delta interval -> %CPU with one decimal
	awk -v d="$1" -v i="$2" -v hz="$HZ" \
		'BEGIN{ printf "%.1f", (d*100.0)/(hz*i) }'
}

echo "================ show_stats.sh ================"
echo "date      : $(date '+%F %T')"
echo "host      : $(hostname)"
echo "nproc     : $NCPU     CLK_TCK: $HZ     interval: ${IVAL}s"
echo "uptime    :$(uptime | sed 's/.*load average/ load average/')"
echo
echo "---- memory (GB) ----"
free -g 2>/dev/null | sed -n '1,3p'
echo

# ---------------------------------------------------------------
# 1. locate the processes
# ---------------------------------------------------------------
echo "---- processes matching '$PAT' ----"
# exclude this script's own pid and its parent (pgrep -f self-match)
PIDS=$(pgrep -f "$PAT" | grep -v -e "^$$\$" -e "^$PPID\$")
if [ -z "$PIDS" ]; then
	echo "NONE FOUND.  Top CPU consumers instead:"
	ps -eo pid,nlwp,etime,%cpu,rss,comm --sort=-%cpu | head -8
	echo "(re-run with PAT=<pattern>)"
	exit 0
fi
CSV=$(echo "$PIDS" | paste -sd, -)
ps -o pid,nlwp,etime,rss,args -p "$CSV" 2>/dev/null | cut -c1-140
echo

# ---------------------------------------------------------------
# 2. whole-box + per-process %CPU over one interval
# ---------------------------------------------------------------
sys0=$(awk '/^cpu /{i=$5; t=0; for(n=2;n<=8;n++) t+=$n; print t" "i}' \
	/proc/stat)
declare -A P0
for p in $PIDS; do P0[$p]=$(read_ticks "/proc/$p"); done

# thread ticks, first sample
declare -A T0 TNAME
for p in $PIDS; do
	for tdir in /proc/$p/task/*; do
		[ -d "$tdir" ] || continue
		tid=${tdir##*/}
		T0["$p:$tid"]=$(read_ticks "$tdir")
		TNAME["$p:$tid"]=$(cat "$tdir/comm" 2>/dev/null)
	done
done

sleep "$IVAL"

sys1=$(awk '/^cpu /{i=$5; t=0; for(n=2;n<=8;n++) t+=$n; print t" "i}' \
	/proc/stat)
echo "---- whole box over ${IVAL}s ----"
echo "$sys0 $sys1" | awk -v n="$NCPU" \
	'{ dt=$3-$1; di=$4-$2;
	   if (dt<=0) { print "no delta"; exit }
	   busy=100.0*(dt-di)/dt;
	   printf "busy: %.1f%% of %d cores  ( ~%.1f cores active )\n",
	          busy, n, busy*n/100.0 }'
echo

echo "---- per-process %CPU over ${IVAL}s ----"
TOTPCT=0
for p in $PIDS; do
	d=$(( $(read_ticks "/proc/$p") - ${P0[$p]} ))
	v=$(pct "$d" "$IVAL")
	nl=$(ls /proc/$p/task 2>/dev/null | wc -l)
	printf "pid %-8s %8s%%   threads_alive: %s\n" "$p" "$v" "$nl"
	TOTPCT=$(awk -v a="$TOTPCT" -v b="$v" 'BEGIN{print a+b}')
done
printf "TOTAL          %8s%%   (=%s cores of %s)\n" "$TOTPCT" \
	"$(awk -v t="$TOTPCT" 'BEGIN{printf "%.1f", t/100.0}')" "$NCPU"
echo

# ---------------------------------------------------------------
# 3. per-thread breakdown
# ---------------------------------------------------------------
echo "---- threads over ${IVAL}s (busy = >50% of one core) ----"
TMP=$(mktemp)
for k in "${!T0[@]}"; do
	p=${k%%:*}; tid=${k##*:}
	cur=$(read_ticks "/proc/$p/task/$tid")
	d=$(( cur - ${T0[$k]} ))
	[ "$d" -le 0 ] && continue
	printf "%s %s %s %s\n" "$(pct "$d" "$IVAL")" "$p" "$tid" \
		"${TNAME[$k]}" >> "$TMP"
done
NBUSY=$(awk '$1>50' "$TMP" 2>/dev/null | wc -l)
NANY=$(wc -l < "$TMP" 2>/dev/null)
NALL=0
for p in $PIDS; do
	NALL=$(( NALL + $(ls /proc/$p/task 2>/dev/null | wc -l) ))
done
echo "threads in pool : $NALL"
echo "threads with ANY cpu : $NANY"
echo "threads >50%    : $NBUSY      <-- THE NUMBER"
echo
echo "top $TOPN threads (%cpu pid tid comm):"
sort -rn "$TMP" 2>/dev/null | head -"$TOPN"
rm -f "$TMP"
echo

# ---------------------------------------------------------------
# 4. probe harvest
# ---------------------------------------------------------------
echo "---- probes in $LOG ----"
if [ -r "$LOG" ]; then
	echo "log mtime: $(date -r "$LOG" '+%F %T')   size: \
$(du -h "$LOG" | cut -f1)"
	for t in 5 6 7 8; do
		n=$(grep -c "DEBUG USE 69120.$t:" "$LOG" 2>/dev/null)
		printf "69120.%s : %s hits\n" "$t" "$n"
	done
	echo "--- last lines of each ---"
	for t in 5 7 8; do
		grep "DEBUG USE 69120.$t:" "$LOG" 2>/dev/null | tail -2
	done
	echo "--- PERF 1007 (phase totals) ---"
	grep "PERF 1007" "$LOG" 2>/dev/null | tail -6
	echo "--- PERF 1001 count: $(grep -c 'PERF 1001' "$LOG") ---"
else
	echo "not readable: $LOG   (set LOG=...)"
fi
echo

# ---------------------------------------------------------------
# 5. verdict hint
# ---------------------------------------------------------------
echo "---- reading ----"
awk -v t="$TOTPCT" -v n="$NCPU" -v b="$NBUSY" 'BEGIN{
  c = t/100.0;
  printf "using %.1f of %d cores; %d threads >50%%\n", c, n, b;
  if (c < n*0.25)
    print "=> SERIAL-BOUND: parallelism is the lever.";
  else if (c > n*0.75)
    print "=> SATURATED: remaining gap is algorithmic, not parallel.";
  else
    print "=> PARTIAL fan-out: send the top-thread list too.";
}'
echo "==============================================="
