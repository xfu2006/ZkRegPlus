#!/usr/bin/env bash
# JET_T1024: read-only host + install check before a BORA PAPER_DATA.py run.
# Usage:  bash scripts/debug/host_check.sh [BORA_DIR] [--jet1tb]
# Remote: ssh HOST 'bash -s' -- BORA_DIR --jet1tb < scripts/debug/host_check.sh
# BORA_DIR defaults to two levels above this script (code/bora). --jet1tb
# also compares against the r3.xl profile of the August jet1tb run.
# Prints FAIL (blocks a run), WARN (speed or space), INFO (record only).
# Exit code = number of FAIL lines. Changes nothing on the host.

BORA=""; JET=0
for a in "$@"; do
  case "$a" in --jet1tb) JET=1 ;; *) BORA="$a" ;; esac
done
if [ -z "$BORA" ]; then
  if [ -n "${BASH_SOURCE[0]}" ] && [ -f "${BASH_SOURCE[0]}" ]; then
    BORA="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
  else
    BORA="$PWD"
  fi
fi
NF=0
ok()   { echo "OK    $*"; }
fail() { echo "FAIL  $*"; NF=$((NF + 1)); }
warn() { echo "WARN  $*"; }
info() { echo "INFO  $*"; }
has()  { command -v "$1" >/dev/null 2>&1; }
rd()   { cat "$1" 2>/dev/null || echo "?"; }

echo "== host_check.sh on $(hostname) $(date '+%F %T') BORA=$BORA"

echo "== 1. host facts (record)"
if has cloud-init; then
  info "cloud-init: $(cloud-init status 2>/dev/null | tr '\n' ' ')"
  p=$(pgrep -a -x 'apt|apt-get|dpkg|unattended-upgr' 2>/dev/null)
  [ -z "$p" ] && ok "no apt/dpkg running" || warn "apt/dpkg still running: $p"
fi
NCPU=$(nproc --all)
MODEL=$(lscpu | sed -n 's/^Model name: *//p' | head -1)
SOCK=$(lscpu | sed -n 's/^Socket(s): *//p' | head -1)
info "cpus $NCPU, sockets $SOCK, model $MODEL"
NNODE=$(ls -d /sys/devices/system/node/node[0-9]* 2>/dev/null | wc -l)
info "numa nodes $NNODE"
has numactl && numactl -H | grep -E '^node [0-9]+ size' | sed 's/^/INFO    /'
MEM=$(free -g | awk '/^Mem:/{print $2}')
SWP=$(free -g | awk '/^Swap:/{print $2}')
info "memory ${MEM} GiB, swap ${SWP} GiB"
info "kernel $(uname -r), $(ldd --version 2>/dev/null | head -1)"
for f in /sys/kernel/mm/transparent_hugepage/{enabled,defrag,khugepaged/defrag} \
         /proc/sys/kernel/numa_balancing \
         /proc/sys/vm/{swappiness,zone_reclaim_mode,overcommit_memory,max_map_count} \
         /sys/devices/system/cpu/cpu0/cpufreq/scaling_{driver,governor}; do
  info "$f: $(rd "$f")"
done
df -h / "$BORA" 2>/dev/null | sed 's/^/INFO    /'

echo "== 2. any BORA machine"
THP=$(rd /sys/kernel/mm/transparent_hugepage/enabled)
case "$THP" in
  *"[never]"*) warn "THP is never: run is slower (results unchanged)" ;;
  *) ok "THP not never" ;;
esac
V=$(env | grep -E '^(RAYON_|MIMALLOC_|CARGO_|RUSTFLAGS|RUST_LOG|ZKR_)' \
      | grep -v -E '^CARGO_HOME=|^RUSTUP_HOME=')
[ -z "$V" ] && ok "no build/run variables in env" \
  || fail "build/run variables set: $(echo $V)"
if has numactl; then
  numactl --cpunodebind=0 --preferred-many=0 true 2>/dev/null \
    && ok "numactl --preferred-many works" \
    || fail "numactl --preferred-many fails (numactl too old?)"
else
  fail "numactl missing"
fi
[ -x /usr/bin/time ] && ok "/usr/bin/time present" || fail "/usr/bin/time missing"
L=$(loginctl show-user "$USER" -p Linger 2>/dev/null | cut -d= -f2)
[ "$L" = yes ] && ok "linger yes" || fail "linger '$L' (Zombie needs yes)"
sudo -n true 2>/dev/null && ok "passwordless sudo" || fail "sudo needs a password"
if has rustup; then
  rustup toolchain list 2>/dev/null | grep -q nightly-2023-02-01 \
    && ok "nightly-2023-02-01 installed (HOME=$HOME)" \
    || fail "nightly-2023-02-01 missing for HOME=$HOME (Zombie)"
else
  fail "rustup missing for HOME=$HOME"
fi
ZD="$BORA/data/src_sig/ms_dlp/zombie"
grep -q '^commit: *ae5ae948' "$ZD/UPSTREAM.txt" 2>/dev/null \
  && ok "Zombie UPSTREAM ae5ae948" || fail "Zombie UPSTREAM.txt missing or not ae5ae948"
[ -f "$ZD/circ/src/target/mod.rs" ] && ok "Zombie circ/src/target/mod.rs present" \
  || fail "Zombie clone incomplete (circ/src/target/mod.rs)"
if [ -d "$BORA/.git" ] || git -C "$BORA" rev-parse >/dev/null 2>&1; then
  info "git HEAD $(git -C "$BORA" rev-parse HEAD 2>/dev/null)"
  n=$(git -C "$BORA" status --porcelain --untracked-files=no 2>/dev/null | wc -l)
  [ "$n" = 0 ] && ok "no modified tracked files" || warn "$n modified tracked files"
fi
FREE=$(df -BG --output=avail "$BORA" 2>/dev/null | tail -1 | tr -dc 0-9)
if [ -n "$FREE" ]; then
  [ "$FREE" -ge 180 ] && ok "free on BORA volume ${FREE} GiB (full run needs 180)" \
    || warn "free on BORA volume ${FREE} GiB < 180 (full run refuses)"
fi

if [ "$JET" = 1 ]; then
  echo "== 3. jet1tb profile (r3.xl, August run)"
  chk() { [ "$2" = "$3" ] && ok "jet1tb $1 = $2" || fail "jet1tb $1 = $2, expect $3"; }
  chk cpus "$NCPU" 128
  chk sockets "$SOCK" 2
  case "$MODEL" in *EPYC-Milan*|*"EPYC 7"*3*) ok "jet1tb cpu $MODEL" ;;
    *) warn "jet1tb cpu '$MODEL', expect AMD EPYC-Milan" ;; esac
  [ "$MEM" -ge 940 ] && [ "$MEM" -le 980 ] && ok "jet1tb memory ${MEM} GiB" \
    || fail "jet1tb memory ${MEM} GiB, expect about 961"
  chk swap_GiB "$SWP" 0
  chk swappiness "$(rd /proc/sys/vm/swappiness)" 60
  chk zone_reclaim_mode "$(rd /proc/sys/vm/zone_reclaim_mode)" 0
  chk overcommit_memory "$(rd /proc/sys/vm/overcommit_memory)" 0
  info "jet1tb August: 8 numa nodes, kernel 6.17 (this host: $NNODE, $(uname -r))"
fi

echo "== FAIL count $NF"
exit "$NF"
