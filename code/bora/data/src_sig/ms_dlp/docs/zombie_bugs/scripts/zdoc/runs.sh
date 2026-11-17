#!/bin/bash
# zdoc: real-prover runs (old / fix1 / fix12), keygen once per (variant, unit); cpus 12-15, 16 GB cap
set -u
export ZSHARP_STDLIB_PATH=$HOME/tmp/same_sample_work/zcopy/zombie/circ/third_party/ZoKrates/zokrates_stdlib/stdlib
S=${SCRATCH:?set SCRATCH to the session scratch dir, see ZOMBIE_BUGS.md}
W=$HOME/tmp/same_sample_work; BIN=$W/zcopy/zombie/circ/target/release/circ_executable
OUT=$S/zdoc/runs; RD=$S/zdoc/rundirs; E=$S/same_sample/fixture/emails/padded
mkdir -p $OUT $RD
declare -A SRC=([old]=zok [fix1]=zok_fix1 [fix12]=zok_fix12)
# job: variant unit email_path email_tag
run() {
  v=$1; u=$2; f=$3; tag=$4; uf=${u//\//__}; d=$RD/${v}_$uf
  gen=false
  if [ ! -f $d/keys/policy1000_gens ]; then
    mkdir -p $d/zkmb $d/keys; cp $W/${SRC[$v]}/$uf.zok $d/zkmb/policy1000.zok; gen=true
  fi
  log=$OUT/${v}.${uf}.${tag}.log
  ( cd $d && ZREAL_EMAIL=$f /usr/bin/time -v systemd-run --user --scope -q -p MemoryMax=16G -p MemorySwapMax=0 taskset -c 12-15 $BIN policy_1000_real $gen prover_verifier ) > $log 2>&1
  rc=$?
  r=$(grep -ao "verify result [a-z]*" $log | awk '{print $3}'); c=$(grep -ao "after reduce linearity [0-9]*" $log | awk '{print $4}')
  printf "%s\t%s\t%s\tkeygen=%s\trc=%s\tverify=%s\tcons=%s\n" $v $u $tag $gen $rc "${r:-NONE}" "${c:-}" | tee -a $OUT/summary.tsv
}
# evidence runs
for v in old fix1 fix12; do
  run $v sit-defn-new-zealand-inland-revenue-number $S/zreal/viol2/nz_near.eml nz_near
  run $v sit-defn-new-zealand-inland-revenue-number $E/1000_02.eml 1000_02
  run $v sit-defn-italy-drivers-license-number $E/1000_02.eml 1000_02
done
# headline: seed 1 draw
U=$(python3 $S/zdoc/scripts/draw.py 1 | awk '$1=="units"{$1="";print}')
M=$(python3 $S/zdoc/scripts/draw.py 1 | awk '$1=="emails"{$1="";print}')
for u in $U; do for v in old fix12; do for e in $M; do run $v $u $E/$e.eml $e; done; done; done
echo ALLDONE | tee -a $OUT/summary.tsv
