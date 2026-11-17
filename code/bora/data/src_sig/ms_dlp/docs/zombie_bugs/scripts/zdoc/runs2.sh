#!/bin/bash
# zdoc: real-prover runs (old / fix1 / fix12), keygen once per (variant, unit); cpus 12-15, 16 GB cap
set -u
export ZSHARP_STDLIB_PATH=$HOME/tmp/same_sample_work/zcopy/zombie/circ/third_party/ZoKrates/zokrates_stdlib/stdlib
S=/tmp/claude-1000/-home-xiang-Desktop-NewResearch-Projects-ZkregPlusAll-PaperDiscussion/bd99bcfb-815e-489d-aa0c-423b97de9fea/scratchpad
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
# resume after the old Czech circuit hit the 16 GB cap: Czech fix12, then Austria old and fix12
M=$(python3 $S/zdoc/scripts/draw.py 1 | awk '$1=="emails"{$1="";print}')
for e in $M; do run fix12 sit-defn-czech-drivers-license-number $E/$e.eml $e; done
for v in old fix12; do for e in $M; do run $v sit-defn-austria-social-security-number $E/$e.eml $e; done; done
echo ALLDONE | tee -a $OUT/summary.tsv
