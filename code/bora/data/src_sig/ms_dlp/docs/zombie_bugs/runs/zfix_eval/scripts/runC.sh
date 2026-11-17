#!/bin/bash
# C: serial prove+verify timing, keys reused, e-mail 1000_01, 3 repetitions, orig and fixed alternating
R=$HOME/tmp/same_sample_work/zfix_run; BIN=$HOME/tmp/same_sample_work/zcopy/zombie/circ/target/release/circ_executable
F=/tmp/claude-1000/-home-xiang-Desktop-NewResearch-Projects-ZkregPlusAll-PaperDiscussion/bd99bcfb-815e-489d-aa0c-423b97de9fea/scratchpad/same_sample/fixture/emails/padded/1000_01.eml
for u in sit-defn-canada-drivers-license-number__comb07 sit-defn-sweden-national-id sit-defn-malta-tax-identification-number__comb00 sit-defn-norway-identification-number sit-defn-thai-population-identification-code sit-defn-japan-my-number-corporate sit-defn-france-national-id-card sit-defn-lithuania-passport-number sit-defn-australia-drivers-license-number__comb15 sit-defn-sweden-passport-number; do
 for rep in 1 2 3; do for v in orig fixed; do
  cd $R/$v/$u || continue
  ZREAL_EMAIL=$F systemd-run --user --scope -q -p MemoryMax=40G -p MemorySwapMax=0 taskset -c 0-11 $BIN policy_1000_real false prover_verifier > $R/logs/C/$v.$u.rep$rep.log 2>&1
  echo "C $v $u $rep rc=$?" >> $R/logs/C/rc.txt
 done; done
done
echo CDONE >> $R/logs/C/rc.txt
