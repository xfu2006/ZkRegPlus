#!/bin/bash
# E: violation e-mails on fixed circuits (keys reused); viol3 also on orig circuits
J=$HOME/tmp/same_sample_work/zgen_fixed/scripts/job.sh
V2=/tmp/claude-1000/-home-xiang-Desktop-NewResearch-Projects-ZkregPlusAll-PaperDiscussion/bd99bcfb-815e-489d-aa0c-423b97de9fea/scratchpad/zreal/viol2
V3=/tmp/claude-1000/-home-xiang-Desktop-NewResearch-Projects-ZkregPlusAll-PaperDiscussion/bd99bcfb-815e-489d-aa0c-423b97de9fea/scratchpad/zfix_eval/viol3
export MEM=${MEM:-24G}
for v in fixed orig; do
 if [ $v = fixed ]; then
  $J fixed sit-defn-italy-drivers-license-number false $V2/italy_near.eml $V2/italy_far.eml
  $J fixed sit-defn-indonesia-passport-number false $V2/indo_near.eml $V2/indo_far.eml
  $J fixed sit-defn-new-zealand-inland-revenue-number false $V2/nz_near.eml
 fi
 $J $v sit-defn-malta-drivers-license-number false $V3/malta_near.eml $V3/malta_far.eml
 $J $v sit-defn-australia-drivers-license-number__comb12 false $V3/ausdl12_near.eml $V3/ausdl12_far.eml
 $J $v sit-defn-austria-passport-number false $V3/austria_near.eml $V3/austria_far.eml
done
$J fixed sit-defn-austria-passport-number false $V3/austria_early.eml $V3/austria_late.eml
$J orig sit-defn-austria-passport-number false $V3/austria_early.eml $V3/austria_late.eml
echo EDONE >> $HOME/tmp/same_sample_work/zfix_run/logs/rc.txt
