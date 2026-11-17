#!/bin/bash
cd /home/xiang/tmp/same_sample_work/zfix_run
J=/home/xiang/tmp/same_sample_work/zgen_fixed/scripts/job.sh
V3=/tmp/claude-1000/-home-xiang-Desktop-NewResearch-Projects-ZkregPlusAll-PaperDiscussion/bd99bcfb-815e-489d-aa0c-423b97de9fea/scratchpad/zfix_eval/viol3
until grep -q K2DONE logs/k2/rc.txt 2>/dev/null; do sleep 10; done
MEM=29G $J orig sit-defn-malta-drivers-license-number false $V3/malta_near.eml $V3/malta_far.eml
MEM=29G xargs -P 2 -L 1 $J < jobs_Lorig_full.txt; echo LORIGFULL_DONE >> logs/rc.txt
