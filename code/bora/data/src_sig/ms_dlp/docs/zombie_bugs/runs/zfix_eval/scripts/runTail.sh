#!/bin/bash
cd $HOME/tmp/same_sample_work/zfix_run
J=$HOME/tmp/same_sample_work/zgen_fixed/scripts/job.sh
V3=${SCRATCH:?set SCRATCH to the session scratch dir, see ZOMBIE_BUGS.md}/zfix_eval/viol3
until grep -q K2DONE logs/k2/rc.txt 2>/dev/null; do sleep 10; done
MEM=29G $J orig sit-defn-malta-drivers-license-number false $V3/malta_near.eml $V3/malta_far.eml
MEM=29G xargs -P 2 -L 1 $J < jobs_Lorig_full.txt; echo LORIGFULL_DONE >> logs/rc.txt
