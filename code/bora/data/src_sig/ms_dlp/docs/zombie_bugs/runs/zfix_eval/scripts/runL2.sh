#!/bin/bash
cd $HOME/tmp/same_sample_work/zfix_run
J=$HOME/tmp/same_sample_work/zgen_fixed/scripts/job.sh
until grep -q TIER_L_DONE logs/rc.txt; do sleep 10; done
MEM=16G xargs -P 3 -L 1 $J < jobs_Lorig_counts.txt; echo LORIG_DONE >> logs/rc.txt
MEM=29G xargs -P 2 -L 1 $J < jobs_retryM.txt; echo RETRY_M_DONE >> logs/rc.txt
