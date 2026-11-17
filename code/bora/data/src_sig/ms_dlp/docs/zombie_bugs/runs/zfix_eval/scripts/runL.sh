#!/bin/bash
cd $HOME/tmp/same_sample_work/zfix_run
J=$HOME/tmp/same_sample_work/zgen_fixed/scripts/job.sh
until grep -q TIER_M_DONE logs/rc.txt; do sleep 10; done
MEM=12G xargs -P 4 -L 1 $J < jobs_retryS.txt; echo RETRY_S_DONE >> logs/rc.txt
MEM=19G xargs -P 3 -L 1 $J < jobs_L.txt; echo TIER_L_DONE >> logs/rc.txt
