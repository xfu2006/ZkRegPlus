#!/bin/bash
cd /home/xiang/tmp/same_sample_work/zfix_run
J=/home/xiang/tmp/same_sample_work/zgen_fixed/scripts/job.sh
MEM=6G xargs -P 10 -L 1 $J < jobs_S.txt; echo TIER_S_DONE >> logs/rc.txt
MEM=12G xargs -P 5 -L 1 $J < jobs_M.txt; echo TIER_M_DONE >> logs/rc.txt
