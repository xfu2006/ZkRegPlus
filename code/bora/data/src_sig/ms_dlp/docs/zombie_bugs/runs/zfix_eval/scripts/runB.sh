#!/bin/bash
cd $HOME/tmp/same_sample_work/zfix_run
MEM=7G xargs -P 8 -L 1 $HOME/tmp/same_sample_work/zgen_fixed/scripts/job.sh < jobs_B.txt
echo BDONE >> logs/rc.txt
