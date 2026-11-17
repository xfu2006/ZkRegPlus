#!/bin/bash
cd /home/xiang/tmp/same_sample_work/zfix_run
until grep -q RETRY_M_DONE logs/rc.txt; do sleep 10; done
./runC.sh
MEM=28G xargs -P 2 -L 1 ./job2k.sh < jobs_2k.txt; echo K2DONE >> logs/k2/rc.txt
