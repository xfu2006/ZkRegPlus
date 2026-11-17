#!/bin/bash
# job2k.sh VARIANT UNIT : keygen + prove + verify with the policy_2000 arm (default witness), for constraint counts at 2,000 bytes
V=$1; U=$2; R=$HOME/tmp/same_sample_work/zfix_run; BIN=$HOME/tmp/same_sample_work/zcopy/zombie/circ/target/release/circ_executable
cd "$R/k2/$V/$U" || exit 9
/usr/bin/time -v systemd-run --user --scope -q -p MemoryMax=${MEM:-28G} -p MemorySwapMax=0 taskset -c 0-11 $BIN policy_2000 true prover_verifier > $R/logs/k2/$V.$U.log 2>&1
echo "k2 $V $U rc=$?" >> $R/logs/k2/rc.txt
