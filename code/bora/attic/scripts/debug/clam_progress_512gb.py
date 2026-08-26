#!/usr/bin/env python3
"""full_clam neo meter, 512 GB box: ONE process carrying all 8 jobs.

This box is the SHAKEDOWN, not the paper run -- its job is to surface
problems early and predict the 1 TB run.  So the headline is the RAM
go/no-go, and the legacy WALL is deliberately not quoted: legacy never
ran 8 jobs in one process at perc 100, so only the per-JOB budget
transfers (same corpus per job, same cpus per job).

  python3 scripts/debug/clam_progress_512gb.py [--legacy] [--fresh]
                                               [--log PATH]
"""

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import clam_progress_common as C          # noqa: E402

# RED line for projected peak RSS.  The owner set 490 GB on 2026-08-18;
# taken as DECIMAL GB = 456 GiB, which leaves ~27 GiB under the box's
# measured MemAvailable of 483.2 GiB.  Override with CLAM_RAM_GIB.
RAM_GIB = float(os.environ.get("CLAM_RAM_GIB", "456"))

TOPO = C.Topology(
	key="512gb",
	label="512 GB (shakedown)",
	n_procs=1,
	n_jobs=8,
	ram_gib=RAM_GIB,
	b_wall_ref=False,
	ram_per_mcs=C.RAM_PER_MCS_ONE_PROC,
	note="1 socket -> single process; the decider is UNAVOIDABLE "
	     "here (numa 1 proves)")


def main():
	print(C.run(TOPO, sys.argv[1:]))
	return 0


if __name__ == "__main__":
	sys.exit(main())
