#!/usr/bin/env python3
"""full_clam neo meter, 1 TB box: TWO processes, 4 jobs each.

This is the paper run and it matches legacy's own topology exactly, so
BOTH references apply -- the per-job stage budget and the wall.  RAM is
reported two ways: the per-process max (comparable to legacy's 527 /
369 GiB halves) and the SUM, which is what the box must actually hold,
since both processes are resident at once.

  python3 scripts/debug/clam_progress_1tb.py [--legacy] [--fresh]
                                             [--log PATH]
"""

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import clam_progress_common as C          # noqa: E402

# RED line for projected peak RSS, BOX-wide (both processes summed).
# The jet box is 961.1 GiB and legacy peaked at 527 + 369 = 896 GiB,
# so 900 is the practical ceiling.  Override with CLAM_RAM_GIB.
RAM_GIB = float(os.environ.get("CLAM_RAM_GIB", "900"))

TOPO = C.Topology(
	key="1tb",
	label="1 TB (production)",
	n_procs=2,
	n_jobs=8,
	ram_gib=RAM_GIB,
	b_wall_ref=True,
	ram_per_mcs=C.RAM_PER_MCS_TWO_HALF,
	note="two-half 4+4; ONE job proves (b_one_proof), and its "
	     "process carries the peak")


def main():
	print(C.run(TOPO, sys.argv[1:]))
	return 0


if __name__ == "__main__":
	sys.exit(main())
