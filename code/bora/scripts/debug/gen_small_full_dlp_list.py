#!/usr/bin/env python3
# Cuts the small_full_dlp corpus list: a strided sample of the full
# Enron master UNION a hard core of files known to drive the top rung.
#
# WHY THE HARD CORE.  bora_data_driver's own sampler (subset(), a
# seeded permutation) draws uniformly, so a plain 5% sample includes
# each known over-cap file with probability 0.05 -- expected 0.45 of
# 9.  Miss them and the tuner never sees a top-rung word, the ladder
# collapses to 3 tiers, and circ3 (12.3M stmt / 21.1M R1CS) -- the
# tier that sets cs1e, decider size and peak RAM -- never appears.
# The run would look cheap and measure nothing.
#
# The core is data/debug/full_dlp_sample/scan_exp.dat, the corpus of
# the CANONICAL full_dlp_sample reference run (4 rungs, hist
# [1120,334,59,7]).  It already contains 5 of the 9 worst files
# (including watson-k/e_mail_bin/379 at 115M prod fan-out) plus 8
# bass-e files; EXTRA_HARD below adds the 3 it lacks.
#
# The output is consumed by read_path_list(), which does NOT strip
# #-comments -- every line must be a real path, so provenance lives
# here and not in the list.
#
# Usage:   python3 scripts/debug/gen_small_full_dlp_list.py [PERC]
#          default PERC: 5   (stride = round(100/PERC))

import os
import sys
import subprocess

REPO = os.path.dirname(os.path.dirname(os.path.dirname(
    os.path.abspath(__file__))))
MASTER_TGZ = "data/paper_data/dlp/cfg/jobs/final_enron_list.txt.tgz"
CORE = "data/debug/full_dlp_sample/scan_exp.dat"
OUT = "data/paper_data/dlp/cfg/jobs/small_full_dlp_list.txt"

# The 3 known over-cap files scan_exp.dat lacks (prod fan-out from
# probe 64901: 107M / 93M / 74.4M).  watson-k/294's directory is
# inferred by analogy with watson-k/e_mail_bin/379, which scan_exp
# confirms; if the ladder gate reports fewer than 4 rungs, widen this
# to the other watson-k/*/294. spellings.
EXTRA_HARD = [
    "data/samples/email/src/maildir/watson-k/e_mail_bin/294.",
    "data/samples/email/src/maildir/martin-t/inbox/83.",
    "data/samples/email/src/maildir/watson-k/deleted_items/317.",
]


def read_master():
    """Master list out of the tgz, maildir entries only (the 2 others
    are .gitignore and README.md, not emails)."""
    out = subprocess.run(["tar", "-xzOf",
                          os.path.join(REPO, MASTER_TGZ)],
                         capture_output=True, check=True).stdout
    return [l.strip() for l in out.decode().splitlines()
            if "src/maildir/" in l]


def read_core():
    """The validated hard core, blank lines dropped."""
    with open(os.path.join(REPO, CORE)) as f:
        return [l.strip() for l in f if l.strip()]


def main():
    perc = float(sys.argv[1]) if len(sys.argv) > 1 else 5.0
    stride = max(1, round(100.0 / perc))
    master = read_master()
    core = read_core()

    # Stride, then union the core.  Sorted+deduped so the file is
    # stable under regeneration and diffable in git.
    sample = master[::stride]
    keep = sorted(set(sample) | set(core) | set(EXTRA_HARD))

    missing = [p for p in EXTRA_HARD if p not in set(master)]
    if missing:
        raise SystemExit("not in master (path wrong?): %s" % missing)

    dst = os.path.join(REPO, OUT)
    with open(dst, "w") as f:
        f.write("\n".join(keep) + "\n")

    n_core_new = len(set(core) - set(sample))
    print("master        : %d maildir files" % len(master))
    print("stride        : every %dth  -> %d" % (stride, len(sample)))
    print("hard core     : %d (%d not already in the stride)"
          % (len(core), n_core_new))
    print("extra hard    : %d" % len(EXTRA_HARD))
    print("WROTE %s : %d files (%.3f%% of master)"
          % (OUT, len(keep), 100.0 * len(keep) / len(master)))


if __name__ == "__main__":
    main()
