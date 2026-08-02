# ---------------------------------------------------------------------
# gen_scan.py -- plant a DENSE scan target for the dlp_hard_set sigs.
#
# Author: Claude Code
# Note:   All code generated under the instructions of the paper
#         author, inspected block-by-block.
#
# WHY PLANTED. dlp_hard's Enron corpus yields aggr_needs_subsigs == 0
# on scan_hard.dat: the SITs barely fire, so the cell proves only that
# the aggressive arm still passes -- it CANNOT compare discharge work.
# This is the clam_hard_set/gen_scan.py design applied to the DLP SITs.
#
# LAYOUT. Every fwd SIT here has the shape  KEYWORD .{0,300} DIGITS .
# We emit
#
#     [ KEYWORD of every fwd SIT, separated by digit-free filler ] x R
#
# so that:
#   - every keyword is PRESENT, so each is a live location the SDE
#     tier must discharge (this is what drives aggr_needs_subsigs);
#   - the file contains NO DIGIT ANYWHERE, so the trailing [0-9]{3}
#     group can never complete -> no fwd chain matches, and the bwd
#     arms (whose FIRST leg is that same digit group) never even
#     start. The file therefore stays a legitimate non-match.
#
# R is the density knob. The digit check below is exhaustive, so a
# violation is reported rather than silently changing the verdict.
#
# usage (from repo root):
#   python3 data/debug/dlp_hard_set/config/gen_scan.py [R] [outfile]
# ---------------------------------------------------------------------

import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", "..", "..", ".."))

MAIN = os.path.join(HERE, "main.dat")
# filler carries no digits and no letters, so it cannot extend a
# keyword into a longer token nor supply a digit group.
FILLER = " ... --- ... "


def unescape(lit):
    """Decode the \\xNN escapes ClamAV ldb regexes use."""
    return re.sub(r"\\x([0-9a-fA-F]{2})",
                  lambda m: chr(int(m.group(1), 16)), lit)


def fwd_keywords(path):
    """Leading literal of every .fwd SIT, i.e. the part before .{n,m}."""
    kws = []
    with open(path, "r", errors="replace") as fh:
        for line in fh:
            name = line.split(";", 1)[0]
            if ".fwd" not in name:
                continue
            body = line.rstrip("\n").rsplit(";", 1)[-1]
            if not body.startswith("/"):
                continue
            body = body[1:]
            cut = body.find(".{")
            if cut <= 0:
                continue
            kw = unescape(body[:cut])
            # a keyword carrying a regex metachar is not a plain
            # literal -- skip rather than plant something wrong.
            if re.search(r"[\[\]\(\)\{\}\|\+\*\?\\]", kw):
                continue
            if kw:
                kws.append(kw)
    return kws


def main():
    r = int(sys.argv[1]) if len(sys.argv) > 1 else 40
    out = sys.argv[2] if len(sys.argv) > 2 else \
        os.path.join(HERE, "scan_dense.txt")

    kws = fwd_keywords(MAIN)
    if not kws:
        sys.exit("no fwd keywords parsed from %s" % MAIN)
    uniq = sorted(set(kws))

    body = []
    for _ in range(r):
        for kw in uniq:
            body.append(kw)
            body.append(FILLER)
    text = "".join(body)

    # EXHAUSTIVE CHECK: a single digit anywhere could let a [0-9]{3}
    # group complete and turn this into a real match.
    bad = [i for i, ch in enumerate(text) if ch.isdigit()]
    if bad:
        sys.exit("planted text carries %d digit(s), first at %d"
                 % (len(bad), bad[0]))

    with open(out, "w") as fh:
        fh.write(text)

    listing = os.path.join(HERE, "scan_dense.dat")
    rel = os.path.relpath(out, ROOT)
    with open(listing, "w") as fh:
        fh.write(rel + "\n")

    print("keywords: %d unique (of %d fwd sigs)" % (len(uniq), len(kws)))
    print("R=%d -> %s (%d bytes)" % (r, out, len(text)))
    print("listing: %s -> %s" % (listing, rel))


if __name__ == "__main__":
    main()
