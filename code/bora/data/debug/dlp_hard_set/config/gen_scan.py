# ---------------------------------------------------------------------
# gen_scan.py -- plant a DENSE scan target for the dlp_hard_set sigs.
#
# Author: Claude Code
# Note:   All code generated under the instructions of the paper
#         author, inspected block-by-block.
#
# WHY PLANTED. dlp_hard's Enron corpus drives aggr NEEDS to 0 on both
# scan_easy.dat and scan_hard.dat (the runner says so itself), so the
# cell proves only that the aggressive arm still passes -- it CANNOT
# compare discharge work. This is clam_hard_set/gen_scan.py's design
# applied to the DLP SITs.
#
# LAYOUT. Every fwd SIT has the shape  KEYWORD .{0,300} TAIL , and the
# matching bwd SIT is  TAIL .{0,300} KEYWORD . We emit, R times:
#
#     [ TAIL exemplars ] [ >300 filler ] [ every KEYWORD ] [ >300 filler ]
#
# so that:
#   - BOTH legs are PRESENT somewhere in the file. This is the whole
#     point: a FIRST attempt planted keywords only, and measured NEEDS
#     stayed 0, because CP discharges a sig whose critical pattern is
#     ABSENT and SED then never runs. Same trap clam_hard's generator
#     documents ("planting L1 alone left CP to discharge everything").
#     With every leg present, CP cannot discharge on absence.
#   - no KEYWORD is ever within 300 chars of a DIGIT, in EITHER
#     direction, so neither the fwd nor the bwd arm can complete. The
#     file stays a legitimate non-match.
#
# R is the density knob. The separation check below is EXHAUSTIVE over
# real offsets (prefix-summed digit counts), so a violation is reported
# rather than silently changing the verdict.
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

# gap the regexes allow between the two legs; we must EXCEED it.
GAP = 300
SEP = 400
# filler carries no digit and no letter, so it can neither supply a
# digit group nor extend a keyword into a longer token.
FILLER = (" ." * (SEP // 2)) + " "

# One satisfying exemplar per distinct TAIL shape in main.dat. There
# are only five, so these are hand-instantiated rather than generated:
#   [0-9]{3}[-x20][0-9]{3}[-x20][0-9]{3}
#   [0-9]{8}[-x20]?[A-Za-z]
#   9[0-9]{2}[-x20]?(5x|6x|7x|8x|9x)[-x20]?[0-9]{4}
#   [A-Za-z][A-Za-z0-9][0-9]{7}
#   [A-Za-z]{3}[CPHFATBLJG][A-Za-z][0-9]{4}[A-Za-z0-9]
TAILS = [
    "123-456-789",
    "12345678A",
    "900-50-1234",
    "AB1234567",
    "ABCCD1234E",
]


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


def check_separation(text, kws):
    """EXHAUSTIVE: no keyword occurrence within GAP of any digit.

    Uses a prefix sum of digit counts so every real offset is checked,
    both directions, without an O(n*m) scan.
    """
    n = len(text)
    pre = [0] * (n + 1)
    for i, ch in enumerate(text):
        pre[i + 1] = pre[i] + (1 if ch.isdigit() else 0)

    bad = []
    for kw in set(kws):
        start = 0
        while True:
            i = text.find(kw, start)
            if i < 0:
                break
            lo = max(0, i - GAP)
            hi = min(n, i + len(kw) + GAP)
            if pre[hi] - pre[lo] > 0:
                bad.append((kw, i))
                if len(bad) > 5:
                    return bad
            start = i + 1
    return bad


def main():
    r = int(sys.argv[1]) if len(sys.argv) > 1 else 40
    # KEYWORD COUNT is the real size knob, not R: the aggressive
    # obligation seed grew to the SAME 10800 slots at R=3 (4.9 KB) and
    # R=40 (65 KB), because it scales with the number of DISTINCT SITs
    # whose keyword is present, not with occurrence count. Cap the
    # keyword set to get a cell that fits a given capacity.
    max_kw = int(sys.argv[2]) if len(sys.argv) > 2 else 0
    out = sys.argv[3] if len(sys.argv) > 3 else \
        os.path.join(HERE, "scan_dense.txt")

    kws = fwd_keywords(MAIN)
    if not kws:
        sys.exit("no fwd keywords parsed from %s" % MAIN)
    uniq = sorted(set(kws))
    if max_kw > 0:
        uniq = uniq[:max_kw]

    body = []
    for _ in range(r):
        body.append("  ".join(TAILS))
        body.append(FILLER)
        # keywords adjacent to each other is fine: a keyword alone
        # matches nothing, every SIT needs its tail too.
        body.append(" ".join(uniq))
        body.append(FILLER)
    text = "".join(body)

    bad = check_separation(text, uniq)
    if bad:
        sys.exit("keyword within %d of a digit: %r" % (GAP, bad[:5]))

    with open(out, "w") as fh:
        fh.write(text)

    listing = os.path.join(HERE, "scan_dense.dat")
    rel = os.path.relpath(out, ROOT)
    with open(listing, "w") as fh:
        fh.write(rel + "\n")

    print("keywords: %d unique (of %d fwd sigs), tails: %d"
          % (len(uniq), len(kws), len(TAILS)))
    print("R=%d -> %s (%d bytes)" % (r, out, len(text)))
    print("separation >%d verified exhaustively" % GAP)


if __name__ == "__main__":
    main()
