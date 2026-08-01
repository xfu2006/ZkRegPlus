# ---------------------------------------------------------------------
# gen.py -- build the clam_hard_set config from the paper ClamAV bundle.
#
# Author: Claude Code
# Note:   All code generated under the instructions of the paper
#         author, inspected block-by-block.
#
# Reads data/paper_data/clamav/config/ STRICTLY READ-ONLY and writes a
# small SDE-dense subset here. The paper DB is 38875 sigs / 11.6 MB,
# which needs the cached AC-DFA; the subset builds fresh in seconds
# while keeping the signature shape that drives SDE cost.
#
# Selection: keep sigs carrying a BOUNDED gap ({a-b} / {-b}) or a ??
# wildcard. A bounded gap is exactly what makes an SDE step "tracked"
# (it carries live locations across chunks instead of collapsing to a
# singleton), so this is the density axis, not the size axis. Sigs with
# only unbounded {a-} gaps or plain literals discharge at the CP tier
# and never reach the circuit under study.
#
# Then rank by BOUNDED-GAP COUNT and keep the top N. Store size is a
# floor on the non-aggressive T_qm (it emits wrap rows per store group),
# so taking all 924 matches costs volume without buying density and
# CapErrs at 29766 rows. The deepest chains (top sig has 28 bounded
# gaps = a 29-step tracked chain) are what make a SINGLE subsig
# expensive to discharge, which is the axis under study.
#
# usage (from repo root):
#   python3 data/debug/clam_hard_set/config/gen.py [top_n]
# ---------------------------------------------------------------------

import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", "..", "..", ".."))
SRC = os.path.join(ROOT, "data", "paper_data", "clamav", "config")

# bounded gap {a-b} or {-b}, or a ?? nibble wildcard
KEEP = re.compile(r"\{[0-9]*-[0-9]+\}|\?\?")
GAP = re.compile(r"\{[0-9]*-[0-9]+\}")
TOP_N = 40


def read_lines(path):
    with open(path, "r", errors="replace") as f:
        return [ln.rstrip("\n") for ln in f]


def main():
    if not os.path.isdir(SRC):
        sys.exit("paper clamav bundle not found: %s" % SRC)

    top_n = int(sys.argv[1]) if len(sys.argv) > 1 else TOP_N
    cands = [ln for ln in read_lines(os.path.join(SRC, "main.dat"))
             if ln and not ln.startswith("#") and KEEP.search(ln)]
    # deepest tracked chains first; ties broken by name for determinism
    cands.sort(key=lambda ln: (-len(GAP.findall(ln)), ln.split(";", 1)[0]))
    sigs = cands[:top_n]
    names = set(ln.split(";", 1)[0] for ln in sigs)

    # tier lists: keep only the entries our subset actually contains,
    # so the CP/DFA/ISED tiering matches the paper config exactly.
    def subset(fname):
        src = os.path.join(SRC, fname)
        if not os.path.exists(src):
            return []
        return [n for n in read_lines(src) if n in names]

    out = {
        "main.dat": sigs,
        "main_dfa.dat": subset("main_dfa.dat"),
        "needs_ised.dat": subset("needs_ised.dat"),
        "needs_ised_igc.dat": subset("needs_ised_igc.dat"),
    }
    for fname, lines in out.items():
        with open(os.path.join(HERE, fname), "w") as f:
            for ln in lines:
                f.write(ln + "\n")
        print("wrote %-20s %5d lines" % (fname, len(lines)))

    gaps = len(GAP.findall("\n".join(sigs)))
    print("bounded gaps across subset: %d" % gaps)


if __name__ == "__main__":
    main()
