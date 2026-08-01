# ---------------------------------------------------------------------
# gen_scan.py -- plant a DENSE scan target for the clam_hard_set sigs.
#
# Author: Claude Code
# Note:   All code generated under the instructions of the paper
#         author, inspected block-by-block.
#
# WHY PLANTED. The signatures are real ClamAV malware patterns, so a
# benign binary barely matches them: scanning merged_188 gives a median
# of 247 candidate rows == the subsig count, i.e. almost no live
# locations. That measures store SIZE, not discharge DENSITY. Same
# reason data/debug/neo_hard_set plants its scan.bin; this is that
# design driven by the paper's own signatures.
#
# LAYOUT. Every subsig here has the shape  L1 {a-b} L2 [...] . We emit
#
#     [ all NON-L1 literals, once ] [ L1 of every subsig ] x R
#
# so that:
#   - every literal of every sig is PRESENT, hence the CP tier cannot
#     discharge on an absent critical pattern and the SDE tier actually
#     runs (planting L1 alone left CP to discharge everything, which is
#     why the first attempt measured FEWER rows, not more);
#   - no L2 ever follows its L1 within the gap window, so no chain
#     completes, every sig still discharges, and the file stays a
#     legitimate non-match. This is the neo_hard "OP appears only
#     before the runs" trick.
#
# R is the density knob: step 1 of every subsig carries R live
# locations. The check below is exhaustive over real offsets, so a
# violation is reported rather than silently changing the verdict.
#
# usage (from repo root):
#   python3 data/debug/clam_hard_set/config/gen_scan.py [R] [outfile]
# ---------------------------------------------------------------------

import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", "..", "..", ".."))

GAP = re.compile(r"\{(\d*)-(\d*)\}|\{(\d+)\}|(\?\?+)")
OFF = re.compile(r"^(EP\+\d+|\*|\d+):")
HEX = re.compile(r"^[0-9a-fA-F]+$")
FILL = b"\x90\x90\x90\x90"


def blocks(field):
    """Split a subsig into (literals, gap bounds between them)."""
    f = OFF.sub("", field.strip())
    lits, gaps, pos = [], [], 0
    for m in GAP.finditer(f):
        lits.append(f[pos:m.start()])
        if m.group(4):                      # ?? run: fixed nibble count
            n = len(m.group(4)) // 2
            gaps.append((n, n))
        elif m.group(3):                    # {n}
            gaps.append((int(m.group(3)), int(m.group(3))))
        else:                               # {a-b} / {-b} / {a-}
            lo = int(m.group(1)) if m.group(1) else 0
            hi = int(m.group(2)) if m.group(2) else 1 << 30
            gaps.append((lo, hi))
        pos = m.end()
    lits.append(f[pos:])
    good = [l if (len(l) >= 8 and len(l) % 2 == 0 and HEX.match(l))
            else None for l in lits]
    return good, gaps


def occurrences(blob, pat):
    out, i = [], blob.find(pat)
    while i >= 0:
        out.append(i)
        i = blob.find(pat, i + 1)
    return out


def main():
    reps = int(sys.argv[1]) if len(sys.argv) > 1 else 8
    out = (sys.argv[2] if len(sys.argv) > 2
           else os.path.join(HERE, "scan_dense.bin"))

    chains = []                             # (l1 bytes, lo, hi, l2 bytes)
    firsts, others = [], []
    for ln in open(os.path.join(HERE, "main.dat"), errors="replace"):
        if not ln.strip():
            continue
        for field in ln.rstrip("\n").split(";")[3:]:
            lits, gaps = blocks(field)
            if len(lits) < 2 or not gaps:
                continue
            l1 = lits[0]
            if l1 is None:
                continue
            firsts.append(bytes.fromhex(l1))
            for l in lits[1:]:
                if l is not None:
                    others.append(bytes.fromhex(l))
            if lits[1] is not None:
                chains.append((bytes.fromhex(l1), gaps[0][0], gaps[0][1],
                               bytes.fromhex(lits[1])))
    if not firsts:
        sys.exit("no leading literals found in main.dat")

    seen = set()
    firsts = [f for f in firsts if not (f in seen or seen.add(f))]
    seen = set()
    others = [o for o in others if not (o in seen or seen.add(o))]

    def build(pre, rep):
        b = bytearray()
        for o in pre:
            b += o + FILL
        for _ in range(reps):
            for f in rep:
                b += f + FILL
        return bytes(b)

    def violations(blob):
        """Exhaustive: no L2 may sit inside [lo,hi] bytes after an L1
        end. A hit means that chain COMPLETES and the file would stop
        being a discharge case."""
        out = []
        for l1, lo, hi, l2 in chains:
            ends = [i + len(l1) for i in occurrences(blob, l1)]
            if not ends:
                continue
            starts = occurrences(blob, l2)
            for e in ends:
                if any(lo <= s - e <= hi for s in starts):
                    out.append((l1, l2))
                    break
        return out

    # Chain-free BY CONSTRUCTION, independent of spacing: drop every
    # literal holding both roles, then all L2s live in the prefix and
    # all L1s after them, so an L2 can never FOLLOW its own L1. Spacing
    # tricks cannot achieve this on their own -- the {a-} gaps are
    # unbounded above -- and dropping offenders one at a time just
    # cascades. The dual-role literals are a few JS sigs that share
    # text between their two legs; they discharge at the CP tier
    # instead of adding density.
    # CONTAINMENT, not equality: an L2 can sit inside a longer literal,
    # so "Sub " planted in the reps block carried another sig's
    # "()\r\n" along with it.
    l2s = set(c[3] for c in chains)
    dual = set(f for f in firsts if any(t in f for t in l2s))
    firsts = [f for f in firsts if f not in dual]
    others = [o for o in others if o not in dual]

    blob = build(others, firsts)
    viol = violations(blob)
    if viol:
        sys.exit("chain would COMPLETE (%d): %s"
                 % (len(viol), [(a.hex(), b.hex()) for a, b in viol[:3]]))

    with open(out, "wb") as f:
        f.write(blob)
    manifest = os.path.join(HERE, "binexec_dense.dat")
    with open(manifest, "w") as f:
        f.write(os.path.relpath(out, ROOT) + "\n")
    print("chains checked %d ; prefix literals %d ; planted %d x %d "
          "reps ; dropped %d dual-role"
          % (len(chains), len(others), len(firsts), reps, len(dual)))
    print("wrote %s (%d bytes) and %s"
          % (os.path.relpath(out, ROOT), len(blob),
             os.path.relpath(manifest, ROOT)))


if __name__ == "__main__":
    main()
