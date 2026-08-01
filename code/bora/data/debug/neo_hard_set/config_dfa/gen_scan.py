# ---------------------------------------------------------------------
# gen_scan.py -- regenerate neo_hard_set/scan.bin at a chosen density.
#
# Author: Claude Code
# Note:   All code generated under the instructions of the paper
#         author, inspected block-by-block.
#
# The README describes this file's layout but the generator itself was
# never checked in ("edit N in the scan.bin generator"). This restores
# it so N -- the density knob for the New8 P4 legacy-vs-neo ladder --
# can be swept without hand-editing bytes.
#
# LAYOUT (matches the shipped scan.bin byte for byte at N=100):
#
#     OP____   [ AB.CD.EF.GH.IJ.KL.MN__ ] x N
#
# against  sed_hard = AB{1-3}CD{1-3}EF{1-3}GH{1-3}IJ{1-3}KL{1-3}MN{1-3}OP
#
# Every gap is a FINITE range, so steps 1..7 are tracked and each run
# keeps a live location at every one of them -- N runs => ~N live
# locations carried at the deep steps, which is exactly the carried
# queue neo bounds and legacy pays for. OP appears ONLY in the prefix,
# never 1-3 bytes after an MN, so step 8 is unreachable, the chain
# never completes and the file stays a discharge (non-match) case.
#
# NOTE: the shipped README says "30 copies"; the actual shipped file is
# N=100 (6 + 22*100 = 2206 bytes). The file is authoritative.
#
# usage (from repo root):
#   python3 data/debug/neo_hard_set/config_dfa/gen_scan.py [N] [out]
# ---------------------------------------------------------------------

import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", "..", "..", ".."))

PREFIX = b"OP____"
RUN = b"AB.CD.EF.GH.IJ.KL.MN__"
DEFAULT_N = 100


def build(n):
    return PREFIX + RUN * n


def main():
    n = int(sys.argv[1]) if len(sys.argv) > 1 else DEFAULT_N
    out = sys.argv[2] if len(sys.argv) > 2 else os.path.join(HERE,
                                                             "scan.bin")
    blob = build(n)

    # self-check: the shipped file must be reproducible exactly, or the
    # layout above is wrong and every swept point would be wrong too.
    ship = os.path.join(HERE, "scan.bin")
    if os.path.exists(ship):
        have = open(ship, "rb").read()
        if have == build(DEFAULT_N):
            print("self-check OK: reproduces shipped scan.bin at N=%d"
                  % DEFAULT_N)
        else:
            print("WARNING: shipped scan.bin (%d B) is NOT build(N=%d) "
                  "(%d B) -- layout drifted, verify before sweeping"
                  % (len(have), DEFAULT_N, len(build(DEFAULT_N))))

    with open(out, "wb") as f:
        f.write(blob)
    print("wrote %s: N=%d, %d bytes, ~%d live locations per tracked step"
          % (os.path.relpath(out, ROOT), n, len(blob), n))


if __name__ == "__main__":
    main()
