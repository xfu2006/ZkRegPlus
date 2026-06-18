#!/usr/bin/env python3
# Build scan_500.dat = 1 forced heaviest-foldable file (NEEDS<=4000) + 499
# random foldable files (NEEDS<=4000), seed=42, from file_needs_rank.tsv.
import random, sys
RANK = "data/debug/full_dlp_sample/config/file_needs_rank.tsv"
OUT  = "data/debug/full_dlp_sample/scan_500.dat"
CUT, N_RAND, SEED = 4000, 499, 42
pool = []        # foldable, NEEDS<=CUT
for ln in open(RANK):
    n, ok, f = ln.rstrip("\n").split("\t", 2)
    if ok == "1" and int(n) <= CUT:
        pool.append((int(n), f))
if not pool:
    sys.exit("empty pool")
forced = max(pool, key=lambda t: t[0])           # heaviest foldable <=CUT
rest = [f for n, f in pool if f != forced[1]]
random.seed(SEED)
rand = random.sample(rest, N_RAND)
with open(OUT, "w") as o:
    o.write(forced[1] + "\n")
    for f in rand:
        o.write(f + "\n")
print("forced: NEEDS=%d %s" % forced)
print("pool(foldable,<=%d)=%d  wrote %d lines -> %s"
      % (CUT, len(pool), 1 + len(rand), OUT))
