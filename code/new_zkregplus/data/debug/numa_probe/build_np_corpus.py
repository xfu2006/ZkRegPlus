#!/usr/bin/env python3
"""Build the tiny NUMA-probe corpus + its isolated runcfg/cache.

GOAL: a corpus small enough that numa_probe_dlp() (the full_dlp sibling)
runs the REAL discharge -> ladder -> multi-job fold path in minutes, while
still building + folding the heavy top ladder rung. The probe measures
per-step fold ms under each numactl policy; it does NOT need the 504k-file
production corpus -- only one high-NEEDS chunk (to size the heavy circuit)
plus a few short fillers so every job folds one word.

COMPOSITION (chunk = chunk_len/2 = 32 bytes; chunks(f) = ceil(bytes/32)):
  1 HARD   : shortest foldable file with NEEDS >= --hard-min (peak chunk
             hits the top rung). Heavy in NEEDS, minimal in length.
  M MEDIUM : shortest foldable files with --med-lo <= NEEDS <= --med-hi.
  E EASY   : shortest NEEDS=0 foldable files, spread across distinct
             senders (maildir owners) like the real enron distribution.
  Total chunks trimmed to <= --budget (default 100); easy is cut first,
  so the corpus may end up < hard+M+E files. num_jobs defaults to the
  selected file count -> exactly one word per job.

ISOLATION (never touches the production dlp cfg/cache):
  config_dir = data/debug/numa_probe  (own regex_pat copy, jobs/, config/)
  cache_dir  = numa_probe             (DB symlinked read-only from
               dlp_corpus_aggr; discharge/ is a fresh empty dir)
  config_out = data/debug/numa_probe/np_ladder.json

Outputs (all under data/debug/numa_probe/):
  jobs/np_corpus_list.txt, runcfg_numa_probe.json, regex_pat/*, config/
and data/cache/numa_probe/ (DB symlinks + empty discharge/).

Run from anywhere:  python3 data/debug/numa_probe/build_np_corpus.py
Stdlib only.
"""
import argparse
import json
import math
import os
import random
import shutil


HERE = os.path.dirname(os.path.abspath(__file__))            # data/debug/numa_probe
REPO = os.path.abspath(os.path.join(HERE, "..", "..", ".."))  # new_zkregplus
# Ranks ~503k files by per-file max NEEDS: "NEEDS \t foldable(1) \t path".
RANK = os.path.join(REPO,
    "data/debug/full_dlp_sample/config/file_needs_rank.tsv")
SRC_CFG = os.path.join(REPO, "data/paper_data/dlp/cfg")       # regex_pat + sig
SRC_CACHE = os.path.join(REPO, "data/cache/dlp_corpus_aggr")  # 40GB DB cache
NP_DIR = HERE                                                 # config_dir
NP_CACHE = os.path.join(REPO, "data/cache/numa_probe")        # cache_dir
CHUNK_BYTES = 32                                              # chunk_len=64 nib


def chunks_of(rel):
    try:
        return max(1, math.ceil(os.path.getsize(
            os.path.join(REPO, rel)) / float(CHUNK_BYTES)))
    except OSError:
        return None


def owner(rel):
    # .../maildir/<owner>/<folder>/<n>. -> owner, for sender spread.
    parts = rel.split("/")
    return parts[6] if len(parts) > 6 else rel


def load_foldable():
    """Return foldable files as list of (needs, path); foldable = col 2 == 1
    (passes discharge / fits the fold), matching build_scan500.py."""
    out = []
    for ln in open(RANK):
        try:
            n, ok, f = ln.rstrip("\n").split("\t", 2)
        except ValueError:
            continue
        if ok == "1":
            out.append((int(n), f))
    return out


def pick(args):
    fold = load_foldable()
    used = set()

    def shortest(cands, k):
        """k shortest distinct (by path) files; cands = [(needs, path)].
        Stat is the cost, so cap the candidate pool to the lowest-NEEDS
        (already roughly short) entries before statting."""
        sized = []
        for n, f in cands:
            if f in used:
                continue
            c = chunks_of(f)
            if c is not None:
                sized.append((c, n, f))
        sized.sort()                      # by chunks asc, then needs, path
        return sized[:k]

    # HARD: high NEEDS, then shortest. Stat only the top-NEEDS slice.
    hard_pool = sorted([(n, f) for n, f in fold if n >= args.hard_min],
                       key=lambda t: -t[0])[:400]
    hard = shortest(hard_pool, args.hard)
    for _, _, f in hard:
        used.add(f)
    # MEDIUM: mid NEEDS, shortest.
    med_pool = [(n, f) for n, f in fold
                if args.med_lo <= n <= args.med_hi]
    med = shortest(med_pool, args.medium)
    for _, _, f in med:
        used.add(f)
    # EASY: NEEDS=0, shortest, spread across distinct senders.
    easy_pool = sorted([(n, f) for n, f in fold if n == 0],
                       key=lambda t: t[1])         # stable by path
    rng = random.Random(args.seed)
    rng.shuffle(easy_pool)                         # spread before stat
    easy_sized = []
    seen_owner = set()
    for n, f in easy_pool:
        if f in used:
            continue
        o = owner(f)
        if o in seen_owner:                        # one per sender first
            continue
        c = chunks_of(f)
        if c is None:
            continue
        seen_owner.add(o)
        easy_sized.append((c, n, f))
        if len(easy_sized) >= args.easy * 4:       # enough to choose from
            break
    easy_sized.sort()                              # shortest first

    # Assemble under the chunk budget: hard + medium are kept; easy trimmed.
    chosen = list(hard) + list(med)
    total = sum(c for c, _, _ in chosen)
    for c, n, f in easy_sized:
        if len(chosen) - len(hard) - len(med) >= args.easy:
            break
        if total + c > args.budget:
            continue
        chosen.append((c, n, f))
        total += c
    return hard, med, chosen, total


def seed_cache():
    """Symlink the read-only DB cache from dlp_corpus_aggr into numa_probe,
    leaving discharge/ a fresh empty dir. build_or_load only writes on a
    cache MISS (verified), so a complete symlink set => read-only hit and
    the production cache is never written through."""
    os.makedirs(NP_CACHE, exist_ok=True)
    n_link = 0
    for name in sorted(os.listdir(SRC_CACHE)):
        if name == "discharge":
            continue
        src = os.path.join(SRC_CACHE, name)
        dst = os.path.join(NP_CACHE, name)
        if os.path.islink(dst) or os.path.exists(dst):
            os.remove(dst) if os.path.islink(dst) else None
        if not os.path.exists(dst):
            os.symlink(src, dst)
            n_link += 1
    os.makedirs(os.path.join(NP_CACHE, "discharge"), exist_ok=True)
    return n_link


def copy_regex(reset):
    src = os.path.join(SRC_CFG, "regex_pat")
    dst = os.path.join(NP_DIR, "regex_pat")
    os.makedirs(dst, exist_ok=True)
    for name in os.listdir(src):
        s = os.path.join(src, name)
        d = os.path.join(dst, name)
        if os.path.isfile(s) and (reset or not os.path.exists(d)):
            shutil.copy2(s, d)
    os.makedirs(os.path.join(NP_DIR, "config"), exist_ok=True)


def write_runcfg(num_jobs):
    rc = {
        "config_dir": os.path.relpath(NP_DIR, REPO),
        "sig_file": "regex_pat/main_data_dlp_internationl.dat",
        "cache_dir": "numa_probe",
        "fanout_cap": 100,
        "chunk_len": 64,
        "range2_bit": 25,
        "config_out": os.path.relpath(
            os.path.join(NP_DIR, "np_ladder.json"), REPO),
        "full_list": "jobs/np_corpus_list.txt",
        "num_jobs": num_jobs,
        "reset": True,
        "k_max": 4,
        "n_buckets": 2048,
        "peel_pct": 90,
    }
    path = os.path.join(NP_DIR, "runcfg_numa_probe.json")
    json.dump(rc, open(path, "w"), indent=2)
    return path, rc


def main():
    ap = argparse.ArgumentParser(
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--budget", type=int, default=100,
                    help="max total chunks across the corpus (default 100)")
    ap.add_argument("--hard", type=int, default=1)
    ap.add_argument("--medium", type=int, default=2)
    ap.add_argument("--easy", type=int, default=6)
    ap.add_argument("--hard-min", type=int, default=3000,
                    help="min NEEDS for the hard file (default 3000)")
    ap.add_argument("--med-lo", type=int, default=600)
    ap.add_argument("--med-hi", type=int, default=1500)
    ap.add_argument("--jobs", type=int, default=0,
                    help="num_jobs (0 = one word per job = file count)")
    ap.add_argument("--seed", type=int, default=42)
    ap.add_argument("--reset-regex", action="store_true",
                    help="overwrite the regex_pat copy")
    args = ap.parse_args()

    if not os.path.isfile(RANK):
        raise SystemExit("missing rank file: %s" % RANK)
    hard, med, chosen, total = pick(args)
    if not chosen:
        raise SystemExit("no files selected (check thresholds / rank file)")

    os.makedirs(os.path.join(NP_DIR, "jobs"), exist_ok=True)
    listp = os.path.join(NP_DIR, "jobs", "np_corpus_list.txt")
    with open(listp, "w") as o:                       # hard first, then rest
        for _, _, f in chosen:
            o.write(f + "\n")

    copy_regex(args.reset_regex)
    n_link = seed_cache()
    num_jobs = args.jobs or len(chosen)
    rcp, rc = write_runcfg(num_jobs)

    print("=== numa_probe corpus ===")
    print("files=%d  total_chunks=%d  (budget=%d)  num_jobs=%d"
          % (len(chosen), total, args.budget, num_jobs))
    print("-- HARD --")
    for c, n, f in hard:
        print("  chunks=%3d needs=%5d  %s" % (c, n, f))
    print("-- MEDIUM --")
    for c, n, f in med:
        print("  chunks=%3d needs=%5d  %s" % (c, n, f))
    print("-- EASY (needs=0 fillers) --")
    for c, n, f in chosen[len(hard) + len(med):]:
        print("  chunks=%3d  %s" % (c, f))
    print("\nwrote:")
    print("  list   : %s" % listp)
    print("  runcfg : %s" % rcp)
    print("  regex  : %s/regex_pat/ (copied)" % NP_DIR)
    print("  cache  : %s (%d DB symlinks + fresh discharge/)"
          % (NP_CACHE, n_link))
    print("\nrun the probe:  python3 zkregplus/src/numa_probe.py "
          "--skip-msm --skip-warm")


if __name__ == "__main__":
    main()
