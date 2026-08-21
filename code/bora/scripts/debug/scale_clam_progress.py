#!/usr/bin/env python3
"""Scale-ClamAV sweep progress: per-round step times and the (rules, R1CS)
curve points, for BOTH sample corpora.  Read-only; safe on a live run.

The leaf runs its two corpora SEQUENTIALLY, one log each, so at any
moment one is done, one is running and the rest are pending -- this
prints all of them rather than only the one being written.

usage: scale_clam_progress.py [--dir D] [--full] [--phases]
"""

import argparse
import glob
import math
import os
import sys
import time

sys.path.insert(0, os.path.join(os.path.dirname(
    os.path.abspath(__file__)), ".."))
import PAPER_DATA as P              # noqa: E402  (path set above)

# Leaf key -> log dir prefix; the trailing * also catches A/B arm dirs.
KEY = "scale_clam"
RUNS = P.SCALE_CLAM_RUNS             # [(corpus_idx, bundle, tag)]
COUNTS = P.SCALE_CLAM_COUNTS         # {"dry": [...], "full": [...]}
# A log untouched this long, with a round still open, is a suspect
# stall.  mtime, never pgrep: `pgrep -f <script>` matches ITSELF.
STALL_S = 20 * 60


def find_run(explicit, arm):
    """Newest leaf dir for this dataset, or the one given.

    A/B arm dirs (<key>_v1_*, <key>_v2_*) are EXCLUDED unless --arm
    asks for one: they are newer than the production sweep, so a plain
    newest-first pick silently reports the wrong run."""
    if explicit:
        return explicit
    # EXACT shapes only. "<key>_*" also matches ad-hoc JobHandle names
    # (a debug run called itself scale_clam_v2dbg and won the sort).
    stem = "%s_%s" % (KEY, arm) if arm else KEY
    pats = ["%s_%s_*" % (stem, m) for m in ("dry", "full")]
    dirs = [d for pat in pats
            for d in glob.glob("/tmp/bora/logs/" + pat)]
    if not dirs:
        sys.exit("no /tmp/bora/logs/%s_{dry,full}_* directory found"
                 % stem)
    return sorted(dirs, key=os.path.getmtime)[-1]


def mode_of(run_dir):
    """dry|full from the leaf dir name; drives the expected count list."""
    base = os.path.basename(run_dir)
    return "full" if "_full_" in base else "dry"


def started_at(run_dir):
    """Run start epoch from the _YYYYmmdd_HHMMSS suffix, else ctime."""
    base = os.path.basename(run_dir)
    for i in range(len(base) - 15):
        chunk = base[i:i + 16]
        if chunk[0] == "_" and chunk[9] == "_":
            try:
                return time.mktime(time.strptime(chunk[1:], "%Y%m%d_%H%M%S"))
            except ValueError:
                pass
    return os.path.getctime(run_dir)


def hm(sec):
    """Seconds as Hh MMm, the unit a sweep is actually read in."""
    sec = max(0, int(sec))
    return "%dh %02dm" % (sec // 3600, (sec % 3600) // 60)


def arm_suffix(run_dir):
    """'_v1'/'_v2' when this is an A/B arm dir, else '' -- the log file
    names carry the same suffix the leaf appended to each tag."""
    base = os.path.basename(run_dir)
    for a in ("_v1_", "_v2_"):
        if a in base:
            return a[:-1]
    return ""


def corpus_logs(run_dir):
    """[(tag, log_path)] for every corpus the leaf will run, present or
    not -- a corpus with no log yet is PENDING, not missing."""
    suf = arm_suffix(run_dir)
    return [("%s%s" % (tag, suf),
             os.path.join(run_dir, "%s%s.log" % (tag, suf)))
            for _, _, tag in RUNS]


def live_log():
    """Absolute path CURRENT_JOB.log points at, or None."""
    try:
        return os.path.realpath("/tmp/bora/CURRENT_JOB.log")
    except OSError:
        return None


def phase_of(r):
    """Which phase an unfinished round reached, from the markers it has
    already emitted."""
    if r["fold_ms"]:
        return "fold done"
    if r["cost"] is not None:
        return "folding"
    if r["tune_ms"]:
        return "key setup"
    if r["db_ms"]:
        return "tuning"
    return "db build"


def round_wall(r):
    """Seconds accounted for by this round's own phase timers."""
    return (r["db_ms"] + r["disch_ms"] + r["tune_ms"]
            + r["fold_ms"]) / 1000.0


def show_corpus(tag, path, want, total, b_full, b_phases,
                now):
    """One corpus block; returns (done, walls) for the ETA fit."""
    if not os.path.isfile(path):
        print("  %-18s PENDING" % tag)
        return [], []
    rounds = P.scale_rounds(path)
    age = now - os.path.getmtime(path)
    n_done = sum(1 for r in rounds.values() if r["done"])
    # The symlink is NOT cleared when a run ends, so it alone would
    # report a finished sweep as RUNNING (and then STALLED).
    live = (os.path.realpath(path) == live_log()
            and n_done < len(want))
    state = "RUNNING" if live else "done"
    print("  %-18s %-7s %d/%d rounds   last write %ds ago%s"
          % (tag, state, n_done, len(want), int(age),
             "  ** STALLED? **" if live and age > STALL_S else ""))
    done, walls = [], []
    for cnt in want:
        r = rounds.get(cnt)
        if r is None:
            print("     %-7d  pending" % cnt)
            continue
        w = round_wall(r)
        lo, hi, over = P.sat_span(r["sat"])
        sat = "-" if lo is None else "%.0f-%.0f%%%s" % (lo, hi,
                                                        "!" if over else "")
        if r["done"]:
            done.append((cnt, r["cost"]))
            walls.append((cnt, w))
        print("     %-7d  %-9s db %6.1fs disch %5.1fs tune %7.1fs "
              "fold %7.1fs | R1CS %-10s x=%5.1f%%  sat %s"
              % (cnt, "done" if r["done"] else phase_of(r),
                 r["db_ms"] / 1000.0, r["disch_ms"] / 1000.0,
                 r["tune_ms"] / 1000.0, r["fold_ms"] / 1000.0,
                 "-" if r["cost"] is None else "{:,}".format(r["cost"]),
                 100.0 * cnt / total,
                 sat))
        if b_full and r["sat"]:
            print("               gauges: %s" % r["sat"])
        if b_phases:
            show_phases(r)
    return done, walls


def show_phases(r):
    """The 69210 breakdown of one round's db_ms.  Silent on a round
    logged without ZKR_DB_PHASE, so old logs still print cleanly."""
    if not (r["cfg_ms"] or r["build_ms"] or r["steps"]):
        return
    print("               db split : cfg %6.1fs   build %7.1fs"
          "   save %6.1fs"
          % (r["cfg_ms"] / 1000.0, r["build_ms"] / 1000.0,
             r["steps"].get("save", 0.0) / 1000.0))
    steps = [(k, v) for k, v in sorted(r["steps"].items())
             if k != "save"]
    if not steps:
        return
    tot = sum(v for _, v in steps)
    print("               build_db : %s"
          % "  ".join("%s %.1fs" % (k.replace("Step ", "S"), v / 1000.0)
                      for k, v in steps))
    top = max(steps, key=lambda kv: kv[1])
    # Name the culprit rather than making the reader scan the row.
    if tot and top[1] / tot > 0.5:
        print("                          <- %s = %.0f%% of build"
              % (top[0], 100.0 * top[1] / tot))


def ratio(a, b):
    """b/a, or 0.0 when the denominator is missing (never raises)."""
    return (float(b) / float(a)) if a else 0.0


def fx(v):
    """A growth multiplier, or a dash when it could not be formed."""
    return "-" if not v else "%.2fx" % v


def project_db(seq, top):
    """Top-round db under the two candidate laws, fitted on the LAST
    pair: a power law, and a fixed multiplier per equal rule step."""
    if len(seq) < 2:
        return
    (c0, r0), (c1, r1) = seq[-2], seq[-1]
    if c1 >= top or not r0["db_ms"] or c1 <= c0:
        return
    rr, g = float(c1) / c0, ratio(r0["db_ms"], r1["db_ms"])
    if rr <= 1.0 or g <= 0.0:
        return
    p = math.log(g) / math.log(rr)
    pw = r1["db_ms"] * (float(top) / c1) ** p
    ex = r1["db_ms"] * g ** ((top - c1) / float(c1 - c0))
    print("  db @%d:  n^%.2f fit %s   |   doubling/step %s"
          % (top, p, hm(pw / 1000.0), hm(ex / 1000.0)))


def growth_block(tag, path, want):
    """Per-round multipliers and the db exponent -- the question this
    sweep exists to answer: is the DB build doubling, or polynomial?"""
    if not os.path.isfile(path):
        return
    rounds = P.scale_rounds(path)
    seq = [(c, rounds[c]) for c in want
           if c in rounds and rounds[c]["done"]]
    if len(seq) < 2:
        return
    print("\nGROWTH -- %s   (db doubling, or polynomial?)" % tag)
    print("  %-17s %7s %8s %8s | %6s %11s"
          % ("rules", "db", "fold", "round", "rules", "db exponent"))
    for (c0, r0), (c1, r1) in zip(seq, seq[1:]):
        rr = float(c1) / max(1, c0)
        g_db = ratio(r0["db_ms"], r1["db_ms"])
        g_fo = ratio(r0["fold_ms"], r1["fold_ms"])
        g_rd = ratio(round_wall(r0), round_wall(r1))
        p = (math.log(g_db) / math.log(rr)
             if rr > 1.0 and g_db > 0.0 else None)
        print("  %6d -> %-7d %6s %8s %8s | %5.2fx %11s"
              % (c0, c1, fx(g_db), fx(g_fo), fx(g_rd), rr,
                 "-" if p is None else "n^%.2f" % p))
    project_db(seq, want[-1])


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--dir", help="leaf log dir (default: newest)")
    ap.add_argument("--full", action="store_true",
                    help="also print every saturation gauge")
    ap.add_argument("--arm", choices=("v1", "v2"),
                    help="report an A/B arm dir instead of production")
    ap.add_argument("--phases", action="store_true",
                    help="per-round db split + build_db step times "
                         "(needs a sweep run with ZKR_DB_PHASE=1)")
    a = ap.parse_args()

    run_dir = find_run(a.dir, a.arm)
    mode = mode_of(run_dir)
    want = COUNTS[mode]
    total = want[-1]
    now = time.time()
    elapsed = now - started_at(run_dir)

    n_want = len(want) * len(RUNS)
    n_have = sum(sum(1 for r in P.scale_rounds(pth).values() if r["done"])
                 for _, pth in corpus_logs(run_dir))
    print("Scale-ClamAV  %s  [%s]  elapsed %s%s"
          % (os.path.basename(run_dir), mode, hm(elapsed),
             "  COMPLETE" if n_have >= n_want else ""))
    print("curve: x = rules as %% of %d, y = R1CS per step "
          "(COST GRAND TOTAL)" % total)

    per_corpus, all_done, all_walls = [], [], []
    for tag, path in corpus_logs(run_dir):
        d, w = show_corpus(tag, path, want, total, a.full,
                           a.phases, now)
        per_corpus.append((tag, d))
        all_done += d
        all_walls += w

    print("\nrounds %d/%d complete" % (len(all_done), n_want))
    if all_walls and len(all_done) < n_want:
        # Rough: round wall grows with rule count, so scale the mean
        # per-rule cost by what is left.  Labelled rough because a
        # 2-point dry fit says nothing.
        per_rule = sum(w for _, w in all_walls) / max(
            1, sum(c for c, _ in all_walls))
        seen = set()
        for tag, path in corpus_logs(run_dir):
            rounds = P.scale_rounds(path) if os.path.isfile(path) else {}
            for c in want:
                if not rounds.get(c, {}).get("done"):
                    seen.add((tag, c))
        left = sum(c for _, c in seen) * per_rule
        print("ETA ~%s remaining (ROUGH: linear in rule count, "
              "%d-round fit)" % (hm(left), len(all_walls)))
    # One curve PER CORPUS: the figure plots the two samples as
    # separate series, so a merged list hides which point is whose.
    for tag, path in corpus_logs(run_dir):
        growth_block(tag, path, want)
    for tag, pts in per_corpus:
        if not pts:
            continue
        print("\ncurve points -- %s  (x %% of %d, rules, R1CS/step)"
              % (tag, total))
        for cnt, cost in sorted(pts):
            print("  %5.1f%%  %-7d %s"
                  % (100.0 * cnt / total, cnt,
                     "-" if cost is None else "{:,}".format(cost)))


if __name__ == "__main__":
    main()
