#!/usr/bin/env python3
"""Scale-DLP sweep progress: per-round step times and the (rules, R1CS)
curve points, for BOTH sample corpora.  Read-only; safe on a live run.

The leaf runs its two corpora SEQUENTIALLY, one log each, so at any
moment one is done, one is running and the rest are pending -- this
prints all of them rather than only the one being written.

usage: scale_dlp_progress.py [--dir D] [--full]
"""

import argparse
import glob
import os
import sys
import time

sys.path.insert(0, os.path.join(os.path.dirname(
    os.path.abspath(__file__)), ".."))
import PAPER_DATA as P              # noqa: E402  (path set above)

# Leaf key -> log dir prefix; the trailing * also catches A/B arm dirs.
KEY = "scale_dlp"
RUNS = P.SCALE_DLP_RUNS             # [(corpus_idx, bundle, tag)]
COUNTS = P.SCALE_DLP_COUNTS         # {"dry": [...], "full": [...]}
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


def show_corpus(tag, path, want, total, b_full, now):
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
    return done, walls


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--dir", help="leaf log dir (default: newest)")
    ap.add_argument("--full", action="store_true",
                    help="also print every saturation gauge")
    ap.add_argument("--arm", choices=("v1", "v2"),
                    help="report an A/B arm dir instead of production")
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
    print("Scale-DLP  %s  [%s]  elapsed %s%s"
          % (os.path.basename(run_dir), mode, hm(elapsed),
             "  COMPLETE" if n_have >= n_want else ""))
    print("curve: x = rules as %% of %d, y = R1CS per step "
          "(COST GRAND TOTAL)" % total)

    per_corpus, all_done, all_walls = [], [], []
    for tag, path in corpus_logs(run_dir):
        d, w = show_corpus(tag, path, want, total, a.full, now)
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
