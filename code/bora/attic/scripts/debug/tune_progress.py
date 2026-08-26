#!/usr/bin/env python3
"""Non-aggr tuner progress meter: which round, how far, which axis
crawls. Read-only; safe to run against a live log."""

import os
import re
import sys
import time

# default live log written by the two-half launcher (a SYMLINK).
DEFAULT_LOG = "/tmp/bora/CURRENT_JOB.log"
# one line per word finished by capacity_probe_par (word_fname="probe").
RE_PERF = re.compile(r"PERF 1001: plan_nd_advice for")
# end of a FAILED round: iter index, round wall ms, the CapErr vec.
RE_ITER = re.compile(
    r"determine_config_non_aggr iter (\d+): round (\d+) ms, bumped (.*)")
# end of a SUCCESSFUL round.
RE_CONV = re.compile(
    r"determine_config_non_aggr CONVERGED @iter (\d+): steps=(\d+)")
# one ("<axis name>", <required value>) pair inside the bumped vec.
RE_PAIR = re.compile(r'\("([^"]*)",\s*(\d+)\)')
# run start stamp, from the log DIRECTORY name (clam_full_YYYYmmdd_HHMMSS).
RE_START = re.compile(r"_(\d{8})_(\d{6})")
# a log untouched this long while no round has ended = suspect stall.
STALL_S = 45 * 60


def axis_of(name):
    """Short axis key: the gadget::field head of a CapErr name."""
    head = name.split(" ")[0].split("(")[0].strip().rstrip(",:")
    return head if head else name[:40]


def elapsed_of(target):
    """Run elapsed seconds from the log dir name, else file ctime."""
    m = RE_START.search(os.path.dirname(target))
    if m:
        try:
            t = time.mktime(time.strptime(m.group(1) + m.group(2),
                                          "%Y%m%d%H%M%S"))
            return time.time() - t, "dir name"
        except ValueError:
            pass
    return time.time() - os.path.getctime(target), "file ctime"


def hm(sec):
    """Seconds as 'Hh MMm'."""
    sec = int(max(sec, 0))
    return "%dh %02dm" % (sec // 3600, (sec % 3600) // 60)


def main():
    """Parse the tuner log and print rounds, progress, bump history."""
    path = sys.argv[1] if len(sys.argv) > 1 else DEFAULT_LOG
    # words per round; measured from round 0 when possible.
    n_words_arg = int(sys.argv[2]) if len(sys.argv) > 2 else 0
    if not os.path.exists(path):
        print("NO LOG: %s" % path)
        sys.exit(2)
    target = os.path.realpath(path)
    with open(target, errors="replace") as fh:
        lines = fh.read().splitlines()

    age = time.time() - os.path.getmtime(target)
    el, el_src = elapsed_of(target)
    print("log        : %s" % target)
    print("started    : %s ago  (from %s)" % (hm(el), el_src))
    print("last write : %.0f s ago  -- %s"
          % (age, "ALIVE" if age < 120 else "QUIET"))

    # walk once: PERF tally per round, plus each round's end record.
    n_perf = 0
    rounds = []          # (iter, wall_ms, [(axis, val)], perf_at_end)
    converged = None     # (iter, steps, perf_at_end)
    for ln in lines:
        if RE_PERF.search(ln):
            n_perf += 1
            continue
        m = RE_ITER.search(ln)
        if m:
            pairs = [(axis_of(a), int(v))
                     for a, v in RE_PAIR.findall(m.group(3))]
            rounds.append((int(m.group(1)), int(m.group(2)), pairs,
                           n_perf))
            continue
        m = RE_CONV.search(ln)
        if m:
            converged = (int(m.group(1)), int(m.group(2)), n_perf)

    # words per round: the PERF count banked by the FIRST ended round.
    ends = [r[3] for r in rounds] + ([converged[2]] if converged else [])
    n_words = n_words_arg or (ends[0] if ends else 0)
    src = "measured" if (ends and not n_words_arg) else \
          ("argv" if n_words_arg else "unknown")
    print("words/round: %s (%s)" % (n_words or "?", src))
    print("PERF lines : %d" % n_perf)

    if converged:
        it, steps, _ = converged
        print("STATE      : CONVERGED @iter %d, steps=%d" % (it, steps))
    else:
        done = len(rounds)
        if n_words:
            cur = n_perf - done * n_words
            pct = 100.0 * cur / n_words
            print("STATE      : in round %d, %d/%d words (%.1f%%)"
                  % (done, cur, n_words, pct))
            # ETA from this round's own rate, not from past rounds.
            past = sum(r[1] for r in rounds) / 1000.0
            in_round = max(el - past, 1.0)
            if cur > 0:
                eta = in_round * (n_words - cur) / cur
                print("round ETA  : %s left (at this round's rate)"
                      % hm(eta))
            else:
                print("round ETA  : n/a (no word finished this round)")
        else:
            print("STATE      : in round 0, %d words done" % n_perf)
        if age > STALL_S:
            print("WARN       : no write for %s -- check the process"
                  % hm(age))

    # round walls + per-axis trajectory (the crawl detector).
    if rounds:
        print("round walls: %s"
              % ", ".join("r%d=%.1fmin" % (r[0], r[1] / 60000.0)
                          for r in rounds))
    print("bump history (axis -> required value, per round):")
    if not rounds:
        print("  (none yet -- round 0 has not ended)")
    seen = {}            # axis -> last required value
    crawl = []           # axes that moved by exactly +1
    for it, _ms, pairs, _p in rounds:
        for ax, val in pairs:
            prev = seen.get(ax)
            if prev is None:
                tag = "NEW"
            elif val - prev == 1:
                tag = "+1  <-- CRAWL"
                crawl.append(ax)
            else:
                tag = "%+d" % (val - prev)
            print("  r%-3d %-34s -> %-8d %s" % (it, ax[:34], val, tag))
            seen[ax] = val

    # verdict
    cp = [a for a in seen if a.startswith("cp::subsigs")]
    print("-" * 62)
    if converged:
        print("VERDICT    : DONE -- tuner converged")
    elif cp:
        print("VERDICT    : FAIL -- cp::subsigs bumped (%d); the exact "
              "seed under-shot. Save this log." % seen[cp[0]])
    elif crawl:
        print("VERDICT    : CRAWL on %s -- +1 per round at ~%.0f min a "
              "round. Stop and fix the seed for this axis."
              % (",".join(sorted(set(crawl))),
                 sum(r[1] for r in rounds) / 60000.0 / len(rounds)))
    elif rounds:
        print("VERDICT    : converging -- %d round(s), jumps not +1. "
              "Let it run." % len(rounds))
    else:
        print("VERDICT    : round 0 still running, no CapErr yet")


if __name__ == "__main__":
    main()
