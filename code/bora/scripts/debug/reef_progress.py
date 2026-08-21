#!/usr/bin/env python3
"""Reef leaf progress: per-category sample acceptance, net-cost stats,
and the Estimate1/Estimate2 totals tab:dna-reef-bora reports.
Read-only; safe on a live run.

Unlike the zombie leaf there is NO resume cache -- eval_reef.py deletes
each variant's metrics CSV in _cleanup(), so the ONLY live signal is the
trace itself.  Every number below therefore comes from the per-sample
line, whose real_net is exactly the total_net_time the final docs log
reports (witness generation + Nova prove + SAFA solve).

usage: reef_progress.py [--log F] [--full] [--watch S]
"""

import argparse
import ast
import glob
import math
import os
import re
import sys
import time

sys.path.insert(0, os.path.join(os.path.dirname(
    os.path.abspath(__file__)), ".."))
import PAPER_DATA as P              # noqa: E402  (path set above)

KEY = "reef"
# Bucket order as dna_reef_bora.BUCKETS declares it, so this view and
# the table generator can never disagree about row order.
BUCKETS = ["non_projectable", "proj_512k", "proj_2M", "proj_4M",
           "proj_8M", "proj_16M"]
# eval_reef.py:733-736 -- the per-variant wall cap.  Reported beside
# the ETA because a DISCARD buys a whole extra run at up to this cost.
VARIANT_TIMEOUT_S = 2000
# The non_projectable bucket runs ~1000 s a sample, so a quiet stretch
# is normal; only a very long one is a stall.  mtime, never pgrep.
STALL_S = 60 * 60

# "[%-16s acc=%d/%d try=%d disc=%d] %s  est_net=%.1fs  real_net=%.1fs
#  p_applied=%s(est %s)  timed_out=%s  chunk=%s"
SAMPLE_RE = re.compile(
    r"^\[(\S+) *acc=(\d+)/(\d+) try=(\d+) disc=(\d+)\] +(\S+) +"
    r"est_net=([\d.]+)s +real_net=(-?[\d.]+)s +"
    r"p_applied=(\S+)\(est (\S+)\) +timed_out=(\S+) +chunk=(\S+)")
DISCARD_RE = re.compile(r"^\s+DISCARD \((\d+)/(\d+)\) (\S+): (.*)$")
STOP_RE = re.compile(r"^\s*STOP: (.+)$")
WARN_RE = re.compile(
    r"^\s+WARN: (\S+) pool exhausted with only (\d+)/(\d+) accepted")
ASSESS_RE = re.compile(
    r"^assessed (\d+) variants across (\d+) categories: (\{.*\})")
WROTE_RE = re.compile(r"^wrote (\S+) and (\S+)")
SETUP_RE = re.compile(r"^setup: (.*)$")


def find_log(explicit):
    """Newest reef leaf run.log, or the one given."""
    if explicit:
        if not os.path.isfile(explicit):
            sys.exit("no such log: %s" % explicit)
        return explicit
    pats = ["%s/%s_%s_*/run.log" % (P.JOB_LOG_DIR, KEY, m)
            for m in ("dry", "full")]
    logs = [f for pat in pats for f in glob.glob(pat)]
    if not logs:
        sys.exit("no %s/%s_{dry,full}_*/run.log found -- leaf not "
                 "started?" % (P.JOB_LOG_DIR, KEY))
    return sorted(logs, key=os.path.getmtime)[-1]


def started_at(log):
    """Run start epoch from the _YYYYmmdd_HHMMSS dir suffix, else ctime."""
    base = os.path.basename(os.path.dirname(log))
    for i in range(len(base) - 15):
        chunk = base[i:i + 16]
        if chunk[0] == "_" and chunk[9] == "_":
            try:
                return time.mktime(time.strptime(chunk[1:],
                                                  "%Y%m%d_%H%M%S"))
            except ValueError:
                pass
    return os.path.getctime(log)


def hm(sec):
    """Seconds as Hh MMm, the unit a 5 h sweep is read in."""
    sec = max(0, int(sec))
    return "%dh %02dm" % (sec // 3600, (sec % 3600) // 60)


def sci(x):
    """LaTeX-free 'a.aaae+bb', matching the table's Estimate columns."""
    return "%.3e" % x if x else "0"


def parse(log):
    """Walk the trace once.

    A sample's fate is decided by the line AFTER it: eval_reef.py prints
    DISCARD or STOP immediately on rejection, and nothing on acceptance.
    """
    st = {"setup": [], "pop": {}, "assessed": None, "cats": {},
          "order": [], "stop": None, "warn": [], "wrote": None}
    try:
        lines = open(log, errors="replace").read().splitlines()
    except OSError:
        return st

    pend = None                        # sample awaiting its verdict

    def flush(verdict):
        if pend is None:
            return
        c = st["cats"].setdefault(
            pend["cat"], {"target": pend["target"], "acc": [],
                          "disc": 0, "tries": 0, "est": pend["est"],
                          "timeouts": 0, "mismatch": 0})
        c["target"] = pend["target"]
        c["tries"] = max(c["tries"], pend["try"])
        if pend["timed_out"]:
            c["timeouts"] += 1
        if pend["applied"] != pend["est_applied"]:
            c["mismatch"] += 1
        if verdict == "acc":
            c["acc"].append(pend["real"])
        else:
            c["disc"] += 1

    for line in lines:
        m = SAMPLE_RE.match(line)
        if m:
            flush("acc")               # previous one survived
            cat = m.group(1)
            if cat not in st["order"]:
                st["order"].append(cat)
            pend = {"cat": cat, "target": int(m.group(3)),
                    "try": int(m.group(4)), "name": m.group(6),
                    "est": float(m.group(7)),
                    "real": float(m.group(8)),
                    "applied": m.group(9), "est_applied": m.group(10),
                    "timed_out": m.group(11) == "True",
                    "chunk": m.group(12)}
            continue
        if DISCARD_RE.match(line):
            flush("disc")
            pend = None
            continue
        m = STOP_RE.match(line)
        if m:
            flush("disc")
            pend = None
            st["stop"] = m.group(1).strip()
            continue
        m = WARN_RE.match(line)
        if m:
            st["warn"].append((m.group(1), int(m.group(2)),
                                int(m.group(3))))
            continue
        m = ASSESS_RE.match(line)
        if m:
            st["assessed"] = int(m.group(1))
            try:
                st["pop"] = ast.literal_eval(m.group(3))
            except (ValueError, SyntaxError):
                st["pop"] = {}
            continue
        m = WROTE_RE.match(line)
        if m:
            flush("acc")
            pend = None
            st["wrote"] = m.group(1)
            continue
        m = SETUP_RE.match(line)
        if m:
            st["setup"].append(m.group(1))
    flush("acc")                       # trailing sample, still running
    return st


def stats(v):
    """(mean, population std) of a sample list; (0, 0) when empty."""
    if not v:
        return 0.0, 0.0
    mu = sum(v) / len(v)
    if len(v) == 1:
        return mu, 0.0
    var = sum((x - mu) ** 2 for x in v) / len(v)
    return mu, math.sqrt(var)


def phase_of(st):
    """Coarse phase from the markers already emitted."""
    if st["wrote"]:
        return "done (log written)"
    if st["cats"]:
        return "sweeping"
    if st["assessed"] is not None:
        return "pool built"
    if st["setup"]:
        return "commitment setup"
    return "starting"


def show(st, elapsed):
    """Per-category block + the two Estimate totals, live."""
    cats = [c for c in BUCKETS if c in st["cats"]]
    cats += [c for c in st["order"] if c not in BUCKETS]
    if not cats:
        print("  (no sample completed yet)")
        return
    print("  %-17s %7s %5s %5s %19s %9s %11s"
          % ("category", "acc/tgt", "try", "disc", "real_net mean+-sd",
             "est_net", "pop count"))
    e1 = e2 = 0.0
    means = []
    n_acc = n_tgt = 0
    for c in cats:
        d = st["cats"][c]
        mu, sd = stats(d["acc"])
        pop = st["pop"].get(c)
        n_acc += len(d["acc"])
        n_tgt += d["target"]
        if mu:
            means.append(mu)
        flag = ""
        if d["timeouts"]:
            flag += " TIMEOUT x%d" % d["timeouts"]
        if d["mismatch"]:
            flag += " PROJ-MISMATCH x%d" % d["mismatch"]
        print("  %-17s %7s %5d %5d %10.2f +- %6.2f %9.1f %11s%s"
              % (c, "%d/%d" % (len(d["acc"]), d["target"]), d["tries"],
                 d["disc"], mu, sd, d["est"],
                 "{:,}".format(pop) if pop else "?", flag))
        if pop and mu:
            e1 += pop * mu
    if st["pop"] and means:
        e2 = sum(st["pop"].get(c, 0) for c in BUCKETS) * min(means)
    print()
    if e1:
        print("  Estimate1 (sum pop*mean)   = %s s = %.2f d"
              % (sci(e1), e1 / 86400.0))
    if e2:
        print("  Estimate2 (all pop*minmean)= %s s = %.2f d"
              % (sci(e2), e2 / 86400.0))
    if e1 and len(means) < len(BUCKETS):
        print("  (PARTIAL: %d of %d buckets sampled -- both estimates "
              "grow)" % (len(means), len(BUCKETS)))
    if n_acc and n_tgt:
        # Every category shares one sample_size, so the run's true
        # target is that size x ALL buckets -- counting only the
        # categories seen so far would shrink the denominator (and the
        # ETA) every time a new bucket opens.
        per_cat = max(st["cats"][c]["target"] for c in cats)
        full_tgt = per_cat * len(BUCKETS)
        rate = elapsed / n_acc
        print("  %d/%d samples accepted (%d/%d in the buckets started),"
              " %.0f s/sample" % (n_acc, full_tgt, n_acc, n_tgt, rate))
        print("  ETA %s  -- a DISCARD costs an extra run (cap %d s each)"
              % (hm(rate * (full_tgt - n_acc)), VARIANT_TIMEOUT_S))


def show_samples(st, log):
    """Every sample line, in order -- the --full view."""
    try:
        lines = open(log, errors="replace").read().splitlines()
    except OSError:
        return
    print("\n  per-sample trace:")
    for line in lines:
        m = SAMPLE_RE.match(line)
        if m:
            print("    %-17s %-14s est=%8.1f real=%8.1f chunk=%s%s"
                  % (m.group(1), m.group(6), float(m.group(7)),
                     float(m.group(8)), m.group(12),
                     "  TIMED_OUT" if m.group(11) == "True" else ""))
        elif DISCARD_RE.match(line) or STOP_RE.match(line):
            print("   %s" % line.strip())


def main():
    ap = argparse.ArgumentParser(
        description="Reef leaf progress (read-only).")
    ap.add_argument("--log", help="explicit run.log path")
    ap.add_argument("--full", action="store_true",
                    help="also print every sample line")
    ap.add_argument("--watch", type=int, default=0, metavar="S",
                    help="re-print every S seconds")
    a = ap.parse_args()

    while True:
        log = find_log(a.log)
        now = time.time()
        t0 = started_at(log)
        age = now - os.path.getmtime(log)
        st = parse(log)

        print("=" * 78)
        print("reef  %s" % os.path.basename(os.path.dirname(log)))
        print("  log     %s  (quiet %s)" % (log, hm(age)))
        print("  elapsed %s   phase: %s" % (hm(now - t0), phase_of(st)))
        if st["assessed"]:
            print("  pool    %s variants across %d categories"
                  % ("{:,}".format(st["assessed"]), len(st["pop"])))
        for s in st["setup"][-2:]:
            print("  setup   %s" % s)
        if st["stop"]:
            print("  !! HARD STOP: %s" % st["stop"])
        for c, got, tgt in st["warn"]:
            print("  !! pool exhausted: %s only %d/%d" % (c, got, tgt))
        if st["wrote"]:
            print("  FINISHED -> %s" % st["wrote"])
        elif age > STALL_S:
            print("  !! STALL SUSPECT: no trace output for %s" % hm(age))
        print()
        show(st, now - t0)
        if a.full:
            show_samples(st, log)
        if not a.watch:
            return 0
        time.sleep(a.watch)


if __name__ == "__main__":
    sys.exit(main())
