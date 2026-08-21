#!/usr/bin/env python3
"""Zombie leaf progress: per-size policy counts, itemized circuit cost,
and the unit cost u that tab:zombie-data reports.  Read-only; safe on a
live run.

Two independent sources, both tolerated missing:
  1. the leaf trace  /tmp/bora/logs/zombie_{dry,full}_*/run.log
     -- phase, per-size i/total, [sched] rounds, failures;
  2. the resume cache run_zombie_<ruleset>.partial.jsonl
     -- the ITEMIZED per-policy record (r1cs, prove_ms, verify_ms,
        proof_bytes, peak_rss), appended the moment a circuit lands.

The partial is what makes an itemized view possible at all: the docs
log is only written after every size finishes.

usage: zombie_progress.py [--log F] [--full] [--top N] [--watch S]
"""

import argparse
import ast
import glob
import json
import os
import re
import sys
import time

sys.path.insert(0, os.path.join(os.path.dirname(
    os.path.abspath(__file__)), ".."))
import PAPER_DATA as P              # noqa: E402  (path set above)

KEY = "zombie"
RULESET = "regex_zombie_international"
# The resume cache, primary (/tmp, wiped by a reboot) then the durable
# docs mirror.  run_zombie.py:_append_partial writes BOTH in lockstep,
# so either is complete; /tmp is preferred only because it is the one
# the running process is definitely appending to.
PARTIAL_TMP = "/tmp/bora_zombie_run/run_zombie_%s.partial.jsonl" % RULESET
PARTIAL_DOCS = os.path.join(P.MS_DLP_DIR, "docs",
                             "run_zombie_%s.partial.jsonl" % RULESET)
# A trace untouched this long, with sizes still pending, is a suspect
# stall.  mtime, never pgrep: `pgrep -f <script>` matches ITSELF.
STALL_S = 30 * 60

# "[run] size=%d %d/%d %-52s -> %s" plus the parallel path's rss tail.
RUN_RE = re.compile(
    r"^\[run\] size=(\d+) +(\d+)/(\d+) +(\S+) +-> +(.*?)\s*$")
# "[sched] size=%d round=%d: %d pending, RAM budget %.0f GiB, max_jobs %d"
SCHED_RE = re.compile(
    r"^\[sched\] size=(\d+) round=(\d+): (\d+) pending, "
    r"RAM budget ([\d.]+) GiB, max_jobs (\d+)")
# "=== run_zombie %s (sizes %s) ==="
START_RE = re.compile(r"^=== run_zombie (\S+) \(sizes (\[.*\])\) ===")
# "[run_zombie] %s : %d results, %d ok across sizes %s"
DONE_RE = re.compile(
    r"^\[run_zombie\] (\S+) : (\d+) results, (\d+) ok across sizes")
SKIP_RE = re.compile(r"^\[run_zombie\] ruleset (\S+) absent")


def find_log(explicit):
    """Newest zombie leaf run.log, or the one given."""
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
    """Seconds as Hh MMm, the unit a multi-hour sweep is read in."""
    sec = max(0, int(sec))
    return "%dh %02dm" % (sec // 3600, (sec % 3600) // 60)


def read_trace(log):
    """Parse the leaf trace into {sizes, per-size counters, phase}."""
    st = {"ruleset": None, "sizes": [], "seen": {}, "sched": {},
          "phase": "starting", "done": None, "absent": None,
          "building": False}
    try:
        text = open(log, errors="replace").read()
    except OSError:
        return st
    for line in text.splitlines():
        m = START_RE.match(line)
        if m:
            st["ruleset"] = m.group(1)
            try:
                st["sizes"] = ast.literal_eval(m.group(2))
            except (ValueError, SyntaxError):
                st["sizes"] = []
            st["phase"] = "measuring"
            continue
        m = SKIP_RE.match(line)
        if m:
            st["absent"] = m.group(1)
            continue
        m = DONE_RE.match(line)
        if m:
            st["done"] = (int(m.group(2)), int(m.group(3)))
            st["phase"] = "done"
            continue
        m = SCHED_RE.match(line)
        if m:
            st["sched"][int(m.group(1))] = {
                "round": int(m.group(2)), "pending": int(m.group(3)),
                "budget_gib": float(m.group(4)),
                "max_jobs": int(m.group(5))}
            continue
        m = RUN_RE.match(line)
        if m:
            sz, i, tot = (int(m.group(1)), int(m.group(2)),
                          int(m.group(3)))
            tag = m.group(5)
            d = st["seen"].setdefault(
                sz, {"i": 0, "total": tot, "ok": 0, "fail": 0,
                     "cached": 0, "last": ""})
            d["i"] = max(d["i"], i)
            d["total"] = tot
            d["last"] = m.group(4)
            if "cached" in tag:
                d["cached"] += 1
            if tag.startswith("failed"):
                d["fail"] += 1
            else:
                d["ok"] += 1
            continue
        if line.startswith("[zombie] building"):
            st["building"] = True
            st["phase"] = "building circ"
        elif line.startswith("[selftest]"):
            st["phase"] = "selftest done"
        elif line.startswith("[scratch] using") and \
                st["phase"] == "starting":
            st["phase"] = "scratch setup"
    return st


def read_partial(explicit=None):
    """Itemized per-policy records from the resume cache, newest copy
    first.  Returns (rows, source_path)."""
    for p in ([explicit] if explicit else (PARTIAL_TMP, PARTIAL_DOCS)):
        if os.path.isfile(p) and os.path.getsize(p) > 0:
            rows = []
            with open(p, errors="replace") as f:
                for line in f:
                    line = line.strip()
                    if not line:
                        continue
                    try:
                        rows.append(json.loads(line))
                    except ValueError:
                        pass          # a torn last line on a live append
            return rows, p
    return [], None


def by_size(rows):
    """Group itemized rows by str_len, de-duped on (regex_name, size):
    a resumed run re-appends a record it already had."""
    out = {}
    for r in rows:
        sz = r.get("str_len")
        if sz is None:
            continue
        out.setdefault(sz, {})[r.get("regex_name")] = r
    return {sz: list(d.values()) for sz, d in out.items()}


def totals(rows):
    """The five aggregates tab:zombie-data prints, over 'ok' rows only
    -- exactly what common.zombie_totals sums."""
    ok = [r for r in rows if r.get("status") == "ok"]
    reg = sum(r.get("pat_len", 0) + r.get("kws_len", 0) for r in ok)
    return {
        "n": len(ok),
        "regex_b": reg,
        "r1cs": sum(r.get("r1cs_cons", 0) for r in ok),
        "prove_s": sum(r.get("prove_ms", 0) for r in ok) / 1000.0,
        "verify_s": sum(r.get("verify_ms", 0) for r in ok) / 1000.0,
        "proof_b": sum(r.get("proof_bytes", 0) for r in ok),
        "rss_gib": max([r.get("peak_rss") or 0 for r in ok] or [0])
                   / 2.0 ** 30,
    }


def show_sizes(st, groups, elapsed):
    """Per-size progress + the itemized block, one row per STR_LENGTH."""
    sizes = st["sizes"] or sorted(set(list(st["seen"]) + list(groups)))
    if not sizes:
        print("  (no size block reached yet)")
        return
    print("  %-6s %-11s %5s %5s %6s | %13s %9s %9s %8s %11s"
          % ("size", "done/total", "ok", "fail", "cached", "r1cs",
             "prove s", "verify s", "proof MB", "u s/B^2"))
    for sz in sizes:
        seen = st["seen"].get(sz)
        rows = groups.get(sz, [])
        t = totals(rows)
        if seen:
            prog = "%d/%d" % (seen["i"], seen["total"])
        elif rows:
            prog = "%d/?" % len(rows)
        else:
            print("  %-6d %-11s %5s %5s %6s | %13s %9s %9s %8s %11s"
                  % (sz, "PENDING", "-", "-", "-", "-", "-", "-",
                     "-", "-"))
            continue
        head = ("  %-6d %-11s %5d %5d %6d | "
                % (sz, prog, seen["ok"] if seen else t["n"],
                   seen["fail"] if seen else 0,
                   seen["cached"] if seen else 0))
        if not t["regex_b"]:
            # Trace says circuits landed but the partial has nothing for
            # this size -- print dashes, never 0: a 0 here would read as
            # a measured cost of zero.
            print(head + "%13s %9s %9s %8s %11s"
                  % ("no itemized", "-", "-", "-", "-"))
        else:
            u = t["prove_s"] / (sz * t["regex_b"])
            print(head + "%13s %9.1f %9.1f %8.2f %11.3e"
                  % ("{:,}".format(t["r1cs"]), t["prove_s"],
                     t["verify_s"], t["proof_b"] / 1e6, u))
        sc = st["sched"].get(sz)
        if sc:
            print("         sched round %d: %d pending, budget %.0f GiB,"
                  " max_jobs %d" % (sc["round"], sc["pending"],
                                     sc["budget_gib"], sc["max_jobs"]))
    tot_done = sum(d["i"] for d in st["seen"].values())
    tot_all = sum(d["total"] for d in st["seen"].values()) or 0
    if tot_all and len(sizes) > len(st["seen"]):
        # sizes not started yet still carry the same policy count
        per = max(d["total"] for d in st["seen"].values())
        tot_all = per * len(sizes)
    if tot_done and tot_all:
        rate = elapsed / tot_done
        print("  overall %d/%d circuits, %.1f s/circuit, ETA %s"
              % (tot_done, tot_all, rate,
                 hm(rate * (tot_all - tot_done))))


def show_slowest(groups, n):
    """The n costliest circuits measured so far -- the RAM/wall risks."""
    rows = [r for g in groups.values() for r in g
            if r.get("status") == "ok"]
    if not rows:
        return
    rows.sort(key=lambda r: r.get("prove_ms", 0), reverse=True)
    print("\n  slowest %d circuits (prove ms):" % min(n, len(rows)))
    print("  %-46s %6s %10s %9s %8s"
          % ("policy", "size", "r1cs", "prove ms", "rss GiB"))
    for r in rows[:n]:
        print("  %-46s %6d %10s %9d %8.1f"
              % (r.get("regex_name", "?")[:46], r.get("str_len", 0),
                 "{:,}".format(r.get("r1cs_cons", 0)),
                 r.get("prove_ms", 0),
                 (r.get("peak_rss") or 0) / 2.0 ** 30))


def show_failures(groups):
    """Every non-ok record; run_zombie is failure-tolerant, so these are
    silent in the trace's own summary line."""
    bad = [r for g in groups.values() for r in g
           if r.get("status") != "ok"]
    if not bad:
        return
    print("\n  %d NON-OK records:" % len(bad))
    for r in bad[:20]:
        print("    %-46s size=%-6d %s %s"
              % (r.get("regex_name", "?")[:46], r.get("str_len", 0),
                 r.get("status", "?"), (r.get("err") or "")[:40]))


def main():
    ap = argparse.ArgumentParser(
        description="Zombie leaf progress (read-only).")
    ap.add_argument("--log", help="explicit run.log path")
    ap.add_argument("--partial", help="explicit partial.jsonl path")
    ap.add_argument("--full", action="store_true",
                    help="also list failures")
    ap.add_argument("--top", type=int, default=8,
                    help="slowest-circuit rows (0 = off)")
    ap.add_argument("--watch", type=int, default=0, metavar="S",
                    help="re-print every S seconds")
    a = ap.parse_args()

    while True:
        log = find_log(a.log)
        now = time.time()
        t0 = started_at(log)
        age = now - os.path.getmtime(log)
        st = read_trace(log)
        rows, src = read_partial(a.partial)
        groups = by_size(rows)

        print("=" * 74)
        print("zombie  %s" % os.path.basename(os.path.dirname(log)))
        print("  log     %s  (quiet %s)" % (log, hm(age)))
        print("  partial %s" % (src or "NONE (no itemized data yet)"))
        print("  elapsed %s   phase: %s" % (hm(now - t0), st["phase"]))
        if st["absent"]:
            print("  !! ruleset %s ABSENT -- leaf will measure nothing"
                  % st["absent"])
        if st["done"]:
            print("  FINISHED: %d results, %d ok"
                  % (st["done"][0], st["done"][1]))
        elif age > STALL_S:
            print("  !! STALL SUSPECT: no trace output for %s" % hm(age))
        print()
        show_sizes(st, groups, now - t0)
        if a.top:
            show_slowest(groups, a.top)
        if a.full:
            show_failures(groups)
        rss = max([totals(g)["rss_gib"] for g in groups.values()] or [0])
        if rss:
            print("\n  peak circuit RSS seen: %.1f GiB" % rss)
        if not a.watch:
            return 0
        time.sleep(a.watch)


if __name__ == "__main__":
    sys.exit(main())
