#!/usr/bin/env python3
"""Zombie leaf progress: per-size policy counts, itemized circuit cost,
the unit cost u that tab:zombie-data reports, a BANKED per-step
timeline, and a live-vs-paper comparison.  Read-only; safe on a live
run.

Three sources, all tolerated missing:
  1. the leaf trace  /tmp/bora/logs/zombie_{dry,full}_*/run.log
     -- phase, per-size i/total, [sched] rounds, failures;
  2. the resume cache run_zombie_<ruleset>.partial.jsonl
     -- the ITEMIZED per-policy record (r1cs, prove_ms, verify_ms,
        proof_bytes, peak_rss), appended the moment a circuit lands;
  3. the PAPER reference run_zombie_<ruleset>.log -- the same file
     gen_zombie_table.py parses.  It supplies the legacy column AND the
     fixed workload the ETA is priced from.

STEP TIMING: run.log carries NO timestamps -- PAPER_DATA.spawn() writes
only the child's stdout -- so per-step wall is BANKED: each invocation
stamps markers it sees for the first time into a state file.  Its
resolution is therefore your polling interval.  prove_ms / verify_ms
are MEASURED and exact; they are never banked.

usage: zombie_progress.py [--log F] [--partial P] [--ref R] [--full]
                          [--top N] [--watch S] [--clear]
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
# Banked step timeline.  Written on EVERY run, no flag; --clear removes
# it.  Keyed by run dir so a new leaf starts a fresh timeline instead of
# inheriting the previous run's stamps.
STATE = "/tmp/bora/zombie_progress.state.json"
STATE_VERSION = 1
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

# ---- PAPER reference (run_zombie_<ruleset>.log) ----------------------
# "== STR_LENGTH = 1000 =="
REF_SIZE_RE = re.compile(r"^== STR_LENGTH = (\d+) ==")
# "date:    2026-07-02" / "logical_cores:   128" / ...
REF_KV_RE = re.compile(r"^(date|os|logical_cores|cpu_model|cpu_mhz|"
                       r"ram_total|sizes):\s+(.*?)\s*$")
# A per-policy row: name pat kws prox r1cs prove verify proof status.
# Matched positionally on 9 whitespace fields, so the header and the
# dashed rule fall out on the int() cast, not on a fragile prefix test.
REF_COLS = 9


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


def paper_raw_roots():
    """raw_data roots to search for the reference, PAPER REPO FIRST.

    The in-repo mirror normally holds a DRY sweep (4% of policies at
    L_T 700/800/1000), so preferring it would silently compare a live
    production run against dry numbers.  Order matters more than
    presence here; both are tolerated missing.
    """
    up = os.path.dirname(os.path.dirname(os.path.dirname(P.REPO)))
    return [os.path.join(up, "ZkregPlusPaper", "usenix27", "data",
                         "raw_data"),
            P.RAW_DATA_ROOT]


def find_ref(explicit):
    """Path of an on-disk paper reference log, or None -> use the
    EMBEDDED constant.  An explicit --ref that does not exist is an
    error, never a silent fall-back to the embedded copy."""
    if explicit:
        if not os.path.isfile(explicit):
            sys.exit("no such reference log: %s" % explicit)
        return explicit
    for root in paper_raw_roots():
        for srv in (P.SERVER, "gcpm1"):
            p = os.path.join(root, srv, P.ZOMBIE_LOG_NAME)
            if os.path.isfile(p):
                return p
    return None


def read_ref(path, b_explicit=False):
    """Reference from `path`, else the EMBEDDED constant.

    An on-disk log WINS -- once this box has produced its own run that
    is what the live column should be measured against -- UNLESS it is
    a DRY sweep.  `--run dry_run` overwrites the raw_data mirror, and
    a dry log prices the ETA against the wrong workload.  Only an
    explicit --ref may select one.
    """
    skipped = None
    if path:
        try:
            ref = parse_ref_text(open(path, errors="replace").read())
            if b_explicit or not ref_is_dry(ref):
                ref["path"] = path
                return ref
            skipped = path
        except OSError:
            pass
    ref = parse_ref_text(REF_EMBED)
    ref["path"] = EMBED_TAG
    ref["skipped_dry"] = skipped
    return ref


def parse_ref_text(text):
    """Parse a paper log into {meta, sizes:{L_T:[row,...]}}.

    Rows are dicts with the same keys the partial uses, so live and
    reference totals go through ONE totals() and can never diverge in
    their definition of 'regex bytes'.
    """
    ref = {"path": None, "meta": {}, "sizes": {}}
    cur = None
    for line in text.splitlines():
        m = REF_SIZE_RE.match(line)
        if m:
            cur = int(m.group(1))
            ref["sizes"][cur] = []
            continue
        m = REF_KV_RE.match(line)
        if m:
            ref["meta"][m.group(1)] = m.group(2)
            continue
        if cur is None:
            continue
        f = line.split()
        if len(f) != REF_COLS:
            continue
        try:
            ref["sizes"][cur].append({
                "regex_name": f[0], "str_len": cur,
                "pat_len": int(f[1]), "kws_len": int(f[2]),
                "prox": int(f[3]), "r1cs_cons": int(f[4]),
                "prove_ms": int(f[5]), "verify_ms": int(f[6]),
                "proof_bytes": int(f[7]), "status": f[8]})
        except ValueError:
            continue           # the header row and the dashed rule
    return ref


def ref_is_dry(ref):
    """True when the reference looks like a dry sweep, so its numbers
    must not be read as the paper's.  The dry leaf runs
    ZOMBIE_DRY_PERC% of the policies; the real one runs all 194."""
    n = max([len(v) for v in ref["sizes"].values()] or [0])
    return n and n < 100


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


def clock(epoch):
    """HH:MM:SS in box-local time."""
    return time.strftime("%H:%M:%S", time.localtime(epoch))


def load_state(run_id):
    """Banked timeline for THIS run, or a fresh one.  A run-id or
    version mismatch discards the bank rather than mixing two runs'
    stamps into one timeline."""
    try:
        st = json.load(open(STATE))
    except (OSError, ValueError):
        return {"version": STATE_VERSION, "run": run_id, "steps": {},
                "order": []}
    if st.get("version") != STATE_VERSION or st.get("run") != run_id:
        return {"version": STATE_VERSION, "run": run_id, "steps": {},
                "order": []}
    return st


def save_state(st):
    """Atomic write; a torn state file would silently lose the bank."""
    try:
        os.makedirs(os.path.dirname(STATE), exist_ok=True)
        tmp = STATE + ".tmp"
        json.dump(st, open(tmp, "w"))
        os.replace(tmp, STATE)
    except OSError:
        pass                   # a read-only /tmp must not kill the view


def bank(st, name, now):
    """Stamp `name` the first time it is ever seen.  Returns nothing;
    re-stamping is what would make the timeline lie."""
    if name not in st["steps"]:
        st["steps"][name] = now
        st["order"].append(name)


def read_trace(log):
    """Parse the leaf trace into {sizes, per-size counters, phase}."""
    st = {"ruleset": None, "sizes": [], "seen": {}, "sched": {},
          "phase": "starting", "done": None, "absent": None,
          "scratch": False, "building": False, "selftest": False}
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
            st["selftest"] = True
            st["phase"] = "selftest done"
        elif line.startswith("[scratch]") and \
                not line.startswith("[scratch] removed"):
            st["scratch"] = True
            if st["phase"] == "starting":
                st["phase"] = "scratch setup"
    return st


def bank_markers(bk, st, now):
    """Stamp every milestone the trace currently satisfies.

    Ordered coarse-to-fine so a first invocation on an already-advanced
    run lists the timeline in the order it happened, not the order the
    dict happened to iterate.
    """
    if st["scratch"]:
        bank(bk, "scratch setup", now)
    if st["building"]:
        bank(bk, "building circ", now)
    if st["selftest"]:
        bank(bk, "selftest done", now)
    for sz in sorted(set(list(st["sched"]) + list(st["seen"]))):
        bank(bk, "size=%d build" % sz, now)
        d = st["seen"].get(sz)
        if d and d["i"]:
            bank(bk, "size=%d time" % sz, now)
        if d and d["total"] and d["i"] >= d["total"]:
            bank(bk, "size=%d done" % sz, now)
    if st["done"]:
        bank(bk, "FINISHED", now)


def show_steps(bk, elapsed, now):
    """The banked timeline: when this meter FIRST saw each milestone."""
    print("-" * 74)
    print("STEPS      : first seen by this meter (resolution = your "
          "polling interval)")
    if not bk["order"]:
        print("  (nothing banked yet -- run again later to build the "
              "timeline)")
        return
    t0 = bk["steps"][bk["order"][0]]
    print("  %-22s %10s %10s %9s" % ("step", "first seen", "since t0",
                                      "delta"))
    prev = None
    for name in bk["order"]:
        t = bk["steps"][name]
        d = "-" if prev is None else hm(t - prev)
        print("  %-22s %10s %10s %9s"
              % (name, clock(t), hm(t - t0), d))
        prev = t
    if "FINISHED" not in bk["steps"]:
        print("  %-22s %10s %10s %9s"
              % ("(running)", "--", hm(now - t0), hm(now - prev)))
    print("  NOTE run.log has no timestamps, so these are OBSERVATION")
    print("       times.  prove/verify below are MEASURED and exact.")


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
                        pass      # a torn last line on a live append
            return rows, p
    return [], None


def totals(rows):
    """The five aggregates tab:zombie-data prints, over 'ok' rows only
    -- exactly what common.zombie_totals sums.  Used for BOTH the live
    partial and the paper reference, so the two columns can never
    disagree about what 'regex bytes' means."""
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


def unit(t, sz):
    """u = prove / (L_T * regex bytes), the price of one input-byte x
    one regex-byte.  Size-normalised, so it stays comparable against
    the paper even on a HALF-FINISHED size -- unlike the totals."""
    if not t["regex_b"] or not sz:
        return 0.0
    return t["prove_s"] / (sz * t["regex_b"])


ROW = "  %-6s %-11s %5s %5s %6s | %13s %9s %9s %8s %11s"


def show_sizes(st, groups, ref):
    """Per-size progress, the itemized block, and the paper column."""
    sizes = st["sizes"] or sorted(set(list(st["seen"]) + list(groups)))
    if not sizes:
        print("  (no size block reached yet)")
        return
    print(ROW % ("size", "done/total", "ok", "fail", "cached", "r1cs",
                 "prove s", "verify s", "proof MB", "u s/B^2"))
    for sz in sizes:
        seen = st["seen"].get(sz)
        rows = groups.get(sz, [])
        t = totals(rows)
        rt = totals(ref["sizes"].get(sz, []))
        if seen:
            prog = "%d/%d" % (seen["i"], seen["total"])
        elif rows:
            prog = "%d/?" % len(rows)
        else:
            print(ROW % (sz, "PENDING", "-", "-", "-", "-", "-", "-",
                         "-", "-"))
            _paper_row(rt, sz)
            continue
        head = (ROW.split("|")[0]
                % (sz, prog, seen["ok"] if seen else t["n"],
                   seen["fail"] if seen else 0,
                   seen["cached"] if seen else 0)) + "| "
        if not t["regex_b"]:
            # Trace says circuits landed but the partial has nothing for
            # this size -- print dashes, never 0: a 0 here would read as
            # a measured cost of zero.
            print(head + "%13s %9s %9s %8s %11s"
                  % ("no itemized", "-", "-", "-", "-"))
        else:
            print(head + "%13s %9.1f %9.1f %8.2f %11.3e"
                  % ("{:,}".format(t["r1cs"]), t["prove_s"],
                     t["verify_s"], t["proof_b"] / 1e6, unit(t, sz)))
        _paper_row(rt, sz)
        if rt["n"] and t["n"]:
            _ratio_row(rows, ref["sizes"].get(sz, []), sz)
        sc = st["sched"].get(sz)
        if sc:
            print("         sched round %d: %d pending, budget %.0f GiB,"
                  " max_jobs %d" % (sc["round"], sc["pending"],
                                     sc["budget_gib"], sc["max_jobs"]))


def _paper_row(rt, sz):
    """The reference totals for this L_T, or a note that it has none."""
    if not rt["n"]:
        print("    %-51s %13s" % ("paper", "no row at this L_T"))
        return
    print("    %-14s %30s %13s %9.1f %9.1f %8.2f %11.3e"
          % ("paper", "n=%d" % rt["n"], "{:,}".format(rt["r1cs"]),
             rt["prove_s"], rt["verify_s"], rt["proof_b"] / 1e6,
             unit(rt, sz)))


def match_by_name(live, ref_rows):
    """(live_totals, ref_totals) over the policies present in BOTH.

    Matching on regex_name is what makes the ratio a BOX ratio.  A
    subset run (the dry sweep takes ZOMBIE_DRY_PERC% of the policies)
    otherwise compares its own 8 policies' mean against the paper's
    194, and those means differ by policy mix, not by machine --
    circuits here span 32k to 524k constraints.
    """
    rm = {r.get("regex_name"): r for r in ref_rows}
    lm = {r.get("regex_name"): r for r in live}
    both = [n for n in lm if n in rm]
    return (totals([lm[n] for n in both]),
            totals([rm[n] for n in both]))


def _ratio_row(live, ref_rows, sz):
    """live/paper over name-matched policies -- see match_by_name."""
    t, rt = match_by_name(live, ref_rows)
    if not t["n"]:
        print("    %-51s %13s" % ("x", "no policy name in common"))
        return
    def r(k):
        return t[k] / rt[k] if rt[k] else 0.0
    print("    %-14s %30s %13.3f %9.3f %9.3f %8.3f %11.3f"
          % ("x (matched)", "n=%d" % t["n"], r("r1cs"), r("prove_s"),
             r("verify_s"), r("proof_b"),
             (unit(t, sz) / unit(rt, sz)) if unit(rt, sz) else 0.0))


def ref_price(ref, sz):
    """Reference prove+verify SECONDS PER POLICY at length sz.

    Exact when the paper log has that L_T.  Otherwise linearly
    interpolated in L_T from the nearest measured size -- the same rule
    gen_zombie_table._linear_interp applies, and the one Zombie's own
    Theta(|s|*|r|) complexity justifies.  Per POLICY, not per pass, so
    a run with a different policy count still prices correctly.
    Returns (seconds_per_policy, exact).
    """
    have = {s: totals(v) for s, v in ref["sizes"].items() if v}
    have = {s: t for s, t in have.items() if t["n"]}
    if not have:
        return 0.0, False
    if sz in have:
        t = have[sz]
        return (t["prove_s"] + t["verify_s"]) / t["n"], True
    near = min(have, key=lambda s: abs(s - sz))
    t = have[near]
    per = (t["prove_s"] + t["verify_s"]) / t["n"]
    return per * float(sz) / near, False


def ref_full_workload(ref):
    """Prove+verify seconds for one COMPLETE reference sweep -- the
    paper's own anchor (18,791.7 s = 5.22 h, which is where
    PAPER_DATA.FULL_COST's 5.2 h for this leaf comes from)."""
    return sum(totals(v)["prove_s"] + totals(v)["verify_s"]
               for v in ref["sizes"].values())


def show_prediction(st, groups, ref, elapsed):
    """ETA priced from the FIXED reference workload, not from a rate.

    A rate learned on the cheapest size is badly wrong here: the paper's
    three sizes cost 1 : 3.5 : 14.5, so extrapolating size 1000's rate
    under-predicts the run by about 3x.  Pricing each REMAINING circuit
    at its reference cost, scaled by the box ratio measured on the
    circuits already done, is right from the first circuit.
    """
    print("-" * 74)
    print("PREDICTION : priced from the reference workload, not a rate")
    sizes = st["sizes"] or sorted(set(list(st["seen"]) + list(groups)))
    if not sizes or not ref["sizes"]:
        print("  (no reference workload -- the size table above is "
              "still live)")
        return
    # How many policies THIS run does per size.  The [run] line's
    # i/total is authoritative but absent until the first circuit runs
    # (and absent entirely on a fully cached run), so fall back to what
    # the partial already holds, then to the reference's own count.
    per = max([d["total"] for d in st["seen"].values()] or [0])
    if not per:
        per = max([len(g) for g in groups.values()] or [0])
    n_ref = max([len(v) for v in ref["sizes"].values()] or [0])
    tot_ref = rem_ref = done_ref = done_live = 0.0
    approx = assumed = False
    for sz in sizes:
        ppp, exact = ref_price(ref, sz)
        if not ppp:
            continue
        approx = approx or not exact
        seen = st["seen"].get(sz)
        n_done = len(groups.get(sz, []))
        n_tot = seen["total"] if seen and seen["total"] else per
        n_tot = max(n_tot, n_done)
        if not n_tot:
            n_tot, assumed = n_ref, True
        tot_ref += ppp * n_tot
        rem_ref += ppp * max(0, n_tot - n_done)
        # Done-so-far is priced by NAME, never by count: the circuits
        # finished first are not a random sample of the cost.
        t, rf = match_by_name(groups.get(sz, []),
                              ref["sizes"].get(sz, []))
        if t["n"]:
            done_ref += rf["prove_s"] + rf["verify_s"]
            done_live += t["prove_s"] + t["verify_s"]
    if not tot_ref:
        print("  (reference has no comparable size)")
        return
    ratio = (done_live / done_ref) if done_ref else 1.0
    full = ref_full_workload(ref)
    print("  paper full sweep                 %10.1f s = %.2f h  "
          "(%d policies x %d sizes)"
          % (full, full / 3600.0, n_ref, len(ref["sizes"])))
    print("  THIS run's reference workload    %10.1f s = %.2f h%s%s"
          % (tot_ref, tot_ref / 3600.0,
             "  interp" if approx else "",
             "  count-assumed" if assumed else ""))
    if done_ref:
        print("  matched so far (by name)         %10.1f s  ->  live "
              "%.1f s   ratio %.3fx" % (done_ref, done_live, ratio))
    else:
        print("  matched so far                   %10s  (ratio "
              "assumed 1.000x)" % "none yet")
    if st["done"]:
        print("  RUN FINISHED -- no ETA.  measured %.1f s of "
              "prove+verify" % done_live)
        return
    remain = rem_ref * ratio
    print("  remaining (reference x ratio)    %10.1f s  = %s"
          % (remain, hm(remain)))
    print("  ETA %s box   total projected %.2f h"
          % (clock(time.time() + remain), (elapsed + remain) / 3600.0))
    print("  EXCLUDES the parallel BUILD phase (codegen+keygen); see "
          "STEPS for its banked cost.")


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


def show_ref_head(ref):
    """Provenance of the legacy column.  Printed even when the machine
    differs, because a box mismatch is exactly what a reader of the
    ratio column needs to know first."""
    if not ref["path"]:
        print("  ref     NONE FOUND -- no legacy column, no prediction")
        return
    m = ref["meta"]
    tag = "DRY" if ref_is_dry(ref) else "REAL"
    n = max([len(v) for v in ref["sizes"].values()] or [0])
    print("  ref     %s" % ref["path"])
    print("          %s  %s  %d policies x sizes %s"
          % (m.get("date", "?"), tag, n,
             m.get("sizes", ",".join(str(s) for s in
                                      sorted(ref["sizes"])))))
    if m.get("cpu_model"):
        print("          %s cores  %s @%s MHz  %s"
              % (m.get("logical_cores", "?"), m.get("cpu_model", "?"),
                 m.get("cpu_mhz", "?"), m.get("ram_total", "?")))
    if tag == "DRY":
        print("          !! DRY sweep -- these are NOT the paper's "
              "numbers")
    if ref.get("skipped_dry"):
        print("          ignored a DRY log (pass --ref to force it):")
        print("          %s" % ref["skipped_dry"])


# =====================================================================
# EMBEDDED PAPER REFERENCE -- 2026-07-02, host zkregplus-large
# (128 cores, AMD EPYC-Milan, 961.1 GiB), the run that produced
# tab:zombie-data.
#
# Verbatim rows from run_zombie_regex_zombie_international.log,
# stripped to the lines the parser reads and single-spaced.  It is fed
# through the SAME parser as an on-disk reference, so the two can never
# drift apart in interpretation -- test_ref_embed_matches_file proves
# they parse to identical dicts.
#
# Embedded rather than read from disk because that log is NOT in git:
# `git ls-files data/paper_data/run_data/data/raw_data/jet1tb/` lists
# only .gitkeep, so on a fresh server there is no reference at all and
# the legacy column plus the ETA would silently vanish.  A run's own
# output still WINS over this constant when it is present on disk.
# =====================================================================
EMBED_TAG = "<embedded 2026-07-02 jet1tb>"
REF_EMBED = """date:    2026-07-02
os:              Linux 6.17.0-35-generic
logical_cores:   128
cpu_model:       AMD EPYC-Milan Processor
cpu_mhz:         1996.248
ram_total:       961.1 GiB
sizes:   1000, 2000, 4000
== STR_LENGTH = 1000 ==
sit-defn-aba-routing/comb00 75 323 300 131072 1351 762 30176 ok
sit-defn-aba-routing/comb01 71 323 300 131072 1348 794 30176 ok
sit-defn-aba-routing/comb02 71 323 300 131072 1355 783 30176 ok
sit-defn-aba-routing/comb03 67 323 300 131072 1363 750 30176 ok
sit-defn-argentina-national-identity-numbers 34 191 300 65536 828 458 29816 ok
sit-defn-australia-bank-account-number 20 330 300 65536 1332 627 29816 ok
sit-defn-australia-business-number 65 161 300 65536 745 447 21296 ok
sit-defn-australia-drivers-license-number/comb00 72 1727 300 262144 5467 2572 30928 ok
sit-defn-australia-drivers-license-number/comb01 59 1727 300 262144 5327 2576 30928 ok
sit-defn-australia-drivers-license-number/comb02 59 1727 300 262144 4363 2554 30928 ok
sit-defn-australia-drivers-license-number/comb03 46 1727 300 262144 4931 2577 30928 ok
sit-defn-australia-drivers-license-number/comb04 54 1727 300 262144 4397 2555 30928 ok
sit-defn-australia-drivers-license-number/comb05 41 1727 300 262144 4402 2573 30928 ok
sit-defn-australia-drivers-license-number/comb06 41 1727 300 262144 4620 2584 30928 ok
sit-defn-australia-drivers-license-number/comb07 28 1727 300 262144 4496 2537 30928 ok
sit-defn-australia-drivers-license-number/comb08 59 1727 300 262144 4531 2524 30928 ok
sit-defn-australia-drivers-license-number/comb09 49 1727 300 262144 4548 2559 30928 ok
sit-defn-australia-drivers-license-number/comb10 49 1727 300 262144 4667 2560 30928 ok
sit-defn-australia-drivers-license-number/comb11 39 1727 300 262144 4656 2561 30928 ok
sit-defn-australia-drivers-license-number/comb12 49 1727 300 262144 4600 2520 30928 ok
sit-defn-australia-drivers-license-number/comb13 39 1727 300 262144 4803 2590 30928 ok
sit-defn-australia-drivers-license-number/comb14 39 1727 300 262144 4618 2573 30928 ok
sit-defn-australia-drivers-license-number/comb15 29 1727 300 262144 4708 2527 30928 ok
sit-defn-australia-drivers-license-number/comb16 8 1727 300 262144 4524 2522 30928 ok
sit-defn-australia-drivers-license-number/comb17 27 1727 300 262144 4574 2548 30928 ok
sit-defn-australia-drivers-license-number/comb18 19 1727 300 262144 4738 2540 30928 ok
sit-defn-australia-passport-number/comb00 17 471 300 131072 1567 830 30176 ok
sit-defn-australia-passport-number/comb01 18 471 300 131072 1568 807 30176 ok
sit-defn-australia-tax-file-number 36 260 300 65536 1099 465 29816 ok
sit-defn-austria-passport-number 21 419 300 131072 1607 899 30176 ok
sit-defn-austria-social-security-number 21 647 300 131072 2092 1057 30568 ok
sit-defn-austria-tax-identification-number 34 431 300 131072 1537 901 30176 ok
sit-defn-austria-value-added-tax 60 394 300 131072 1441 728 30176 ok
sit-defn-belgium-passport-number 19 496 300 131072 1865 978 30176 ok
sit-defn-belgium-value-added-tax-number 64 148 300 65536 864 425 21296 ok
sit-defn-brazil-cpf-number/comb00 44 105 300 65536 749 410 21296 ok
sit-defn-brazil-cpf-number/comb01 9 105 300 65536 774 362 21296 ok
sit-defn-brazil-legal-entity-number 56 308 300 65536 1413 646 29816 ok
sit-defn-bulgaria-uniform-civil-number 26 671 300 131072 2435 1312 30568 ok
sit-defn-canada-bank-account-number/comb00 20 699 300 131072 2139 970 30568 ok
sit-defn-canada-bank-account-number/comb01 9 699 300 131072 2115 960 30568 ok
sit-defn-canada-drivers-license-number/comb00 20 3441 300 524288 9387 5803 48000 ok
sit-defn-canada-drivers-license-number/comb01 10 3441 300 524288 10603 5141 48000 ok
sit-defn-canada-drivers-license-number/comb02 72 3441 300 524288 17902 5932 48000 ok
sit-defn-canada-drivers-license-number/comb03 68 3441 300 524288 11275 5414 48000 ok
sit-defn-canada-drivers-license-number/comb04 68 3441 300 524288 10243 5176 48000 ok
sit-defn-canada-drivers-license-number/comb05 64 3441 300 524288 10796 5456 48000 ok
sit-defn-canada-drivers-license-number/comb06 68 3441 300 524288 11136 5512 48000 ok
sit-defn-canada-drivers-license-number/comb07 64 3441 300 524288 10923 5429 48000 ok
sit-defn-canada-drivers-license-number/comb08 64 3441 300 524288 10928 5422 48000 ok
sit-defn-canada-drivers-license-number/comb09 60 3441 300 524288 10605 5434 48000 ok
sit-defn-canada-drivers-license-number/comb10 19 3441 300 524288 9035 5196 48000 ok
sit-defn-canada-drivers-license-number/comb11 37 3441 300 524288 10766 5436 48000 ok
sit-defn-canada-drivers-license-number/comb12 33 3441 300 524288 11480 5455 48000 ok
sit-defn-canada-drivers-license-number/comb13 58 3441 300 524288 11023 5466 48000 ok
sit-defn-canada-drivers-license-number/comb14 54 3441 300 524288 10817 5488 48000 ok
sit-defn-canada-drivers-license-number/comb15 54 3441 300 524288 10883 5498 48000 ok
sit-defn-canada-drivers-license-number/comb16 50 3441 300 524288 10964 5419 48000 ok
sit-defn-canada-passport-number 19 492 300 131072 1833 982 30568 ok
sit-defn-canada-social-insurance-number 44 578 300 131072 2055 1031 30568 ok
sit-defn-chile-identity-card-number 51 855 300 262144 2385 1265 30928 ok
sit-defn-china-resident-identity-card-number 29 93 300 32768 577 211 20936 ok
sit-defn-croatia-identity-card-number 8 692 300 131072 2312 1195 30568 ok
sit-defn-croatia-personal-identification-number 14 692 300 131072 2314 1253 30568 ok
sit-defn-cyprus-passport-number 18 316 300 131072 1373 763 30176 ok
sit-defn-czech-drivers-license-number 29 3155 300 524288 8266 4717 48000 ok
sit-defn-czech-passport-number 8 309 300 65536 1241 614 29816 ok
sit-defn-czech-personal-identity-number/comb00 25 957 300 131072 3130 1624 30568 ok
sit-defn-czech-personal-identity-number/comb01 20 957 300 131072 2967 1624 30568 ok
sit-defn-czech-personal-identity-number/comb02 21 957 300 131072 3059 1614 30568 ok
sit-defn-czech-personal-identity-number/comb03 16 957 300 131072 3041 1615 30568 ok
sit-defn-denmark-personal-identification-number 27 1779 300 262144 5260 2848 47640 ok
sit-defn-drug-enforcement-agency-number 27 106 300 65536 645 275 21296 ok
sit-defn-ecuador-unique-identification-number 39 566 300 131072 2117 1088 30568 ok
sit-defn-estonia-drivers-license-number 16 3261 300 524288 9004 4894 48000 ok
sit-defn-estonia-passport-number 16 285 300 131072 1200 584 30176 ok
sit-defn-estonia-personal-identification-code 26 705 300 131072 2505 1242 30568 ok
sit-defn-finland-drivers-license-number 31 3311 300 524288 9812 4957 48000 ok
sit-defn-finland-european-health-insurance-number 29 307 300 65536 1192 524 29816 ok
sit-defn-finland-passport-number 19 472 300 131072 1651 893 30176 ok
sit-defn-france-drivers-license-number 9 3294 300 524288 9820 4874 48000 ok
sit-defn-france-health-insurance-number 33 51 300 32768 469 171 20936 ok
sit-defn-france-national-id-card 15 227 300 131072 997 440 30176 ok
sit-defn-france-passport-number 27 433 300 131072 1625 810 30176 ok
sit-defn-france-social-security-number/comb00 21 377 300 65536 1490 738 29816 ok
sit-defn-france-social-security-number/comb01 17 377 300 65536 1435 694 29816 ok
sit-defn-france-tax-identification-number 62 367 300 131072 1464 799 30176 ok
sit-defn-germany-drivers-license-number 49 3703 300 524288 10846 5476 48000 ok
sit-defn-germany-tax-identification-number 57 524 300 131072 1861 983 30176 ok
sit-defn-germany-value-added-tax-number 59 173 300 65536 868 481 29816 ok
sit-defn-greece-passport-number 19 228 300 131072 1104 532 30176 ok
sit-defn-greece-social-security-number 21 170 300 65536 850 370 21296 ok
sit-defn-hungary-drivers-license-number 19 3183 300 524288 8445 4695 48000 ok
sit-defn-hungary-passport-number 21 285 300 131072 1234 675 30176 ok
sit-defn-hungary-personal-identification-number 26 118 300 32768 669 340 20936 ok
sit-defn-hungary-tax-identification-number 18 470 300 131072 1684 972 30176 ok
sit-defn-hungary-value-added-tax-number 24 136 300 131072 884 425 30176 ok
sit-defn-india-drivers-license-number 68 3155 300 524288 8221 4667 48000 ok
sit-defn-india-gst-number 86 106 300 131072 699 265 21656 ok
sit-defn-india-permanent-account-number 60 52 300 131072 598 195 21656 ok
sit-defn-india-voter-id-card 19 172 300 131072 1060 428 30176 ok
sit-defn-indonesia-drivers-license-number/comb00 22 1871 300 262144 5030 2831 30928 ok
sit-defn-indonesia-drivers-license-number/comb01 32 1871 300 262144 4919 2837 30928 ok
sit-defn-indonesia-identity-card-number 32 87 300 32768 588 213 20936 ok
sit-defn-indonesia-passport-number 23 417 300 131072 1607 918 30176 ok
sit-defn-ireland-drivers-license-number 19 3251 300 524288 9657 4894 48000 ok
sit-defn-ireland-personal-public-service-number/comb00 21 922 300 262144 3120 1621 30928 ok
sit-defn-ireland-personal-public-service-number/comb01 27 922 300 262144 3137 1623 30928 ok
sit-defn-israel-bank-account-number/comb00 32 85 300 32768 528 212 20936 ok
sit-defn-israel-bank-account-number/comb01 9 85 300 32768 568 213 20936 ok
sit-defn-israel-national-identification-number 8 194 300 65536 928 422 29816 ok
sit-defn-italy-drivers-license-number 63 3299 300 524288 9721 4906 48000 ok
sit-defn-italy-passport-number 22 476 300 131072 1633 912 30176 ok
sit-defn-italy-value-added-tax-number 36 85 300 65536 685 316 21296 ok
sit-defn-japan-drivers-license-number 9 212 300 65536 1071 476 21296 ok
sit-defn-japan-my-number-corporate 14 29 300 32768 325 105 20544 ok
sit-defn-japan-my-number-personal 54 22 300 32768 339 126 20544 ok
sit-defn-japan-passport-number 19 97 300 65536 644 256 21296 ok
sit-defn-japan-residence-card-number 30 103 300 65536 575 223 21296 ok
sit-defn-japan-resident-registration-number 9 199 300 32768 766 355 20936 ok
sit-defn-japan-social-insurance-number/comb00 20 112 300 32768 533 213 20936 ok
sit-defn-japan-social-insurance-number/comb01 16 112 300 32768 570 212 20936 ok
sit-defn-japan-social-insurance-number/comb02 11 112 300 32768 597 297 20936 ok
sit-defn-latvia-passport-number 22 398 300 131072 1544 859 30176 ok
sit-defn-latvia-personal-code/comb00 20 1548 300 262144 4777 2304 47640 ok
sit-defn-latvia-personal-code/comb01 16 1548 300 262144 4680 2305 47640 ok
sit-defn-lithuania-passport-number 14 353 300 131072 1450 794 30176 ok
sit-defn-lithuania-personal-code 26 710 300 131072 2226 1158 30568 ok
sit-defn-luxemburg-national-identification-number-natural-persons 17 493 300 131072 1623 894 30176 ok
sit-defn-luxemburg-national-identification-number-non-natural-persons 52 669 300 131072 2426 1308 30568 ok
sit-defn-malaysia-passport-number 16 447 300 131072 1618 869 30176 ok
sit-defn-malta-drivers-license-number 40 3155 300 524288 9413 4709 48000 ok
sit-defn-malta-tax-identification-number/comb00 16 685 300 131072 2227 1134 30568 ok
sit-defn-malta-tax-identification-number/comb01 8 685 300 131072 2192 1126 30568 ok
sit-defn-medicare-beneficiary-identifier-card 246 221 300 131072 1023 493 30176 ok
sit-defn-netherlands-citizens-service-number 36 623 300 131072 2073 991 30568 ok
sit-defn-netherlands-passport-number 14 325 300 131072 1425 760 30176 ok
sit-defn-netherlands-value-added-tax-number 58 121 300 65536 739 378 21296 ok
sit-defn-new-zealand-bank-account-number 80 137 300 65536 718 403 21296 ok
sit-defn-new-zealand-drivers-license-number 19 1769 300 262144 4790 2710 30928 ok
sit-defn-new-zealand-inland-revenue-number 48 151 300 65536 729 407 21296 ok
sit-defn-new-zealand-ministry-of-health-number 61 128 300 131072 767 411 30176 ok
sit-defn-new-zealand-social-welfare-number 34 153 300 65536 673 349 21296 ok
sit-defn-norway-identification-number 24 145 300 32768 786 328 20936 ok
sit-defn-philippines-national-identification-number 34 163 300 65536 803 455 21296 ok
sit-defn-philippines-passport-number/comb00 29 293 300 131072 1316 700 30176 ok
sit-defn-philippines-passport-number/comb01 24 293 300 131072 1267 595 30176 ok
sit-defn-philippines-unified-multi-purpose-identification-number 29 130 300 32768 694 252 20936 ok
sit-defn-poland-drivers-license-number 34 3201 300 524288 9635 4847 48000 ok
sit-defn-poland-identity-card 19 155 300 65536 712 279 29816 ok
sit-defn-poland-national-id 21 152 300 65536 790 358 21296 ok
sit-defn-poland-passport-number 19 394 300 131072 1561 828 30176 ok
sit-defn-poland-regon-number/comb00 31 343 300 65536 1371 764 29816 ok
sit-defn-poland-regon-number/comb01 8 343 300 65536 1341 747 29816 ok
sit-defn-portugal-drivers-license-number/comb00 58 3221 300 524288 9017 4805 48000 ok
sit-defn-portugal-drivers-license-number/comb01 53 3221 300 524288 9736 4696 48000 ok
sit-defn-portugal-passport-number 16 413 300 131072 1511 826 30176 ok
sit-defn-portugal-tax-identification-number 34 448 300 131072 1714 910 30176 ok
sit-defn-qatari-id-card-number 28 151 300 65536 823 415 21296 ok
sit-defn-romania-drivers-license-number 19 3355 300 524288 9848 4992 48000 ok
sit-defn-romania-passport-number 10 285 300 65536 1131 564 21296 ok
sit-defn-russia-passport-number-international 27 149 300 65536 750 397 21296 ok
sit-defn-saudi-arabia-national-id 9 81 300 32768 595 212 20936 ok
sit-defn-slovakia-drivers-license-number 19 3155 300 524288 8115 4619 48000 ok
sit-defn-slovakia-personal-number 29 767 300 131072 2659 1359 30568 ok
sit-defn-slovenia-passport-number 24 387 300 131072 1497 833 30176 ok
sit-defn-slovenia-tax-identification-number 18 423 300 131072 1678 899 30176 ok
sit-defn-slovenia-unique-master-citizen-number 29 575 300 131072 1934 898 30568 ok
sit-defn-south-africa-identification-number 30 60 300 32768 525 211 20936 ok
sit-defn-south-korea-passport-number 35 191 300 131072 943 434 21656 ok
sit-defn-south-korea-resident-registration-number 20 127 300 32768 732 299 20936 ok
sit-defn-spain-dni 27 375 300 131072 1436 725 30176 ok
sit-defn-spain-drivers-license-number 19 3465 300 524288 8784 5102 48000 ok
sit-defn-spain-social-security-number 36 124 300 65536 667 313 21296 ok
sit-defn-spain-tax-identification-number 27 545 300 131072 2233 1088 30568 ok
sit-defn-sweden-drivers-license-number 20 3293 300 524288 9679 4932 48000 ok
sit-defn-sweden-national-id 38 412 300 131072 1487 828 30176 ok
sit-defn-sweden-passport-number 8 690 300 131072 2261 1256 30568 ok
sit-defn-switzerland-ssn-ahv-number 47 448 300 131072 1683 836 30568 ok
sit-defn-taiwan-resident-certificate-number 19 224 300 131072 1003 476 30176 ok
sit-defn-thai-population-identification-code 14 55 300 32768 475 172 20936 ok
sit-defn-uae-identity-card-number 44 353 300 131072 1334 735 30176 ok
sit-defn-uk-electoral-roll-number 21 114 300 65536 776 365 29816 ok
sit-defn-uk-national-health-service-number 34 316 300 65536 1367 674 29816 ok
sit-defn-uk-national-insurance-number/comb00 27 517 300 131072 1986 961 30568 ok
sit-defn-uk-national-insurance-number/comb01 80 517 300 131072 1907 887 30568 ok
sit-defn-ukraine-passport-international 22 79 300 65536 593 221 21296 ok
sit-defn-us-bank-account-number 11 897 300 131072 2235 1236 30176 ok
sit-defn-us-drivers-license-number 32 2296 300 524288 6457 3702 31288 ok
sit-defn-us-individual-taxpayer-identification-number/comb00 76 239 300 131072 1315 684 30176 ok
sit-defn-us-individual-taxpayer-identification-number/comb01 66 239 300 131072 1407 679 30176 ok
sit-defn-us-individual-taxpayer-identification-number/comb02 66 239 300 131072 1329 741 30176 ok
sit-defn-us-individual-taxpayer-identification-number/comb03 56 239 300 131072 1352 732 30176 ok
sit-defn-us-uk-passport-number 19 344 300 131072 1281 574 30176 ok
== STR_LENGTH = 2000 ==
sit-defn-aba-routing/comb00 75 323 300 262144 4493 2687 30928 ok
sit-defn-aba-routing/comb01 71 323 300 262144 4556 2687 30928 ok
sit-defn-aba-routing/comb02 71 323 300 262144 4727 2703 30928 ok
sit-defn-aba-routing/comb03 67 323 300 262144 4633 2688 30928 ok
sit-defn-argentina-national-identity-numbers 34 191 300 131072 2579 1466 30568 ok
sit-defn-australia-bank-account-number 20 330 300 131072 5736 2396 30568 ok
sit-defn-australia-business-number 65 161 300 131072 2396 1352 30176 ok
sit-defn-australia-drivers-license-number/comb00 72 1727 300 524288 18256 9907 48000 ok
sit-defn-australia-drivers-license-number/comb01 59 1727 300 524288 15623 9913 48000 ok
sit-defn-australia-drivers-license-number/comb02 59 1727 300 524288 15549 9873 48000 ok
sit-defn-australia-drivers-license-number/comb03 46 1727 300 524288 15689 9941 48000 ok
sit-defn-australia-drivers-license-number/comb04 54 1727 300 524288 18271 9959 48000 ok
sit-defn-australia-drivers-license-number/comb05 41 1727 300 524288 19604 9879 48000 ok
sit-defn-australia-drivers-license-number/comb06 41 1727 300 524288 15606 9933 48000 ok
sit-defn-australia-drivers-license-number/comb07 28 1727 300 524288 15493 9805 48000 ok
sit-defn-australia-drivers-license-number/comb08 59 1727 300 524288 16272 10006 48000 ok
sit-defn-australia-drivers-license-number/comb09 49 1727 300 524288 16492 10088 48000 ok
sit-defn-australia-drivers-license-number/comb10 49 1727 300 524288 19083 10148 48000 ok
sit-defn-australia-drivers-license-number/comb11 39 1727 300 524288 16825 10039 48000 ok
sit-defn-australia-drivers-license-number/comb12 49 1727 300 524288 17612 10120 48000 ok
sit-defn-australia-drivers-license-number/comb13 39 1727 300 524288 16663 9781 48000 ok
sit-defn-australia-drivers-license-number/comb14 39 1727 300 524288 16714 10165 48000 ok
sit-defn-australia-drivers-license-number/comb15 29 1727 300 524288 16025 10150 48000 ok
sit-defn-australia-drivers-license-number/comb16 8 1727 300 524288 18281 10118 48000 ok
sit-defn-australia-drivers-license-number/comb17 27 1727 300 524288 16909 10183 48000 ok
sit-defn-australia-drivers-license-number/comb18 19 1727 300 524288 15763 10163 48000 ok
sit-defn-australia-passport-number/comb00 17 471 300 262144 5792 2976 30928 ok
sit-defn-australia-passport-number/comb01 18 471 300 262144 4982 2973 30928 ok
sit-defn-australia-tax-file-number 36 260 300 131072 3086 1750 30568 ok
sit-defn-austria-passport-number 21 419 300 262144 5040 3113 30928 ok
sit-defn-austria-social-security-number 21 647 300 262144 6833 3979 47640 ok
sit-defn-austria-tax-identification-number 34 431 300 262144 5077 3056 30928 ok
sit-defn-austria-value-added-tax 60 394 300 262144 4662 2692 30928 ok
sit-defn-belgium-passport-number 19 496 300 262144 6056 3567 30928 ok
sit-defn-belgium-value-added-tax-number 64 148 300 131072 2379 1339 30176 ok
sit-defn-brazil-cpf-number/comb00 44 105 300 131072 2188 1186 30176 ok
sit-defn-brazil-cpf-number/comb01 9 105 300 131072 2164 1197 30176 ok
sit-defn-brazil-legal-entity-number 56 308 300 131072 4298 2342 30568 ok
sit-defn-bulgaria-uniform-civil-number 26 671 300 262144 7763 4794 47640 ok
sit-defn-canada-bank-account-number/comb00 20 699 300 262144 6532 3721 47640 ok
sit-defn-canada-bank-account-number/comb01 9 699 300 262144 6690 3725 47640 ok
sit-defn-canada-drivers-license-number/comb00 20 3441 300 1048576 33735 21652 48752 ok
sit-defn-canada-drivers-license-number/comb01 10 3441 300 1048576 32940 20802 48752 ok
sit-defn-canada-drivers-license-number/comb02 72 3441 300 1048576 36065 20948 48752 ok
sit-defn-canada-drivers-license-number/comb03 68 3441 300 1048576 35102 20602 48752 ok
sit-defn-canada-drivers-license-number/comb04 68 3441 300 1048576 35629 21659 48752 ok
sit-defn-canada-drivers-license-number/comb05 64 3441 300 1048576 35173 20890 48752 ok
sit-defn-canada-drivers-license-number/comb06 68 3441 300 1048576 33977 20846 48752 ok
sit-defn-canada-drivers-license-number/comb07 64 3441 300 1048576 38792 21528 48752 ok
sit-defn-canada-drivers-license-number/comb08 64 3441 300 1048576 35832 20873 48752 ok
sit-defn-canada-drivers-license-number/comb09 60 3441 300 1048576 34088 20837 48752 ok
sit-defn-canada-drivers-license-number/comb10 19 3441 300 1048576 32513 20274 48752 ok
sit-defn-canada-drivers-license-number/comb11 37 3441 300 1048576 34027 20516 48752 ok
sit-defn-canada-drivers-license-number/comb12 33 3441 300 1048576 35775 20789 48752 ok
sit-defn-canada-drivers-license-number/comb13 58 3441 300 1048576 36783 21939 48752 ok
sit-defn-canada-drivers-license-number/comb14 54 3441 300 1048576 33738 20530 48752 ok
sit-defn-canada-drivers-license-number/comb15 54 3441 300 1048576 32943 20437 48752 ok
sit-defn-canada-drivers-license-number/comb16 50 3441 300 1048576 35717 20901 48752 ok
sit-defn-canada-passport-number 19 492 300 262144 6020 3406 47640 ok
sit-defn-canada-social-insurance-number 44 578 300 262144 6598 3926 47640 ok
sit-defn-chile-identity-card-number 51 855 300 524288 8891 4665 48000 ok
sit-defn-china-resident-identity-card-number 29 93 300 65536 1503 733 29816 ok
sit-defn-croatia-identity-card-number 8 692 300 262144 8323 4567 47640 ok
sit-defn-croatia-personal-identification-number 14 692 300 262144 9148 4608 47640 ok
sit-defn-cyprus-passport-number 18 316 300 262144 4360 2515 30928 ok
sit-defn-czech-drivers-license-number 29 3155 300 1048576 28630 18163 48752 ok
sit-defn-czech-passport-number 8 309 300 131072 3987 2296 30568 ok
sit-defn-czech-personal-identity-number/comb00 25 957 300 262144 10357 6346 47640 ok
sit-defn-czech-personal-identity-number/comb01 20 957 300 262144 10672 6360 47640 ok
sit-defn-czech-personal-identity-number/comb02 21 957 300 262144 10492 6359 47640 ok
sit-defn-czech-personal-identity-number/comb03 16 957 300 262144 10249 6406 47640 ok
sit-defn-denmark-personal-identification-number 27 1779 300 524288 17860 10903 48392 ok
sit-defn-drug-enforcement-agency-number 27 106 300 131072 1826 925 30176 ok
sit-defn-ecuador-unique-identification-number 39 566 300 262144 6706 4019 47640 ok
sit-defn-estonia-drivers-license-number 16 3261 300 1048576 32088 19289 48752 ok
sit-defn-estonia-passport-number 16 285 300 262144 3819 2182 30928 ok
sit-defn-estonia-personal-identification-code 26 705 300 262144 9086 4705 47640 ok
sit-defn-finland-drivers-license-number 31 3311 300 1048576 32685 19536 48752 ok
sit-defn-finland-european-health-insurance-number 29 307 300 131072 3596 2008 30568 ok
sit-defn-finland-passport-number 19 472 300 262144 5499 3243 30928 ok
sit-defn-france-drivers-license-number 9 3294 300 1048576 30860 19308 48752 ok
sit-defn-france-health-insurance-number 33 51 300 65536 1236 688 29816 ok
sit-defn-france-national-id-card 15 227 300 262144 3011 1587 30928 ok
sit-defn-france-passport-number 27 433 300 262144 5148 3116 30928 ok
sit-defn-france-social-security-number/comb00 21 377 300 131072 4334 2450 30568 ok
sit-defn-france-social-security-number/comb01 17 377 300 131072 4332 2462 30568 ok
sit-defn-france-tax-identification-number 62 367 300 262144 4556 2721 30928 ok
sit-defn-germany-drivers-license-number 49 3703 300 1048576 38746 22008 48752 ok
sit-defn-germany-tax-identification-number 57 524 300 262144 6936 3783 30928 ok
sit-defn-germany-value-added-tax-number 59 173 300 131072 2563 1394 30568 ok
sit-defn-greece-passport-number 19 228 300 262144 3303 1845 30928 ok
sit-defn-greece-social-security-number 21 170 300 131072 2440 1408 30176 ok
sit-defn-hungary-drivers-license-number 19 3183 300 1048576 32280 18734 48752 ok
sit-defn-hungary-passport-number 21 285 300 262144 3821 2176 30928 ok
sit-defn-hungary-personal-identification-number 26 118 300 65536 1969 1161 29816 ok
sit-defn-hungary-tax-identification-number 18 470 300 262144 5665 3430 30928 ok
sit-defn-hungary-value-added-tax-number 24 136 300 262144 2459 1329 30928 ok
sit-defn-india-drivers-license-number 68 3155 300 1048576 28890 18240 48752 ok
sit-defn-india-gst-number 86 106 300 262144 1820 909 30536 ok
sit-defn-india-permanent-account-number 60 52 300 262144 1412 718 30536 ok
sit-defn-india-voter-id-card 19 172 300 262144 2910 1611 30928 ok
sit-defn-indonesia-drivers-license-number/comb00 22 1871 300 524288 18422 11213 48000 ok
sit-defn-indonesia-drivers-license-number/comb01 32 1871 300 524288 18445 11323 48000 ok
sit-defn-indonesia-identity-card-number 32 87 300 65536 1555 848 29816 ok
sit-defn-indonesia-passport-number 23 417 300 262144 5136 3084 30928 ok
sit-defn-ireland-drivers-license-number 19 3251 300 1048576 29902 19386 48752 ok
sit-defn-ireland-personal-public-service-number/comb00 21 922 300 524288 10056 6302 48000 ok
sit-defn-ireland-personal-public-service-number/comb01 27 922 300 524288 10619 6323 48000 ok
sit-defn-israel-bank-account-number/comb00 32 85 300 65536 1487 860 29816 ok
sit-defn-israel-bank-account-number/comb01 9 85 300 65536 1471 860 29816 ok
sit-defn-israel-national-identification-number 8 194 300 131072 2783 1549 30568 ok
sit-defn-italy-drivers-license-number 63 3299 300 1048576 29837 18962 48752 ok
sit-defn-italy-passport-number 22 476 300 262144 5339 3124 30928 ok
sit-defn-italy-value-added-tax-number 36 85 300 131072 1914 1181 30176 ok
sit-defn-japan-drivers-license-number 9 212 300 131072 3095 1804 30176 ok
sit-defn-japan-my-number-corporate 14 29 300 65536 802 405 21296 ok
sit-defn-japan-my-number-personal 54 22 300 65536 911 409 21296 ok
sit-defn-japan-passport-number 19 97 300 131072 1733 912 30176 ok
sit-defn-japan-residence-card-number 30 103 300 131072 1583 768 30176 ok
sit-defn-japan-resident-registration-number 9 199 300 65536 2004 1091 29816 ok
sit-defn-japan-social-insurance-number/comb00 20 112 300 65536 1449 738 29816 ok
sit-defn-japan-social-insurance-number/comb01 16 112 300 65536 1466 840 29816 ok
sit-defn-japan-social-insurance-number/comb02 11 112 300 65536 1508 1006 29816 ok
sit-defn-latvia-passport-number 22 398 300 262144 5748 3004 30928 ok
sit-defn-latvia-personal-code/comb00 20 1548 300 524288 25588 8870 48392 ok
sit-defn-latvia-personal-code/comb01 16 1548 300 524288 14830 8923 48392 ok
sit-defn-lithuania-passport-number 14 353 300 262144 4419 2606 30928 ok
sit-defn-lithuania-personal-code 26 710 300 262144 8644 4406 47640 ok
sit-defn-luxemburg-national-identification-number-natural-persons 17 493 300 262144 5359 3116 30928 ok
sit-defn-luxemburg-national-identification-number-non-natural-persons 52 669 300 262144 8819 4657 47640 ok
sit-defn-malaysia-passport-number 16 447 300 262144 5410 3240 30928 ok
sit-defn-malta-drivers-license-number 40 3155 300 1048576 33362 18233 48752 ok
sit-defn-malta-tax-identification-number/comb00 16 685 300 262144 7186 4337 47640 ok
sit-defn-malta-tax-identification-number/comb01 8 685 300 262144 7408 4291 47640 ok
sit-defn-medicare-beneficiary-identifier-card 246 221 300 262144 2676 1444 30928 ok
sit-defn-netherlands-citizens-service-number 36 623 300 262144 6235 3618 47640 ok
sit-defn-netherlands-passport-number 14 325 300 262144 4195 2469 30928 ok
sit-defn-netherlands-value-added-tax-number 58 121 300 131072 1984 1056 30176 ok
sit-defn-new-zealand-bank-account-number 80 137 300 131072 1987 1186 30176 ok
sit-defn-new-zealand-drivers-license-number 19 1769 300 524288 20033 11144 48000 ok
sit-defn-new-zealand-inland-revenue-number 48 151 300 131072 2180 1202 30176 ok
sit-defn-new-zealand-ministry-of-health-number 61 128 300 262144 2151 1116 30928 ok
sit-defn-new-zealand-social-welfare-number 34 153 300 131072 2001 1045 30176 ok
sit-defn-norway-identification-number 24 145 300 65536 1978 1055 29816 ok
sit-defn-philippines-national-identification-number 34 163 300 131072 2465 1321 30176 ok
sit-defn-philippines-passport-number/comb00 29 293 300 262144 3890 2274 30928 ok
sit-defn-philippines-passport-number/comb01 24 293 300 262144 3848 2205 30928 ok
sit-defn-philippines-unified-multi-purpose-identification-number 29 130 300 65536 1705 891 29816 ok
sit-defn-poland-drivers-license-number 34 3201 300 1048576 29166 18760 48752 ok
sit-defn-poland-identity-card 19 155 300 131072 2021 967 30568 ok
sit-defn-poland-national-id 21 152 300 131072 2172 1205 30176 ok
sit-defn-poland-passport-number 19 394 300 262144 4682 2838 30928 ok
sit-defn-poland-regon-number/comb00 31 343 300 131072 4279 2440 30568 ok
sit-defn-poland-regon-number/comb01 8 343 300 131072 4258 2489 30568 ok
sit-defn-portugal-drivers-license-number/comb00 58 3221 300 1048576 29696 18642 48752 ok
sit-defn-portugal-drivers-license-number/comb01 53 3221 300 1048576 29488 18785 48752 ok
sit-defn-portugal-passport-number 16 413 300 262144 4657 2809 30928 ok
sit-defn-portugal-tax-identification-number 34 448 300 262144 5743 3452 30928 ok
sit-defn-qatari-id-card-number 28 151 300 131072 2425 1349 30176 ok
sit-defn-romania-drivers-license-number 19 3355 300 1048576 31693 20237 48752 ok
sit-defn-romania-passport-number 10 285 300 131072 3635 2149 30176 ok
sit-defn-russia-passport-number-international 27 149 300 131072 2183 1207 30176 ok
sit-defn-saudi-arabia-national-id 9 81 300 65536 1440 843 29816 ok
sit-defn-slovakia-drivers-license-number 19 3155 300 1048576 28949 17999 48752 ok
sit-defn-slovakia-personal-number 29 767 300 262144 9678 5135 47640 ok
sit-defn-slovenia-passport-number 24 387 300 262144 4633 2835 30928 ok
sit-defn-slovenia-tax-identification-number 18 423 300 262144 5208 3097 30928 ok
sit-defn-slovenia-unique-master-citizen-number 29 575 300 262144 6119 3374 47640 ok
sit-defn-south-africa-identification-number 30 60 300 65536 1492 846 29816 ok
sit-defn-south-korea-passport-number 35 191 300 262144 2743 1517 30536 ok
sit-defn-south-korea-resident-registration-number 20 127 300 65536 1690 904 29816 ok
sit-defn-spain-dni 27 375 300 262144 4525 2465 30928 ok
sit-defn-spain-drivers-license-number 19 3465 300 1048576 32981 20228 48752 ok
sit-defn-spain-social-security-number 36 124 300 131072 1995 1059 30176 ok
sit-defn-spain-tax-identification-number 27 545 300 262144 8137 4160 47640 ok
sit-defn-sweden-drivers-license-number 20 3293 300 1048576 31889 19310 48752 ok
sit-defn-sweden-national-id 38 412 300 262144 4735 2749 30928 ok
sit-defn-sweden-passport-number 8 690 300 262144 9388 4859 47640 ok
sit-defn-switzerland-ssn-ahv-number 47 448 300 262144 5094 2790 47640 ok
sit-defn-taiwan-resident-certificate-number 19 224 300 262144 2879 1696 30928 ok
sit-defn-thai-population-identification-code 14 55 300 65536 1231 697 29816 ok
sit-defn-uae-identity-card-number 44 353 300 262144 4327 2453 30928 ok
sit-defn-uk-electoral-roll-number 21 114 300 131072 1970 1059 30568 ok
sit-defn-uk-national-health-service-number 34 316 300 131072 4019 2293 30568 ok
sit-defn-uk-national-insurance-number/comb00 27 517 300 262144 5935 3313 47640 ok
sit-defn-uk-national-insurance-number/comb01 80 517 300 262144 5873 3310 47640 ok
sit-defn-ukraine-passport-international 22 79 300 131072 1515 852 30176 ok
sit-defn-us-bank-account-number 11 897 300 262144 7794 4688 30928 ok
sit-defn-us-drivers-license-number 32 2296 300 1048576 23165 14786 48360 ok
sit-defn-us-individual-taxpayer-identification-number/comb00 76 239 300 262144 4134 2420 30928 ok
sit-defn-us-individual-taxpayer-identification-number/comb01 66 239 300 262144 4094 2381 30928 ok
sit-defn-us-individual-taxpayer-identification-number/comb02 66 239 300 262144 4384 2335 30928 ok
sit-defn-us-individual-taxpayer-identification-number/comb03 56 239 300 262144 4089 2376 30928 ok
sit-defn-us-uk-passport-number 19 344 300 262144 3902 2225 30928 ok
== STR_LENGTH = 4000 ==
sit-defn-aba-routing/comb00 75 323 300 524288 20766 11104 48000 ok
sit-defn-aba-routing/comb01 71 323 300 524288 19950 10847 48000 ok
sit-defn-aba-routing/comb02 71 323 300 524288 20583 10865 48000 ok
sit-defn-aba-routing/comb03 67 323 300 524288 19447 10791 48000 ok
sit-defn-argentina-national-identity-numbers 34 191 300 262144 9978 5267 47640 ok
sit-defn-australia-bank-account-number 20 330 300 262144 16364 10063 47640 ok
sit-defn-australia-business-number 65 161 300 262144 9614 5367 30928 ok
sit-defn-australia-drivers-license-number/comb00 72 1727 300 1048576 59854 41423 48752 ok
sit-defn-australia-drivers-license-number/comb01 59 1727 300 1048576 59824 40827 48752 ok
sit-defn-australia-drivers-license-number/comb02 59 1727 300 1048576 59659 40750 48752 ok
sit-defn-australia-drivers-license-number/comb03 46 1727 300 1048576 59700 40560 48752 ok
sit-defn-australia-drivers-license-number/comb04 54 1727 300 1048576 59864 41167 48752 ok
sit-defn-australia-drivers-license-number/comb05 41 1727 300 1048576 60483 41196 48752 ok
sit-defn-australia-drivers-license-number/comb06 41 1727 300 1048576 60615 41039 48752 ok
sit-defn-australia-drivers-license-number/comb07 28 1727 300 1048576 59873 40275 48752 ok
sit-defn-australia-drivers-license-number/comb08 59 1727 300 1048576 62913 40490 48752 ok
sit-defn-australia-drivers-license-number/comb09 49 1727 300 1048576 61041 40231 48752 ok
sit-defn-australia-drivers-license-number/comb10 49 1727 300 1048576 63106 40314 48752 ok
sit-defn-australia-drivers-license-number/comb11 39 1727 300 1048576 65264 40749 48752 ok
sit-defn-australia-drivers-license-number/comb12 49 1727 300 1048576 63027 40366 48752 ok
sit-defn-australia-drivers-license-number/comb13 39 1727 300 1048576 61568 40526 48752 ok
sit-defn-australia-drivers-license-number/comb14 39 1727 300 1048576 62091 50069 48752 ok
sit-defn-australia-drivers-license-number/comb15 29 1727 300 1048576 62686 40408 48752 ok
sit-defn-australia-drivers-license-number/comb16 8 1727 300 1048576 62547 40635 48752 ok
sit-defn-australia-drivers-license-number/comb17 27 1727 300 1048576 66407 40367 48752 ok
sit-defn-australia-drivers-license-number/comb18 19 1727 300 1048576 60343 40465 48752 ok
sit-defn-australia-passport-number/comb00 17 471 300 524288 21811 13003 48000 ok
sit-defn-australia-passport-number/comb01 18 471 300 524288 20743 13015 48000 ok
sit-defn-australia-tax-file-number 36 260 300 262144 12506 6896 47640 ok
sit-defn-austria-passport-number 21 419 300 524288 18884 12402 48000 ok
sit-defn-austria-social-security-number 21 647 300 524288 28533 17742 48392 ok
sit-defn-austria-tax-identification-number 34 431 300 524288 18659 12249 48000 ok
sit-defn-austria-value-added-tax 60 394 300 524288 18710 10806 48000 ok
sit-defn-belgium-passport-number 19 496 300 524288 27166 15493 48000 ok
sit-defn-belgium-value-added-tax-number 64 148 300 262144 9611 5276 30928 ok
sit-defn-brazil-cpf-number/comb00 44 105 300 262144 8663 4751 30928 ok
sit-defn-brazil-cpf-number/comb01 9 105 300 262144 8601 4745 30928 ok
sit-defn-brazil-legal-entity-number 56 308 300 262144 15939 9959 47640 ok
sit-defn-bulgaria-uniform-civil-number 26 671 300 524288 37583 20706 48392 ok
sit-defn-canada-bank-account-number/comb00 20 699 300 524288 29512 16264 48392 ok
sit-defn-canada-bank-account-number/comb01 9 699 300 524288 30389 16157 48392 ok
sit-defn-canada-drivers-license-number/comb00 20 3441 300 2097152 144351 90706 82208 ok
sit-defn-canada-drivers-license-number/comb01 10 3441 300 2097152 122693 78186 82208 ok
sit-defn-canada-drivers-license-number/comb02 72 3441 300 2097152 147764 94283 82208 ok
sit-defn-canada-drivers-license-number/comb03 68 3441 300 2097152 147106 92719 82208 ok
sit-defn-canada-drivers-license-number/comb04 68 3441 300 2097152 144490 98675 82208 ok
sit-defn-canada-drivers-license-number/comb05 64 3441 300 2097152 145240 93890 82208 ok
sit-defn-canada-drivers-license-number/comb06 68 3441 300 2097152 152669 90892 82208 ok
sit-defn-canada-drivers-license-number/comb07 64 3441 300 2097152 145532 91866 82208 ok
sit-defn-canada-drivers-license-number/comb08 64 3441 300 2097152 163853 97463 82208 ok
sit-defn-canada-drivers-license-number/comb09 60 3441 300 2097152 137623 94326 82208 ok
sit-defn-canada-drivers-license-number/comb10 19 3441 300 2097152 130974 82256 82208 ok
sit-defn-canada-drivers-license-number/comb11 37 3441 300 2097152 138828 96107 82208 ok
sit-defn-canada-drivers-license-number/comb12 33 3441 300 2097152 143422 93508 82208 ok
sit-defn-canada-drivers-license-number/comb13 58 3441 300 2097152 150810 92333 82208 ok
sit-defn-canada-drivers-license-number/comb14 54 3441 300 2097152 144648 92233 82208 ok
sit-defn-canada-drivers-license-number/comb15 54 3441 300 2097152 141699 94528 82208 ok
sit-defn-canada-drivers-license-number/comb16 50 3441 300 2097152 146014 95875 82208 ok
sit-defn-canada-passport-number 19 492 300 524288 23091 14123 48392 ok
sit-defn-canada-social-insurance-number 44 578 300 524288 31611 17655 48392 ok
sit-defn-chile-identity-card-number 51 855 300 1048576 33961 19241 48752 ok
sit-defn-china-resident-identity-card-number 29 93 300 131072 4886 2796 30568 ok
sit-defn-croatia-identity-card-number 8 692 300 524288 34381 20447 48392 ok
sit-defn-croatia-personal-identification-number 14 692 300 524288 33071 20444 48392 ok
sit-defn-cyprus-passport-number 18 316 300 524288 17666 10161 48000 ok
sit-defn-czech-drivers-license-number 29 3155 300 2097152 114877 77410 82208 ok
sit-defn-czech-passport-number 8 309 300 262144 17462 9951 47640 ok
sit-defn-czech-personal-identity-number/comb00 25 957 300 524288 43738 28673 48392 ok
sit-defn-czech-personal-identity-number/comb01 20 957 300 524288 43547 28391 48392 ok
sit-defn-czech-personal-identity-number/comb02 21 957 300 524288 45370 28580 48392 ok
sit-defn-czech-personal-identity-number/comb03 16 957 300 524288 50658 28374 48392 ok
sit-defn-denmark-personal-identification-number 27 1779 300 1048576 67603 44278 81848 ok
sit-defn-drug-enforcement-agency-number 27 106 300 262144 5655 3504 30928 ok
sit-defn-ecuador-unique-identification-number 39 566 300 524288 24543 16348 48392 ok
sit-defn-estonia-drivers-license-number 16 3261 300 2097152 149592 123362 82208 ok
sit-defn-estonia-passport-number 16 285 300 524288 14845 9067 48000 ok
sit-defn-estonia-personal-identification-code 26 705 300 524288 29000 18268 48392 ok
sit-defn-finland-drivers-license-number 31 3311 300 2097152 144399 95424 82208 ok
sit-defn-finland-european-health-insurance-number 29 307 300 262144 14313 7852 47640 ok
sit-defn-finland-passport-number 19 472 300 524288 21124 14267 48000 ok
sit-defn-france-drivers-license-number 9 3294 300 2097152 145958 95672 82208 ok
sit-defn-france-health-insurance-number 33 51 300 131072 3842 2155 30568 ok
sit-defn-france-national-id-card 15 227 300 524288 10489 6583 48000 ok
sit-defn-france-passport-number 27 433 300 524288 21645 13543 48000 ok
sit-defn-france-social-security-number/comb00 21 377 300 262144 16691 9892 47640 ok
sit-defn-france-social-security-number/comb01 17 377 300 262144 16368 9944 47640 ok
sit-defn-france-tax-identification-number 62 367 300 524288 19588 10831 48000 ok
sit-defn-germany-drivers-license-number 49 3703 300 2097152 158998 115749 82208 ok
sit-defn-germany-tax-identification-number 57 524 300 524288 23186 15296 48392 ok
sit-defn-germany-value-added-tax-number 59 173 300 262144 10068 5422 47640 ok
sit-defn-greece-passport-number 19 228 300 524288 13703 7185 48000 ok
sit-defn-greece-social-security-number 21 170 300 262144 9876 5299 30928 ok
sit-defn-hungary-drivers-license-number 19 3183 300 2097152 147144 90513 82208 ok
sit-defn-hungary-passport-number 21 285 300 524288 13028 8205 48000 ok
sit-defn-hungary-personal-identification-number 26 118 300 131072 6646 4142 30568 ok
sit-defn-hungary-tax-identification-number 18 470 300 524288 22841 14401 48000 ok
sit-defn-hungary-value-added-tax-number 24 136 300 524288 10212 5132 48000 ok
sit-defn-india-drivers-license-number 68 3155 300 2097152 113460 74997 82208 ok
sit-defn-india-gst-number 86 106 300 524288 6076 3573 31288 ok
sit-defn-india-permanent-account-number 60 52 300 524288 3947 2262 31288 ok
sit-defn-india-voter-id-card 19 172 300 524288 10444 6487 48000 ok
sit-defn-indonesia-drivers-license-number/comb00 22 1871 300 1048576 80597 54395 48752 ok
sit-defn-indonesia-drivers-license-number/comb01 32 1871 300 1048576 83648 51709 48752 ok
sit-defn-indonesia-identity-card-number 32 87 300 131072 4912 2853 30568 ok
sit-defn-indonesia-passport-number 23 417 300 524288 19096 12041 48000 ok
sit-defn-ireland-drivers-license-number 19 3251 300 2097152 144350 104803 82208 ok
sit-defn-ireland-personal-public-service-number/comb00 21 922 300 1048576 38191 25399 48752 ok
sit-defn-ireland-personal-public-service-number/comb01 27 922 300 1048576 45693 28658 48752 ok
sit-defn-israel-bank-account-number/comb00 32 85 300 131072 4632 2813 30568 ok
sit-defn-israel-bank-account-number/comb01 9 85 300 131072 5332 2851 30568 ok
sit-defn-israel-national-identification-number 8 194 300 262144 12234 6417 47640 ok
sit-defn-italy-drivers-license-number 63 3299 300 2097152 119595 78563 82208 ok
sit-defn-italy-passport-number 22 476 300 524288 22435 13647 48000 ok
sit-defn-italy-value-added-tax-number 36 85 300 262144 6729 4138 30928 ok
sit-defn-japan-drivers-license-number 9 212 300 262144 13358 7359 30928 ok
sit-defn-japan-my-number-corporate 14 29 300 131072 2409 1392 30176 ok
sit-defn-japan-my-number-personal 54 22 300 131072 2602 1481 30176 ok
sit-defn-japan-passport-number 19 97 300 262144 5550 3452 30928 ok
sit-defn-japan-residence-card-number 30 103 300 262144 4723 2854 30928 ok
sit-defn-japan-resident-registration-number 9 199 300 131072 6846 4187 30568 ok
sit-defn-japan-social-insurance-number/comb00 20 112 300 131072 4568 2807 30568 ok
sit-defn-japan-social-insurance-number/comb01 16 112 300 131072 4511 2833 30568 ok
sit-defn-japan-social-insurance-number/comb02 11 112 300 131072 4921 3249 30568 ok
sit-defn-latvia-passport-number 22 398 300 524288 19980 13083 48000 ok
sit-defn-latvia-personal-code/comb00 20 1548 300 1048576 67852 41257 81848 ok
sit-defn-latvia-personal-code/comb01 16 1548 300 1048576 62393 41045 81848 ok
sit-defn-lithuania-passport-number 14 353 300 524288 15830 9880 48000 ok
sit-defn-lithuania-personal-code 26 710 300 524288 31257 18951 48392 ok
sit-defn-luxemburg-national-identification-number-natural-persons 17 493 300 524288 22654 13764 48000 ok
sit-defn-luxemburg-national-identification-number-non-natural-persons 52 669 300 524288 33014 18654 48392 ok
sit-defn-malaysia-passport-number 16 447 300 524288 23942 14386 48000 ok
sit-defn-malta-drivers-license-number 40 3155 300 2097152 111172 76729 82208 ok
sit-defn-malta-tax-identification-number/comb00 16 685 300 524288 27477 17649 48392 ok
sit-defn-malta-tax-identification-number/comb01 8 685 300 524288 31805 17560 48392 ok
sit-defn-medicare-beneficiary-identifier-card 246 221 300 524288 10853 5746 48000 ok
sit-defn-netherlands-citizens-service-number 36 623 300 524288 22101 14506 48392 ok
sit-defn-netherlands-passport-number 14 325 300 524288 16578 10318 48000 ok
sit-defn-netherlands-value-added-tax-number 58 121 300 262144 6756 4107 30928 ok
sit-defn-new-zealand-bank-account-number 80 137 300 262144 6601 4360 30928 ok
sit-defn-new-zealand-drivers-license-number 19 1769 300 1048576 73076 46926 48752 ok
sit-defn-new-zealand-inland-revenue-number 48 151 300 262144 8502 4632 30928 ok
sit-defn-new-zealand-ministry-of-health-number 61 128 300 524288 10235 4129 48000 ok
sit-defn-new-zealand-social-welfare-number 34 153 300 262144 6915 4010 30928 ok
sit-defn-norway-identification-number 24 145 300 131072 8244 4416 47280 ok
sit-defn-philippines-national-identification-number 34 163 300 262144 9441 4932 30928 ok
sit-defn-philippines-passport-number/comb00 29 293 300 524288 16059 9120 48000 ok
sit-defn-philippines-passport-number/comb01 24 293 300 524288 17779 9329 48000 ok
sit-defn-philippines-unified-multi-purpose-identification-number 29 130 300 131072 6081 3570 30568 ok
sit-defn-poland-drivers-license-number 34 3201 300 2097152 112451 77377 82208 ok
sit-defn-poland-identity-card 19 155 300 262144 6348 3624 47640 ok
sit-defn-poland-national-id 21 152 300 262144 9673 4889 30928 ok
sit-defn-poland-passport-number 19 394 300 524288 21034 12006 48000 ok
sit-defn-poland-regon-number/comb00 31 343 300 262144 17401 9669 47640 ok
sit-defn-poland-regon-number/comb01 8 343 300 262144 18823 10791 47640 ok
sit-defn-portugal-drivers-license-number/comb00 58 3221 300 2097152 115039 82370 82208 ok
sit-defn-portugal-drivers-license-number/comb01 53 3221 300 2097152 108167 72188 82208 ok
sit-defn-portugal-passport-number 16 413 300 524288 19768 12223 48000 ok
sit-defn-portugal-tax-identification-number 34 448 300 524288 24977 13907 48000 ok
sit-defn-qatari-id-card-number 28 151 300 262144 10091 5508 30928 ok
sit-defn-romania-drivers-license-number 19 3355 300 2097152 153333 97923 82208 ok
sit-defn-romania-passport-number 10 285 300 262144 13561 8450 30928 ok
sit-defn-russia-passport-number-international 27 149 300 262144 8534 4675 30928 ok
sit-defn-saudi-arabia-national-id 9 81 300 131072 4557 2799 30568 ok
sit-defn-slovakia-drivers-license-number 19 3155 300 2097152 134534 91072 82208 ok
sit-defn-slovakia-personal-number 29 767 300 524288 36403 20602 48392 ok
sit-defn-slovenia-passport-number 24 387 300 524288 19535 12035 48000 ok
sit-defn-slovenia-tax-identification-number 18 423 300 524288 21671 13077 48000 ok
sit-defn-slovenia-unique-master-citizen-number 29 575 300 524288 23405 13757 48392 ok
sit-defn-south-africa-identification-number 30 60 300 131072 5265 2815 30568 ok
sit-defn-south-korea-passport-number 35 191 300 524288 11017 6099 31288 ok
sit-defn-south-korea-resident-registration-number 20 127 300 131072 5919 3608 30568 ok
sit-defn-spain-dni 27 375 300 524288 17818 9881 48000 ok
sit-defn-spain-drivers-license-number 19 3465 300 2097152 155502 102462 82208 ok
sit-defn-spain-social-security-number 36 124 300 262144 6517 4094 30928 ok
sit-defn-spain-tax-identification-number 27 545 300 524288 28092 18263 48392 ok
sit-defn-sweden-drivers-license-number 20 3293 300 2097152 146807 92945 82208 ok
sit-defn-sweden-national-id 38 412 300 524288 17117 10944 48000 ok
sit-defn-sweden-passport-number 8 690 300 524288 35443 21501 48392 ok
sit-defn-switzerland-ssn-ahv-number 47 448 300 524288 17173 10769 48392 ok
sit-defn-taiwan-resident-certificate-number 19 224 300 524288 10908 6684 48000 ok
sit-defn-thai-population-identification-code 14 55 300 131072 3740 2186 30568 ok
sit-defn-uae-identity-card-number 44 353 300 524288 17630 9761 48000 ok
sit-defn-uk-electoral-roll-number 21 114 300 262144 5908 3579 47640 ok
sit-defn-uk-national-health-service-number 34 316 300 262144 13951 9175 47640 ok
sit-defn-uk-national-insurance-number/comb00 27 517 300 524288 20755 12996 48392 ok
sit-defn-uk-national-insurance-number/comb01 80 517 300 524288 20693 12693 48392 ok
sit-defn-ukraine-passport-international 22 79 300 262144 4929 2882 30928 ok
sit-defn-us-bank-account-number 11 897 300 524288 27352 18740 48392 ok
sit-defn-us-drivers-license-number 32 2296 300 2097152 103396 68558 49112 ok
sit-defn-us-individual-taxpayer-identification-number/comb00 76 239 300 524288 16896 9579 48000 ok
sit-defn-us-individual-taxpayer-identification-number/comb01 66 239 300 524288 17724 9518 48000 ok
sit-defn-us-individual-taxpayer-identification-number/comb02 66 239 300 524288 14036 8887 48000 ok
sit-defn-us-individual-taxpayer-identification-number/comb03 56 239 300 524288 14222 9440 48000 ok
sit-defn-us-uk-passport-number 19 344 300 524288 16818 9526 48000 ok
"""

def main():
    ap = argparse.ArgumentParser(
        description="Zombie leaf progress (read-only).")
    ap.add_argument("--log", help="explicit run.log path")
    ap.add_argument("--partial", help="explicit partial.jsonl path")
    ap.add_argument("--ref", help="explicit paper reference log")
    ap.add_argument("--full", action="store_true",
                    help="also list failures")
    ap.add_argument("--top", type=int, default=8,
                    help="slowest-circuit rows (0 = off)")
    ap.add_argument("--watch", type=int, default=0, metavar="S",
                    help="re-print every S seconds")
    ap.add_argument("--clear", action="store_true",
                    help="delete the banked step timeline and exit")
    a = ap.parse_args()

    if a.clear:
        try:
            os.unlink(STATE)
            print("removed %s" % STATE)
        except FileNotFoundError:
            print("no state file at %s" % STATE)
        return 0

    ref = read_ref(find_ref(a.ref), bool(a.ref))
    while True:
        log = find_log(a.log)
        now = time.time()
        run_id = os.path.basename(os.path.dirname(log))
        t0 = started_at(log)
        age = now - os.path.getmtime(log)
        st = read_trace(log)
        rows, src = read_partial(a.partial)
        groups = by_size(rows)
        bk = load_state(run_id)
        bank_markers(bk, st, now)
        save_state(bk)

        print("=" * 74)
        print("zombie  %s   state %s" % (run_id, STATE))
        print("  log     %s  (quiet %s)" % (log, hm(age)))
        print("  partial %s" % (src or "NONE (no itemized data yet)"))
        print("  elapsed %s   phase: %s" % (hm(now - t0), st["phase"]))
        show_ref_head(ref)
        if st["absent"]:
            print("  !! ruleset %s ABSENT -- leaf will measure nothing"
                  % st["absent"])
        if st["done"]:
            print("  FINISHED: %d results, %d ok"
                  % (st["done"][0], st["done"][1]))
        elif age > STALL_S:
            print("  !! STALL SUSPECT: no trace output for %s" % hm(age))
        show_steps(bk, now - t0, now)
        print("-" * 74)
        print("SIZES      : live vs the paper reference")
        show_sizes(st, groups, ref)
        show_prediction(st, groups, ref, now - t0)
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
