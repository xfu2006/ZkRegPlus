#!/usr/bin/env python3
"""Reef leaf progress: per-bucket sample acceptance, net-cost stats, the
Estimate1/Estimate2 totals tab:dna-reef-bora reports, a BANKED per-step
timeline, and a live-vs-paper comparison.  Read-only; safe on a live
run.

Unlike the zombie leaf there is NO resume cache -- eval_reef.py deletes
each variant's metrics CSV in _cleanup(), so the ONLY live signal is the
trace itself.  Every live number below therefore comes from the
per-sample line, whose real_net is exactly the total_net_time the final
docs log reports (witness generation + Nova prove + SAFA solve).

The PAPER reference (reef_sample_run.log, the same file dna_reef_bora.py
parses) supplies three things the live trace cannot: the legacy column,
the ITEMIZED per-step breakdown, and the fixed workload the ETA is
priced from.

STEP TIMING: run.log carries NO timestamps -- PAPER_DATA.spawn() writes
only the child's stdout -- so per-step wall is BANKED: each invocation
stamps markers it sees for the first time into a state file.  Its
resolution is therefore your polling interval.  real_net is MEASURED
and exact; it is never banked.

usage: reef_progress.py [--log F] [--ref R] [--full] [--watch S]
                        [--clear]
"""

import argparse
import ast
import glob
import json
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
# Banked step timeline.  Written on EVERY run, no flag; --clear removes
# it.  Keyed by run dir so a new leaf starts a fresh timeline.
STATE = "/tmp/bora/reef_progress.state.json"
STATE_VERSION = 1
# Reference per-step keys, net components first then the fixed floor.
# eval_reef._NET_COMPONENTS defines the first three; everything after
# the bar is excluded from net by the agreed comparison rule.
NET_KEYS = ["witness_generation_0", "prove_0", "fa_solver"]
FLOOR_KEYS = ["commitment_read", "snark_setup", "fa_builder",
              "r1cs_init", "consistency_proof"]

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

# ---- PAPER reference (reef_sample_run.log) ---------------------------
REF_GEN_RE = re.compile(r"^# generated: (\S+ \S+) by")
REF_WALL_RE = re.compile(r"^# total run time: ([\d.]+) s")
REF_KV_RE = re.compile(r"^(os|logical_cores|cpu_model|cpu_mhz|"
                       r"ram_total|doc):\s+(.*?)\s*$")
# "  non_projectable     24434    88.9%   835.2 / 835.2 / 835.2"
REF_POP_RE = re.compile(
    r"^  (\S+) +(\d+) +[\d.]+% +[\d.]+ / ([\d.]+) / [\d.]+\s*$")
# "[non_projectable]  samples=10  timed_out=0"
REF_CAT_RE = re.compile(r"^\[(\S+)\] +samples=(\d+) +timed_out=(\d+)")
# "   net_cost(s):  n=10 min=930.47 max=1125.00 mean=1055.35 std=68.70"
# "   * witness_generation_0 n=10 min=926.08 ... mean=1051.03 std=68.70"
REF_STAT_RE = re.compile(
    r"^\s+(?:\*\s+)?(\S+?):?\s+n=(\d+)\s+min=([\d.]+)\s+"
    r"max=([\d.]+)\s+mean=([\d.]+)\s+std=([\d.]+)\s*$")


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


def paper_raw_roots():
    """raw_data roots to search for the reference, PAPER REPO FIRST.

    The in-repo mirror normally holds a DRY sweep (1 sample/bucket,
    22.9 min), so preferring it would silently compare a live
    production run against dry numbers.
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
            p = os.path.join(root, srv, P.REEF_LOG_NAME)
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
    """Parse a paper log into {meta, pop, cats}.

    cats[name] = {samples, timed_out, net, wall, comps{key: mean}},
    where net/wall are (mean, std).
    """
    ref = {"path": None, "meta": {}, "pop": {}, "cats": {},
           "wall_s": None, "generated": None}
    lines = text.splitlines()
    cur = None
    for line in lines:
        m = REF_GEN_RE.match(line)
        if m:
            ref["generated"] = m.group(1)
            continue
        m = REF_WALL_RE.match(line)
        if m:
            ref["wall_s"] = float(m.group(1))
            continue
        m = REF_KV_RE.match(line)
        if m:
            ref["meta"][m.group(1)] = m.group(2)
            continue
        m = REF_POP_RE.match(line)
        if m:
            ref["pop"][m.group(1)] = int(m.group(2))
            continue
        m = REF_CAT_RE.match(line)
        if m:
            cur = m.group(1)
            ref["cats"][cur] = {"samples": int(m.group(2)),
                                "timed_out": int(m.group(3)),
                                "net": None, "wall": None, "comps": {}}
            continue
        m = REF_STAT_RE.match(line)
        if m and cur:
            key, mean, std = m.group(1), float(m.group(5)), \
                float(m.group(6))
            c = ref["cats"][cur]
            if key.startswith("net_cost"):
                c["net"] = (mean, std)
            elif key.startswith("wall_time"):
                c["wall"] = (mean, std)
            else:
                c["comps"][key] = mean
    return ref


def ref_is_dry(ref):
    """True when the reference looks like a dry sweep, so its numbers
    must not be read as the paper's.  The dry leaf takes 1 sample per
    bucket; the real one takes 10."""
    n = max([c["samples"] for c in ref["cats"].values()] or [0])
    return bool(n) and n < 5


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


def clock(epoch):
    """HH:MM:SS in box-local time."""
    return time.strftime("%H:%M:%S", time.localtime(epoch))


def sci(x):
    """LaTeX-free 'a.aaae+bb', matching the table's Estimate columns."""
    return "%.3e" % x if x else "0"


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
    """Stamp `name` the first time it is ever seen.  Re-stamping is
    what would make the timeline lie, so it never happens."""
    if name not in st["steps"]:
        st["steps"][name] = now
        st["order"].append(name)


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


def cat_order(st, ref):
    """Buckets in table order, then any the trace invented."""
    seen = set(st["cats"]) | set(ref["cats"])
    out = [c for c in BUCKETS if c in seen]
    out += [c for c in st["order"] if c not in out]
    return out


def bank_markers(bk, st, ref, now):
    """Stamp every milestone the trace currently satisfies, coarse to
    fine, so a first invocation on an already-advanced run lists the
    timeline in the order it happened."""
    if st["setup"]:
        bank(bk, "commitment setup", now)
    if st["assessed"] is not None:
        bank(bk, "pool built", now)
    for c in cat_order(st, ref):
        d = st["cats"].get(c)
        if not d:
            continue
        bank(bk, "%s open" % c, now)
        if d["target"] and len(d["acc"]) >= d["target"]:
            bank(bk, "%s done" % c, now)
    if st["wrote"]:
        bank(bk, "FINISHED", now)


def show_steps(bk, now):
    """The banked timeline: when this meter FIRST saw each milestone."""
    print("-" * 78)
    print("STEPS      : first seen by this meter (resolution = your "
          "polling interval)")
    if not bk["order"]:
        print("  (nothing banked yet -- run again later to build the "
              "timeline)")
        return
    t0 = bk["steps"][bk["order"][0]]
    print("  %-24s %10s %10s %9s" % ("step", "first seen", "since t0",
                                      "delta"))
    prev = None
    for name in bk["order"]:
        t = bk["steps"][name]
        d = "-" if prev is None else hm(t - prev)
        print("  %-24s %10s %10s %9s"
              % (name, clock(t), hm(t - t0), d))
        prev = t
    if "FINISHED" not in bk["steps"]:
        print("  %-24s %10s %10s %9s"
              % ("(running)", "--", hm(now - t0), hm(now - prev)))
    print("  NOTE run.log has no timestamps, so these are OBSERVATION")
    print("       times.  real_net below is MEASURED and exact.")


def show(st, ref, elapsed):
    """Per-bucket block, the paper column, and the two Estimates."""
    cats = cat_order(st, ref)
    if not cats:
        print("  (no sample completed yet)")
        return
    print("  %-17s %7s %5s %5s %19s %9s %11s"
          % ("category", "acc/tgt", "try", "disc", "real_net mean+-sd",
             "est_net", "pop count"))
    e1 = e2 = 0.0
    means = []
    n_acc = n_tgt = 0
    pop = dict(ref["pop"])
    pop.update(st["pop"] or {})
    for c in cats:
        d = st["cats"].get(c)
        rc = ref["cats"].get(c)
        n = pop.get(c)
        if d:
            mu, sd = stats(d["acc"])
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
                  % (c, "%d/%d" % (len(d["acc"]), d["target"]),
                     d["tries"], d["disc"], mu, sd, d["est"],
                     "{:,}".format(n) if n else "?", flag))
            if n and mu:
                e1 += n * mu
        else:
            mu = 0.0
            print("  %-17s %7s %5s %5s %19s %9s %11s"
                  % (c, "PENDING", "-", "-", "-", "-",
                     "{:,}".format(n) if n else "?"))
        if rc and rc["net"]:
            x = (" x %.3f" % (mu / rc["net"][0])) if mu else ""
            print("    %-15s %7s %5s %5s %10.2f +- %6.2f %9s %11s%s"
                  % ("paper", "n=%d" % rc["samples"], "", "",
                     rc["net"][0], rc["net"][1], "",
                     "{:,}".format(n) if n else "?", x))
    if pop and means:
        e2 = sum(pop.get(c, 0) for c in BUCKETS) * min(means)
    print()
    _estimates(e1, e2, ref, pop, len(means))
    if n_acc and n_tgt:
        # Every category shares one sample_size, so the run's true
        # target is that size x ALL buckets -- counting only the
        # categories seen so far would shrink the denominator (and the
        # ETA) every time a new bucket opens.
        per = max(st["cats"][c]["target"] for c in st["cats"])
        full = per * len(BUCKETS)
        print("  %d/%d samples accepted (%d/%d in the buckets started)"
              % (n_acc, full, n_acc, n_tgt))


def _estimates(e1, e2, ref, pop, n_means):
    """Live Estimate1/Estimate2 beside the paper's own."""
    r1 = sum(pop.get(c, 0) * ref["cats"][c]["net"][0]
             for c in ref["cats"]
             if ref["cats"][c]["net"] and pop.get(c))
    rmin = min([ref["cats"][c]["net"][0] for c in ref["cats"]
                if ref["cats"][c]["net"]] or [0])
    r2 = sum(pop.get(c, 0) for c in BUCKETS) * rmin if rmin else 0
    for lab, live, paper in (("Estimate1 (sum pop*mean)   ", e1, r1),
                             ("Estimate2 (all pop*minmean)", e2, r2)):
        if not live and not paper:
            continue
        line = "  %s = %s s = %8.2f d" % (
            lab, sci(live) if live else "    -    ",
            live / 86400.0 if live else 0.0)
        if paper:
            line += " | paper %s = %7.2f d" % (sci(paper),
                                                paper / 86400.0)
            if live:
                line += "  x %.3f" % (live / paper)
        print(line)
    if e1 and n_means < len(BUCKETS):
        print("  (PARTIAL: %d of %d buckets sampled -- both live "
              "estimates grow)" % (n_means, len(BUCKETS)))
    if e1 or e2:
        # eval_reef prints real_net as %.1f, so a cheap bucket's mean
        # carries ~0.1 s of quantisation.  On proj_512k (7.3 s) that is
        # ~0.2% and it lands whole in Estimate2, which multiplies the
        # MINIMUM mean by all 27,500 variants -- the live figure can
        # therefore differ from the final table in the 3rd digit.
        print("  (live means read real_net at 1 decimal; Estimate2 "
              "inherits ~0.2% of that)")


def show_prediction(st, ref, elapsed):
    """ETA priced from the FIXED reference workload, not from a rate.

    The buckets differ by 144x in cost (7.33 s to 1055.35 s), so a rate
    learned on the bucket in flight is meaningless.  Pricing each
    REMAINING sample at its reference WALL cost, scaled by the box
    ratio measured on NET (the only quantity the live trace reports),
    is right from the first sample.
    """
    print("-" * 78)
    print("PREDICTION : priced from the reference workload, not a rate")
    if not ref["cats"]:
        print("  (no reference workload -- the bucket table above is "
              "still live)")
        return
    per_ref = max([c["samples"] for c in ref["cats"].values()] or [0])
    per = max([d["target"] for d in st["cats"].values()] or [0]) \
        or per_ref
    tot = rem = done_ref = done_live = 0.0
    n_rem = 0
    for c in BUCKETS:
        rc = ref["cats"].get(c)
        if not rc or not rc["wall"]:
            continue
        d = st["cats"].get(c)
        got = len(d["acc"]) if d else 0
        tot += per * rc["wall"][0]
        rem += max(0, per - got) * rc["wall"][0]
        n_rem += max(0, per - got)
        if d and d["acc"] and rc["net"]:
            done_ref += got * rc["net"][0]
            done_live += sum(d["acc"])
    if not tot:
        print("  (reference has no comparable bucket)")
        return
    # Self-check: the model, run at the reference's OWN sample count,
    # must reproduce the reference's own header wall time.  If it does
    # not, the parse is wrong and every number here is suspect.
    model = sum(per_ref * ref["cats"][c]["wall"][0] for c in BUCKETS
                if ref["cats"].get(c) and ref["cats"][c]["wall"])
    if ref["wall_s"]:
        d = model - ref["wall_s"]
        print("  model self-check                %10.1f s vs the log's "
              "own %.1f s  (delta %+.1f s)" % (model, ref["wall_s"], d))
    print("  THIS run's reference workload   %10.1f s = %.2f h  "
          "(%d samples x %d buckets)" % (tot, tot / 3600.0, per,
                                          len(BUCKETS)))
    ratio = (done_live / done_ref) if done_ref else 1.0
    if done_ref:
        print("  matched so far (net)            %10.1f s  ->  live "
              "%.1f s   ratio %.3fx" % (done_ref, done_live, ratio))
    else:
        print("  matched so far                  %10s  (ratio "
              "assumed 1.000x)" % "none yet")
    if st["wrote"]:
        print("  RUN FINISHED -- no ETA.  measured %.1f s of net"
              % done_live)
        return
    remain = rem * ratio
    print("  remaining (%d samples x ratio)   %10.1f s  = %s"
          % (n_rem, remain, hm(remain)))
    print("  ETA %s box   total projected %.2f h"
          % (clock(time.time() + remain), (elapsed + remain) / 3600.0))
    disc = sum(d["disc"] for d in st["cats"].values())
    print("  RISK a DISCARD buys one extra variant run (cap %d s); %d "
          "so far" % (VARIANT_TIMEOUT_S, disc))


def show_per_step(ref):
    """Reef's per-step breakdown.  PAPER REFERENCE ONLY.

    eval_reef.py holds the itemized `results` dict in memory and writes
    it only to the final docs log, so the live trace cannot supply it.
    Left of the bar is net (witness generation + Nova prove + SAFA
    solve); right of it is the fixed floor the comparison excludes.
    """
    if not ref["cats"]:
        return
    print("-" * 78)
    print("PER-STEP   : PAPER REFERENCE ONLY -- eval_reef.py writes the")
    print("             itemized dict only to the final docs log, so it")
    print("             is NOT in the live trace.  s, mean over samples.")
    keys = [k for k in NET_KEYS + FLOOR_KEYS
            if any(k in c["comps"] for c in ref["cats"].values())]
    short = {"witness_generation_0": "wit_gen", "prove_0": "prove",
             "fa_solver": "fa_solv", "commitment_read": "cmt_read",
             "snark_setup": "snark_st", "fa_builder": "fa_build",
             "r1cs_init": "r1cs_in", "consistency_proof": "consist"}
    hdr = "  %-17s %9s" % ("bucket", "net")
    for k in keys:
        hdr += (" ||" if k == FLOOR_KEYS[0] else "")
        hdr += " %9s" % short.get(k, k[:9])
    print(hdr)
    for c in BUCKETS:
        rc = ref["cats"].get(c)
        if not rc:
            continue
        row = "  %-17s %9.2f" % (c, rc["net"][0] if rc["net"] else 0.0)
        for k in keys:
            row += (" ||" if k == FLOOR_KEYS[0] else "")
            row += " %9.2f" % rc["comps"].get(k, 0.0)
        print(row)
    print("  || right of the bar = the fixed floor, EXCLUDED from net.")


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


def show_ref_head(ref):
    """Provenance of the legacy column.  Printed even when the machine
    differs, because a box mismatch is exactly what a reader of the
    ratio column needs to know first."""
    if not ref["path"]:
        print("  ref     NONE FOUND -- no legacy column, no prediction")
        return
    m = ref["meta"]
    tag = "DRY" if ref_is_dry(ref) else "REAL"
    n = max([c["samples"] for c in ref["cats"].values()] or [0])
    print("  ref     %s" % ref["path"])
    print("          %s  %s  %d samples/bucket  %s s total"
          % (ref["generated"] or "?", tag, n,
             "%.1f" % ref["wall_s"] if ref["wall_s"] else "?"))
    if m.get("cpu_model"):
        print("          %s cores  %s @%s MHz  %s"
              % (m.get("logical_cores", "?"), m.get("cpu_model", "?"),
                 m.get("cpu_mhz", "?"), m.get("ram_total", "?")))
    if m.get("doc"):
        print("          doc %s" % m["doc"])
    if tag == "DRY":
        print("          !! DRY sweep -- these are NOT the paper's "
              "numbers")
    if ref.get("skipped_dry"):
        print("          ignored a DRY log (pass --ref to force it):")
        print("          %s" % ref["skipped_dry"])


# =====================================================================
# EMBEDDED PAPER REFERENCE -- 2026-06-23, host zkregplus-large
# (128 cores, AMD EPYC-Milan, 961.1 GiB), the run that produced
# tab:dna-reef-bora.
#
# Verbatim rows from reef_sample_run.log,
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
EMBED_TAG = "<embedded 2026-06-23 jet1tb>"
REF_EMBED = """# generated: 2026-06-23 19:20:08 by scripts/eval_reef.py
# total run time: 18600.3 s (310.0 min)
  non_projectable     24434    88.9%   835.2 / 835.2 / 835.2
  proj_512k              58     0.2%   5.5 / 5.5 / 5.5
  proj_2M               132     0.5%   13.3 / 13.3 / 13.3
  proj_4M              1194     4.3%   24.4 / 24.4 / 24.4
  proj_8M               869     3.2%   47.5 / 47.5 / 47.5
  proj_16M              813     3.0%   95.6 / 95.6 / 95.6
os:              Linux 6.17.0-35-generic
logical_cores:   128
cpu_model:       AMD EPYC-Milan Processor
cpu_mhz:         1996.249
ram_total:       961.1 GiB
doc:             NC_000017.11.reef.txt (83257441 bytes, padded table 134217728 = 2^27)
timed_out: 0 of 60 samples
[non_projectable]  samples=10  timed_out=0
   net_cost(s):  n=10 min=930.47 max=1125.00 mean=1055.35 std=68.70
   wall_time(s): n=10 min=1018.70 max=1213.88 mean=1142.38 std=69.88
   * witness_generation_0 n=10 min=926.08 max=1120.65 mean=1051.03 std=68.70
   * prove_0              n=10 min=0.28 max=0.32 mean=0.30 std=0.02
   * fa_solver            n=10 min=3.94 max=4.11 mean=4.02 std=0.04
     consistency_proof    n=10 min=6.67 max=6.97 mean=6.79 std=0.09
     commitment_read      n=10 min=29.35 max=31.14 mean=30.45 std=0.57
     snark_setup          n=10 min=31.74 max=35.47 mean=33.58 std=1.44
     fa_builder           n=10 min=0.61 max=10.90 mean=5.30 std=2.91
     r1cs_init            n=10 min=5.67 max=6.04 mean=5.79 std=0.16
[proj_512k]  samples=10  timed_out=0
   net_cost(s):  n=10 min=6.95 max=7.85 mean=7.33 std=0.38
   wall_time(s): n=10 min=95.10 max=100.41 mean=97.21 std=1.85
   * witness_generation_0 n=10 min=2.58 max=3.36 mean=2.92 std=0.33
   * prove_0              n=10 min=0.25 max=0.29 mean=0.27 std=0.02
   * fa_solver            n=10 min=4.09 max=4.22 mean=4.14 std=0.05
     consistency_proof    n=10 min=6.67 max=7.03 mean=6.84 std=0.10
     commitment_read      n=10 min=29.34 max=31.00 mean=30.06 std=0.55
     snark_setup          n=10 min=27.32 max=30.51 mean=28.76 std=1.20
     fa_builder           n=10 min=14.28 max=14.73 mean=14.37 std=0.12
     r1cs_init            n=10 min=5.68 max=6.02 mean=5.73 std=0.10
[proj_2M]  samples=10  timed_out=0
   net_cost(s):  n=10 min=15.88 max=19.46 mean=18.43 std=0.90
   wall_time(s): n=10 min=105.28 max=112.45 mean=110.45 std=1.93
   * witness_generation_0 n=10 min=11.54 max=15.12 mean=14.04 std=0.89
   * prove_0              n=10 min=0.26 max=0.30 mean=0.29 std=0.01
   * fa_solver            n=10 min=4.04 max=4.20 mean=4.10 std=0.05
     consistency_proof    n=10 min=6.63 max=7.05 mean=6.81 std=0.12
     commitment_read      n=10 min=29.48 max=30.84 mean=30.16 std=0.51
     snark_setup          n=10 min=29.01 max=31.27 mean=30.75 std=0.61
     fa_builder           n=10 min=14.17 max=14.70 mean=14.42 std=0.19
     r1cs_init            n=10 min=5.68 max=5.71 mean=5.69 std=0.01
[proj_4M]  samples=10  timed_out=0
   net_cost(s):  n=10 min=29.95 max=36.22 mean=35.04 std=1.73
   wall_time(s): n=10 min=118.51 max=128.07 mean=126.43 std=2.71
   * witness_generation_0 n=10 min=25.42 max=31.81 mean=30.62 std=1.77
   * prove_0              n=10 min=0.26 max=0.30 mean=0.29 std=0.01
   * fa_solver            n=10 min=4.03 max=4.27 mean=4.13 std=0.06
     consistency_proof    n=10 min=6.70 max=7.09 mean=6.84 std=0.13
     commitment_read      n=10 min=29.25 max=30.63 mean=29.71 std=0.49
     snark_setup          n=10 min=28.42 max=31.48 mean=30.90 std=0.84
     fa_builder           n=10 min=13.86 max=14.16 mean=13.98 std=0.10
     r1cs_init            n=10 min=5.67 max=6.03 mean=5.74 std=0.11
[proj_8M]  samples=10  timed_out=0
   net_cost(s):  n=10 min=59.40 max=71.91 mean=67.25 std=4.15
   wall_time(s): n=10 min=147.68 max=162.75 mean=156.79 std=4.99
   * witness_generation_0 n=10 min=55.00 max=67.51 mean=62.87 std=4.15
   * prove_0              n=10 min=0.26 max=0.30 mean=0.28 std=0.02
   * fa_solver            n=10 min=4.02 max=4.17 mean=4.10 std=0.04
     consistency_proof    n=10 min=6.65 max=6.97 mean=6.81 std=0.12
     commitment_read      n=10 min=29.28 max=30.77 mean=29.84 std=0.47
     snark_setup          n=10 min=28.80 max=31.76 mean=29.94 std=1.13
     fa_builder           n=10 min=12.79 max=13.27 mean=13.10 std=0.15
     r1cs_init            n=10 min=5.68 max=5.71 mean=5.69 std=0.01
[proj_16M]  samples=10  timed_out=0
   net_cost(s):  n=10 min=120.89 max=147.80 mean=137.35 std=10.57
   wall_time(s): n=10 min=208.35 max=239.00 mean=226.77 std=11.57
   * witness_generation_0 n=10 min=116.59 max=143.46 mean=132.95 std=10.53
   * prove_0              n=10 min=0.26 max=0.30 mean=0.28 std=0.01
   * fa_solver            n=10 min=4.03 max=4.45 mean=4.12 std=0.11
     consistency_proof    n=10 min=6.62 max=7.00 mean=6.84 std=0.13
     commitment_read      n=10 min=29.26 max=29.79 mean=29.54 std=0.18
     snark_setup          n=10 min=29.12 max=32.17 mean=30.88 std=1.31
     fa_builder           n=10 min=11.61 max=13.02 mean=12.24 std=0.55
     r1cs_init            n=10 min=5.67 max=5.71 mean=5.69 std=0.01
"""

def main():
    ap = argparse.ArgumentParser(
        description="Reef leaf progress (read-only).")
    ap.add_argument("--log", help="explicit run.log path")
    ap.add_argument("--ref", help="explicit paper reference log")
    ap.add_argument("--full", action="store_true",
                    help="also print every sample line")
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
        st = parse(log)
        bk = load_state(run_id)
        bank_markers(bk, st, ref, now)
        save_state(bk)

        print("=" * 78)
        print("reef  %s   state %s" % (run_id, STATE))
        print("  log     %s  (quiet %s)" % (log, hm(age)))
        print("  elapsed %s   phase: %s" % (hm(now - t0), phase_of(st)))
        if st["assessed"]:
            print("  pool    %s variants across %d categories"
                  % ("{:,}".format(st["assessed"]), len(st["pop"])))
        for s in st["setup"][-2:]:
            print("  setup   %s" % s)
        show_ref_head(ref)
        if st["stop"]:
            print("  !! HARD STOP: %s" % st["stop"])
        for c, got, tgt in st["warn"]:
            print("  !! pool exhausted: %s only %d/%d" % (c, got, tgt))
        if st["wrote"]:
            print("  FINISHED -> %s" % st["wrote"])
        elif age > STALL_S:
            print("  !! STALL SUSPECT: no trace output for %s" % hm(age))
        show_steps(bk, now)
        print("-" * 78)
        print("BUCKETS    : live vs the paper reference")
        show(st, ref, now - t0)
        show_prediction(st, ref, now - t0)
        show_per_step(ref)
        if a.full:
            show_samples(st, log)
        if not a.watch:
            return 0
        time.sleep(a.watch)


if __name__ == "__main__":
    sys.exit(main())
