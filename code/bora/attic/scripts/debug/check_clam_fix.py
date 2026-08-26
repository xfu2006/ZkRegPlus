#!/usr/bin/env python3
"""M102 clam-crash fix: server-side go/no-go check (~25 min mark).

Checks the running (or finished) full_clam part1 log for:
  1. log freshness (CURRENT_JOB.log symlink may be STALE),
  2. zero "carried subsig ... outside the obligation seed" panics,
  3. tuner progress ("determine_config_non_aggr iter" lines),
plus the NEO seed line, other panics, convergence and verify status.

Usage:  python scripts/debug/check_clam_fix.py [part1_log]
        default log: /tmp/bora/CURRENT_JOB.log
Exit:   0 = OK so far (incl. "too early"), 1 = FAIL, 2 = no log.
"""

import os
import re
import sys
import time

# default live log written by the two-half launcher (a SYMLINK).
DEFAULT_LOG = "/tmp/bora/CURRENT_JOB.log"
# a target mtime older than this is treated as a stale symlink.
STALE_S = 2 * 3600
# the crash fired ~1469 s in; before that "no iter lines" = early.
EARLY_S = 35 * 60

# crash 1 (seed side): carried queue entry not in the obligation seed
RE_CARRIED = re.compile(r"carried subsig \d+ outside the obligation")
# crash 2 (compute_sig side): the DNF walk could not find a subsig's
# verdict because compute_sig's list had dropped it. Both must be 0.
RE_MISSING = re.compile(r"cannot find subsig_id: \d+")
# tuner progress line: present = the old crash point was passed
RE_ITER = re.compile(r"determine_config_non_aggr iter")
# demand sanity. The fix makes neo_subsig_demand count the FULL demand
# instead of chain-only, so cs must RISE above the diagnosed 319; a cs
# still equal to 319 means the new binary is not the one running.
RE_SEED = re.compile(r"NEO SUBSIG SEED: demand cs=(\d+) igc=(\d+)")
OLD_DEMAND_CS = 319
# CP seed sanity. The exact seed prints need = 1 + max_w(sed+dfa+ised);
# the killed crawl already proved clam needs > 26, so need <= 26 means
# the old proxy seed (or a wrong formula) is running.
RE_CP_SEED = re.compile(r"NEO CP SEED: no_crit_pat=(\d+) need=(\d+)")
CP_NEED_MIN = 27
# any cp::subsigs bump = the crawl is back = the exact seed under-shot
# (formula refuted for some word). Zero expected. The pair may sit
# ANYWHERE in the bumped vec, so match the pair and gate on the line
# carrying "bumped [" (an anchored r'bumped \[\("cp::subsigs' gave a
# FALSE PASS on '[("comp_sig::sigs", 9), ("cp::subsigs", 231)]').
# Line-gated so a caught probe panic quoting the name is not counted.
RE_CP_PAIR = re.compile(r'\("cp::subsigs[^"]*",\s*(\d+)\)')
BUMP_TAG = "bumped ["
# the true abort marker (tuner hands an unmappable CapErr to the
# driver and the whole job dies rc=101)
RE_FATAL = re.compile(r"unmapped CapErr")
# panic header + known-noise classes: poison cascade is a symptom,
# and caught probe panics are normal tuner traffic until proven not
RE_PANIC = re.compile(r"panicked at")
RE_POISON = re.compile(r"Mutex poisoned")
# end-of-run success markers
RE_VERIFY = re.compile(r"Verify (Batch|Individual).*(PASS|pass)")
RE_CONV = re.compile(r"CONVERGED", re.IGNORECASE)


def read_log(path):
    """Resolve+read the log; return (text, target, age_s) or exit 2."""
    if not os.path.exists(path):
        print("NO LOG: %s" % path)
        sys.exit(2)
    target = os.path.realpath(path)
    age = time.time() - os.path.getmtime(target)
    with open(target, errors="replace") as fh:
        return fh.read(), target, age


def main():
    """Run all checks, print PASS/FAIL/PENDING per item, set exit."""
    path = sys.argv[1] if len(sys.argv) > 1 else DEFAULT_LOG
    text, target, age = read_log(path)
    print("log: %s" % target)
    print("age: %.0f s (%.1f min)" % (age, age / 60.0))
    fail = False

    # 1. freshness (the symlink was stale on 08-16, doc sec 14)
    if age > STALE_S:
        print("WARN: log older than %d h -- STALE symlink? point "
              "me at the run's part1 log directly." % (STALE_S // 3600))

    # 2. the fixed assert must be gone (was 269 hits)
    n_carried = len(RE_CARRIED.findall(text))
    if n_carried == 0:
        print("PASS: 0 'carried subsig' panics (was 269)")
    else:
        first = next(l for l in text.splitlines()
                     if RE_CARRIED.search(l))
        print("FAIL: %d 'carried subsig' panics -- fix refuted, "
              "keep the failed_tgz bundle" % n_carried)
        print("      first: %s" % first.strip())
        fail = True

    # 2b. crash 2: the compute_sig DNF walk (was 325 hits)
    n_missing = len(RE_MISSING.findall(text))
    if n_missing == 0:
        print("PASS: 0 'cannot find subsig_id' panics (was 325)")
    else:
        print("FAIL: %d 'cannot find subsig_id' panics -- compute_sig "
              "still missing a subsig verdict" % n_missing)
        fail = True

    # 3a. the true abort marker (rc=101 path)
    fatal = [l for l in text.splitlines() if RE_FATAL.search(l)]
    if fatal:
        print("FAIL: run aborted -- %s" % fatal[-1].strip())
        fail = True

    # 3b. tuner progress (absent in the crashed run)
    n_iter = len(RE_ITER.findall(text))
    if n_iter > 0:
        print("PASS: %d tuner iter line(s) -- old crash point passed"
              % n_iter)
    elif not fail:
        if age < EARLY_S:
            print("PENDING: no tuner iter lines yet (log %.0f min "
                  "old) -- re-run me later" % (age / 60.0))
        else:
            print("WARN: no tuner iter lines after %.0f min -- "
                  "check the run is alive (log mtime, not pgrep)"
                  % (age / 60.0))

    # 3c. panic census, classified: poison cascade = symptom noise;
    # caught probe panics are NORMAL tuner traffic; anything with an
    # unrecognized message is printed for a human verdict.
    lines = text.splitlines()
    n_poison = len([l for l in lines if RE_POISON.search(l)])
    msgs = {}
    for i, l in enumerate(lines):
        if not RE_PANIC.search(l) or RE_POISON.search(l):
            continue
        m = lines[i + 1].strip() if i + 1 < len(lines) else ""
        if RE_CARRIED.search(l) or RE_CARRIED.search(m):
            continue
        if RE_POISON.search(m) or not m or RE_PANIC.search(m):
            continue
        msgs[m] = msgs.get(m, 0) + 1
    if n_poison:
        print("INFO: %d Mutex-poisoned lines (cascade noise, look "
              "at the census below for the cause)" % n_poison)
    if msgs:
        print("WARN: unclassified panic message(s) -- caught CapErr "
              "probes are normal during tuning; anything else, "
              "paste this census back to the session:")
        top = sorted(msgs.items(), key=lambda k: -k[1])[:8]
        for m, c in top:
            print("      %5d  %s" % (c, m[:66]))

    # 4. demand sanity: diagnosed run was cs=319 igc=8
    m = RE_SEED.search(text)
    if m:
        cs, igc = int(m.group(1)), int(m.group(2))
        print("INFO: NEO SUBSIG SEED demand cs=%d igc=%d" % (cs, igc))
        if cs == OLD_DEMAND_CS:
            print("FAIL: demand cs is still %d (chain-only). The fix "
                  "makes it count the FULL demand, so this binary is "
                  "the OLD one -- rebuild/redeploy." % OLD_DEMAND_CS)
            fail = True
        else:
            print("PASS: demand cs rose above the chain-only %d, so "
                  "the unfiltered count is live" % OLD_DEMAND_CS)
    else:
        print("INFO: no NEO SUBSIG SEED line yet")

    # 4b. CP seed sanity: the exact seed must clear the crawl-proven
    # demand, and no cp::subsigs CapErr may ever fire again.
    m = RE_CP_SEED.search(text)
    if m:
        nc, need = int(m.group(1)), int(m.group(2))
        print("INFO: NEO CP SEED no_crit_pat=%d need=%d" % (nc, need))
        if need < CP_NEED_MIN:
            print("FAIL: CP seed need=%d < %d (the killed crawl proved "
                  ">26) -- old proxy seed or wrong formula running"
                  % (need, CP_NEED_MIN))
            fail = True
        else:
            print("PASS: CP seed need=%d >= %d (exact seed live)"
                  % (need, CP_NEED_MIN))
    else:
        print("INFO: no NEO CP SEED need= line yet (old-format line or "
              "pre-seed phase)")
    cp_vals = [RE_CP_PAIR.search(l).group(1)
               for l in text.splitlines()
               if BUMP_TAG in l and RE_CP_PAIR.search(l)]
    if not cp_vals:
        print("PASS: 0 cp::subsigs bumps (crawl gone)")
    else:
        print("FAIL: %d cp::subsigs bump(s) -> %s -- the exact seed "
              "under-shot; save the log for the session"
              % (len(cp_vals), ",".join(cp_vals)))
        fail = True

    # 5. later-stage markers, informational
    n_conv = len(RE_CONV.findall(text))
    n_ver = len(RE_VERIFY.findall(text))
    if n_conv:
        print("INFO: %d CONVERGED line(s)" % n_conv)
    if n_ver:
        print("INFO: %d verify PASS line(s)" % n_ver)

    print("VERDICT: %s" % ("FAIL" if fail else "OK so far"))
    sys.exit(1 if fail else 0)


if __name__ == "__main__":
    main()
