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

# the fixed assert (crash signature), count must be 0
RE_CARRIED = re.compile(r"carried subsig \d+ outside the obligation")
# tuner progress line: present = the old crash point was passed
RE_ITER = re.compile(r"determine_config_non_aggr iter")
# demand sanity: same DB/demand shape as the diagnosed run
RE_SEED = re.compile(r"NEO SUBSIG SEED: demand cs=(\d+) igc=(\d+)")
# any other fatal noise the greps above would miss
RE_PANIC = re.compile(r"panicked at|unmapped CapErr")
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

    # 3. tuner progress (absent in the crashed run)
    n_iter = len(RE_ITER.findall(text))
    other = [l for l in text.splitlines() if RE_PANIC.search(l)
             and not RE_CARRIED.search(l)]
    if n_iter > 0:
        print("PASS: %d tuner iter line(s) -- old crash point passed"
              % n_iter)
    elif other:
        print("FAIL: no tuner iter lines and %d other panic line(s)"
              % len(other))
        fail = True
    elif age < EARLY_S:
        print("PENDING: no tuner iter lines yet (log %.0f min old; "
              "the tuner starts ~25 min in) -- re-run me later"
              % (age / 60.0))
    else:
        print("WARN: no tuner iter lines after %.0f min and no "
              "panic -- check the run is alive (log mtime, not "
              "pgrep)" % (age / 60.0))

    # 4. demand sanity: diagnosed run was cs=319 igc=8
    m = RE_SEED.search(text)
    if m:
        cs, igc = m.group(1), m.group(2)
        tag = "" if (cs, igc) == ("319", "8") else \
            "  (differs from the diagnosed 319/8 -- different DB?)"
        print("INFO: NEO SUBSIG SEED demand cs=%s igc=%s%s"
              % (cs, igc, tag))
    else:
        print("INFO: no NEO SUBSIG SEED line yet")

    # 5. other panics (coverage: silence is not success)
    if other and not fail:
        print("FAIL: %d unrelated panic line(s), last:" % len(other))
        print("      %s" % other[-1].strip())
        fail = True

    # 6. later-stage markers, informational
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
