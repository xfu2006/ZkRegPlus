#!/usr/bin/env python3
# verify_logs.py -- sanity-check per-job log isolation after the
# 2026-05-15 set_job_id-propagation fix.
#
# Run from zkregplus/src/ (no args defaults to ../../data/cache/logs).
#
# What it checks
# --------------
# 1. Existence + size of each log_job_<N>.txt under the logs dir.
# 2. Canary line counts in each per-job log. Before the fix these
#    lines all collapsed onto log_job_0.txt; after the fix every
#    job >= 1 must have a non-zero count.
# 3. Wrong-tag detection: any "[job J]" line inside log_job_K.txt
#    with J != K would mean the logger or a caller mis-routed.
# 4. Structural diff: lines present in log_job_0.txt but absent
#    from every other per-job log (after normalising away the
#    [job N] tag and numeric/timing noise). Each diff line is
#    classified as SETUP (pre-job-loop one-offs, ignored) or
#    HOT (gen_step_cs / gen_witness / build_stmt / Pass / etc.,
#    the region close to the STALL). HOT diffs are printed in
#    full so they can be re-investigated.
#
# Exit code 0 if all canaries non-zero in every job AND no HOT
# diffs unique to job 0.  Non-zero otherwise.

import argparse, os, re, sys
from collections import defaultdict
from pathlib import Path

# ---- dependency check -------------------------------------------
# verify_logs.py is stdlib-only. No external CLI tools or pip deps.
# Only requirement is a readable per-job log directory; that is
# checked again inside main() with a user-readable error.
_PY_MIN = (3, 6)
if sys.version_info < _PY_MIN:
    sys.exit(f"ERR: verify_logs.py needs Python >= {_PY_MIN[0]}."
             f"{_PY_MIN[1]}; got {sys.version_info[:3]}")

# ---- normalisation ----------------------------------------------
JOB_TAG_RE = re.compile(r'^\[job \d+\]\s*')
HEX_RE     = re.compile(r'0x[0-9a-fA-F]+')
TIME_RE    = re.compile(r'\s+\d+(\.\d+)?\s*(ms|us|s|ns|ks)\b')
NUM_RE     = re.compile(r'\b\d+\b')

def normalize(line: str) -> str:
    s = line.rstrip('\n')
    s = JOB_TAG_RE.sub('', s)
    s = HEX_RE.sub('<H>', s)
    s = TIME_RE.sub(' <T>', s)
    s = NUM_RE.sub('<N>', s)
    return s

# ---- canary phrases (must appear in every per-job log) ----------
CANARIES = [
    "### gen_step_cs START",
    "gen_witness step 3.1",
    "gen_witness step 4",
    "gen_witness step 11",
    "## build_stmt: CP",
    "## CP mapper data len",
    # SED / DFA only fire on circuits where the mapper is wired in
    # -- treated as "expected in some jobs" rather than hard fail.
]
SOFT_CANARIES = [
    "## build_stmt: SED",
    "## build_stmt: DFA",
    "## dfa gadgets data len",
]

# ---- classification keywords ------------------------------------
# A line that hits HOT_KEYS is in the gen_witness / gen_step_cs
# / prove_step region -- "close to STALL". If unique to job 0
# this is a routing bug.
HOT_KEYS = (
    "gen_step_cs", "gen_witness step", "build_stmt",
    "circuit_super gen_cs step", "prove_step:",
    "Pass 1.", "Pass 2.", "Pass 3.",
    "Generate Advice", "after msg3",
    "CP mapper data len", "dfa gadgets data len",
    "advice step",
)
# A line that hits SETUP_KEYS is a pre-job-loop one-off; OK to be
# unique to job 0.
SETUP_KEYS = (
    "Driver New", "preprocess(", "ZIP driver step",
    "ZKP driver starts", "KEYS info",
    "PERF 1001", "PERF 1002", "PERF 1003",
    "PERF 1004", "PERF 1005",
    "build_circs", "setup_qa", "fold_pot starts",
    "load DB", "vec_pp", "cs1e_pp", "qa_pp", "vec_F",
    "Statement Total Size",  # one-shot config printer
    "WITNESS structure",     # one-shot config printer
)

def classify(s: str) -> str:
    for k in HOT_KEYS:
        if k in s: return "HOT"
    for k in SETUP_KEYS:
        if k in s: return "SETUP"
    return "OTHER"

WRONG_TAG_RE = re.compile(r'\[job (\d+)\]')

# ---- main -------------------------------------------------------
def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--logs-dir", default=None,
        help="path to log_job_*.txt dir (default: ../../data/cache/logs)")
    ap.add_argument("--max-hot-print", type=int, default=20)
    ap.add_argument("--max-other-print", type=int, default=5)
    args = ap.parse_args()

    here = Path(__file__).resolve().parent
    logs_dir = (Path(args.logs_dir).resolve() if args.logs_dir
        else (here.parent.parent / "data" / "cache" / "logs").resolve())
    if not logs_dir.is_dir():
        print(f"ERR: logs dir not found: {logs_dir}", file=sys.stderr)
        return 2

    files = sorted(
        logs_dir.glob("log_job_*.txt"),
        key=lambda p: int(re.match(r"log_job_(\d+)\.txt", p.name).group(1))
    )
    if not files:
        print(f"ERR: no log_job_*.txt files in {logs_dir}", file=sys.stderr)
        return 2

    print(f"== Per-job log isolation check ({len(files)} files) ==")
    print(f"   dir: {logs_dir}")
    print()

    # 1. sizes
    print("== Sizes ==")
    for f in files:
        sz = f.stat().st_size
        print(f"  {f.name:24s}  {sz:>12d} bytes")
    print()

    # 2. canaries
    print("== Canary counts (HARD: must be > 0 in every job after fix) ==")
    fail_canary = False
    contents = {f.name: f.read_text(errors='replace') for f in files}
    header = "  " + f"{'canary':50s} " + " ".join(
        f"{f.name:>17s}" for f in files)
    print(header)
    for c in CANARIES:
        row_counts = [contents[f.name].count(c) for f in files]
        bad = any(rc == 0 for rc in row_counts)
        if bad: fail_canary = True
        marker = "  <- FAIL" if bad else ""
        row = "  " + f"{c:50s} " + " ".join(
            f"{n:>17d}" for n in row_counts) + marker
        print(row)
    print()
    print("== Soft canaries (informational, OK if 0 in some jobs) ==")
    for c in SOFT_CANARIES:
        row = "  " + f"{c:50s} " + " ".join(
            f"{contents[f.name].count(c):>17d}" for f in files)
        print(row)
    print()

    # 3. wrong-tag
    print("== Wrong-tag detection ==")
    any_wrong = False
    for f in files:
        m = re.match(r"log_job_(\d+)\.txt", f.name)
        expected = int(m.group(1))
        wrong = 0
        with f.open() as fh:
            for line in fh:
                mm = WRONG_TAG_RE.match(line)
                if mm and int(mm.group(1)) != expected:
                    wrong += 1
        if wrong:
            any_wrong = True
            print(f"  {f.name}: {wrong} lines have [job J] J != {expected} <- FAIL")
        else:
            print(f"  {f.name}: clean")
    print()

    # 4. structural diff -- lines unique to job 0 after normalisation
    print("== Structural diff: lines present only in log_job_0 ==")
    fail_hot = False
    if len(files) < 2:
        print("  skip (need >= 2 jobs)")
    else:
        sets = {}
        for f in files:
            with f.open(errors='replace') as fh:
                sets[f.name] = set(normalize(l) for l in fh)
        job0 = files[0].name
        others = set().union(*(sets[f.name] for f in files[1:]))
        only_in_0 = sets[job0] - others
        buckets = defaultdict(list)
        for ln in only_in_0:
            buckets[classify(ln)].append(ln)
        print(f"  total unique-to-job-0 lines: {len(only_in_0)}")
        for k in ("SETUP", "HOT", "OTHER"):
            print(f"  {k}: {len(buckets[k])}")
        print()
        if buckets["HOT"]:
            fail_hot = True
            print("  ** HOT-PATH unique-to-job-0 lines (close to STALL):")
            for ln in sorted(buckets["HOT"])[:args.max_hot_print]:
                print("    " + ln[:160])
            extra = len(buckets["HOT"]) - args.max_hot_print
            if extra > 0:
                print(f"    ... ({extra} more)")
        if buckets["OTHER"]:
            print()
            print("  OTHER unique-to-job-0 sample (informational):")
            for ln in sorted(buckets["OTHER"])[:args.max_other_print]:
                print("    " + ln[:160])

    print()
    ok = (not fail_canary) and (not any_wrong) and (not fail_hot)
    print("== RESULT: " + ("PASS" if ok else "FAIL") + " ==")
    return 0 if ok else 1

if __name__ == "__main__":
    sys.exit(main())
