#!/usr/bin/env python3
"""bisect_job3.py -- isolate the job-3 BATCH-PROOF-VERIFICATION failure.

Drives the retargeted `full_debug` test (zkp_driver.rs): each trial scans an
explicit slice of job 3's file list (binexec_p3.dat) via the ZKR_DBG_LIST env
var, under the FAITHFUL full_clamav config (full SNARK, one proof). The batch
self-verify does NOT abort on failure -- it logs an ERROR and finishes -- so
the oracle is grep-based, not exit-code based.

Strategy: binary search (the single-file hypothesis) that auto-escalates to
delta-debugging (ddmin) + a size-threshold probe when "neither half reproduces
but the whole does", i.e. when the fault is NOT a single file but an
aggregate/interaction across job 3's corpus.

ALL temp/config artifacts live under /tmp/bora/bisec. On exit (always, even on
OOM-halt / budget-exceeded / panic) the whole session -- audit.json,
verify_results.log, state.json, job3_master.txt, and every trial log + slice --
is packed into /tmp/bisect_job3.tgz (literal name, overwritten each run).

Oracle (checked in this order):
  OOM-HALT  child SIGKILL(-9/137), or SIGABRT(-6/134)+alloc-failed marker,
            or OOM log markers  -> STOP EVERYTHING (move to the 1TB box;
            re-run the same command to resume).
  FAIL      log has 'BATCH PROOF VERIFICATION FAILED'
  PASS      run_complete.sentinel rewritten, no FAIL line, no OOM
  UNRESOLVED  anything else (build err / unrelated panic / timeout): retry once

Usage:
  python3 bisect_job3.py                 # full run (auto-detects proj_root)
  python3 bisect_job3.py --rebuild       # force-rebuild the test binary
  python3 bisect_job3.py --max-trials 40 --timeout 21600
  python3 bisect_job3.py --proj-root /abs/path/to/new_zkregplus
Resume: just re-run the identical command -- settled subsets are skipped;
OOM-marked subsets are retried (use this after switching to the 1TB server).
"""

import argparse, json, os, random, re, subprocess, sys, tarfile, time
from hashlib import sha1
from pathlib import Path

# ----------------------------------------------------------------------------
# constants / paths
# ----------------------------------------------------------------------------
BISEC      = Path("/tmp/bora/bisec")
SLICES     = BISEC / "slices"
LOGS       = BISEC / "logs"
AUDIT      = BISEC / "audit.json"
STATE      = BISEC / "state.json"
VERIFY_LOG = BISEC / "verify_results.log"
MASTER     = BISEC / "job3_master.txt"

# single bundle of the whole session, ALWAYS rewritten on exit (finally), so an
# OOM-halt / budget-exceeded / panic still leaves one artifact. Literal name.
PACK_TGZ   = "/tmp/bisect_job3.tgz"
PACK_ITEMS = [AUDIT, STATE, VERIFY_LOG, MASTER, SLICES, LOGS]

TEST_FILTER = "zkp_driver::tests_zkp_driver::test_full_debug_main"
PKG         = "zkregplus"

REL_BINEXEC  = "data/debug/full_clamav/config/binexec_p3.dat"
REL_SENTINEL = "data/cache/run_complete.sentinel"
REL_JOBLOG   = "data/cache/logs/log_job_0.txt"
REL_KEYDIR   = "data/cache/full_data"
KEY_FILES = ["g16_main.key", "g16_main.key.meta", "g16_cp.key",
             "g16_cp.key.meta", "g16_main.sidecar.cf", "g16_cp.sidecar.cf",
             "g16_cp.sidecar.cp"]

FAIL_MARK = "BATCH PROOF VERIFICATION FAILED"
# ordered: which boolean sub-check inside verify_batch returned false
SUBCHECKS = [
    ("fs challenge (ch/rc) mismatch",  "fs_challenge_mismatch"),
    ("qa_nizk verif fails",            "qa_nizk"),
    ("kzg verif fails",                "kzg_agg"),
    ("cs1e kzg_all_ocm1 verif fails",  "cs1e_com1"),
    ("cs1e kzg_all_com2 res2 fails",   "cs1e_com2"),
    ("qanizk2 fails",                  "qa_nizk2"),
    ("snark main fails.",              "snark_main"),
    ("snark_v_cp fails.",              "snark_cp"),
]
DETAIL_PREFIXES = ("snark main details:", "snark_v_cp details:",
                   "DEBUG USE 6901.2.0 public input:", "ZKR_DBG_LIST override:")
OOM_MARKS = ["memory allocation of", "out of memory", "cannot allocate memory",
             "killed process", "oom-kill", "oom_kill", "oom killer"]
ALLOC_FAIL_MARK = "memory allocation of"   # mimalloc / rust alloc abort

# verdicts
OOM, FAIL, PASS, UNRES = "OOM", "FAIL", "PASS", "UNRESOLVED"


class OOMHalt(Exception):
    def __init__(self, indices, key, peak):
        self.indices, self.key, self.peak = indices, key, peak


class BudgetExceeded(Exception):
    pass


# ----------------------------------------------------------------------------
# small utilities
# ----------------------------------------------------------------------------
def log(msg):
    print(f"[bisect {time.strftime('%H:%M:%S')}] {msg}", flush=True)


def loud(lines):
    bar = "#" * 70
    print("\n" + bar, flush=True)
    for ln in lines:
        print("##  " + ln, flush=True)
    print(bar + "\n", flush=True)


def subset_key(indices):
    s = ",".join(str(i) for i in sorted(indices))
    return sha1(s.encode()).hexdigest()[:12]


def find_proj_root(explicit):
    if explicit:
        p = Path(explicit).resolve()
        if not (p / REL_BINEXEC).exists():
            sys.exit(f"--proj-root {p} has no {REL_BINEXEC}")
        return p
    # walk up from this script and from cwd for the dir that holds binexec_p3
    starts = [Path(__file__).resolve().parent, Path.cwd().resolve()]
    seen = set()
    for start in starts:
        for d in [start, *start.parents]:
            if d in seen:
                continue
            seen.add(d)
            if (d / REL_BINEXEC).exists():
                return d
    sys.exit("could not auto-detect proj_root (no ancestor has "
             f"{REL_BINEXEC}); pass --proj-root")


def pack_session():
    """Bundle the whole bisect session (audit, summaries, every trial log and
    slice) into PACK_TGZ. ALWAYS runs from main's finally -- an OOM-halt,
    budget-exceeded, or panic still leaves a single artifact. Overwrites the
    literal PACK_TGZ each run; directories (slices/, logs/) recurse."""
    try:
        with tarfile.open(PACK_TGZ, "w:gz") as t:
            for p in PACK_ITEMS:
                if p.exists():
                    t.add(p, arcname=p.name)
        log(f"packed session -> {PACK_TGZ}")
    except Exception as e:
        log(f"WARN: could not pack session: {e}")


# ----------------------------------------------------------------------------
# build / preflight
# ----------------------------------------------------------------------------
def build_test_binary(proj_root, rebuild):
    if STATE.exists() and not rebuild:
        st = json.loads(STATE.read_text())
        exe = st.get("exe")
        if exe and Path(exe).exists():
            log(f"reusing test binary {exe}")
            return exe
    log("building test binary (cargo test --no-run) ...")
    cmd = ["cargo", "test", "-p", PKG, "--release", "--lib", "--no-run",
           "--message-format=json"]
    proc = subprocess.run(cmd, cwd=proj_root, capture_output=True, text=True)
    if proc.returncode != 0:
        sys.stderr.write(proc.stderr[-4000:])
        sys.exit("cargo build failed")
    exe = None
    for line in proc.stdout.splitlines():
        try:
            obj = json.loads(line)
        except json.JSONDecodeError:
            continue
        if obj.get("reason") != "compiler-artifact":
            continue
        tgt = obj.get("target", {})
        if obj.get("executable") and tgt.get("name") == PKG \
                and "lib" in tgt.get("kind", []):
            exe = obj["executable"]
    if not exe or not Path(exe).exists():
        sys.exit("could not locate the zkregplus lib test binary")
    STATE.write_text(json.dumps({"exe": exe, "proj_root": str(proj_root)},
                                indent=2))
    log(f"test binary: {exe}")
    return exe


def preflight_keys(proj_root):
    kd = proj_root / REL_KEYDIR
    missing = [f for f in KEY_FILES if not (kd / f).exists()]
    if missing:
        # Don't abort: the driver auto-flips to build + persist the keys
        # on the first run (full_debug's cold-cache path). The FIRST trial
        # therefore pays a multi-hour fold + keygen once; all later trials
        # reuse the persisted keys. Warn loudly so the long trial 1 is
        # expected (and beware OOM on a small box).
        loud([f"SNARK KEYS MISSING under {kd}",
              f"missing: {missing}",
              "NOT aborting -- the first trial will auto-build + persist",
              "them (multi-hour fold + keygen, one time). Later trials",
              "reuse them. Watch trial 1 for OOM on a small box."])
        return
    log(f"snark keys present under {kd}")


def load_master(proj_root):
    src = proj_root / REL_BINEXEC
    raw = src.read_text().splitlines()
    files = [ln for ln in raw if ln.strip() != ""]   # drop blank lines
    MASTER.write_text("\n".join(f"{i}\t{p}" for i, p in enumerate(files))
                      + "\n")
    log(f"job-3 master list: {len(files)} files "
        f"({len(raw)-len(files)} blank lines dropped) -> {MASTER}")
    return files


# ----------------------------------------------------------------------------
# trial runner + oracle
# ----------------------------------------------------------------------------
class Runner:
    def __init__(self, proj_root, exe, master, timeout, max_trials):
        self.proj_root = proj_root
        self.exe = exe
        self.master = master
        self.timeout = timeout
        self.max_trials = max_trials
        self.sentinel = proj_root / REL_SENTINEL
        self.joblog = proj_root / REL_JOBLOG
        self.audit = json.loads(AUDIT.read_text()) if AUDIT.exists() else {}
        self.n_runs = 0

    def _classify(self, rc, log_text, joblog_text):
        low = log_text.lower()
        oom = (rc in (-9, 137)
               or (rc in (-6, 134) and ALLOC_FAIL_MARK in log_text)
               or any(m in low for m in OOM_MARKS))
        if oom:
            return OOM
        if FAIL_MARK in log_text or FAIL_MARK in joblog_text:
            return FAIL
        if self.sentinel.exists():
            return PASS
        return UNRES

    def _scan_markers(self, log_text):
        sub = None
        for mark, name in SUBCHECKS:
            if mark in log_text:
                sub = name
                break
        details = [ln.strip() for ln in log_text.splitlines()
                   if ln.strip().startswith(DETAIL_PREFIXES)]
        return sub, details[-6:]

    def _record(self, key, indices, verdict, sub, details, secs, logpath):
        rec = {"key": key, "size": len(indices), "verdict": verdict,
               "subcheck": sub, "details": details, "secs": round(secs, 1),
               "indices": sorted(indices), "log": str(logpath)}
        self.audit[key] = rec
        AUDIT.write_text(json.dumps(self.audit, indent=1))
        with VERIFY_LOG.open("a") as f:
            f.write(f"trial={key} size={len(indices)} verdict={verdict} "
                    f"subcheck={sub} secs={rec['secs']} "
                    f"details={details} idx={sorted(indices)[:8]}"
                    f"{'...' if len(indices) > 8 else ''}\n")
        return rec

    def run(self, indices):
        """Return verdict string. Raises OOMHalt / BudgetExceeded."""
        indices = sorted(set(indices))
        key = subset_key(indices)
        cached = self.audit.get(key)
        if cached and cached["verdict"] != OOM:
            return cached["verdict"]          # resume: skip settled
        if self.n_runs >= self.max_trials:
            raise BudgetExceeded()
        self.n_runs += 1

        # write the slice list (verbatim paths, one per line, no blanks)
        slice_path = SLICES / f"slice_{key}.dat"
        slice_path.write_text("\n".join(self.master[i] for i in indices)
                              + "\n")
        # pre-run cleanup so a stale sentinel / joblog can't cause a misread
        for p in (self.sentinel, self.joblog):
            try:
                p.unlink()
            except FileNotFoundError:
                pass

        logpath = LOGS / f"trial_{key}.log"
        env = dict(os.environ, ZKR_DBG_LIST=str(slice_path))
        cmd = [self.exe, TEST_FILTER, "--exact", "--nocapture",
               "--test-threads=1"]
        log(f"trial {key}: size={len(indices)} -> running ...")
        t0 = time.time()
        rc, timed_out = self._spawn(cmd, env, logpath)
        secs = time.time() - t0

        log_text = self._read(logpath)
        joblog_text = self._read(self.joblog)
        verdict = UNRES if timed_out else \
            self._classify(rc, log_text, joblog_text)
        sub, details = self._scan_markers(log_text)
        self._record(key, indices, verdict, sub, details, secs, logpath)

        if verdict == OOM:
            peak = self._peak_rss_hint(log_text)
            self._record(key, indices, OOM, sub, details, secs, logpath)
            raise OOMHalt(indices, key, peak)
        if verdict == FAIL:
            loud([f"TRIAL {key}  FAIL  (rc={rc}, {secs:.0f}s)",
                  f"SUBCHECK: {sub or 'UNKNOWN (no marker -- check log!)'}",
                  f"slice size = {len(indices)}",
                  *[f"detail: {d}" for d in details]])
        else:
            log(f"trial {key}: {verdict} ({secs:.0f}s)")

        # one retry for UNRESOLVED (transient), then accept
        if verdict == UNRES and not timed_out and not cached:
            log(f"trial {key}: UNRESOLVED -> one retry")
            return self._retry(indices, key)
        return verdict

    def _retry(self, indices, key):
        for p in (self.sentinel, self.joblog):
            try:
                p.unlink()
            except FileNotFoundError:
                pass
        slice_path = SLICES / f"slice_{key}.dat"
        logpath = LOGS / f"trial_{key}_retry.log"
        env = dict(os.environ, ZKR_DBG_LIST=str(slice_path))
        cmd = [self.exe, TEST_FILTER, "--exact", "--nocapture",
               "--test-threads=1"]
        t0 = time.time()
        rc, timed_out = self._spawn(cmd, env, logpath)
        secs = time.time() - t0
        log_text = self._read(logpath)
        joblog_text = self._read(self.joblog)
        verdict = UNRES if timed_out else \
            self._classify(rc, log_text, joblog_text)
        sub, details = self._scan_markers(log_text)
        self._record(key, indices, verdict, sub, details, secs, logpath)
        if verdict == OOM:
            raise OOMHalt(indices, key, self._peak_rss_hint(log_text))
        if verdict == FAIL:
            loud([f"TRIAL {key}  FAIL (on retry)  (rc={rc}, {secs:.0f}s)",
                  f"SUBCHECK: {sub or 'UNKNOWN (no marker -- check log!)'}",
                  f"slice size = {len(indices)}",
                  *[f"detail: {d}" for d in details]])
        elif verdict == PASS:
            log(f"trial {key}: retry settled -> PASS")
        else:
            log(f"trial {key}: still UNRESOLVED -> treating as not-FAIL "
                f"(bisection floor)")
        return verdict

    def _spawn(self, cmd, env, logpath):
        with logpath.open("wb") as out:
            proc = subprocess.Popen(cmd, cwd=self.proj_root, env=env,
                                    stdout=out, stderr=subprocess.STDOUT)
            try:
                rc = proc.wait(timeout=self.timeout)
                return rc, False
            except subprocess.TimeoutExpired:
                proc.kill()
                proc.wait()
                log(f"  TIMEOUT after {self.timeout}s -> killed")
                return proc.returncode, True

    @staticmethod
    def _read(path):
        try:
            return Path(path).read_text(errors="replace")
        except FileNotFoundError:
            return ""

    @staticmethod
    def _peak_rss_hint(log_text):
        peaks = re.findall(r"MEM[^\n]*?(\d+)\s*GB", log_text)
        return max((int(x) for x in peaks), default=None)


# ----------------------------------------------------------------------------
# search: binary search -> ddmin / threshold probe
# ----------------------------------------------------------------------------
def split(L, n):
    n = min(n, len(L))
    k, m = divmod(len(L), n)
    out, i = [], 0
    for j in range(n):
        sz = k + (1 if j < m else 0)
        out.append(L[i:i + sz])
        i += sz
    return [c for c in out if c]


def ddmin(run, L):
    """Canonical delta-debugging; returns a 1-minimal FAILing subset."""
    L = list(L)
    n = 2
    while len(L) >= 2:
        chunks = split(L, n)
        hit = next((c for c in chunks if run.run(c) == FAIL), None)
        if hit is not None:                       # reduce to subset
            L, n = hit, 2
            continue
        comp_hit = None
        if n > 2:                                 # complements (n==2 redundant)
            for c in chunks:
                cs = set(c)
                comp = [x for x in L if x not in cs]
                if comp and run.run(comp) == FAIL:
                    comp_hit = comp
                    break
        if comp_hit is not None:                  # reduce to complement
            L, n = comp_hit, max(n - 1, 2)
            continue
        if n >= len(L):
            break
        n = min(len(L), n * 2)
    return L


def threshold_probe(run, L):
    """Neither half of L FAILs but L does. Locate the minimal failing SIZE K
    via size-bisection over random subsets, then confirm with a second
    independent random subset of size K. Returns (K, is_aggregate)."""
    lo, hi = len(L) // 2, len(L)                  # half passed, full fails
    while lo + 1 < hi:
        mid = (lo + hi) // 2
        if run.run(random.sample(L, mid)) == FAIL:
            hi = mid
        else:
            lo = mid
    K = hi
    if K >= len(L):
        return K, True                            # needs essentially all
    confirm = run.run(random.sample(L, K)) == FAIL
    return K, confirm                             # two random size-K both fail


def localize(run, indices):
    """Binary search with ddmin / threshold escalation.
    Returns (result_indices, classification:str, extra:dict)."""
    L = list(indices)
    while len(L) > 1:
        half = len(L) // 2
        A, B = L[:half], L[half:]
        if run.run(A) == FAIL:        # culprit in first half
            L = A
            continue
        if run.run(B) == FAIL:        # culprit in second half
            L = B
            continue
        # neither half FAILs but L does -> single-file conjecture REFUTED
        loud(["SINGLE-FILE CONJECTURE REFUTED",
              f"set of {len(L)} files FAILs, but neither half does.",
              "running size-threshold probe ..."])
        K, aggregate = threshold_probe(run, L)
        if aggregate:
            return L, "aggregate", {"threshold_size": K}
        log(f"threshold not size-uniform (K={K}); running ddmin for the "
            "minimal interacting set")
        minimal = ddmin(run, L)
        return minimal, ("single" if len(minimal) == 1 else "interaction"), \
            {"threshold_size": K}
    return L, ("single" if len(L) == 1 else "empty"), {}


# ----------------------------------------------------------------------------
# main
# ----------------------------------------------------------------------------
def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--proj-root", default=None)
    ap.add_argument("--rebuild", action="store_true")
    ap.add_argument("--timeout", type=int, default=21600,
                    help="per-trial timeout seconds (default 6h)")
    ap.add_argument("--max-trials", type=int, default=60)
    ap.add_argument("--seed", type=int, default=0)
    args = ap.parse_args()

    random.seed(args.seed)
    for d in (BISEC, SLICES, LOGS):
        d.mkdir(parents=True, exist_ok=True)

    proj_root = find_proj_root(args.proj_root)
    log(f"proj_root = {proj_root}")
    preflight_keys(proj_root)
    exe = build_test_binary(proj_root, args.rebuild)
    master = load_master(proj_root)
    if not master:
        sys.exit("job-3 list is empty")

    run = Runner(proj_root, exe, master, args.timeout, args.max_trials)
    full = list(range(len(master)))

    try:
        # 1. baseline: the full job-3 corpus must reproduce in isolation
        log("baseline: confirming full job-3 list FAILs in isolation ...")
        base = run.run(full)
        if base != FAIL:
            loud(["BASELINE DID NOT REPRODUCE",
                  f"full job-3 ({len(full)} files) verdict = {base}",
                  "The batch-verify failure is NOT isolable to job 3 alone",
                  "(needs the real 8-job concurrency / memory footprint, or",
                  "it is environmental). Nothing to bisect."])
            return
        loud([f"baseline FAIL confirmed on {len(full)} files",
              f"subcheck = {run.audit[subset_key(full)]['subcheck']}"])

        # 2. localize
        result, kind, extra = localize(run, full)

    except OOMHalt as e:
        loud(["OOM-HALT  (passive detection on the 512GB box)",
              f"subset key={e.key} size={len(e.indices)} OOMed"
              + (f", peak~{e.peak} GB" if e.peak else ""),
              "This subset's FAIL/PASS is UNKNOWN -> stopping.",
              "Move to the 1TB server and re-run the SAME command;",
              "settled trials are skipped, this OOM subset is retried.",
              f"audit: {AUDIT}"])
        sys.exit(3)
    except BudgetExceeded:
        loud([f"max-trials ({args.max_trials}) exhausted -- stopping.",
              "raise --max-trials to continue; progress is saved/resumable.",
              f"audit: {AUDIT}"])
        sys.exit(4)
    finally:
        pack_session()

    # 3. report (the result set was already tested during localize, so its
    # verdict is cached -- read it, don't risk another expensive run here)
    confirm = run.audit.get(subset_key(result), {}).get("verdict", "?")
    files = [master[i] for i in sorted(result)]
    if kind == "single":
        loud(["RESULT: SINGLE-FILE FAULT",
              f"culprit (idx {sorted(result)[0]}): {files[0]}",
              f"reconfirm = {confirm}"])
    elif kind == "interaction":
        loud(["RESULT: INTERACTION FAULT (minimal failing set)",
              f"{len(files)} files must be present together:",
              *[f"  idx {i}: {master[i]}" for i in sorted(result)],
              f"reconfirm = {confirm}"])
    elif kind == "aggregate":
        loud(["RESULT: AGGREGATE / THRESHOLD FAULT",
              f"needs ~{extra.get('threshold_size')} of job 3's "
              f"{len(full)} files; NOT a specific file.",
              "Two independent random subsets of that size both FAIL.",
              "Likely a whole-corpus accumulation (e.g. lookup-share /",
              "batch-aggregation budget), not a single bad sample."])
    else:
        loud([f"RESULT: {kind}", f"set = {sorted(result)}"])

    log(f"done in {run.n_runs} trials. audit={AUDIT} verify_log={VERIFY_LOG}")


if __name__ == "__main__":
    main()
