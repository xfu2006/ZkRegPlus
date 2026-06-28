#!/usr/bin/env python3
"""bisect_job3.py -- locate job 3's BATCH-PROOF-VERIFICATION failure by
8-way CONCURRENT bisection through the REAL multi-job runner.

The 2026-06-24 full_clam run aborted because job 3's `verify_batch` returned
false. full_clam runs 8 jobs (binexec_p0.dat..binexec_p7.dat) concurrently;
job_id 3 <-> binexec_p3.dat by construction. job_id is purely cosmetic
(logging only), so re-running job-3 content at any runtime id reproduces the
same proof/verify outcome.

Strategy (faithful real-runner, not the single-job test harness):
  * COPY binexec_p3.dat into our OWN folder data/debug/full_clam_bisect/config
    (the production full_clamav config is never written -- only read).
  * Each round, split the current failing file-set into N=8 shares
    (slice_0.dat..slice_{N-1}.dat in that folder), run the new Rust test
    `test_full_clam_bisect` ONCE -> 8 jobs prove+verify CONCURRENTLY (same
    config/capacities as full_clamav, cached g16 keys reused read-only).
  * The failing share's log_job_{id}.txt carries the FAIL marker -> recurse
    into that one eighth. Down to one file = the culprit.
  * SPLIT-FIRST: no lone-job baseline (it costs ~a full_clam() run but is the
    LESS faithful single-job context). Go straight to the 8-way split; a
    failing share both confirms reproduction AND localizes in one round.
  * NO share fails at round 1 -> QUIT and recommend re-running full_clam()
    (~same cost as a lone-job baseline but faithful + precise sub-check).
  * A DEEPER round all-passes (its parent share was confirmed failing) ->
    report that minimal failing set as aggregate/interaction within it.

The batch self-verify logs an ERROR and finishes (no assert/abort), so the
oracle is grep-based per log_job_{id}.txt, not exit-code based.

ALL working artifacts (audit/state/logs/pack) live under /tmp/bora/bisec; the
slices live in the repo's own bisect folder. On exit (always, even on
OOM/budget/panic) the session is packed into /tmp/bisect_job3.tgz.

Oracle (per run, checked in this order):
  OOM-HALT  child SIGKILL(-9/137) or SIGABRT(-6/134)+alloc marker or OOM logs
            -> STOP EVERYTHING (move to the 1TB box; re-run to resume).
  COMPLETED run_complete.sentinel rewritten, no OOM -> read per-share FAIL.
  UNRESOLVED  no sentinel and not OOM (build err / panic / timeout): retry once.

Usage:
  python3 bisect_job3.py                 # full run (auto-detects proj_root)
  python3 bisect_job3.py --rebuild       # force-rebuild the test binary
  python3 bisect_job3.py --fanout 8 --max-trials 40 --timeout 21600
  python3 bisect_job3.py --proj-root /abs/path/to/new_zkregplus
Resume: just re-run the identical command -- settled subsets are skipped;
OOM-marked subsets are retried (use this after switching to the 1TB server).
"""

import argparse, json, os, re, shutil, subprocess, sys, tarfile, time
from hashlib import sha1
from pathlib import Path

# ----------------------------------------------------------------------------
# constants / paths
# ----------------------------------------------------------------------------
BISEC      = Path("/tmp/bora/bisec")          # working area (audit/logs/pack)
LOGS       = BISEC / "logs"                    # per-trial captured stdout
AUDIT      = BISEC / "audit.json"
STATE      = BISEC / "state.json"
VERIFY_LOG = BISEC / "verify_results.log"
MASTER     = BISEC / "job3_master.txt"
SUMMARY    = BISEC / "result_summary.txt"   # final human-readable verdict
SESSION    = BISEC / "session_dump.txt"     # full 2>&1 console capture

# single bundle of the whole session, ALWAYS rewritten on exit (finally), so an
# OOM-halt / budget / panic still leaves one artifact. LOGS holds per-trial
# stdout AND snapshotted log_job_*.txt + slice_*.dat (purged each round).
PACK_TGZ   = "/tmp/bisect_job3.tgz"
PACK_ITEMS = [AUDIT, STATE, VERIFY_LOG, MASTER, SUMMARY, SESSION, LOGS]
REPORT_SNAPSHOT = None   # set in main to proj_root/REL_REPORT; packed if exists

TEST_FILTER = "zkp_driver::tests_zkp_driver::test_full_clam_bisect"
PKG         = "zkregplus"

# source = job 3's list (READ ONLY, copied into our own folder)
REL_BINEXEC  = "data/debug/full_clamav/config/binexec_p3.dat"
# our own folder: where slice_{i}.dat are written and ZKR_BISECT_DIR points
REL_BISECT_DIR = "data/debug/full_clam_bisect/config"
REL_REPORT_DIR = "data/debug/full_clam_bisect/reports"
REL_REPORT   = "data/debug/full_clam_bisect/reports/report2.dat"
REL_SENTINEL = "data/cache/run_complete.sentinel"
REL_JOBLOGDIR = "data/cache/logs"
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
                   "DEBUG USE 6901.2.0 public input:")
OOM_MARKS = ["memory allocation of", "out of memory", "cannot allocate memory",
             "killed process", "oom-kill", "oom_kill", "oom killer"]
ALLOC_FAIL_MARK = "memory allocation of"   # mimalloc / rust alloc abort

# run-level status
OOM, COMPLETED, UNRES = "OOM", "COMPLETED", "UNRESOLVED"


class OOMHalt(Exception):
    def __init__(self, indices, key, peak):
        self.indices, self.key, self.peak = indices, key, peak


class BudgetExceeded(Exception):
    pass


class Tee:
    """Duplicate every write to the real stream AND a file -- the in-process
    equivalent of `cmd 2>&1 | tee dump.txt`, so the full console session
    (every log line, loud banner, RESULT verdict) is saved for the pack."""
    def __init__(self, stream, fh):
        self.stream, self.fh = stream, fh

    def write(self, s):
        self.stream.write(s)
        self.fh.write(s)

    def flush(self):
        self.stream.flush()
        self.fh.flush()


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


def subset_key(indices, n):
    s = ",".join(str(i) for i in sorted(indices)) + f"|n{n}"
    return sha1(s.encode()).hexdigest()[:12]


def split(L, n):
    """Split list L into n contiguous-ish non-empty shares."""
    n = min(n, len(L))
    k, m = divmod(len(L), n)
    out, i = [], 0
    for j in range(n):
        sz = k + (1 if j < m else 0)
        out.append(L[i:i + sz])
        i += sz
    return [c for c in out if c]


def find_proj_root(explicit):
    if explicit:
        p = Path(explicit).resolve()
        if not (p / REL_BINEXEC).exists():
            sys.exit(f"--proj-root {p} has no {REL_BINEXEC}")
        return p
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
    """Bundle the whole bisect session into PACK_TGZ. ALWAYS runs from main's
    finally -- an OOM-halt / budget / panic still leaves one artifact."""
    try:
        items = list(PACK_ITEMS)
        if REPORT_SNAPSHOT is not None:
            items.append(REPORT_SNAPSHOT)
        with tarfile.open(PACK_TGZ, "w:gz") as t:
            for p in items:
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
        loud([f"SNARK KEYS MISSING under {kd}",
              f"missing: {missing}",
              "NOT aborting -- the first run will auto-build + persist them",
              "(multi-hour fold + keygen, one time). Later runs reuse them.",
              "Watch the first trial for OOM on a small box."])
        return
    log(f"snark keys present under {kd}")


def load_master(proj_root):
    """Copy binexec_p3.dat into our own folder and return its file list."""
    src = proj_root / REL_BINEXEC
    raw = src.read_text().splitlines()
    files = [ln for ln in raw if ln.strip() != ""]   # drop blank lines
    bdir = proj_root / REL_BISECT_DIR
    bdir.mkdir(parents=True, exist_ok=True)
    (proj_root / REL_REPORT_DIR).mkdir(parents=True, exist_ok=True)
    # our own master copy (never touches the production config)
    (bdir / "binexec_p3_master.dat").write_text("\n".join(files) + "\n")
    MASTER.write_text("\n".join(f"{i}\t{p}" for i, p in enumerate(files))
                      + "\n")
    log(f"job-3 master list: {len(files)} files "
        f"({len(raw)-len(files)} blank lines dropped) -> copied into {bdir}")
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
        self.bisect_dir = proj_root / REL_BISECT_DIR
        self.sentinel = proj_root / REL_SENTINEL
        self.joblogdir = proj_root / REL_JOBLOGDIR
        self.audit = json.loads(AUDIT.read_text()) if AUDIT.exists() else {}
        self.n_runs = 0

    def joblog(self, i):
        return self.joblogdir / f"log_job_{i}.txt"

    def _is_oom(self, rc, log_text):
        low = log_text.lower()
        return (rc in (-9, 137)
                or (rc in (-6, 134) and ALLOC_FAIL_MARK in log_text)
                or any(m in low for m in OOM_MARKS))

    def _scan_subcheck(self, log_text):
        for mark, name in SUBCHECKS:
            if mark in log_text:
                return name
        return None

    def _record(self, key, indices, n, status, shares, failing, secs, logp):
        rec = {"key": key, "size": len(indices), "n": n, "status": status,
               "failing": {str(i): {"sub": sub, "indices": shares[i]}
                           for i, sub in failing.items()},
               "secs": round(secs, 1), "indices": sorted(indices),
               "log": str(logp)}
        self.audit[key] = rec
        AUDIT.write_text(json.dumps(self.audit, indent=1))
        with VERIFY_LOG.open("a") as f:
            f.write(f"trial={key} size={len(indices)} n={n} status={status} "
                    f"failing_shares={sorted(failing)} "
                    f"subchecks={[failing[i] for i in sorted(failing)]} "
                    f"secs={rec['secs']}\n")
        return rec

    def _spawn(self, env, logpath):
        cmd = [self.exe, TEST_FILTER, "--exact", "--nocapture",
               "--test-threads=1"]
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

    def _snapshot(self, stem):
        """Copy this trial's per-job logs + slice lists into LOGS (which is
        packed) before the next round purges them, tagged by the trial stem."""
        for jl in sorted(self.joblogdir.glob("log_job_*.txt")):
            try:
                shutil.copy2(jl, LOGS / f"{stem}_{jl.name}")
            except Exception:
                pass
        for sl in sorted(self.bisect_dir.glob("slice_*.dat")):
            try:
                shutil.copy2(sl, LOGS / f"{stem}_{sl.name}")
            except Exception:
                pass

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

    def _do_run(self, shares, n, logpath):
        """Write slice_*.dat, run ONE n-job batch, return (status, failing)."""
        # purge stale per-job logs + sentinel + old slices so we never misread
        for old in self.joblogdir.glob("log_job_*.txt"):
            try:
                old.unlink()
            except FileNotFoundError:
                pass
        for old in self.bisect_dir.glob("slice_*.dat"):
            try:
                old.unlink()
            except FileNotFoundError:
                pass
        try:
            self.sentinel.unlink()
        except FileNotFoundError:
            pass
        for i, sh in enumerate(shares):
            (self.bisect_dir / f"slice_{i}.dat").write_text(
                "\n".join(self.master[k] for k in sh) + "\n")
        env = dict(os.environ, ZKR_BISECT_DIR=str(self.bisect_dir),
                   ZKR_BISECT_NJOBS=str(n))
        rc, timed_out = self._spawn(env, logpath)
        main_log = self._read(logpath)
        self._snapshot(logpath.stem)   # preserve job logs + slices for the pack
        if self._is_oom(rc, main_log):
            return OOM, {}
        if timed_out or not self.sentinel.exists():
            return UNRES, {}
        failing = {}
        for i in range(n):
            jl = self._read(self.joblog(i))
            if FAIL_MARK in jl or f"Job {i} {FAIL_MARK}" in main_log:
                failing[i] = self._scan_subcheck(jl) or \
                    self._scan_subcheck(main_log)
        return COMPLETED, failing

    def run_shares(self, indices, n):
        """Split `indices` into n shares, run the real n-job batch.
        Returns (status, shares, failing{share_idx: subcheck}).
        Raises OOMHalt / BudgetExceeded."""
        indices = sorted(set(indices))
        n = min(n, len(indices))
        shares = split(indices, n)
        n = len(shares)
        key = subset_key(indices, n)
        cached = self.audit.get(key)
        if cached and cached["status"] != OOM:
            failing = {int(i): v["sub"]
                       for i, v in cached["failing"].items()}
            return cached["status"], shares, failing
        if self.n_runs >= self.max_trials:
            raise BudgetExceeded()
        self.n_runs += 1

        logpath = LOGS / f"trial_{key}.log"
        log(f"trial {key}: {len(indices)} files -> {n} shares, running ...")
        t0 = time.time()
        status, failing = self._do_run(shares, n, logpath)
        secs = time.time() - t0
        self._record(key, indices, n, status, shares, failing, secs, logpath)

        if status == OOM:
            peak = self._peak_rss_hint(self._read(logpath))
            raise OOMHalt(indices, key, peak)
        if status == UNRES and not cached:
            log(f"trial {key}: UNRESOLVED -> one retry")
            t0 = time.time()
            status, failing = self._do_run(shares, n,
                                           LOGS / f"trial_{key}_retry.log")
            secs = time.time() - t0
            self._record(key, indices, n, status, shares, failing, secs,
                         LOGS / f"trial_{key}_retry.log")
            if status == OOM:
                raise OOMHalt(indices, key,
                              self._peak_rss_hint(
                                  self._read(LOGS / f"trial_{key}_retry.log")))

        if failing:
            loud([f"TRIAL {key}  ({len(indices)} files / {n} shares, "
                  f"{secs:.0f}s)",
                  f"FAILING shares: {sorted(failing)}",
                  *[f"  share {i}: subcheck={failing[i]}, "
                    f"{len(shares[i])} files" for i in sorted(failing)]])
        else:
            log(f"trial {key}: all {n} shares PASS ({secs:.0f}s)")
        return status, shares, failing


# ----------------------------------------------------------------------------
# search: 8-way concurrent recursion
# ----------------------------------------------------------------------------
def localize_8way(run, indices, fanout):
    """Recurse: split into <=fanout shares, run concurrently, descend into the
    single failing share until it is one file. Returns (result, kind, extra).
    `confirmed` flips true once we descend into a share we OBSERVED failing, so
    an all-pass round can tell round-1 'no_repro' (quit -> full_clam) from a
    deeper 'aggregate' (interaction within a confirmed-failing set)."""
    cur = list(indices)
    confirmed = False
    while len(cur) > 1:
        n = min(fanout, len(cur))
        status, shares, failing = run.run_shares(cur, n)
        if status != COMPLETED:
            return cur, "inconclusive", {"status": status}
        if not failing:
            return cur, ("aggregate" if confirmed else "no_repro"), {}
        if len(failing) > 1:
            return cur, "multi", {
                "failing": {i: shares[i] for i in failing},
                "subchecks": {i: failing[i] for i in failing}}
        (i, sub), = failing.items()
        cur = shares[i]
        confirmed = True
    return cur, "single", {}


# ----------------------------------------------------------------------------
# main
# ----------------------------------------------------------------------------
def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--proj-root", default=None)
    ap.add_argument("--rebuild", action="store_true")
    ap.add_argument("--fanout", type=int, default=8,
                    help="shares per round (concurrent jobs); default 8")
    ap.add_argument("--timeout", type=int, default=21600,
                    help="per-trial timeout seconds (default 6h)")
    ap.add_argument("--max-trials", type=int, default=60)
    args = ap.parse_args()

    global REPORT_SNAPSHOT
    for d in (BISEC, LOGS):
        d.mkdir(parents=True, exist_ok=True)

    # full 2>&1 console capture for the pack (in-process tee). flush-on-write
    # (log() uses flush=True) keeps SESSION current before pack_session reads it.
    dump_fh = open(SESSION, "w")
    sys.stdout = Tee(sys.__stdout__, dump_fh)
    sys.stderr = Tee(sys.__stderr__, dump_fh)

    proj_root = find_proj_root(args.proj_root)
    REPORT_SNAPSHOT = proj_root / REL_REPORT   # packed if the run produced it
    log(f"proj_root = {proj_root}")
    preflight_keys(proj_root)
    exe = build_test_binary(proj_root, args.rebuild)
    master = load_master(proj_root)
    if not master:
        sys.exit("job-3 list is empty")

    run = Runner(proj_root, exe, master, args.timeout, args.max_trials)
    full = list(range(len(master)))

    def emit(lines):
        """Print the verdict banner AND save it to SUMMARY (packed)."""
        loud(lines)
        try:
            SUMMARY.write_text("\n".join(lines) + "\n")
        except Exception as e:
            log(f"WARN: could not write summary: {e}")

    try:
        # split-first: no lone-job baseline. The 8-way split fills the box and
        # (common case) confirms reproduction AND localizes in one round. If NO
        # share ever fails at round 1, quit and recommend full_clam() (~same
        # cost as a lone-job baseline, but faithful + precise sub-check).
        log("split-first: 8-way concurrent recursion (no lone-job baseline)...")
        result, kind, extra = localize_8way(run, full, args.fanout)

        files = [master[i] for i in sorted(result)]
        if kind == "single":
            lines = ["RESULT: SINGLE-FILE FAULT",
                     f"culprit (idx {sorted(result)[0]}): {files[0]}"]
        elif kind == "no_repro":
            lines = ["RESULT: NO 1/8 SHARE REPRODUCED THE FAILURE (round 1)",
                     f"every {args.fanout}-way share of job 3 "
                     f"({len(result)} files) PASSED. No lone-job baseline was",
                     "run -- it costs ~a full_clam() run but is LESS faithful.",
                     "-> RE-RUN full_clam() for the faithful, precise sub-check",
                     "error; the failure likely needs the whole job-3 fold or",
                     "the real 8-job co-residency, not captured by a 1/8 split."]
        elif kind == "aggregate":
            lines = ["RESULT: AGGREGATE / INTERACTION WITHIN A FAILING SET",
                     f"a CONFIRMED-failing set of {len(result)} files FAILs",
                     f"together, but every {args.fanout}-way share PASSES.",
                     "-> not one bad file: accumulation (lookup-share /",
                     "batch-agg budget) or an interaction across these files.",
                     f"minimal failing set ({len(result)} files): see {MASTER}"]
        elif kind == "multi":
            fail = extra["failing"]
            subs = extra["subchecks"]
            lines = ["RESULT: MULTIPLE FAILING SHARES "
                     "(>1 culprit / split interaction)",
                     f"{len(fail)} of {args.fanout} shares FAIL; stopping per",
                     "stop-and-report. Re-run bisect on each to pin its culprit:",
                     *[f"  share {i}: subcheck={subs[i]}, {len(fail[i])} files "
                       f"(idx {sorted(fail[i])[:6]}"
                       f"{'...' if len(fail[i])>6 else ''})"
                       for i in sorted(fail)]]
        else:
            lines = [f"RESULT: {kind}", f"extra = {extra}",
                     f"set ({len(result)} files): {sorted(result)[:12]}"]
        lines += [f"trials={run.n_runs}", f"audit={AUDIT}",
                  f"verify_log={VERIFY_LOG}", f"pack={PACK_TGZ}"]
        emit(lines)

    except OOMHalt as e:
        emit(["RESULT: OOM-HALT (passive detection)",
              f"subset key={e.key} size={len(e.indices)} OOMed"
              + (f", peak~{e.peak} GB" if e.peak else ""),
              "This subset's verdict is UNKNOWN -> stopping.",
              "Move to the 1TB server and re-run the SAME command;",
              "settled trials are skipped, this OOM subset is retried.",
              f"audit: {AUDIT}"])
        sys.exit(3)
    except BudgetExceeded:
        emit([f"RESULT: max-trials ({args.max_trials}) exhausted -- stopping.",
              "raise --max-trials to continue; progress is saved/resumable.",
              f"audit: {AUDIT}"])
        sys.exit(4)
    finally:
        pack_session()

    log(f"done in {run.n_runs} trials. audit={AUDIT} pack={PACK_TGZ}")


if __name__ == "__main__":
    main()
