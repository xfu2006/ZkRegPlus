#!/usr/bin/env python3
"""
run_full_dlp.py -- server driver for the sampled DLP discharge + 2-circuit run.

Pipeline (each step is a `cargo test` invocation; config flows ONLY through
JSON files, never stdout-parsing or source edits):

  0 compile      cargo test --no-run                       (build the test bin)
  1 manifests    build binexec_sample{1,2,3}.dat           (Python; fixture =
                 already present, real = pass_list +- measure_report ranking)
  2 sample1      full_dlp_sample1  -> C1.json  (small cfg; builds+caches DB)
  3 sample2      full_dlp_sample2  -> C2.json  (big   cfg)
  4 sample3      full_dlp_sample3              (read C1,C2 -> coverage report)
  5 full_dlp     full_dlp                      (read C1,C2 -> 2-circ Pass-1 cost)

Reliability properties:
  * config handoff = CapParams JSON files written/read by Rust (CapParams::
    save_json / load_json). The driver never scrapes stdout or edits .rs.
  * each step is IDEMPOTENT: it has an on-disk artifact (DB cache, C1.json,
    C2.json, reports). A crash/restart resumes mid-pipeline; --force redoes.
  * the expensive DB build happens once (step 2 via build_or_load) and every
    later step loads the cache instantly.
  * fixture vs real data is a --data flag (paths only); same code, same driver.

Each Rust step reads ONE env var, ZKR_DLP_RUNCFG, pointing at a per-step JSON
the driver writes (schema in build_runcfg()). Run under tmux/nohup for long
real-data builds.

Arguments:
  --data {fixture,real}  Path set to run against (default: fixture). The ONLY
                         knob to switch fixture<->real -- same code/steps.
                           fixture -> data/paper_data/dlp/ (tiny test DB)
                           real    -> data/paper_data/dlp/cfg/
                                      (full DLP-international + dlp_intl_data_aggr)
  --only STEP            Run just this one step (skip all others).
  --from STEP            Start at this step and run to the end (skip earlier).
  --force                Re-run steps even if their artifacts already exist
                         (defeats the idempotent skip).
  --threads N            ZKR_DC_THREADS = determine_config probe parallelism
                         (default: 4).
  --dry-run              Print the plan + each step's runcfg JSON; run nothing.

  STEP is one of the ordered pipeline stages:
    compile -> manifests -> sample1 -> sample2 -> sample3 -> full_dlp

Behavior:
  * Idempotent/resumable: each step checks for its artifact (the DB cache,
    dlp_config_C1.json, dlp_config_C2.json, the reports) and SKIPS if present,
    so a crash mid-pipeline resumes. --force overrides.
  * Logs: per-step output -> scripts/run_full_dlp_out/<step>.log; the per-step
    runcfg JSON -> scripts/run_full_dlp_out/runcfg_<step>.json.
  * Cargo always runs from the workspace root with the project's lld RUSTFLAGS.
  * --data real: the `manifests` step is a stub (errors if binexec_sample*.dat
    are absent) -- the pass-list + measure_report auto-build is still TODO.

Usage:
  python3 scripts/run_full_dlp.py --data fixture            # full pipeline
  python3 scripts/run_full_dlp.py --data fixture --only sample1
  python3 scripts/run_full_dlp.py --data fixture --from sample3  # resume
  python3 scripts/run_full_dlp.py --data fixture --force     # ignore artifacts
  python3 scripts/run_full_dlp.py --data real --dry-run      # preview only
  python3 scripts/run_full_dlp.py --data real --threads 8    # real run
"""

import argparse
import datetime
import json
import os
import subprocess
import sys

# ---------------------------------------------------------------------------
# Paths. REPO_ROOT = the new_zkregplus workspace root. This file lives at
# zkregplus/src/, so go up three levels. All cargo runs happen from
# REPO_ROOT; data paths are repo-root-relative so they match the binexec
# manifests the Rust side reads.
# ---------------------------------------------------------------------------
REPO_ROOT = os.path.dirname(os.path.dirname(os.path.dirname(
    os.path.abspath(__file__))))
RUN_DIR = "/tmp/run_full_dlp_out"   # temp logs+runcfgs (kept OUT of the repo)
# Config handoff (C1/C2) + reports live with the other configs, not in the
# input config_dir. Repo-root-relative; resolved via p()/proj_root().
CFG_DIR = "data/paper_data/dlp/cfg"
REPORT_DIR = "data/paper_data/dlp/report"

# RUSTFLAGS mirrors the project's compile.sh (lld linker, warnings off).
RUSTFLAGS = "-C link-args=-fuse-ld=lld -Awarnings"

# Per-dataset path sets. Switching fixture<->real is data only; the Rust test
# functions and this driver are identical across the two. `config_dir` holds
# the sig file + binexec manifests; outputs (C1/C2/reports) land beside them.
DATASETS = {
    "fixture": {
        "config_dir": "data/paper_data/dlp",
        "sig_file":   "main_dlp_sample.dat",
        "cache_dir":  "dlp_sample_cache",
        "scan1":      "binexec_sample1.dat",   # easy
        "scan2":      "binexec_sample2.dat",   # hard
        "scan3":      "binexec_sample3.dat",   # all / random
        "fanout_cap": 10,        # cheap fan-out for the tiny fixture
        "chunk_len":  512,
        "range2_bit": 25,
    },
    "real": {
        "config_dir": "data/paper_data/dlp/cfg",
        "sig_file":   "main_data_dlp_internationl.dat",
        "cache_dir":  "dlp_intl_data_aggr",
        "scan1":      "binexec_sample1.dat",
        "scan2":      "binexec_sample2.dat",
        "scan3":      "binexec_sample3.dat",
        "fanout_cap": 100,
        "chunk_len":  256,   # 256 words*31B ~= 8KB ZK step (fewer folding
                             # steps -> shorter sample2 tuning)
        "range2_bit": 25,
    },
}

# Output config files (the handoff) + reports, relative to config_dir.
C1_NAME = "dlp_config_C1.json"      # small (easy) config from sample1
C2_NAME = "dlp_config_C2.json"      # big (hard) config from sample2
REPORT3_NAME = "dlp_report_sample3.txt"
REPORT_FULL_NAME = "dlp_report_full.txt"

# Rust test functions (full libtest path under zkregplus).
TEST_MOD = "zkp_driver::tests_zkp_driver"


def ts():
    return datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S")


def log(msg):
    print("[%s] %s" % (ts(), msg), flush=True)


def p(*parts):
    """Join under REPO_ROOT into an absolute path."""
    return os.path.join(REPO_ROOT, *parts)


def build_runcfg(ds, step):
    """The per-step run-config the Rust side reads via ZKR_DLP_RUNCFG. Every
    field is repo-root-relative (config_dir) or a name under it; Rust resolves
    them the same way run_db_bundle already does."""
    cd = ds["config_dir"]
    cfg = {
        "config_dir": cd,
        "sig_file":   ds["sig_file"],
        "cache_dir":  ds["cache_dir"],
        "fanout_cap": ds["fanout_cap"],
        "chunk_len":  ds["chunk_len"],
        "range2_bit": ds["range2_bit"],
        # config handoff paths (repo-root-relative; live in CFG_DIR)
        "config_c1":  os.path.join(CFG_DIR, C1_NAME),
        "config_c2":  os.path.join(CFG_DIR, C2_NAME),
    }
    if step == "sample1":
        cfg["scan_file"]  = ds["scan1"]
        cfg["config_out"] = os.path.join(CFG_DIR, C1_NAME)
    elif step == "sample2":
        cfg["scan_file"]  = ds["scan2"]
        cfg["config_out"] = os.path.join(CFG_DIR, C2_NAME)
    elif step == "sample3":
        cfg["scan_file"]   = ds["scan3"]
        cfg["report_out"]  = os.path.join(REPORT_DIR, REPORT3_NAME)
    elif step == "full_dlp":
        cfg["scan_file"]   = ds["scan3"]   # real: swap to the full pass list
        cfg["report_out"]  = os.path.join(REPORT_DIR, REPORT_FULL_NAME)
    return cfg


def artifacts(ds, step):
    """On-disk outputs that mark a step done (for idempotent skip)."""
    return {
        "sample1":  [p(CFG_DIR, C1_NAME)],
        "sample2":  [p(CFG_DIR, C2_NAME)],
        "sample3":  [p(REPORT_DIR, REPORT3_NAME)],
        "full_dlp": [p(REPORT_DIR, REPORT_FULL_NAME)],
    }.get(step, [])


def have_artifacts(ds, step):
    arts = artifacts(ds, step)
    return bool(arts) and all(os.path.isfile(a) for a in arts)


def run_cargo_test(test_name, runcfg_path, log_path, threads):
    """Invoke one Rust step. Returns the process exit code. Output is teed to
    log_path so a server run leaves a per-step record."""
    env = dict(os.environ)
    env["RUSTFLAGS"] = RUSTFLAGS
    env["ZKR_DLP_RUNCFG"] = runcfg_path
    env["ZKR_DC_THREADS"] = str(threads)
    cmd = ["cargo", "test", "-p", "zkregplus", "--release", "--",
           "%s::%s" % (TEST_MOD, test_name), "--exact", "--nocapture"]
    log("RUN  %s   (log: %s)" % (" ".join(cmd), log_path))
    with open(log_path, "w") as lf:
        lf.write("# %s\n# ZKR_DLP_RUNCFG=%s\n# %s\n\n"
                 % (ts(), runcfg_path, " ".join(cmd)))
        lf.flush()
        proc = subprocess.Popen(cmd, cwd=REPO_ROOT, env=env,
                                stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT, text=True)
        for line in proc.stdout:
            lf.write(line)
            lf.flush()
        proc.wait()
    return proc.returncode


# ---------------------------------------------------------------------------
# Steps
# ---------------------------------------------------------------------------
def step_compile(ds, args):
    env = dict(os.environ); env["RUSTFLAGS"] = RUSTFLAGS
    cmd = ["cargo", "test", "-p", "zkregplus", "--release", "--no-run"]
    log("RUN  " + " ".join(cmd))
    return subprocess.call(cmd, cwd=REPO_ROOT, env=env)


def step_manifests(ds, args):
    """Fixture: manifests already exist -> verify. Real: TODO build from the
    aggressive pass list (joined with measure_report for the easy/hard rank);
    left as an explicit gap so a missing pass list fails loudly, not silently.
    """
    cd = ds["config_dir"]
    needed = [ds["scan1"], ds["scan2"], ds["scan3"]]
    missing = [m for m in needed if not os.path.isfile(p(cd, m))]
    if not missing:
        for m in needed:
            n = sum(1 for _ in open(p(cd, m)))
            log("manifest OK  %s  (%d files)" % (m, n))
        return 0
    if args.data == "fixture":
        log("ERROR fixture manifests missing: %s" % missing)
        return 1
    log("ERROR real manifests missing: %s\n"
        "      build them from the aggressive pass list + measure_report "
        "(easy=lowest max_occ_per_chunk, hard=highest, S1~50/S2~50/S3 1%%)."
        % missing)
    return 1


def step_rust(step_name, test_fn):
    """step_name drives the runcfg/artifacts (build_runcfg keys off it);
    test_fn is the cargo test path. They differ (sample1 vs full_dlp_sample1)."""
    def _run(ds, args):
        os.makedirs(RUN_DIR, exist_ok=True)
        runcfg = build_runcfg(ds, step_name)
        runcfg_path = os.path.join(RUN_DIR, "runcfg_%s.json" % step_name)
        with open(runcfg_path, "w") as f:
            json.dump(runcfg, f, indent=2)
        log_path = os.path.join(RUN_DIR, "%s.log" % step_name)
        rc = run_cargo_test(test_fn, runcfg_path, log_path, args.threads)
        if rc != 0:
            log("STEP %s FAILED (rc=%d); see %s" % (step_name, rc, log_path))
            return rc
        # verify the step actually produced its artifact(s)
        for a in artifacts(ds, step_name):
            if not os.path.isfile(a):
                log("STEP %s rc=0 but artifact missing: %s" % (step_name, a))
                return 1
        return 0
    return _run


# ordered pipeline: (name, runner, idempotent?)
def make_steps():
    return [
        ("compile",   step_compile,            False),
        ("manifests", step_manifests,          False),
        ("sample1",   step_rust("sample1",  "full_dlp_sample1"), True),
        ("sample2",   step_rust("sample2",  "full_dlp_sample2"), True),
        ("sample3",   step_rust("sample3",  "full_dlp_sample3"), True),
        ("full_dlp",  step_rust("full_dlp", "full_dlp"),         True),
    ]


def print_summary(ds):
    log("==== SUMMARY ====")
    for name, fn in [("C1 (easy/small)", C1_NAME), ("C2 (hard/big)", C2_NAME)]:
        fp = p(CFG_DIR, fn)
        if os.path.isfile(fp):
            c = json.load(open(fp))
            log("%s  %s" % (name, json.dumps(
                {k: c[k] for k in ("subsigs", "perc_pats_expansion_rate",
                 "avg_active_pats_per_subsig", "cp_subsigs",
                 "aggr_needs_subsigs") if k in c})))
        else:
            log("%s  (not produced)" % name)
    for label, fn in [("sample3 coverage", REPORT3_NAME),
                      ("full_dlp cost", REPORT_FULL_NAME)]:
        fp = p(REPORT_DIR, fn)
        log("%s -> %s" % (label, fp if os.path.isfile(fp) else "(none)"))


def pack_results(status):
    """Bundle the downloadable outputs (configs + reports + logs) into
    /tmp/dlp_results.tgz on COMPLETE or ERROR, for scp off the server."""
    import tarfile
    out = "/tmp/dlp_results.tgz"
    items = []
    for d, fns in ((CFG_DIR, (C1_NAME, C2_NAME)),
                   (REPORT_DIR, (REPORT3_NAME, REPORT_FULL_NAME))):
        for fn in fns:
            fp = p(d, fn)
            if os.path.isfile(fp):
                items.append((fp, os.path.join(os.path.basename(d), fn)))
    if os.path.isdir(RUN_DIR):
        for n in sorted(os.listdir(RUN_DIR)):
            fp = os.path.join(RUN_DIR, n)
            if os.path.isfile(fp):
                items.append((fp, os.path.join("logs", n)))
    with tarfile.open(out, "w:gz") as tf:
        for src, arc in items:
            tf.add(src, arcname=arc)
    log("PACKED [%s] %d files -> %s" % (status, len(items), out))


def main():
    ap = argparse.ArgumentParser(description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--data", choices=list(DATASETS), default="real",
                    help="path set: fixture (tiny test DB) or real "
                         "(full DLP-international). Default real.")
    ap.add_argument("--with-full", action="store_true",
                    help="also run the final full_dlp step (off by "
                         "default: a no-arg run stops after sample3)")
    ap.add_argument("--only",
                    help="run only this step (compile|manifests|sample1|"
                         "sample2|sample3|full_dlp)")
    ap.add_argument("--from", dest="from_step",
                    help="start at this step and run to the end")
    ap.add_argument("--force", action="store_true",
                    help="re-run steps even if their artifacts exist")
    ap.add_argument("--threads", type=int, default=4,
                    help="ZKR_DC_THREADS for the determine_config probe")
    ap.add_argument("--dry-run", action="store_true",
                    help="print the plan + per-step runcfg, run nothing")
    args = ap.parse_args()

    ds = DATASETS[args.data]
    steps = make_steps()
    names = [s[0] for s in steps]
    os.makedirs(RUN_DIR, exist_ok=True)
    os.makedirs(p(CFG_DIR), exist_ok=True)
    os.makedirs(p(REPORT_DIR), exist_ok=True)

    if args.only and args.only not in names:
        sys.exit("unknown --only step %r (have %s)" % (args.only, names))
    if args.from_step and args.from_step not in names:
        sys.exit("unknown --from step %r (have %s)" % (args.from_step, names))

    log("DLP driver: data=%s repo=%s" % (args.data, REPO_ROOT))
    started = args.from_step is None
    for name, fn, idem in steps:
        if args.only and name != args.only:
            continue
        if name == "full_dlp" and not (args.with_full
                                       or args.only == "full_dlp"):
            continue
        if not started:
            if name == args.from_step:
                started = True
            else:
                continue
        if args.dry_run:
            log("PLAN %s  runcfg=%s" % (name,
                json.dumps(build_runcfg(ds, name)) if name not in
                ("compile", "manifests") else "(n/a)"))
            continue
        if idem and not args.force and have_artifacts(ds, name):
            log("SKIP %s (artifact present: %s)"
                % (name, [os.path.relpath(a, REPO_ROOT)
                          for a in artifacts(ds, name)]))
            continue
        log("---- STEP %s ----" % name)
        rc = fn(ds, args)
        if rc != 0:
            log("PIPELINE ABORTED at %s (rc=%d)" % (name, rc))
            pack_results("ERROR")
            sys.exit(rc)

    if not args.dry_run:
        print_summary(ds)
        pack_results("COMPLETE")
    log("DLP driver done.")


if __name__ == "__main__":
    main()
