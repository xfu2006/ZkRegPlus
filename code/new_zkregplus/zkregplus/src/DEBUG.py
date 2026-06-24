#!/usr/bin/env python3
"""
DEBUG.py -- reproduce the b_correct (failed SDE coverage) panic on the
isolated suspect files, capturing PROBE 78010 output.

Run from zkregplus/src (or anywhere -- paths resolve from this file):
    python3 DEBUG.py

It (1) writes suspect_list.txt + runcfg_sample.json under data/paper_data/dlp/cfg,
then (2) runs full_dlp_sample with the probe env vars, tee'ing to /tmp/sample_repro.log.
"""
import os
import json
import subprocess
import sys

# src dir = this file's dir; proj root = ../.. (the new_zkregplus tree)
SRC_DIR = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(SRC_DIR, "..", ".."))
CFG_DIR = os.path.join(ROOT, "data", "paper_data", "dlp", "cfg")

SUSPECT_LIST = os.path.join(CFG_DIR, "jobs", "suspect_list.txt")
RUNCFG = os.path.join(CFG_DIR, "config", "runcfg_sample.json")
LOG = "/tmp/sample_repro.log"

SUSPECTS = [
    "data/samples/email/src/maildir/dasovich-j/all_documents/3512.",
    "data/samples/email/src/maildir/dasovich-j/notes_inbox/1704.",
    "data/samples/email/src/maildir/farmer-d/deleted_items/365.",
    "data/samples/email/src/maildir/whalley-l/all_documents/654.",
    "data/samples/email/src/maildir/whalley-l/discussion_threads/522.",
    "data/samples/email/src/maildir/whalley-l/notes_inbox/311.",
]

RUNCFG_JSON = {
    "config_dir": "data/paper_data/dlp/cfg",
    "sig_file": "regex_pat/main_data_dlp_internationl.dat",
    "cache_dir": "dlp_corpus_aggr",
    "fanout_cap": 100,
    "chunk_len": 64,
    "range2_bit": 25,
    "config_out": "data/paper_data/dlp/cfg/config/dlp_ladder_sample.json",
    "full_list": "jobs/final_enron_list.txt.tgz",
    "scan_file": "jobs/suspect_list.txt",
    "num_jobs": 1,
    "reset": True,
    "k_max": 4,
    "n_buckets": 2048,
    "peel_pct": 90,
}


def write_inputs():
    os.makedirs(os.path.dirname(SUSPECT_LIST), exist_ok=True)
    os.makedirs(os.path.dirname(RUNCFG), exist_ok=True)
    with open(SUSPECT_LIST, "w") as f:
        f.write("\n".join(SUSPECTS) + "\n")
    with open(RUNCFG, "w") as f:
        json.dump(RUNCFG_JSON, f, indent=2)
    print(f"[DEBUG.py] wrote {SUSPECT_LIST} ({len(SUSPECTS)} files)")
    print(f"[DEBUG.py] wrote {RUNCFG}")


def run():
    env = dict(os.environ)
    env["RUST_BACKTRACE"] = "1"
    env["RUSTFLAGS"] = "-C link-args=-fuse-ld=lld -Awarnings"
    env["ZKR_DLP_RUNCFG"] = RUNCFG
    env["ZKR_PROBE_77317"] = "1"

    cargo = [
        "cargo", "test", "-p", "zkregplus", "--release", "--",
        "zkp_driver::tests_zkp_driver::full_dlp_sample",
        "--exact", "--nocapture",
    ]
    print(f"[DEBUG.py] running: {' '.join(cargo)}")
    print(f"[DEBUG.py] tee -> {LOG}")
    # stream stdout/stderr to console AND log file
    with open(LOG, "w") as logf:
        proc = subprocess.Popen(
            cargo, cwd=SRC_DIR, env=env,
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
        )
        for line in proc.stdout:
            sys.stdout.write(line)
            logf.write(line)
        proc.wait()
    print(f"[DEBUG.py] exit code = {proc.returncode}; full log at {LOG}")
    return proc.returncode


if __name__ == "__main__":
    write_inputs()
    sys.exit(run())
