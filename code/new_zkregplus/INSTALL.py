#!/usr/bin/env python3
# ---------------------------------------------------------------------
# INSTALL.py  --  one-shot data installer for new_zkregplus.
#
# Downloads + extracts the sample archive into data/, runs the binexec
# and email merge pipelines (folded in from the former
# data/samples/gen_data.py and gen_merged128k_email.py), and deploys
# the chromosome-17 (sig_c21) variants.  All scratch lives under
# /tmp/bora_install and is removed on completion.  
#
# Run from anywhere:
#   python3 INSTALL.py             menu: pick ALL / email / dna / binexec
#   python3 INSTALL.py --data all  non-interactive (all|email|dna|binexec)
#   python3 INSTALL.py --test      run inline unit tests and exit
#   python3 INSTALL.py --skip-tests  install without the unit tests
#
# NOTE: python file generated under the instruction of paper author.
#   code reviewed and tested manually by paper author.
# ---------------------------------------------------------------------

import argparse
import hashlib
import os
import random
import re
import shutil
import subprocess
import sys
import tempfile
import time
import unittest
from concurrent.futures import ThreadPoolExecutor

# ---- paths (anchored on this file so cwd never matters) -------------
ROOT        = os.path.dirname(os.path.abspath(__file__))
DATA_DIR    = os.path.join(ROOT, "data")
SAMPLES_DIR = os.path.join(DATA_DIR, "samples")
SRC_SIG_DIR = os.path.join(DATA_DIR, "src_sig")
CACHE_MAIN  = os.path.join(DATA_DIR, "cache", "main")
TMP_DIR     = "/tmp/bora_install"                 # all scratch (item 4)
EXTRACT_DIR = os.path.join(TMP_DIR, "extract")

# ---- Google Drive ids (src_sig.7z intentionally NOT fetched) --------
SAMPLES_ID  = "1OM_W54JxPEiV3S26XwY7f1qhEAVyFtv_"   # samples.7z
SIG_C21_ID  = "1F79N8kFVFAXLhOoJ2oT8nzVJI5DWpcZR"   # sig_c21*.7z
SIG_C21_TOP = "sig_c21_variantsls"                  # archive top dir

# ---- email-pipeline globals (re-anchored from the former script) ----
SRC_DIR          = os.path.join(SAMPLES_DIR, "email", "src", "maildir")
TARGET_DIR       = os.path.join(SAMPLES_DIR, "email_merged128k")
RECORDS_DIR      = os.path.join(SAMPLES_DIR, "merged_records_email")
SA_DIR           = os.path.join(SRC_SIG_DIR, "spamassasin")
SA_SCRIPT        = os.path.join(SA_DIR, "sa_baseline_scan.sh")
MANIFEST_PATH    = os.path.join(RECORDS_DIR, "email_filelist.txt")
MAP_PATH         = os.path.join(RECORDS_DIR, "email_merge_map.txt")
REMOVE_LIST_PATH = os.path.join(RECORDS_DIR, "email_remove_list.txt")
SA_TSV_PATH      = os.path.join(TMP_DIR, "email_merged128k_flagged.tsv")
UNIT_TEST_TMP    = os.path.join(TMP_DIR, "merge128k_tests")
TARGET_SIZE      = 128 * 1024                     # 128 KB merge target

# ---- binexec-pipeline globals (from the former gen_data.py) ---------
BINEXEC_SRC = "binexec"                           # under SAMPLES_DIR
BINEXEC_TGT = "binexec_merged128k"
# Leave <100 KiB headroom under 32 MiB so the loc encoding never
# overflows range2_bit=26 in full_data4 (see discharge_sig.rs).
SPLIT_SIZE  = 32 * 1024 * 1024 - 100 * 1024


# =====================================================================
# download tooling + filesystem helpers
# =====================================================================

# Verify gdown (pip) + 7za (p7zip) are present; exit with hints if not.
# SA tools are checked later by check_dependencies(need_sa=True).
def check_install_deps():
    missing = []
    try:
        import gdown  # noqa: F401
    except ImportError:
        missing.append(("python module 'gdown'", "pip install gdown"))
    if shutil.which("7za") is None:
        missing.append(("7za", "sudo apt install p7zip-full"))
    if missing:
        for what, how in missing:
            print("ERROR: %s is required." % what)
            print("  Install with: %s" % how)
        sys.exit(1)


# Download a Google Drive file id to dest (skips if already present).
def gdrive_download(file_id, dest):
    import gdown
    if os.path.isfile(dest):
        print("  cached: %s" % dest)
        return
    url = "https://drive.google.com/uc?export=download&id=%s" % file_id
    gdown.download(url, dest, quiet=False)


# Extract a .7z archive into out_dir (created if missing).
def extract_7z(archive, out_dir):
    os.makedirs(out_dir, exist_ok=True)
    subprocess.run(["7za", "x", "-y", "-bd", "-bb0", archive,
                    "-o" + out_dir], check=True,
                   stdout=subprocess.DEVNULL)


# Remove the CONTENTS of d but keep the directory itself (item-4 rule).
def empty_dir(d):
    os.makedirs(d, exist_ok=True)
    for n in os.listdir(d):
        p = os.path.join(d, n)
        if os.path.isdir(p) and not os.path.islink(p):
            shutil.rmtree(p)
        else:
            os.remove(p)


# Move every child of src_dir into dst_dir (kept); src_dir left empty.
def move_children(src_dir, dst_dir):
    os.makedirs(dst_dir, exist_ok=True)
    for n in os.listdir(src_dir):
        shutil.move(os.path.join(src_dir, n),
                    os.path.join(dst_dir, n))


# =====================================================================
# binexec merge pipeline  (folded from the former gen_data.py)
# =====================================================================

# All file infos under dir_path, sorted ascending by (size, name).
def get_file_info(dir_path):
    vec_all = []
    for e in os.scandir(dir_path):
        if e.is_file():
            vec_all.append({"name": e.name,
                            "file_size": e.stat().st_size})
    vec_all.sort(key=lambda r: (r["file_size"], r["name"]))
    return vec_all


# Total bytes across a list of file infos.
def sum_filesize(vec_finfo):
    return sum(rec["file_size"] for rec in vec_finfo)


# Hard-exit with msg unless bcond holds.
def my_assert(bcond, msg):
    if not bcond:
        print("ERROR: " + msg)
        sys.exit(1)


# Greedy ascending pack: merge files under target_size into bins; a
# file already >= target_size forms its own (later split) bin.
def binexec_get_merge_plan(f_info, target_size):
    start = 0
    res = []
    while start < len(f_info):
        list_src = []
        end = start
        while end < len(f_info) and \
                sum_filesize(list_src) + f_info[end]["file_size"] \
                < target_size:
            list_src.append(f_info[end])
            end += 1
        if len(list_src) == 0:
            list_src.append(f_info[end])
            end += 1
        my_assert(len(list_src) > 0, "list_src len is 0")
        if len(list_src) > 1:
            my_assert(sum_filesize(list_src) <= target_size,
                      "sumfilesize > target!")
        nameid = len(res)
        target_name = ("merged_" + str(nameid)
                       if len(list_src) > 1 else list_src[0]["name"])
        res.append({"target_name": target_name, "list_src": list_src})
        start = end
    total = sum(len(r["list_src"]) for r in res)
    print("Merged: total_files:", total, "len(f_info)", len(f_info))
    my_assert(total == len(f_info), "total_files!=f_info")
    return res


# Materialize the plan with cat (merge) / cp (small) / split (large),
# writing a per-source record under merge_records/.
def binexec_exec_merge_plan(src_dir, dest_dir, plan, split_size):
    frec = open("merge_records/" + src_dir + ".txt", "w")
    for item in plan:
        if len(item["list_src"]) > 1:
            cmd = "cat "
            srec = item["target_name"] + ": "
            for rec in item["list_src"]:
                cmd += " " + src_dir + "/" + rec["name"]
                srec += " " + rec["name"]
            cmd += " > " + dest_dir + "/" + item["target_name"]
            print("MERGE cmd: " + cmd)
            os.system(cmd)
            frec.write(srec + "\n")
        if len(item["list_src"]) == 1:
            rec = item["list_src"][0]
            if rec["file_size"] < split_size:
                cmd = "cp " + src_dir + "/" + rec["name"] + " " + dest_dir
                print("COPY cmd: " + cmd)
                os.system(cmd)
            else:
                cmd = ("split -b " + str(split_size) +
                       " --numeric-suffixes=0 --suffix-length=2 " +
                       src_dir + "/" + rec["name"] + " " +
                       dest_dir + "/" + rec["name"] + "__")
                print("SPLIT cmd: " + cmd)
                os.system(cmd)
    frec.close()


# Recreate binexec_merged128k from binexec, running under SAMPLES_DIR
# (relative paths, as the former gen_data.py main did).
def install_binexec():
    prev = os.getcwd()
    os.chdir(SAMPLES_DIR)
    try:
        os.makedirs("merge_records", exist_ok=True)
        shutil.rmtree(BINEXEC_TGT, ignore_errors=True)
        os.makedirs(BINEXEC_TGT)
        mylist = get_file_info(BINEXEC_SRC)
        plan = binexec_get_merge_plan(mylist, TARGET_SIZE)
        binexec_exec_merge_plan(BINEXEC_SRC, BINEXEC_TGT, plan,
                                SPLIT_SIZE)
        print("binexec merge done -> %s" % BINEXEC_TGT)
    finally:
        os.chdir(prev)


# =====================================================================
# archive deploy
# =====================================================================

# Deploy the extracted samples/ payload (binexec, email, merge_records,
# ...) into data/samples/.
def deploy_samples(extract_root):
    src = os.path.join(extract_root, "samples")
    # keep the repo's samples/.gitignore (archive's is incomplete).
    shutil.copytree(src, SAMPLES_DIR, dirs_exist_ok=True,
                    ignore=shutil.ignore_patterns(".gitignore"))


# Deploy the chr17 (sig_c21) payload: chr17_samples -> data/samples/,
# the remaining top folder -> data/src_sig/chr17_variants (item 3).
# Each destination keeps its dir name; contents are replaced.
def deploy_chr17(extract_root):
    top = os.path.join(extract_root, SIG_C21_TOP)
    samp = os.path.join(top, "chr17_samples")
    dst_samp = os.path.join(SAMPLES_DIR, "chr17_samples")
    empty_dir(dst_samp)
    move_children(samp, dst_samp)
    os.rmdir(samp)
    dst_var = os.path.join(SRC_SIG_DIR, "chr17_variants")
    empty_dir(dst_var)
    move_children(top, dst_var)


# =====================================================================
# email merge pipeline  (folded verbatim from gen_merged128k_email.py)
# =====================================================================

# ---- step framing ---------------------------------------------------

# Mark step start.  Prints banner; returns wall-clock t0 for step_done.
def step_enter(name):
    print(f"entering step: {name}")
    return time.time()


# Mark step completion.  Prints elapsed wall-clock as H:MM:SS.
def step_done(name, t0):
    dt = int(time.time() - t0)
    h, rem = divmod(dt, 3600)
    m, s   = divmod(rem, 60)
    print(f"step {name} completed. total time: "
          f"{h}:{m:02d}:{s:02d}")


# ---- dependency / folder checks -------------------------------------

# Verify required external tools.  When need_sa is True, both spamc
# and spamd must be on PATH.  On any miss, print every install line
# at once and sys.exit(1).  Never interactive.
def check_dependencies(need_sa):
    missing = []
    if need_sa:
        for tool, pkg in (("spamc", "spamassassin"),
                          ("spamd", "spamassassin")):
            if shutil.which(tool) is None:
                missing.append((tool, pkg))
    if missing:
        for tool, pkg in missing:
            print(f"ERROR: {tool} is required.")
            print(f"  Install with: sudo apt install {pkg}")
        sys.exit(1)


# Verify src_dir exists; create target_dir and records_dir if missing;
# require sa_dir only when need_sa is True.  Exits on hard errors.
def check_data_folders(src_dir, target_dir, records_dir,
                       sa_dir, need_sa):
    if not os.path.isdir(src_dir):
        print(f"ERROR: source dir not found: {src_dir}")
        sys.exit(1)
    if need_sa and not os.path.isdir(sa_dir):
        print(f"ERROR: SA rules dir not found: {sa_dir}")
        sys.exit(1)
    os.makedirs(target_dir,  exist_ok=True)
    os.makedirs(records_dir, exist_ok=True)


# ---- block 2: canonical file list + manifest ------------------------

# Enumerate src_root recursively in canonical (relpath-sorted) order.
# Returns [{"relpath": str, "size": int}, ...].  os.walk's default
# order is filesystem-dependent, so we sort dirnames/filenames in
# place at every level.  Symlinks and non-regular files are skipped.
def canonical_file_list(src_root):
    out = []
    for dirpath, dirnames, filenames in os.walk(
            src_root, topdown=True, followlinks=False):
        dirnames.sort()
        filenames.sort()
        for fn in filenames:
            full = os.path.join(dirpath, fn)
            if os.path.islink(full) or not os.path.isfile(full):
                continue
            rp = os.path.relpath(full, src_root)
            out.append({"relpath": rp,
                        "size":    os.path.getsize(full)})
    # Defensive final sort; survives any future walker swap.
    out.sort(key=lambda r: (r["relpath"], r["size"]))
    return out


# Body text of the manifest: one "relpath\tsize\n" line per file.
def _filelist_body_text(file_list):
    return "".join(f"{r['relpath']}\t{r['size']}\n"
                   for r in file_list)


# Write the file list as human-readable UTF-8 text:
#   <relpath>\t<size>\n  ...
#   # sha256 = <hex>\n
# Trailer hashes the body so a human can recompute with sha256sum.
def write_file_manifest(file_list, path):
    body = _filelist_body_text(file_list)
    h    = hashlib.sha256(body.encode("utf-8")).hexdigest()
    tmp  = path + ".tmp"
    with open(tmp, "w", encoding="utf-8", newline="\n") as f:
        f.write(body)
        f.write(f"# sha256 = {h}\n")
    os.replace(tmp, path)


# Read the manifest; verify the sha256 trailer matches the body.
def read_file_manifest(path):
    with open(path, "r", encoding="utf-8") as f:
        lines = f.read().splitlines()
    if not lines or not lines[-1].startswith("# sha256 = "):
        raise ValueError("manifest missing sha256 trailer")
    expected = lines[-1].split("= ", 1)[1].strip()
    body     = "".join(l + "\n" for l in lines[:-1])
    actual   = hashlib.sha256(body.encode("utf-8")).hexdigest()
    if expected != actual:
        raise ValueError(
            f"manifest sha256 mismatch: {actual} != {expected}")
    out = []
    for ln in lines[:-1]:
        rp, sz = ln.split("\t")
        out.append({"relpath": rp, "size": int(sz)})
    return out


# ---- block 3: merge plan --------------------------------------------

# Greedy in-order packing into target_size bins.  Walks the canonical
# file list once, growing each bin while the next file fits; if the
# first file in a bin already exceeds target_size, it forms its own
# (solo, oversize) bin.  Target names are merged_NNNNN with width
# sized to len(file_list).  Returns
# [{"target_name": str, "list_src": [{"relpath","size"}, ...]}, ...].
def compute_merge_plan(file_list, target_size):
    plan = []
    if not file_list:
        return plan
    width = max(5, len(str(len(file_list))))
    start = 0
    while start < len(file_list):
        bin_src   = []
        bin_total = 0
        end       = start
        while end < len(file_list) and \
                bin_total + file_list[end]["size"] <= target_size:
            bin_src.append(file_list[end])
            bin_total += file_list[end]["size"]
            end += 1
        if not bin_src:
            # First file alone exceeds target_size: solo bin.
            bin_src.append(file_list[end])
            end += 1
        idx = len(plan)
        plan.append({
            "target_name": f"merged_{idx:0{width}d}",
            "list_src":    bin_src,
        })
        start = end
    assert sum(len(b["list_src"]) for b in plan) == len(file_list)
    for b in plan:
        if len(b["list_src"]) > 1:
            sz = sum(s["size"] for s in b["list_src"])
            assert sz <= target_size
    return plan


# ---- block 4: execute merge plan ------------------------------------

# Copy one bin's sources back-to-back into target_path.  Streams 1MB
# at a time; verifies the output size matches the planned total.
def _write_one_merged_file(src_root, target_path, list_src):
    expected = sum(s["size"] for s in list_src)
    tmp = target_path + ".tmp"
    with open(tmp, "wb") as out:
        for s in list_src:
            sp = os.path.join(src_root, s["relpath"])
            with open(sp, "rb") as f:
                shutil.copyfileobj(f, out, length=1 << 20)
    actual = os.path.getsize(tmp)
    if actual != expected:
        os.remove(tmp)
        raise RuntimeError(
            f"size mismatch on {target_path}: "
            f"{actual} != {expected}")
    os.replace(tmp, target_path)


# Materialize plan into target_dir at max parallelism.  Wipes
# target_dir first; uses ThreadPoolExecutor (I/O-bound, GIL-friendly).
def exec_merge_plan(src_root, target_dir, plan, jobs=None):
    jobs = jobs or os.cpu_count() or 1
    shutil.rmtree(target_dir, ignore_errors=True)
    os.makedirs(target_dir)
    with ThreadPoolExecutor(max_workers=jobs) as ex:
        futures = [
            ex.submit(
                _write_one_merged_file, src_root,
                os.path.join(target_dir, b["target_name"]),
                b["list_src"])
            for b in plan
        ]
        for fut in futures:
            fut.result()


# ---- block 5: remove-list I/O + SA TSV parsing ---------------------

_MERGED_RE = re.compile(r"^merged_\d+$")


# Sort + dedup; reject any entry containing a path separator.
def _canonicalize_names(names):
    canon = sorted(set(names))
    for n in canon:
        if "/" in n or "\\" in n:
            raise ValueError(f"path separator in name: {n!r}")
    return canon


# Write the remove list as canonical UTF-8 text: one basename per
# line, LF only, single trailing newline.  Empty list -> empty file
# (zero bytes).  Atomic via .tmp + os.replace.
def write_remove_list(names, path):
    canon = _canonicalize_names(names)
    tmp   = path + ".tmp"
    with open(tmp, "w", encoding="utf-8", newline="\n") as f:
        for n in canon:
            print(n, file=f)
    os.replace(tmp, path)


# Read the remove list back as canonical (sorted+deduped) UTF-8
# text.  Tolerant of blank lines, CRLFs, and trailing whitespace.
# Rejects any entry containing a path separator.
def read_remove_list(path):
    out = []
    with open(path, "r", encoding="utf-8") as f:
        for ln in f:
            n = ln.strip()
            if not n:
                continue
            if "/" in n or "\\" in n:
                raise ValueError(
                    f"path separator in name: {n!r}")
            out.append(n)
    return sorted(set(out))


# Delete target_dir/<name> for each name in parallel.  Missing
# files are tolerated.  Returns (n_deleted, n_missing).
def apply_remove_list(target_dir, names, jobs=None):
    jobs = jobs or os.cpu_count() or 1

    def _rm(n):
        try:
            os.remove(os.path.join(target_dir, n))
            return (1, 0)
        except FileNotFoundError:
            return (0, 1)

    n_deleted = 0
    n_missing = 0
    if names:
        with ThreadPoolExecutor(max_workers=jobs) as ex:
            for d, m in ex.map(_rm, names):
                n_deleted += d
                n_missing += m
    return n_deleted, n_missing


# Parse a sa_baseline_scan.sh TSV.  Each line is
# "<score>/<threshold>\t<abs path to merged_NNNNN>".  Returns the
# sorted, deduped set of merged basenames; malformed lines and
# non-merged-style basenames are skipped silently.
def parse_sa_tsv(tsv_path):
    out = []
    with open(tsv_path, "r", encoding="utf-8") as f:
        for ln in f:
            ln = ln.rstrip("\n\r")
            if not ln or "\t" not in ln:
                continue
            _, p = ln.split("\t", 1)
            bn = os.path.basename(p.strip())
            if _MERGED_RE.match(bn):
                out.append(bn)
    return sorted(set(out))


# ---- block 6: run_spamassassin --------------------------------------

# Shell out to sa_baseline_scan.sh with ENRON/OUT/JOBS env overrides
# (max parallelism via JOBS=cpu_count, which the script forwards to
# both `xargs -P` and `spamd --max-children`).  Parse the resulting
# TSV.  Returns the canonical (sorted+deduped) flagged basenames.
def run_spamassassin(target_dir, sa_dir, out_tsv, jobs=None):
    jobs = jobs or os.cpu_count() or 1
    sh   = os.path.join(sa_dir, "sa_baseline_scan.sh")
    if not os.path.isfile(sh):
        raise FileNotFoundError(f"SA script not found: {sh}")
    env = os.environ.copy()
    env["ENRON"] = os.path.abspath(target_dir)
    env["OUT"]   = os.path.abspath(out_tsv)
    env["JOBS"]  = str(jobs)
    subprocess.run(["bash", sh], env=env, check=True)
    return parse_sa_tsv(out_tsv)


# ---- block 7: merge map + records glue -----------------------------

# Write the plan as canonical UTF-8 TSV:
#   <target_name>\t<relpath_1>\t<relpath_2>...\n
# One line per bin in plan order.  Rejects relpaths containing
# tab/newline (would corrupt the TSV).
def write_merge_map(plan, path):
    for b in plan:
        for s in b["list_src"]:
            rp = s["relpath"]
            if "\t" in rp or "\n" in rp or "\r" in rp:
                raise ValueError(
                    f"tab/newline in relpath: {rp!r}")
    tmp = path + ".tmp"
    with open(tmp, "w", encoding="utf-8", newline="\n") as f:
        for b in plan:
            row = [b["target_name"]] + [
                s["relpath"] for s in b["list_src"]]
            print("\t".join(row), file=f)
    os.replace(tmp, path)


# Read the merge map.  Target names must match merged_NNNNN and be
# strictly increasing in plan order.  Returns a list of dicts:
# [{"target_name": str, "list_src": [{"relpath": str}, ...]}, ...].
def read_merge_map(path):
    plan = []
    last = -1
    with open(path, "r", encoding="utf-8") as f:
        for ln in f:
            ln = ln.rstrip("\n\r")
            if not ln:
                continue
            parts = ln.split("\t")
            tn    = parts[0]
            if not _MERGED_RE.match(tn):
                raise ValueError(f"bad target_name: {tn!r}")
            idx = int(tn.split("_")[1])
            if idx <= last:
                raise ValueError(
                    f"non-monotonic target index: {tn}")
            last = idx
            plan.append({
                "target_name": tn,
                "list_src": [
                    {"relpath": rp} for rp in parts[1:]],
            })
    return plan


# Step [e] glue.  Writes filelist + merge_map; if remove_names is
# not None, also writes the remove list.  remove_names=None means
# SA wasn't run; remove_names=[] means SA ran and flagged nothing.
def write_all_records(records_dir, file_list, plan,
                      remove_names):
    os.makedirs(records_dir, exist_ok=True)
    write_file_manifest(
        file_list,
        os.path.join(records_dir, "email_filelist.txt"))
    write_merge_map(
        plan,
        os.path.join(records_dir, "email_merge_map.txt"))
    if remove_names is not None:
        write_remove_list(
            remove_names,
            os.path.join(records_dir, "email_remove_list.txt"))


# ---- block 8: integration tests (run inside main, not --test) -----

# Integration test 1.  Pick n_samples random sources from the plan;
# for each, locate (target_name, offset, size) and verify the bytes
# in target_dir/<target_name> at [offset, offset+size] match the
# source file's bytes.  Samples whose target was removed are
# skipped.  Hard-exits on mismatch.
def integ_test_random_sample_in_merged(src_root, target_dir, plan,
                                       remove_names, n_samples,
                                       seed=20260520):
    flat = []
    for b in plan:
        off = 0
        for s in b["list_src"]:
            flat.append((s["relpath"], b["target_name"],
                         off, s["size"]))
            off += s["size"]
    if not flat:
        print("integ test 1: no sources to verify; skipped")
        return
    removed = set(remove_names or [])
    rng     = random.Random(seed)
    n_ok    = 0
    n_skip  = 0
    for _ in range(n_samples):
        rp, tn, off, sz = rng.choice(flat)
        if tn in removed:
            n_skip += 1
            continue
        with open(os.path.join(target_dir, tn), "rb") as f:
            f.seek(off)
            got = f.read(sz)
        with open(os.path.join(src_root, rp), "rb") as f:
            want = f.read()
        if got != want:
            print(
                f"integ test 1 FAILED: {rp} in {tn} "
                f"@ off={off} size={sz}")
            div = -1
            for i in range(min(len(got), len(want))):
                if got[i] != want[i]:
                    div = i
                    break
            print(f"  first diff offset: {div}")
            sys.exit(1)
        n_ok += 1
    print(f"integ test 1: {n_ok} samples verified, "
          f"{n_skip} skipped (on remove list); seed={seed}")


# Integration test 2.  Verify
#   sum(originals under src_root)
#   == sum(removed-merged sizes reconstructed from filelist + map)
#    + sum(sizes of merged blobs remaining on disk).
# Hard-exits on mismatch.
def integ_test_size_accounting(src_root, target_dir,
                               remove_names, records_dir):
    t_orig = 0
    for dp, _, fns in os.walk(src_root, followlinks=False):
        for fn in fns:
            full = os.path.join(dp, fn)
            if os.path.islink(full) or not os.path.isfile(full):
                continue
            t_orig += os.path.getsize(full)
    t_remain = sum(
        os.path.getsize(os.path.join(target_dir, n))
        for n in os.listdir(target_dir)
        if os.path.isfile(os.path.join(target_dir, n)))
    fl = read_file_manifest(
        os.path.join(records_dir, "email_filelist.txt"))
    size_of  = {r["relpath"]: r["size"] for r in fl}
    plan_map = read_merge_map(
        os.path.join(records_dir, "email_merge_map.txt"))
    removed   = set(remove_names or [])
    t_removed = 0
    for b in plan_map:
        if b["target_name"] in removed:
            for s in b["list_src"]:
                t_removed += size_of[s["relpath"]]
    if t_orig != t_remain + t_removed:
        print("integ test 2 FAILED: size accounting mismatch")
        print(f"  T_orig:    {t_orig}")
        print(f"  T_remain:  {t_remain}")
        print(f"  T_removed: {t_removed}")
        print(f"  delta:     "
              f"{t_orig - (t_remain + t_removed)}")
        sys.exit(1)
    print(f"integ test 2: size accounting OK "
          f"(orig={t_orig}, removed={t_removed}, "
          f"remaining={t_remain})")


# ---- unit tests -----------------------------------------------------

class TestBlock1(unittest.TestCase):
    """Block 1: dep + data-folder checks."""

    def setUp(self):
        self.tdir = tempfile.mkdtemp(dir=UNIT_TEST_TMP)

    # Happy path: missing target/records get created.
    def test_check_data_folders_ok(self):
        src = os.path.join(self.tdir, "src"); os.makedirs(src)
        tgt = os.path.join(self.tdir, "tgt")
        rec = os.path.join(self.tdir, "rec")
        sa  = os.path.join(self.tdir, "sa");  os.makedirs(sa)
        check_data_folders(src, tgt, rec, sa, need_sa=True)
        self.assertTrue(os.path.isdir(tgt))
        self.assertTrue(os.path.isdir(rec))

    # Missing src is always fatal.
    def test_check_data_folders_missing_src(self):
        src = os.path.join(self.tdir, "missing")
        tgt = os.path.join(self.tdir, "tgt")
        rec = os.path.join(self.tdir, "rec")
        sa  = os.path.join(self.tdir, "sa"); os.makedirs(sa)
        with self.assertRaises(SystemExit):
            check_data_folders(src, tgt, rec, sa, need_sa=False)

    # Missing sa is fatal only when need_sa=True.
    def test_check_data_folders_sa_gating(self):
        src = os.path.join(self.tdir, "src"); os.makedirs(src)
        tgt = os.path.join(self.tdir, "tgt")
        rec = os.path.join(self.tdir, "rec")
        sa  = os.path.join(self.tdir, "missing")
        with self.assertRaises(SystemExit):
            check_data_folders(src, tgt, rec, sa, need_sa=True)
        check_data_folders(src, tgt, rec, sa, need_sa=False)

    # need_sa=False imposes no tool requirements.
    def test_check_dependencies_no_sa(self):
        check_dependencies(need_sa=False)

    # need_sa=True exits iff a tool is missing.
    def test_check_dependencies_sa(self):
        have_all = (shutil.which("spamc") is not None
                    and shutil.which("spamd") is not None)
        if have_all:
            check_dependencies(need_sa=True)
        else:
            with self.assertRaises(SystemExit):
                check_dependencies(need_sa=True)


class TestBlock2(unittest.TestCase):
    """Block 2: canonical file list + manifest."""

    def setUp(self):
        self.tdir = tempfile.mkdtemp(dir=UNIT_TEST_TMP)

    # Build a tree where files are created in randomized order to
    # stress the canonicality of the enumerator.  Each (relpath,
    # content) pair is written in a shuffled order driven by seed.
    def _build_tree(self, root, files, seed):
        rng  = random.Random(seed)
        idxs = list(range(len(files)))
        rng.shuffle(idxs)
        for i in idxs:
            rp, data = files[i]
            full = os.path.join(root, rp)
            os.makedirs(os.path.dirname(full), exist_ok=True)
            with open(full, "wb") as f:
                f.write(data)

    # canonical_file_list is stable across creation orders, and the
    # resulting manifests are byte-identical (req: CANONICAL list).
    def test_canonical_file_list_stable(self):
        files = [
            ("a/b/c.txt",            b"abc"),
            ("a/b/d.txt",            b"dddd"),
            ("a/zz.txt",             b"z"),
            ("x.txt",                b"xxxxx"),
            ("subdir/inner/deep.txt", b"deep"),
        ]
        root1 = os.path.join(self.tdir, "r1")
        root2 = os.path.join(self.tdir, "r2")
        self._build_tree(root1, files, 1)
        self._build_tree(root2, files, 42)
        fl1 = canonical_file_list(root1)
        fl2 = canonical_file_list(root2)
        self.assertEqual(fl1, fl2)
        m1 = os.path.join(self.tdir, "m1.txt")
        m2 = os.path.join(self.tdir, "m2.txt")
        write_file_manifest(fl1, m1)
        write_file_manifest(fl2, m2)
        with open(m1, "r", encoding="utf-8") as f:
            t1 = f.read()
        with open(m2, "r", encoding="utf-8") as f:
            t2 = f.read()
        self.assertEqual(t1, t2)

    # Symlinks are excluded; nested files appear under their relpath.
    def test_canonical_file_list_filters(self):
        root = os.path.join(self.tdir, "root")
        os.makedirs(os.path.join(root, "sub"))
        with open(os.path.join(root, "real.txt"), "wb") as f:
            f.write(b"r")
        with open(os.path.join(root, "sub", "x.txt"), "wb") as f:
            f.write(b"x")
        os.symlink(os.path.join(root, "real.txt"),
                   os.path.join(root, "sym.txt"))
        fl  = canonical_file_list(root)
        rps = [r["relpath"] for r in fl]
        self.assertIn("real.txt", rps)
        self.assertIn(os.path.join("sub", "x.txt"), rps)
        self.assertNotIn("sym.txt", rps)

    # Manifest is human-readable UTF-8 with a sha256 trailer.
    def test_manifest_human_readable(self):
        fl = [{"relpath": "a", "size": 10},
              {"relpath": "b", "size": 20}]
        p  = os.path.join(self.tdir, "man.txt")
        write_file_manifest(fl, p)
        with open(p, "r", encoding="utf-8") as f:
            text = f.read()
        self.assertTrue(text.startswith("a\t10\nb\t20\n"))
        lines = text.splitlines()
        self.assertEqual(len(lines), 3)
        self.assertTrue(lines[-1].startswith("# sha256 = "))
        self.assertEqual(len(lines[-1].split("= ", 1)[1]), 64)
        self.assertTrue(text.endswith("\n"))

    # Read returns the original list; tampering raises ValueError.
    def test_manifest_roundtrip_and_tamper(self):
        fl = [{"relpath": "a/b", "size": 7},
              {"relpath": "x",   "size": 9}]
        p  = os.path.join(self.tdir, "man.txt")
        write_file_manifest(fl, p)
        self.assertEqual(read_file_manifest(p), fl)
        with open(p, "r", encoding="utf-8") as f:
            text = f.read()
        bad = text.replace("a/b\t7\n", "a/b\t8\n")
        with open(p, "w", encoding="utf-8", newline="\n") as f:
            f.write(bad)
        with self.assertRaises(ValueError):
            read_file_manifest(p)

    # Empty list -> manifest holds only the sha256 trailer.
    def test_manifest_empty(self):
        p = os.path.join(self.tdir, "man.txt")
        write_file_manifest([], p)
        self.assertEqual(read_file_manifest(p), [])

    # Atomic write leaves no .tmp sibling.
    def test_manifest_atomic(self):
        fl = [{"relpath": "z", "size": 1}]
        p  = os.path.join(self.tdir, "man.txt")
        write_file_manifest(fl, p)
        self.assertFalse(os.path.exists(p + ".tmp"))


class TestBlock3(unittest.TestCase):
    """Block 3: compute_merge_plan."""

    # All small files coalesce into one bin.
    def test_all_small(self):
        fl = [{"relpath": f"f{i}", "size": s}
              for i, s in enumerate([10, 20, 30, 40])]
        plan = compute_merge_plan(fl, 100)
        self.assertEqual(len(plan), 1)
        self.assertEqual([s["relpath"]
                          for s in plan[0]["list_src"]],
                         ["f0", "f1", "f2", "f3"])

    # Mixture of singletons and a multi-file bin.
    def test_tight_pack(self):
        fl = [{"relpath": "a", "size": 60},
              {"relpath": "b", "size": 50},
              {"relpath": "c", "size": 60},
              {"relpath": "d", "size": 10}]
        plan = compute_merge_plan(fl, 100)
        self.assertEqual(len(plan), 3)
        self.assertEqual([s["relpath"]
                          for s in plan[0]["list_src"]], ["a"])
        self.assertEqual([s["relpath"]
                          for s in plan[1]["list_src"]], ["b"])
        self.assertEqual([s["relpath"]
                          for s in plan[2]["list_src"]],
                         ["c", "d"])

    # Oversize file forms its own solo bin.
    def test_oversize_solo(self):
        fl = [{"relpath": "big", "size": 200},
              {"relpath": "a",   "size": 30},
              {"relpath": "b",   "size": 40}]
        plan = compute_merge_plan(fl, 100)
        self.assertEqual(len(plan), 2)
        self.assertEqual([s["relpath"]
                          for s in plan[0]["list_src"]], ["big"])
        self.assertEqual([s["relpath"]
                          for s in plan[1]["list_src"]],
                         ["a", "b"])

    # Single-file list.
    def test_single_file(self):
        fl   = [{"relpath": "only", "size": 50}]
        plan = compute_merge_plan(fl, 100)
        self.assertEqual(len(plan), 1)
        self.assertEqual(plan[0]["target_name"], "merged_00000")

    # Empty list.
    def test_empty_list(self):
        self.assertEqual(compute_merge_plan([], 100), [])

    # Two calls produce identical plans.
    def test_determinism(self):
        fl = [{"relpath": f"f{i:03d}",
               "size": (i * 7) % 41 + 1}
              for i in range(50)]
        self.assertEqual(compute_merge_plan(fl, 100),
                         compute_merge_plan(fl, 100))

    # Every source ends up in exactly one bin.
    def test_count_invariant(self):
        fl = [{"relpath": f"f{i}", "size": (i * 13) % 71 + 5}
              for i in range(200)]
        plan  = compute_merge_plan(fl, 256)
        total = sum(len(b["list_src"]) for b in plan)
        self.assertEqual(total, len(fl))

    # Multi-file bins never exceed target_size.
    def test_size_invariant(self):
        fl = [{"relpath": f"f{i}", "size": (i * 13) % 71 + 5}
              for i in range(200)]
        plan = compute_merge_plan(fl, 256)
        for b in plan:
            if len(b["list_src"]) > 1:
                self.assertLessEqual(
                    sum(s["size"] for s in b["list_src"]),
                    256)

    # Names are zero-padded; lex order == plan order.
    def test_name_width(self):
        fl   = [{"relpath": f"f{i:04d}", "size": 1}
                for i in range(2000)]
        plan = compute_merge_plan(fl, 1)
        names = [b["target_name"] for b in plan]
        self.assertEqual(names, sorted(names))
        self.assertEqual(names[0],  "merged_00000")
        self.assertEqual(names[-1], "merged_01999")


class TestBlock4(unittest.TestCase):
    """Block 4: exec_merge_plan."""

    def setUp(self):
        self.tdir = tempfile.mkdtemp(dir=UNIT_TEST_TMP)
        self.src  = os.path.join(self.tdir, "src")
        self.tgt  = os.path.join(self.tdir, "tgt")
        os.makedirs(self.src)

    def _write_src(self, rp, data):
        full = os.path.join(self.src, rp)
        os.makedirs(os.path.dirname(full) or ".",
                    exist_ok=True)
        with open(full, "wb") as f:
            f.write(data)

    def _build_basic(self):
        self._write_src("a", b"AAAA")
        self._write_src("b", b"BBBB")
        self._write_src("c", b"C" * 200)
        self._write_src("d", b"D")

    # Output is byte-exact concatenation in canonical order.
    def test_byte_exact(self):
        self._build_basic()
        plan = [
            {"target_name": "merged_00000",
             "list_src": [
                 {"relpath": "a", "size": 4},
                 {"relpath": "b", "size": 4},
                 {"relpath": "d", "size": 1}]},
            {"target_name": "merged_00001",
             "list_src": [{"relpath": "c", "size": 200}]},
            {"target_name": "merged_00002",
             "list_src": [{"relpath": "a", "size": 4}]},
        ]
        exec_merge_plan(self.src, self.tgt, plan)
        with open(os.path.join(self.tgt, "merged_00000"),
                  "rb") as f:
            self.assertEqual(f.read(), b"AAAABBBBD")
        with open(os.path.join(self.tgt, "merged_00001"),
                  "rb") as f:
            self.assertEqual(f.read(), b"C" * 200)
        with open(os.path.join(self.tgt, "merged_00002"),
                  "rb") as f:
            self.assertEqual(f.read(), b"AAAA")

    # Bin order on disk matches plan order (zero-padded names).
    def test_bin_order(self):
        self._build_basic()
        plan = [
            {"target_name": "merged_00000",
             "list_src": [{"relpath": "a", "size": 4}]},
            {"target_name": "merged_00001",
             "list_src": [{"relpath": "b", "size": 4}]},
        ]
        exec_merge_plan(self.src, self.tgt, plan)
        self.assertEqual(sorted(os.listdir(self.tgt)),
                         ["merged_00000", "merged_00001"])

    # Wipes target_dir before writing.
    def test_wipe(self):
        self._build_basic()
        os.makedirs(self.tgt, exist_ok=True)
        with open(os.path.join(self.tgt, "junk"), "wb") as f:
            f.write(b"x")
        plan = [{"target_name": "merged_00000",
                 "list_src": [{"relpath": "a", "size": 4}]}]
        exec_merge_plan(self.src, self.tgt, plan)
        self.assertEqual(os.listdir(self.tgt),
                         ["merged_00000"])

    # No extra files in target_dir, no .tmp leftovers.
    def test_no_extras(self):
        self._build_basic()
        plan = [{"target_name": "merged_00000",
                 "list_src": [{"relpath": "a", "size": 4}]}]
        exec_merge_plan(self.src, self.tgt, plan)
        names = os.listdir(self.tgt)
        self.assertEqual(len(names), len(plan))
        for n in names:
            self.assertFalse(n.endswith(".tmp"))

    # Idempotent: byte-identical outputs across two runs.
    def test_idempotent(self):
        self._build_basic()
        plan = [
            {"target_name": "merged_00000",
             "list_src": [
                 {"relpath": "a", "size": 4},
                 {"relpath": "b", "size": 4}]},
            {"target_name": "merged_00001",
             "list_src": [{"relpath": "c", "size": 200}]},
        ]

        def _hash_dir(d):
            out = {}
            for n in sorted(os.listdir(d)):
                with open(os.path.join(d, n), "rb") as f:
                    out[n] = hashlib.sha256(f.read()).hexdigest()
            return out

        exec_merge_plan(self.src, self.tgt, plan)
        h_a = _hash_dir(self.tgt)
        exec_merge_plan(self.src, self.tgt, plan)
        h_b = _hash_dir(self.tgt)
        self.assertEqual(h_a, h_b)


class TestBlock5(unittest.TestCase):
    """Block 5: remove-list I/O + SA TSV parser."""

    def setUp(self):
        self.tdir = tempfile.mkdtemp(dir=UNIT_TEST_TMP)

    # Canonical text on disk: sorted, deduped, LF, trailing newline.
    def test_write_text_exact(self):
        p = os.path.join(self.tdir, "rm.txt")
        write_remove_list(
            ["merged_00003", "merged_00001", "merged_00003"], p)
        with open(p, "r", encoding="utf-8") as f:
            text = f.read()
        self.assertEqual(text,
                         "merged_00001\nmerged_00003\n")

    # Empty list -> empty file.
    def test_empty(self):
        p = os.path.join(self.tdir, "rm.txt")
        write_remove_list([], p)
        self.assertEqual(os.path.getsize(p), 0)
        self.assertEqual(read_remove_list(p), [])

    # Roundtrip preserves canonical content.
    def test_roundtrip(self):
        names = ["merged_00010", "merged_00002"]
        p = os.path.join(self.tdir, "rm.txt")
        write_remove_list(names, p)
        self.assertEqual(read_remove_list(p),
                         ["merged_00002", "merged_00010"])

    # Two writes (one with shuffled input) are byte-identical.
    def test_canonical_twice(self):
        names = ["merged_00010", "merged_00002", "merged_00005"]
        p_a = os.path.join(self.tdir, "a.txt")
        p_b = os.path.join(self.tdir, "b.txt")
        write_remove_list(names, p_a)
        rng = random.Random(7)
        sh  = list(names); rng.shuffle(sh)
        write_remove_list(sh, p_b)
        with open(p_a, "r", encoding="utf-8") as f:
            a = f.read()
        with open(p_b, "r", encoding="utf-8") as f:
            b = f.read()
        self.assertEqual(a, b)

    # Path separators rejected on both write and read.
    def test_reject_path_sep(self):
        p = os.path.join(self.tdir, "rm.txt")
        with self.assertRaises(ValueError):
            write_remove_list(["foo/bar"], p)
        with open(p, "w", encoding="utf-8", newline="\n") as f:
            f.write("good_name\nbad/name\n")
        with self.assertRaises(ValueError):
            read_remove_list(p)

    # Tolerant read: blank lines, CRLFs, trailing whitespace.
    def test_tolerant_read(self):
        p = os.path.join(self.tdir, "rm.txt")
        with open(p, "wb") as f:
            f.write(b"merged_00002\r\n\nmerged_00001  \n")
        self.assertEqual(read_remove_list(p),
                         ["merged_00001", "merged_00002"])

    # Atomic write leaves no .tmp sibling.
    def test_atomic(self):
        p = os.path.join(self.tdir, "rm.txt")
        write_remove_list(["x"], p)
        self.assertFalse(os.path.exists(p + ".tmp"))

    # Apply removes listed files, tolerates missing, idempotent.
    def test_apply_idempotent(self):
        for i in range(5):
            with open(
                os.path.join(self.tdir, f"merged_{i:05d}"),
                "wb"
            ) as f:
                f.write(b"x")
        out = apply_remove_list(
            self.tdir,
            ["merged_00001", "merged_00003", "merged_99999"])
        self.assertEqual(out, (2, 1))
        self.assertFalse(os.path.exists(
            os.path.join(self.tdir, "merged_00001")))
        self.assertFalse(os.path.exists(
            os.path.join(self.tdir, "merged_00003")))
        self.assertTrue(os.path.exists(
            os.path.join(self.tdir, "merged_00000")))
        out2 = apply_remove_list(
            self.tdir,
            ["merged_00001", "merged_00003", "merged_99999"])
        self.assertEqual(out2, (0, 3))

    # Parallel apply against 200 files.
    def test_apply_parallel(self):
        for i in range(200):
            with open(
                os.path.join(self.tdir, f"merged_{i:05d}"),
                "wb"
            ) as f:
                f.write(b".")
        names = [f"merged_{i:05d}" for i in range(200)]
        out   = apply_remove_list(self.tdir, names)
        self.assertEqual(out, (200, 0))
        self.assertEqual(os.listdir(self.tdir), [])

    # Empty list apply: (0, 0), dir untouched.
    def test_apply_empty(self):
        with open(os.path.join(self.tdir, "x"), "wb") as f:
            f.write(b".")
        self.assertEqual(apply_remove_list(self.tdir, []),
                         (0, 0))

    # parse_sa_tsv: scrambled rows -> sorted+deduped basenames.
    def test_parse_tsv_basic(self):
        p = os.path.join(self.tdir, "x.tsv")
        with open(p, "w", encoding="utf-8") as f:
            f.write("5.7/5.0\t/abs/dir/merged_00005\n")
            f.write("7.4/5.0\t/abs/dir/merged_00002\n")
            f.write("5.7/5.0\t/abs/dir/merged_00005\n")
        self.assertEqual(parse_sa_tsv(p),
                         ["merged_00002", "merged_00005"])

    # parse_sa_tsv: empty TSV -> [].
    def test_parse_tsv_empty(self):
        p = os.path.join(self.tdir, "x.tsv")
        open(p, "w").close()
        self.assertEqual(parse_sa_tsv(p), [])

    # parse_sa_tsv: malformed/non-matching lines skipped.
    def test_parse_tsv_malformed(self):
        p = os.path.join(self.tdir, "x.tsv")
        with open(p, "w", encoding="utf-8") as f:
            f.write("no-tab-here\n")
            f.write("5.0/5.0\t/abs/not_merged_thing\n")
            f.write("5.0/5.0\t/abs/merged_00007\n")
        self.assertEqual(parse_sa_tsv(p), ["merged_00007"])


_HAVE_SA = (shutil.which("spamc") is not None
            and shutil.which("spamd") is not None
            and os.path.isfile(SA_SCRIPT))


class TestBlock6(unittest.TestCase):
    """Block 6: run_spamassassin."""

    def setUp(self):
        self.tdir = tempfile.mkdtemp(dir=UNIT_TEST_TMP)

    # Missing SA script raises before any subprocess call.
    def test_missing_script(self):
        tgt = os.path.join(self.tdir, "tgt"); os.makedirs(tgt)
        sa  = os.path.join(self.tdir, "sa");  os.makedirs(sa)
        out = os.path.join(self.tdir, "x.tsv")
        with self.assertRaises(FileNotFoundError):
            run_spamassassin(tgt, sa, out)

    # End-to-end wiring smoke test (slow; gated on spamc).
    @unittest.skipUnless(_HAVE_SA, "spamc/spamd/SA dir missing")
    def test_smoke(self):
        tgt = os.path.join(self.tdir, "tgt"); os.makedirs(tgt)
        ham  = (
            "From: bob@example.com\n"
            "To: alice@example.com\n"
            "Date: Mon, 01 Jan 2024 00:00:00 +0000\n"
            "Subject: Meeting tomorrow\n"
            "\n"
            "Hi Alice, are we still on for the meeting?\n"
        )
        spam = (
            "From: spammer@example.com\n"
            "To: victim@example.com\n"
            "Date: Mon, 01 Jan 2024 00:00:00 +0000\n"
            "Subject: BUY V14GR4 NOW!!! CHEAP MEDICATIONS\n"
            "\n"
            "Click here to buy cheap pills! Best prices.\n"
        )
        for i, body in enumerate([ham, spam]):
            with open(os.path.join(tgt, f"merged_{i:05d}"),
                      "wb") as f:
                f.write(body.encode("utf-8"))
        out = os.path.join(self.tdir, "scan.tsv")
        try:
            flagged = run_spamassassin(tgt, SA_DIR, out)
        except subprocess.CalledProcessError as e:
            self.skipTest(f"sa_baseline_scan.sh failed: {e}")
        self.assertIsInstance(flagged, list)
        for n in flagged:
            self.assertTrue(_MERGED_RE.match(n))

    # Two runs on the same corpus -> byte-identical remove lists.
    @unittest.skipUnless(_HAVE_SA, "spamc/spamd/SA dir missing")
    def test_canonical_twice(self):
        tgt = os.path.join(self.tdir, "tgt"); os.makedirs(tgt)
        msgs = [
            ("From: a@e.com\n"
             "Date: Mon, 01 Jan 2024 00:00:00 +0000\n"
             "Subject: hello\n\nordinary message body\n"),
            ("From: b@e.com\n"
             "Date: Mon, 01 Jan 2024 00:00:00 +0000\n"
             "Subject: BUY V14GR4 NOW CHEAP MEDS\n"
             "\nbuy buy buy now now now!!!\n"),
        ]
        for i, m in enumerate(msgs):
            with open(os.path.join(tgt, f"merged_{i:05d}"),
                      "wb") as f:
                f.write(m.encode("utf-8"))
        out_a = os.path.join(self.tdir, "a.tsv")
        out_b = os.path.join(self.tdir, "b.tsv")
        try:
            list_a = run_spamassassin(tgt, SA_DIR, out_a)
            list_b = run_spamassassin(tgt, SA_DIR, out_b)
        except subprocess.CalledProcessError as e:
            self.skipTest(f"sa_baseline_scan.sh failed: {e}")
        self.assertEqual(list_a, list_b)
        ra = os.path.join(self.tdir, "ra.txt")
        rb = os.path.join(self.tdir, "rb.txt")
        write_remove_list(list_a, ra)
        write_remove_list(list_b, rb)
        with open(ra, "r", encoding="utf-8") as f:
            ta = f.read()
        with open(rb, "r", encoding="utf-8") as f:
            tb = f.read()
        self.assertEqual(ta, tb)


class TestBlock7(unittest.TestCase):
    """Block 7: merge map + write_all_records."""

    def setUp(self):
        self.tdir = tempfile.mkdtemp(dir=UNIT_TEST_TMP)

    def _basic_plan(self):
        return [
            {"target_name": "merged_00000",
             "list_src": [
                 {"relpath": "a",     "size": 4},
                 {"relpath": "sub/b", "size": 8}]},
            {"target_name": "merged_00001",
             "list_src": [{"relpath": "c", "size": 200}]},
            {"target_name": "merged_00002",
             "list_src": [
                 {"relpath": "d", "size": 1},
                 {"relpath": "e", "size": 1}]},
        ]

    # Exact canonical text on disk.
    def test_text_exact(self):
        plan = self._basic_plan()
        p    = os.path.join(self.tdir, "map.txt")
        write_merge_map(plan, p)
        with open(p, "r", encoding="utf-8") as f:
            text = f.read()
        expected = ("merged_00000\ta\tsub/b\n"
                    "merged_00001\tc\n"
                    "merged_00002\td\te\n")
        self.assertEqual(text, expected)

    # Plan order on disk; lex sort of lines equals file order.
    def test_plan_order(self):
        plan = self._basic_plan()
        p    = os.path.join(self.tdir, "map.txt")
        write_merge_map(plan, p)
        with open(p, "r", encoding="utf-8") as f:
            lines = f.read().splitlines()
        self.assertEqual(lines, sorted(lines))

    # Read returns plan shape (relpaths only, no sizes).
    def test_roundtrip(self):
        plan = self._basic_plan()
        p    = os.path.join(self.tdir, "map.txt")
        write_merge_map(plan, p)
        got = read_merge_map(p)
        expected = [
            {"target_name": b["target_name"],
             "list_src": [{"relpath": s["relpath"]}
                          for s in b["list_src"]]}
            for b in plan
        ]
        self.assertEqual(got, expected)

    # Two writes are byte-identical.
    def test_canonical_twice(self):
        plan = self._basic_plan()
        pa = os.path.join(self.tdir, "a.txt")
        pb = os.path.join(self.tdir, "b.txt")
        write_merge_map(plan, pa)
        write_merge_map(plan, pb)
        with open(pa, "r", encoding="utf-8") as f:
            ta = f.read()
        with open(pb, "r", encoding="utf-8") as f:
            tb = f.read()
        self.assertEqual(ta, tb)

    # Tab/newline in relpath rejected.
    def test_reject_tab_newline(self):
        for bad_rp in ("a\tb", "a\nb", "a\rb"):
            bad = [{"target_name": "merged_00000",
                    "list_src": [{"relpath": bad_rp,
                                  "size": 1}]}]
            with self.assertRaises(ValueError):
                write_merge_map(bad,
                                os.path.join(self.tdir, "m.txt"))

    # Corrupted map raises on read.
    def test_corrupted_map(self):
        p = os.path.join(self.tdir, "map.txt")
        with open(p, "w", encoding="utf-8", newline="\n") as f:
            f.write("merged_00005\ta\n")
            f.write("merged_00003\tb\n")
        with self.assertRaises(ValueError):
            read_merge_map(p)
        with open(p, "w", encoding="utf-8", newline="\n") as f:
            f.write("not_a_merged_name\ta\n")
        with self.assertRaises(ValueError):
            read_merge_map(p)

    # Atomic write leaves no .tmp sibling.
    def test_atomic(self):
        p = os.path.join(self.tdir, "map.txt")
        write_merge_map(self._basic_plan(), p)
        self.assertFalse(os.path.exists(p + ".tmp"))

    # write_all_records emits 3 files byte-identical across runs.
    def test_write_all_records_twice(self):
        plan = self._basic_plan()
        fl   = [{"relpath": "a",     "size": 4},
                {"relpath": "sub/b", "size": 8},
                {"relpath": "c",     "size": 200},
                {"relpath": "d",     "size": 1},
                {"relpath": "e",     "size": 1}]
        rm   = ["merged_00001"]

        d_a = os.path.join(self.tdir, "ra")
        d_b = os.path.join(self.tdir, "rb")
        write_all_records(d_a, fl, plan, rm)
        write_all_records(d_b, fl, plan, rm)

        for fn in ("email_filelist.txt",
                   "email_merge_map.txt",
                   "email_remove_list.txt"):
            with open(os.path.join(d_a, fn), "r",
                      encoding="utf-8") as f:
                ta = f.read()
            with open(os.path.join(d_b, fn), "r",
                      encoding="utf-8") as f:
                tb = f.read()
            self.assertEqual(ta, tb, fn)

    # remove_names=None: no remove list file emitted.
    def test_write_all_records_no_sa(self):
        plan = self._basic_plan()
        fl   = [{"relpath": "a", "size": 4}]
        d    = os.path.join(self.tdir, "r")
        write_all_records(d, fl, plan, None)
        self.assertFalse(os.path.exists(
            os.path.join(d, "email_remove_list.txt")))
        self.assertTrue(os.path.exists(
            os.path.join(d, "email_filelist.txt")))
        self.assertTrue(os.path.exists(
            os.path.join(d, "email_merge_map.txt")))


# ---- runner ---------------------------------------------------------

# Wipe UNIT_TEST_TMP, run unittest, rmtree on exit.  Every test must
# create its own subdir via tempfile.mkdtemp(dir=UNIT_TEST_TMP) so the
# outer rmtree is the only cleanup needed.
def run_unit_tests():
    shutil.rmtree(UNIT_TEST_TMP, ignore_errors=True)
    os.makedirs(UNIT_TEST_TMP)
    try:
        prog = unittest.main(argv=[sys.argv[0], "-v"], exit=False)
    finally:
        shutil.rmtree(UNIT_TEST_TMP, ignore_errors=True)
    if not prog.result.wasSuccessful():
        sys.exit(1)


# Format n bytes as e.g. "8.62 GiB" for human-readable stats.
def _human_size(n):
    if n < 1024:
        return f"{n} B"
    x = float(n)
    for unit in ("KiB", "MiB", "GiB", "TiB", "PiB"):
        x /= 1024
        if x < 1024:
            return f"{x:.2f} {unit}"
    return f"{x:.2f} EiB"


# Print up-front warning about the two SA modes; exit if the remove
# list is missing and --rescan was not requested.
def _print_time_warning(rescan, list_exists):
    print("=" * 60)
    print("gen_merged128k_email.py")
    print("=" * 60)
    # Estimates measured on the Enron 517k-file / 11k-bin corpus
    # at 32 cores; update if the dataset materially changes.
    if rescan:
        print("MODE: --rescan -> running SpamAssassin")
        print("      (~16 min: a/b/c/e ~45 s + SA scan ~15 min)")
    elif list_exists:
        print("MODE: existing remove list found -> reading it")
        print("      (~1 min: merge pipeline only)")
    else:
        print("ERROR: remove list not found at:")
        print(f"  {REMOVE_LIST_PATH}")
        print("  Re-run with --rescan to run SpamAssassin and")
        print("  generate it (~16 min on this dataset).")
        sys.exit(1)
    print()


# Execute steps [a]-[e], run integration tests, then stats.  Every
# major step is framed by step_enter / step_done with wall-clock.
def _run_pipeline(args):
    list_exists = os.path.isfile(REMOVE_LIST_PATH)
    _print_time_warning(args.rescan, list_exists)

    check_dependencies(need_sa=args.rescan)
    check_data_folders(SRC_DIR, TARGET_DIR, RECORDS_DIR,
                       SA_DIR, need_sa=args.rescan)

    t0 = step_enter("[a] canonical_file_list")
    fl = canonical_file_list(SRC_DIR)
    print(f"  files: {len(fl)}")
    step_done("[a] canonical_file_list", t0)

    t0 = step_enter("[b] compute_merge_plan")
    plan = compute_merge_plan(fl, TARGET_SIZE)
    print(f"  bins:  {len(plan)}")
    step_done("[b] compute_merge_plan", t0)

    t0 = step_enter("[c] exec_merge_plan")
    exec_merge_plan(SRC_DIR, TARGET_DIR, plan)
    step_done("[c] exec_merge_plan", t0)

    t0 = step_enter("[d] spam filter")
    if args.rescan:
        flagged = run_spamassassin(TARGET_DIR, SA_DIR,
                                   SA_TSV_PATH)
        write_remove_list(flagged, REMOVE_LIST_PATH)
        print(f"  flagged (SA scan): {len(flagged)}")
    else:
        flagged = read_remove_list(REMOVE_LIST_PATH)
        print(f"  flagged (existing list): {len(flagged)}")
    n_del, n_miss = apply_remove_list(TARGET_DIR, flagged)
    print(f"  deleted: {n_del}, missing: {n_miss}")
    step_done("[d] spam filter", t0)

    t0 = step_enter("[e] write_all_records")
    write_all_records(RECORDS_DIR, fl, plan, flagged)
    step_done("[e] write_all_records", t0)

    t0 = step_enter("integration tests")
    integ_test_random_sample_in_merged(
        SRC_DIR, TARGET_DIR, plan, flagged,
        args.integ_samples)
    integ_test_size_accounting(
        SRC_DIR, TARGET_DIR, flagged, RECORDS_DIR)
    step_done("integration tests", t0)

    # Final stats.
    n_orig    = len(fl)
    t_orig    = sum(r["size"] for r in fl)
    size_of   = {r["relpath"]: r["size"] for r in fl}
    removed_s = set(flagged)
    n_removed = len(flagged)
    t_removed = sum(
        size_of[s["relpath"]]
        for b in plan if b["target_name"] in removed_s
        for s in b["list_src"])
    final_files = [
        n for n in os.listdir(TARGET_DIR)
        if os.path.isfile(os.path.join(TARGET_DIR, n))]
    n_final = len(final_files)
    t_final = sum(
        os.path.getsize(os.path.join(TARGET_DIR, n))
        for n in final_files)

    n_generated = len(plan)
    print()
    print("=== summary ===")
    print(f"original set:     {n_orig} files, "
          f"{t_orig} bytes ({_human_size(t_orig)})")
    print(f"merged generated: {n_generated} files")
    print(f"merged removed:   {n_removed} files, "
          f"{t_removed} bytes ({_human_size(t_removed)})")
    print(f"merged left:      {n_final} files, "
          f"{t_final} bytes ({_human_size(t_final)})")
    print(f"records: "
          f"{os.path.join(RECORDS_DIR, 'email_filelist.txt')}")
    print(f"         "
          f"{os.path.join(RECORDS_DIR, 'email_merge_map.txt')}")
    if os.path.isfile(REMOVE_LIST_PATH):
        print(f"         {REMOVE_LIST_PATH}")
    print("done.")


# =====================================================================
# install orchestration
# =====================================================================

# Remove ALL scratch under /tmp/bora_install (item 4).
def cleanup_temp():
    shutil.rmtree(TMP_DIR, ignore_errors=True)


# =====================================================================
# per-dataset setup (clean) + install
#
# Each clean_X empties only that dataset's target dirs (keeping the dir
# names, per item 4).  cache/main is ensured-present but never wiped
# (the install does not repopulate its expensive DFA/key caches, so
# wiping it would be the one "overkill") -- main() handles that once.
# =====================================================================

# Download + extract + deploy the shared samples.7z payload once per
# run (binexec and email both consume it).
_samples_ready = False


def ensure_samples_deployed():
    global _samples_ready
    if _samples_ready:
        return
    samples_7z = os.path.join(TMP_DIR, "samples.7z")
    print("  download samples.7z")
    gdrive_download(SAMPLES_ID, samples_7z)
    print("  extract + deploy samples")
    extract_7z(samples_7z, EXTRACT_DIR)
    deploy_samples(EXTRACT_DIR)
    _samples_ready = True


# ---- binexec (CentOS binaries) -------------------------------------

# Empty the binexec target dirs (kept).
def clean_binexec():
    empty_dir(os.path.join(SAMPLES_DIR, "binexec_merged128k"))
    empty_dir(os.path.join(SAMPLES_DIR, "merge_records"))


# Deploy samples + run the binexec merge.
def install_dataset_binexec():
    ensure_samples_deployed()
    install_binexec()


# ---- email (Enron) -------------------------------------------------

# Empty the email target dirs (kept).
def clean_email():
    empty_dir(os.path.join(SAMPLES_DIR, "email_merged128k"))
    empty_dir(os.path.join(SAMPLES_DIR, "merged_records_email"))


# Deploy samples + run the email merge + SpamAssassin scan (rescan
# hardwired on, per spec) + the inline integration tests.
def install_dataset_email():
    ensure_samples_deployed()
    _run_pipeline(argparse.Namespace(rescan=True, integ_samples=100))


# ---- dna (chr17 / sig_c21 variants) --------------------------------

# Empty the dna target dirs (kept).
def clean_dna():
    empty_dir(os.path.join(SAMPLES_DIR, "chr17_samples"))
    empty_dir(os.path.join(SRC_SIG_DIR, "chr17_variants"))


# Download + extract sig_c21.7z and deploy chr17_samples / chr17_variants.
def install_dataset_dna():
    sig_7z = os.path.join(TMP_DIR, "sig_c21.7z")
    print("  download sig_c21.7z")
    gdrive_download(SIG_C21_ID, sig_7z)
    print("  extract sig_c21.7z")
    extract_7z(sig_7z, EXTRACT_DIR)
    deploy_chr17(EXTRACT_DIR)


# Registry in menu order: (key, label, est. installed GB, clean, install).
DATASETS = [
    ("email",   "email (Enron)",          3.8,
     clean_email,   install_dataset_email),
    ("dna",     "dna (chr17 variants)",   6.6,
     clean_dna,     install_dataset_dna),
    ("binexec", "binexec (CentOS bins)",  1.5,
     clean_binexec, install_dataset_binexec),
]


# =====================================================================
# install orchestration
# =====================================================================

# Show the sized menu and return the ordered list of dataset keys to
# install.  Empty input (or no tty) -> ALL.
def select_datasets():
    total = sum(d[2] for d in DATASETS)
    all_keys = [d[0] for d in DATASETS]
    if not sys.stdin.isatty():
        print("non-interactive: installing ALL.")
        return all_keys
    print("Select data to install:")
    print("  (1) ALL                      ~%4.1f GB   [default]" % total)
    for i, (key, label, gb, _c, _i) in enumerate(DATASETS, start=2):
        print("  (%d) %-24s ~%4.1f GB" % (i, label, gb))
    try:
        choice = input("choice [1]: ").strip().lower()
    except EOFError:
        choice = ""
    if choice in ("", "1", "all"):
        return all_keys
    for i, d in enumerate(DATASETS, start=2):
        if choice in (str(i), d[0]):
            return [d[0]]
    print("unrecognized choice %r; installing ALL." % choice)
    return all_keys


def main():
    keys = [d[0] for d in DATASETS]
    ap = argparse.ArgumentParser(
        description="Install new_zkregplus data into ./data.")
    ap.add_argument("--data", choices=["all"] + keys,
                    help="non-interactive dataset selection")
    ap.add_argument("--test", action="store_true",
                    help="run inline unit tests and exit")
    ap.add_argument("--skip-tests", action="store_true",
                    help="skip the inline unit tests")
    args = ap.parse_args()

    if args.test:
        run_unit_tests()
        return

    if args.data:
        selected = keys if args.data == "all" else [args.data]
    else:
        selected = select_datasets()

    check_install_deps()
    # email unit tests are only relevant (and only need spamd) when the
    # email dataset is in the selection.
    if "email" in selected and not args.skip_tests:
        run_unit_tests()

    os.makedirs(TMP_DIR, exist_ok=True)
    os.makedirs(CACHE_MAIN, exist_ok=True)        # ensure (never wiped)
    by_key = {d[0]: d for d in DATASETS}
    try:
        for key in selected:
            _, label, _gb, clean_fn, install_fn = by_key[key]
            print("=== install %s ===" % label)
            clean_fn()                            # empty targets (item 4)
            install_fn()
    finally:
        cleanup_temp()

    print("INSTALL complete: %s" % ", ".join(selected))


if __name__ == "__main__":
    main()
