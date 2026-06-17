#!/usr/bin/env python3
# ---------------------------------------------------------------------
# INSTALL.py  --  one-shot data installer for new_zkregplus.
#
# Downloads + extracts the sample archive into data/, runs the binexec
# merge pipeline (folded in from the former data/samples/gen_data.py),
# and deploys the chromosome-17 (sig_c21) variants.  The email dataset
# only scans the maildir and reports a merge plan (no merged blobs or
# records are written).  All scratch lives under /tmp/bora_install and
# is removed on completion.
#
# Run from anywhere:
#   python3 INSTALL.py             menu: pick ALL / email / dna / binexec
#   python3 INSTALL.py --data all  non-interactive (all|email|dna|binexec)
#
# NOTE: python file generated under the instruction of paper author.
#   code reviewed and tested manually by paper author.
# ---------------------------------------------------------------------

import argparse
import os
import shutil
import subprocess
import sys
import time

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
SIG_C21_ID  = "https://drive.google.com/file/d/1314OL6_FYLmBH2i2_kQd7fwuVv73g6LU/view?usp=sharing"   # sig_c21*.7z
SIG_C21_TOP = "chr17_variants"                      # archive top dir

# ---- email-pipeline globals (re-anchored from the former script) ----
SRC_DIR          = os.path.join(SAMPLES_DIR, "email", "src", "maildir")
TARGET_DIR       = os.path.join(SAMPLES_DIR, "email_merged128k")
RECORDS_DIR      = os.path.join(SAMPLES_DIR, "merged_records_email")
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


# Download a Google Drive file to dest (skips if already present).
# Accepts either a bare file id (SAMPLES_ID) or a full share URL
# (".../file/d/<id>/view?usp=sharing", as SIG_C21_ID now is); fuzzy=True
# lets gdown extract the id from the URL form.
def gdrive_download(file_id_or_url, dest):
    import gdown
    if os.path.isfile(dest):
        print("  cached: %s" % dest)
        return
    if "://" in file_id_or_url:
        gdown.download(url=file_id_or_url, output=dest,
                       quiet=False, fuzzy=True)
    else:
        url = ("https://drive.google.com/uc?export=download&id=%s"
               % file_id_or_url)
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


# Deploy the chr17 (sig_c21) payload: the whole top folder (INCLUDING
# chr17_samples) -> data/src_sig/chr17_variants (item 3).  chr17_samples
# is NOT moved out; instead data/samples/chr17_samples is a symlink into
# chr17_variants/chr17_samples, so the corpus lives in one place only.
# The link target is relative, so it survives a repo relocation.
def deploy_chr17(extract_root):
    top = os.path.join(extract_root, SIG_C21_TOP)
    dst_var = os.path.join(SRC_SIG_DIR, "chr17_variants")
    empty_dir(dst_var)
    move_children(top, dst_var)
    # expose chr17_variants/chr17_samples under data/samples/ via symlink.
    link_target = os.path.join(dst_var, "chr17_samples")
    link_path   = os.path.join(SAMPLES_DIR, "chr17_samples")
    os.makedirs(SAMPLES_DIR, exist_ok=True)
    if os.path.islink(link_path):          # stale link: unlink only
        os.remove(link_path)
    elif os.path.isdir(link_path):         # legacy real dir: drop it
        shutil.rmtree(link_path)
    elif os.path.exists(link_path):
        os.remove(link_path)
    os.symlink(os.path.relpath(link_target, SAMPLES_DIR), link_path)


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


# ---- folder checks --------------------------------------------------

# Verify src_dir exists; create target_dir and records_dir if missing.
# Exits on hard errors.
def check_data_folders(src_dir, target_dir, records_dir):
    if not os.path.isdir(src_dir):
        print(f"ERROR: source dir not found: {src_dir}")
        sys.exit(1)
    os.makedirs(target_dir,  exist_ok=True)
    os.makedirs(records_dir, exist_ok=True)


# ---- block 2: canonical file list -----------------------------------

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


# Scan the maildir and compute the merge plan as a dry run.  The
# merged email_merged128k blobs and records are no longer created.
def _run_pipeline():
    check_data_folders(SRC_DIR, TARGET_DIR, RECORDS_DIR)

    t0 = step_enter("[a] canonical_file_list")
    fl = canonical_file_list(SRC_DIR)
    print(f"  files: {len(fl)}")
    step_done("[a] canonical_file_list", t0)

    t0 = step_enter("[b] compute_merge_plan")
    plan = compute_merge_plan(fl, TARGET_SIZE)
    print(f"  bins:  {len(plan)}")
    step_done("[b] compute_merge_plan", t0)

    # Final stats (dry run -- nothing is written to disk).
    n_orig      = len(fl)
    t_orig      = sum(r["size"] for r in fl)
    n_generated = len(plan)
    print()
    print("=== summary ===")
    print(f"original set: {n_orig} files, "
          f"{t_orig} bytes ({_human_size(t_orig)})")
    print(f"merge plan:   {n_generated} bins (not materialized)")
    print("note: email_merged128k and records are not created.")
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


# Deploy samples + scan the maildir and compute the merge plan.
def install_dataset_email():
    ensure_samples_deployed()
    _run_pipeline()


# ---- dna (chr17 / sig_c21 variants) --------------------------------

# Empty the dna target dirs (kept).  chr17_samples under samples/ is a
# symlink into chr17_variants; UNLINK it (never empty_dir -- that would
# follow the link and delete the real payload).  chr17_variants holds
# the real chr17_samples, so emptying it wipes the corpus.
def clean_dna():
    link = os.path.join(SAMPLES_DIR, "chr17_samples")
    if os.path.islink(link):
        os.remove(link)
    elif os.path.isdir(link):              # legacy real dir from old layout
        shutil.rmtree(link)
    elif os.path.exists(link):
        os.remove(link)
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
    args = ap.parse_args()

    if args.data:
        selected = keys if args.data == "all" else [args.data]
    else:
        selected = select_datasets()

    check_install_deps()

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
