#!/usr/bin/env python3
# ---------------------------------------------------------------------
# INSTALL.py  --  one-shot data installer for new_zkregplus.
#
# Downloads + extracts data into data/.  The email dataset (Enron) is
# fetched from the CMU source and placed under data/samples/email/src/
# maildir; samples.7z is a byte-identical fallback used only when the
# CMU host is unreachable.  The binexec merge pipeline and chr17
# (sig_c21) variants deploy from samples.7z / sig_c21.7z.  All scratch
# lives under /tmp/bora_install and is removed on completion.
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

# ---- email (Enron) source ------------------------------------------
# Primary = the CMU release (May 7 2015).  EMAIL_TREE_DIGEST is sha256
# over the sorted "sha256  ./relpath" manifest of maildir; it gates a
# freshly downloaded corpus before we trust it.
ENRON_URL = ("https://www.cs.cmu.edu/~./enron/"
             "enron_mail_20150507.tar.gz")
EMAIL_DIR     = os.path.join(SAMPLES_DIR, "email")
EMAIL_MAILDIR = os.path.join(EMAIL_DIR, "src", "maildir")
EMAIL_README  = os.path.join(EMAIL_DIR, "README.md")
EMAIL_TREE_DIGEST = \
    "1381aa3063f8c8f0975d20532c5b7a8cafac016af35fe676d5e6405cc199ba7a"
EMAIL_README_TEXT = (
    "source: https://www.cs.cmu.edu/~./enron/\n"
    "May 7, 2015 version: "
    "https://www.cs.cmu.edu/~./enron/enron_mail_20150507.tar.gz\n"
    "\n"
    "The emails live in the sibling folder src/maildir/.\n"
)

# ---- binexec-pipeline globals (from the former gen_data.py) ---------
BINEXEC_SRC = "binexec"                           # under SAMPLES_DIR
BINEXEC_TGT = "binexec_merged128k"
TARGET_SIZE = 128 * 1024                          # 128 KB merge target
# Leave <100 KiB headroom under 32 MiB so the loc encoding never
# overflows range2_bit=26 in full_data4 (see discharge_sig.rs).
SPLIT_SIZE  = 32 * 1024 * 1024 - 100 * 1024


# =====================================================================
# toolchain install  (Rust 1.76 + system build deps)
#
# Brings a bare Ubuntu 24 instance to a buildable state: apt build deps
# (incl. lld, required by the fused-ld link), p7zip, pip+gdown, and the
# rustup-managed 1.76.0 toolchain pinned by ./rust-toolchain.  Idempotent;
# needs sudo for apt.
# =====================================================================

APT_PACKAGES = [
    "build-essential", "lld", "pkg-config", "libssl-dev",
    "curl", "git", "p7zip-full", "python3-pip",
]
RUST_VERSION = "1.76.0"


# Run argv, echoing it; raise on non-zero.
def run_cmd(argv):
    print("  $ " + " ".join(argv))
    subprocess.run(argv, check=True)


# Install apt build deps (lld is required by the fused-ld link).
def install_apt_deps():
    sudo = [] if os.geteuid() == 0 else ["sudo"]
    run_cmd(sudo + ["apt-get", "update"])
    run_cmd(sudo + ["apt-get", "install", "-y"] + APT_PACKAGES)


# pip-install gdown (Ubuntu 24 is PEP-668 managed -> retry w/ override).
def install_pip_deps():
    try:
        run_cmd([sys.executable, "-m", "pip", "install", "--user",
                 "gdown"])
    except subprocess.CalledProcessError:
        run_cmd([sys.executable, "-m", "pip", "install", "--user",
                 "--break-system-packages", "gdown"])


# Install rustup non-interactively, then the pinned 1.76.0 toolchain.
def install_rust():
    cargo_bin = os.path.expanduser("~/.cargo/bin")
    rustup = os.path.join(cargo_bin, "rustup")
    if shutil.which("rustup") is None and not os.path.isfile(rustup):
        run_cmd(["bash", "-c",
                 "curl --proto '=https' --tlsv1.2 -sSf "
                 "https://sh.rustup.rs | sh -s -- -y "
                 "--default-toolchain " + RUST_VERSION])
    run_cmd([rustup, "toolchain", "install", RUST_VERSION])
    persist_cargo_env()
    print("  rust %s ready (pinned by ./rust-toolchain)" % RUST_VERSION)


# Append `source ~/.cargo/env` to ~/.bashrc so new shells get cargo on
# PATH. Idempotent: skips if any .cargo/env line is already present
# (rustup usually adds its own `. "$HOME/.cargo/env"`).
def persist_cargo_env():
    rc = os.path.expanduser("~/.bashrc")
    try:
        existing = open(rc).read() if os.path.isfile(rc) else ""
        if ".cargo/env" in existing:
            return
        with open(rc, "a") as f:
            f.write('\n# added by new_zkregplus INSTALL.py\n'
                    'source "$HOME/.cargo/env"\n')
        print("  persisted cargo PATH -> %s" % rc)
    except OSError as e:
        print("  WARN: could not update %s (%s)" % (rc, e))


# Full toolchain bring-up for a fresh instance (force all steps).
def install_toolchain():
    print("=== install toolchain (Rust %s + build deps) ==="
          % RUST_VERSION)
    install_apt_deps()
    install_pip_deps()
    install_rust()
    print("toolchain ready -- build with:")
    print('  RUSTFLAGS="-C link-args=-fuse-ld=lld -Awarnings" '
          "cargo build --release")


# True if every binary the apt packages provide is already on PATH.
def apt_tools_present():
    need = ("ld.lld", "7za", "cc", "pkg-config", "git", "curl")
    return all(shutil.which(b) is not None for b in need)


# True if the gdown python module imports.
def have_gdown():
    try:
        import gdown  # noqa: F401
        return True
    except ImportError:
        return False


# True if rustup exists AND the pinned 1.76.0 toolchain is installed.
def have_rust():
    rustup = shutil.which("rustup") or \
        os.path.join(os.path.expanduser("~/.cargo/bin"), "rustup")
    if not os.path.isfile(rustup) and shutil.which("rustup") is None:
        return False
    try:
        out = subprocess.run([rustup, "toolchain", "list"],
                             capture_output=True, text=True, check=True)
        return RUST_VERSION in out.stdout
    except (subprocess.CalledProcessError, FileNotFoundError):
        return False


# Default gate: install only the tools that are missing (idempotent).
def ensure_toolchain():
    ok_apt, ok_gdown, ok_rust = \
        apt_tools_present(), have_gdown(), have_rust()
    if ok_apt and ok_gdown and ok_rust:
        print("toolchain present (apt deps, gdown, rust %s)."
              % RUST_VERSION)
        return
    print("=== ensure toolchain (installing missing tools) ===")
    if not ok_apt:
        install_apt_deps()
    if not ok_gdown:
        install_pip_deps()
    if not ok_rust:
        install_rust()


# =====================================================================
# download tooling + filesystem helpers
# =====================================================================

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

# Write the source-provenance README beside src/ (both install paths).
def write_email_readme():
    os.makedirs(EMAIL_DIR, exist_ok=True)
    with open(EMAIL_README, "w") as f:
        f.write(EMAIL_README_TEXT)


# True if the CMU host answers a quick HEAD for the tarball.
def cmu_email_available():
    try:
        subprocess.run(
            ["curl", "-fsI", "--connect-timeout", "10",
             "--max-time", "20", ENRON_URL],
            check=True, stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL)
        return True
    except (subprocess.CalledProcessError, FileNotFoundError):
        return False


# sha256 over the sorted "sha256  ./relpath" manifest of maildir,
# matching the fingerprint compared against EMAIL_TREE_DIGEST.
def maildir_tree_digest(maildir):
    cmd = ("set -o pipefail; find . -type f -print0 | LC_ALL=C sort -z "
           "| xargs -0 sha256sum | sha256sum")
    out = subprocess.run(["bash", "-c", cmd], cwd=maildir,
                         capture_output=True, text=True, check=True)
    return out.stdout.split()[0]


# Empty the maildir so a re-install lands a clean corpus.
def clean_email():
    shutil.rmtree(EMAIL_MAILDIR, ignore_errors=True)


# Download the CMU tarball, verify its fingerprint, wipe-then-place the
# maildir at EMAIL_MAILDIR, and drop all scratch.  Raises on failure.
def install_email_from_cmu():
    scratch  = os.path.join(TMP_DIR, "enron_cmu")
    tar_path = os.path.join(TMP_DIR, "enron_mail_20150507.tar.gz")
    try:
        shutil.rmtree(scratch, ignore_errors=True)
        os.makedirs(scratch, exist_ok=True)
        print("  download enron_mail_20150507.tar.gz")
        subprocess.run(["curl", "-fL", "--retry", "3", "-o", tar_path,
                        ENRON_URL], check=True)
        print("  extract enron_mail_20150507.tar.gz")
        subprocess.run(["tar", "-xzf", tar_path, "-C", scratch],
                       check=True)
        src_maildir = os.path.join(scratch, "maildir")
        print("  verify corpus fingerprint")
        digest = maildir_tree_digest(src_maildir)
        if digest != EMAIL_TREE_DIGEST:
            raise RuntimeError(
                "CMU maildir digest mismatch: got %s" % digest)
        shutil.rmtree(EMAIL_MAILDIR, ignore_errors=True)
        os.makedirs(os.path.dirname(EMAIL_MAILDIR), exist_ok=True)
        shutil.move(src_maildir, EMAIL_MAILDIR)
        write_email_readme()
        print("  email (CMU) -> %s" % EMAIL_MAILDIR)
    finally:
        if os.path.isfile(tar_path):
            os.remove(tar_path)
        shutil.rmtree(scratch, ignore_errors=True)


# Fallback: deploy the maildir (among other samples) from samples.7z.
def install_email_from_samples7z():
    ensure_samples_deployed()
    write_email_readme()


# Prefer the CMU source; fall back to samples.7z only when CMU is
# unreachable or its download/verify fails.
def install_dataset_email():
    if cmu_email_available():
        try:
            install_email_from_cmu()
            return
        except Exception as e:
            print("  CMU install failed (%s); using samples.7z." % e)
    else:
        print("  CMU source unavailable; using samples.7z.")
    install_email_from_samples7z()


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
    ap.add_argument("--toolchain", action="store_true",
                    help="install Rust 1.76 + system build deps, then "
                         "exit (unless --data is also given)")
    args = ap.parse_args()

    if args.toolchain:
        install_toolchain()
        if not args.data:
            return

    if args.data:
        selected = keys if args.data == "all" else [args.data]
    else:
        selected = select_datasets()

    ensure_toolchain()                            # install missing tools

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

    print("\n" + "=" * 64)
    print("  IMPORTANT: if `cargo` is 'command not found' in THIS shell:")
    print("      source ~/.cargo/env")
    print("  New shells pick it up automatically (added to ~/.bashrc).")
    print("=" * 64)
    print("INSTALL complete: %s" % ", ".join(selected))


if __name__ == "__main__":
    main()
