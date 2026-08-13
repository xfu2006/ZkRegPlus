#!/usr/bin/env python3
# ---------------------------------------------------------------------
# INSTALL.py  --  one-shot data installer for bora.
#
# Downloads + extracts data into data/.  The email dataset (Enron) is
# fetched from the CMU source and placed under data/samples/email/src/
# maildir; samples.7z is a byte-identical fallback used only when the
# CMU host is unreachable.  The binexec corpus comes from its Zenodo
# deposit (DOI 10.5281/zenodo.21909549), which also carries the licence
# texts and the per-file manifest; the chr17 (dna) corpus comes from its own
# Zenodo deposit (DOI 10.5281/zenodo.21911045).  Both are sha256-verified.
# All scratch lives under /tmp/bora_install and is removed on completion.
#
# Run from anywhere:
#   python3 INSTALL.py             menu: pick ALL / email / dna / binexec
#   python3 INSTALL.py --data all  non-interactive (all|email|dna|binexec)
#
# NOTE: python file generated under the instruction of paper author.
#   code reviewed and tested manually by paper author.
# ---------------------------------------------------------------------

import argparse
import hashlib
import os
import shutil
import subprocess
import sys
import tarfile
import urllib.request

# ---- paths (anchored on this file so cwd never matters) -------------
# this file lives in scripts/, so the repo root is one level up.
ROOT        = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DATA_DIR    = os.path.join(ROOT, "data")
SAMPLES_DIR = os.path.join(DATA_DIR, "samples")
SRC_SIG_DIR = os.path.join(DATA_DIR, "src_sig")
CACHE_MAIN  = os.path.join(DATA_DIR, "cache", "main")
TMP_DIR     = "/tmp/bora_install"                 # all scratch (item 4)
EXTRACT_DIR = os.path.join(TMP_DIR, "extract")

# ---- Google Drive ids (src_sig.7z intentionally NOT fetched) --------
# Drive now serves ONLY the email fallback.  binexec and dna both come from
# Zenodo: DOI-pinned, sha256-verified, and free of Drive's download logging.
# SAMPLES_ID = "1OM_W54JxPEiV3S26XwY7f1qhEAVyFtv_"  # samples.7z -- RETIRED.
#   It backed only the email fallback, which is commented out below: the
#   fallback bypassed EMAIL_TREE_DIGEST, so a CMU outage silently yielded an
#   unverified corpus.  Enron now comes from CMU or not at all.
# SIG_C21_ID = ".../1314OL6_FYLmBH2i2_kQd7fwuVv73g6LU/..."  # superseded by
#                                                    # Zenodo, see DNA_URL
SIG_C21_TOP = "chr17_variants"                      # archive top dir

# ---- src_sig/.gitignore (canonical) --------------------------------
# Ignore everything under chr17_variants (large datasets) EXCEPT the
# scripts/ source tree, so the eval/gen scripts stay version-controlled
# while the corpora do not.  INSTALL.py OVERWRITES this on the dna deploy:
# an older single-line `chr17_variants` ignore would otherwise swallow
# scripts/ too, so anyone who installs without pulling a fresh checkout
# would lose those scripts from git.  Kept byte-identical to the committed
# data/src_sig/.gitignore.
SRC_SIG_GITIGNORE = os.path.join(SRC_SIG_DIR, ".gitignore")
SRC_SIG_GITIGNORE_TEXT = (
    "# Ignore everything under chr17_variants (large datasets: chr17_samples,\n"
    "# reef, reef_regex, variants, docs, ...) EXCEPT the scripts/ source tree.\n"
    "# Using chr17_variants/* (not chr17_variants) leaves the directory itself\n"
    "# un-excluded so the scripts/ re-include below can take effect; the sibling\n"
    "# data folders stay ignored, so `git reset --hard` never touches them.\n"
    "chr17_variants/*\n"
    "!chr17_variants/scripts/\n"
    "chr17_variants/scripts/__pycache__/\n"
)

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

# ---- binexec target dir (merge runs via samples/gen_data.py) --------
BINEXEC_TGT = "binexec_merged128k"


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
            f.write('\n# added by bora INSTALL.py\n'
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
# Only the email fallback still uses this: binexec and dna both moved to
# Zenodo (http_download + sha256).  Accepts either a bare file id (as
# SAMPLES_ID is) or a full ".../file/d/<id>/view?usp=sharing" share URL. We
# extract the id ourselves and always hand gdown a uc?id= link, so it works
# on older gdown (<4.0) too -- those lack the fuzzy= kwarg that the URL form
# would otherwise need (TypeError: unexpected keyword 'fuzzy').
def _extract_drive_id(s):
    import re
    for pat in (r"/file/d/([A-Za-z0-9_-]+)",      # .../file/d/<id>/view
                r"[?&]id=([A-Za-z0-9_-]+)",        # uc?export=...&id=<id>
                r"/d/([A-Za-z0-9_-]+)"):           # /d/<id>
        m = re.search(pat, s)
        if m:
            return m.group(1)
    return s  # already a bare id


def gdrive_download(file_id_or_url, dest):
    import gdown
    if os.path.isfile(dest):
        print("  cached: %s" % dest)
        return
    file_id = _extract_drive_id(file_id_or_url)
    url = ("https://drive.google.com/uc?export=download&id=%s" % file_id)
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
# binexec corpus source  (Zenodo)
#
# The CentOS corpus is archived at Zenodo with a DOI and a per-file
# manifest.  Two DOIs exist and they are not interchangeable:
#
#   concept  https://doi.org/10.5281/zenodo.21909549   latest version
#   version  https://doi.org/10.5281/zenodo.21909550   THESE bytes
#
# The paper cites the CONCEPT doi; the VERSION record is pinned here so
# a future v2 can never silently hand the installer different bytes than
# BINEXEC_SHA256 describes.  A doi.org URL resolves to an HTML landing
# page rather than to the file, so the direct file URL is what gets
# fetched; the digest is the integrity guarantee either way.
#
# The archive expands to centos_pack/{samples,licenses,manifest,
# README.md}.  ONLY samples/ goes into binexec/ -- gen_data.py merges
# every file it finds in that directory, so a stray README or licence
# text would become a scanned document and change the merge plan.
# =====================================================================

BINEXEC_DIR    = os.path.join(SAMPLES_DIR, "binexec")
BINEXEC_DOI    = "https://doi.org/10.5281/zenodo.21909549"
BINEXEC_URL    = ("https://zenodo.org/records/21909550/files/"
                  "centos_pack.tgz?download=1")
BINEXEC_SHA256 = ("7d7cd1ca57895d3649dfa7320d7b91605772ea771a"
                  "86954e43ecda4dd2591d4d")
LICENSES_DIR   = os.path.join(DATA_DIR, "licenses")
MANIFEST_DIR   = os.path.join(DATA_DIR, "manifest")
BINEXEC_DOC    = os.path.join(DATA_DIR, "DATASET_BINEXEC.md")

# ---- dna (chr17 x NCBI ClinVar) Zenodo deposit ----------------------
# DNA_DOI is the CONCEPT doi (always resolves to the newest version, cite
# this); DNA_URL pins version v1 so the bytes never move under us.  The
# archive omits scripts/ (they live in git), Reef's commitment file, and
# Reef's target/ + tests/ -- all regenerated on first use; see its
# README.md and PROVENANCE.md.
DNA_DOI    = "https://doi.org/10.5281/zenodo.21911045"
DNA_URL    = ("https://zenodo.org/records/21911046/files/"
              "bora_dna.7z?download=1")
DNA_SHA256 = ("fd83ee6bcde431037ce986b0b52a7597000b439a0"
              "4461cf74a420c4892a2d0ca")
REEF_DIR   = os.path.join(SRC_SIG_DIR, "chr17_variants", "reef")
REEF_BIN   = os.path.join(REEF_DIR, "target", "release", "reef")

# ---- oversized in-repo fixtures (the bigfiles pack) -----------------
# anonymous.4open.science refuses to serve any file over 8 MB, and it gives
# no warning when it drops one -- the file is simply absent.  Thirteen
# tracked fixtures exceed that, so the anonymous snapshot ships them inside
# one xz archive instead of as loose files and restores them here.
#
# Nothing is regenerated or re-encoded: the archive holds the exact bytes
# that are in git, and every restored file is checked against the digest
# recorded when the pack was built (scripts/prepare_open4s/prepare.py).
#
# The expected digests are READ FROM BIGFILES_SUMS rather than hardcoded
# here.  tar records mtimes, so a rebuilt pack has a different sha256 even
# from identical inputs; a constant in this file would drift silently the
# first time the snapshot was rebuilt.
#
# A full git checkout has these files loose and no pack, so this is a no-op
# there.  Both absent is a broken artifact and raises.
BIGFILES_PACK = os.path.join(DATA_DIR, "bigfiles.tar.xz")
BIGFILES_SUMS = os.path.join(DATA_DIR, "bigfiles.sha256")

# Set by main() from --verify / --skip-reef-build; the DATASETS registry
# calls install functions with no arguments, so flags travel as module state.
_VERIFY_ALL = False
_SKIP_REEF_BUILD = False


def sha256_file(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


# Stream a URL to dest, reporting progress on a single line.  Uses
# urllib so this path needs no curl/wget/gdown.
def http_download(url, dest):
    os.makedirs(os.path.dirname(dest), exist_ok=True)
    tmp = dest + ".part"
    with urllib.request.urlopen(url, timeout=120) as r, open(tmp, "wb") as f:
        total = int(r.headers.get("Content-Length") or 0)
        done = 0
        while True:
            chunk = r.read(1 << 20)
            if not chunk:
                break
            f.write(chunk)
            done += len(chunk)
            if total:
                print("\r    %5.1f%%  %d/%d MB"
                      % (100.0 * done / total, done >> 20, total >> 20),
                      end="", flush=True)
        print()
    os.replace(tmp, dest)


# =====================================================================
# bigfiles pack -- restore the fixtures 4open.science will not serve
# =====================================================================

# Parse data/bigfiles.sha256 -> (pack_digest, {repo-rel path: digest}).
# Format is `sha256␣␣name`, first line the pack itself, the rest members.
def read_bigfiles_sums():
    pack_sha, members = None, {}
    with open(BIGFILES_SUMS) as fh:
        for line in fh:
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            digest, _, name = line.partition("  ")
            if not name:
                raise RuntimeError("malformed line in %s: %r"
                                   % (BIGFILES_SUMS, line))
            if pack_sha is None and name == os.path.basename(BIGFILES_PACK):
                pack_sha = digest
            else:
                members[name] = digest
    if pack_sha is None:
        raise RuntimeError("%s names no digest for %s"
                           % (BIGFILES_SUMS, os.path.basename(BIGFILES_PACK)))
    if not members:
        raise RuntimeError("%s lists no members" % BIGFILES_SUMS)
    return pack_sha, members


# Restore the 13 oversized fixtures from data/bigfiles.tar.xz.
#
# Idempotent: returns early when every member is already present and
# correct, so re-running INSTALL.py costs one pass of hashing and nothing
# else.  Raises rather than half-restoring -- a silently missing fixture
# would surface much later as an unexplained eval failure.
def restore_bigfiles():
    have_pack = os.path.isfile(BIGFILES_PACK)
    have_sums = os.path.isfile(BIGFILES_SUMS)

    if not have_pack and not have_sums:
        # Ordinary full checkout: the fixtures are loose in git.
        return

    if not have_pack or not have_sums:
        raise RuntimeError(
            "incomplete bigfiles pack: %s is present but %s is missing. "
            "Re-download the artifact; do not proceed."
            % ((BIGFILES_PACK, BIGFILES_SUMS) if have_pack
               else (BIGFILES_SUMS, BIGFILES_PACK)))

    pack_sha, members = read_bigfiles_sums()

    missing = [rel for rel in members
               if not os.path.isfile(os.path.join(ROOT, rel))]
    if not missing:
        stale = [rel for rel, want in members.items()
                 if sha256_file(os.path.join(ROOT, rel)) != want]
        if not stale:
            print("=== bigfiles: %d fixture(s) already restored and verified"
                  % len(members))
            return
        print("=== bigfiles: %d restored file(s) do not match their digest, "
              "re-extracting" % len(stale))
    else:
        print("=== restore %d oversized fixture(s) from %s ==="
              % (len(missing), os.path.basename(BIGFILES_PACK)))

    got = sha256_file(BIGFILES_PACK)
    if got != pack_sha:
        raise RuntimeError(
            "%s sha256 mismatch\n  expected %s\n  got      %s\n"
            "The archive was altered in transit; every fixture it holds "
            "would be wrong.  Re-download the artifact."
            % (BIGFILES_PACK, pack_sha, got))
    print("    archive sha256 OK (%s)" % pack_sha[:16])

    with tarfile.open(BIGFILES_PACK, "r:xz") as tf:
        names = [m.name for m in tf.getmembers()]
        unexpected = sorted(set(names) - set(members))
        if unexpected:
            raise RuntimeError(
                "%s holds %d member(s) with no recorded digest (%s); "
                "refusing to extract unverifiable files"
                % (BIGFILES_PACK, len(unexpected), ", ".join(unexpected[:3])))
        # "tar" rather than "data": it still blocks absolute paths and ../
        # traversal, but keeps the mode bits.  Older Pythons have no filter=.
        try:
            tf.extractall(ROOT, filter="tar")
        except TypeError:                      # Python < 3.12
            tf.extractall(ROOT)

    bad = []
    for rel, want in sorted(members.items()):
        p = os.path.join(ROOT, rel)
        if not os.path.isfile(p):
            bad.append("%s: not restored" % rel)
        elif sha256_file(p) != want:
            bad.append("%s: digest mismatch" % rel)
    if bad:
        raise RuntimeError("bigfiles restore failed:\n  " + "\n  ".join(bad))
    print("    restored and verified %d file(s)" % len(members))


# Check every file named in manifest.list against its recorded digest.
def verify_manifest(sample_dir, manifest_list):
    bad, n = [], 0
    with open(manifest_list) as fh:
        for line in fh:
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            digest, name = line.split(None, 1)
            p = os.path.join(sample_dir, name)
            n += 1
            if not os.path.isfile(p) or sha256_file(p) != digest:
                bad.append(name)
    if bad:
        raise RuntimeError("%d/%d files failed verification (%s...)"
                           % (len(bad), n, ", ".join(bad[:3])))
    print("    verified %d files against manifest.list" % n)


# Download the Zenodo archive, verify it, and deploy it.  The live tree
# is not touched until the staged copy passes its digest check, so a
# failed or truncated download leaves the existing corpus intact.
def install_binexec_from_zenodo(verify_all=False):
    tgz = os.path.join(TMP_DIR, "centos_pack.tgz")
    print("  download centos_pack.tgz (327 MB) <- %s" % BINEXEC_DOI)
    http_download(BINEXEC_URL, tgz)
    got = sha256_file(tgz)
    if got != BINEXEC_SHA256:
        raise RuntimeError("archive digest mismatch:\n  expected %s\n"
                           "  got      %s" % (BINEXEC_SHA256, got))
    print("    archive sha256 OK")

    stage = os.path.join(TMP_DIR, "pack")
    shutil.rmtree(stage, ignore_errors=True)
    os.makedirs(stage)
    print("  extract")
    with tarfile.open(tgz, "r:gz") as tf:
        try:
            tf.extractall(stage, filter="data")   # py>=3.12
        except TypeError:
            tf.extractall(stage)
    root = os.path.join(stage, "centos_pack")

    if verify_all:
        print("  verify all files against manifest.list")
        verify_manifest(os.path.join(root, "samples"),
                        os.path.join(root, "manifest", "manifest.list"))

    print("  deploy")
    # data/samples/ is gitignored, so samples/gen_data.py is absent from a
    # fresh checkout.  deploy_samples() used to plant the corrected master
    # there, but the Zenodo path no longer goes through samples.7z -- so
    # plant it here or install_binexec() runs a file that does not exist.
    shutil.copy2(os.path.join(DATA_DIR, "gen_data.py"),
                 os.path.join(SAMPLES_DIR, "gen_data.py"))
    empty_dir(BINEXEC_DIR)
    move_children(os.path.join(root, "samples"), BINEXEC_DIR)
    for src, dst in ((os.path.join(root, "licenses"), LICENSES_DIR),
                     (os.path.join(root, "manifest"), MANIFEST_DIR)):
        empty_dir(dst)
        move_children(src, dst)
    shutil.move(os.path.join(root, "README.md"), BINEXEC_DOC)
    print("    binexec  -> %s" % BINEXEC_DIR)
    print("    licences -> %s" % LICENSES_DIR)
    print("    manifest -> %s" % MANIFEST_DIR)


# Superseded source: the corpus used to ship inside the Google Drive
# samples.7z.  Drive has no DOI, throttles large files and reports
# downloads to the file owner.  The email fallback that was samples.7z's
# last consumer has since been retired too, so NOTHING fetches from Drive
# any more and ensure_samples_deployed() is itself commented out below.
# def install_binexec_from_gdrive():
#     ensure_samples_deployed()


# =====================================================================
# binexec merge  (delegated to the canonical samples/gen_data.py)
# =====================================================================

# Recreate binexec_merged128k by running samples/gen_data.py with its
# original semantics (relative paths; it rm/mkdir's the target itself).
# gen_data.py opens merge_records/binexec.txt for write but does NOT
# create that dir, so ensure it exists first or the merge aborts before
# any file lands in binexec_merged128k.
def install_binexec():
    prev = os.getcwd()
    os.chdir(SAMPLES_DIR)
    try:
        os.makedirs("merge_records", exist_ok=True)
        run_cmd([sys.executable, "gen_data.py"])
        print("binexec merge done -> %s" % BINEXEC_TGT)
    finally:
        os.chdir(prev)
    verify_split_size()


# gen_data.py splits corpus files over 32 MiB.  The size of each chunk
# fingerprints WHICH gen_data.py actually ran: the stale copy shipped
# inside samples.7z leaves only 16 bytes of headroom under 32 MiB, which
# overflows the range2_bit=26 loc field in full_data4.  That corruption is
# SILENT (no crash, just wrong locations inside the proof), so fail loudly
# here instead.  Ported from the retired data/DOWNLOAD.py, which checked
# only the FIRST chunk -- a file splitting into three leaves two full
# chunks, so that missed the offset being dropped on any later one.
SPLIT_SIZE = 32 * 1024 * 1024 - 100 * 1024
BORDER     = 32 * 1024 * 1024


def verify_split_size():
    d = os.path.join(SAMPLES_DIR, BINEXEC_TGT)
    fams = {}
    for n in os.listdir(d):
        stem, sep, idx = n.rpartition("__")
        if sep and idx.isdigit():
            fams.setdefault(stem, []).append((int(idx), n))
    if not fams:
        raise RuntimeError("no split chunks under %s: gen_data.py did not "
                           "run, or no corpus file exceeds %d bytes"
                           % (d, SPLIT_SIZE))
    for stem, items in sorted(fams.items()):
        items.sort()
        for pos, (_idx, n) in enumerate(items):
            sz = os.path.getsize(os.path.join(d, n))
            if sz >= BORDER:
                raise RuntimeError("%s is %d bytes, at or over the 32 MiB "
                                   "border" % (n, sz))
            # every chunk but the trailing remainder must be exactly full
            if pos != len(items) - 1 and sz != SPLIT_SIZE:
                raise RuntimeError(
                    "%s is %d bytes, expected %d (32MiB - 100KiB); "
                    "samples/gen_data.py is the wrong version"
                    % (n, sz, SPLIT_SIZE))
        total = sum(os.path.getsize(os.path.join(d, n)) for _i, n in items)
        src = os.path.join(BINEXEC_DIR, stem)
        if os.path.isfile(src) and total != os.path.getsize(src):
            raise RuntimeError("%s chunks total %d bytes, source is %d"
                               % (stem, total, os.path.getsize(src)))
        print("    split OK: %s -> %d chunks, %d full at %d B"
              % (stem, len(items), len(items) - 1, SPLIT_SIZE))


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
    # samples.7z ships a stale gen_data.py (the -16 split-size semantics);
    # overwrite it with the corrected master under data/ (-100KiB headroom)
    # so install_binexec runs the right version, not the archived one.
    shutil.copy2(os.path.join(DATA_DIR, "gen_data.py"),
                 os.path.join(SAMPLES_DIR, "gen_data.py"))


# Overwrite data/src_sig/.gitignore with the canonical content, so an old
# single-line `chr17_variants` ignore (which swallowed scripts/) is fixed
# in place wherever INSTALL.py runs.
def write_src_sig_gitignore():
    os.makedirs(SRC_SIG_DIR, exist_ok=True)
    with open(SRC_SIG_GITIGNORE, "w") as f:
        f.write(SRC_SIG_GITIGNORE_TEXT)
    print("  wrote %s (scripts/ tracked; corpora ignored)"
          % SRC_SIG_GITIGNORE)


# Deploy the chr17 (sig_c21) payload: the whole top folder (INCLUDING
# chr17_samples) -> data/src_sig/chr17_variants (item 3).  chr17_samples
# is NOT moved out; instead data/samples/chr17_samples is a symlink into
# chr17_variants/chr17_samples, so the corpus lives in one place only.
# The link target is relative, so it survives a repo relocation.
# The six scripts under chr17_variants/scripts/ are version-controlled, but
# they sit INSIDE the directory clean_dna() empties.  PAPER_DATA.py launches
# eval_reef.py and dry_run_eval_reef.py from that exact path, so losing them
# breaks the reproduction run -- and it is invisible without `git status`.
# Snapshot before the wipe, restore after the deploy.  A filesystem copy, not
# `git checkout --`: the artifact may be unpacked from a tarball with no git
# metadata.  (The Zenodo archive also omits scripts/, so nothing would
# restore them otherwise.)
# ---- Reef build ----------------------------------------------------
# The Zenodo archive ships Reef as SOURCE ONLY -- target/ was 1.0 GB of build
# artifacts that also embedded absolute build paths -- so the binary is
# produced here.  eval_reef.py resolves REEF_BIN to exactly
# target/release/reef and refuses to run without it, so a dna install that
# skipped this would fail much later, during evaluation, not now.
#
# NOTE: reef/rust-toolchain pins channel = "nightly", NOT the 1.76.0 this
# script installs for the main crate.  rustup reads that file and switches
# automatically, installing nightly if absent.  "nightly" FLOATS, so this
# build can break on an upstream compiler change; reef/UPSTREAM.txt records
# the dated-nightly workaround.
def cargo_exe():
    return (shutil.which("cargo") or
            os.path.join(os.path.expanduser("~/.cargo/bin"), "cargo"))


# Run argv inside cwd, echoing it; raise on non-zero.
def run_cmd_in(argv, cwd):
    print("  $ (cd %s && %s)" % (cwd, " ".join(argv)))
    subprocess.run(argv, cwd=cwd, check=True)


def build_reef():
    cargo = cargo_exe()
    if shutil.which("cargo") is None and not os.path.isfile(cargo):
        raise RuntimeError(
            "cargo not found; run `python3 scripts/INSTALL.py --toolchain` "
            "first, or `source ~/.cargo/env` in this shell")
    print("  build reef (pulls crates.io deps; takes several minutes)")
    run_cmd_in([cargo, "build", "--release", "--features", "metrics"],
               REEF_DIR)


# Confirm the build produced a runnable binary at the exact path
# eval_reef.py looks for.  Checked rather than assumed: a cargo run that
# exits 0 without emitting the binary (wrong --features, renamed target)
# would otherwise surface only at evaluation time.
def verify_reef_binary():
    if not os.path.isfile(REEF_BIN):
        raise RuntimeError(
            "reef build produced no binary at %s (eval_reef.py needs exactly "
            "this path)" % REEF_BIN)
    if not os.access(REEF_BIN, os.X_OK):
        raise RuntimeError("%s exists but is not executable" % REEF_BIN)
    with open(REEF_BIN, "rb") as f:
        magic = f.read(4)
    if magic != b"\x7fELF":
        raise RuntimeError("%s is not an ELF executable (magic %r)"
                           % (REEF_BIN, magic))
    size = os.path.getsize(REEF_BIN)
    if size < (1 << 20):
        raise RuntimeError("%s is only %d bytes; the build looks truncated"
                           % (REEF_BIN, size))
    print("    reef binary OK: target/release/reef (%.1f MB)"
          % (size / (1024.0 ** 2)))


CHR17_SCRIPTS = os.path.join(SRC_SIG_DIR, "chr17_variants", "scripts")
_CHR17_SNAP = None


def snapshot_chr17_scripts():
    if not os.path.isdir(CHR17_SCRIPTS):
        return None
    snap = os.path.join(TMP_DIR, "chr17_scripts")
    shutil.rmtree(snap, ignore_errors=True)
    shutil.copytree(CHR17_SCRIPTS, snap,
                    ignore=shutil.ignore_patterns("__pycache__"))
    print("  saved %d script(s) from chr17_variants/scripts/"
          % len(os.listdir(snap)))
    return snap


def restore_chr17_scripts(snap):
    if snap is not None:
        if os.path.isdir(CHR17_SCRIPTS):
            shutil.rmtree(CHR17_SCRIPTS)
        shutil.move(snap, CHR17_SCRIPTS)
        print("  restored chr17_variants/scripts/ (working-tree copy)")
    # Guard the two PAPER_DATA.py entry points: this is the case that would
    # otherwise fail silently at evaluation time, long after the install.
    for n in ("eval_reef.py", "dry_run_eval_reef.py"):
        if not os.path.isfile(os.path.join(CHR17_SCRIPTS, n)):
            raise RuntimeError(
                "%s missing after the dna deploy; PAPER_DATA.py launches it "
                "for the Reef baseline. Restore with: git checkout -- "
                "data/src_sig/chr17_variants/scripts/" % n)


def deploy_chr17(extract_root):
    top = os.path.join(extract_root, SIG_C21_TOP)
    dst_var = os.path.join(SRC_SIG_DIR, "chr17_variants")
    empty_dir(dst_var)
    move_children(top, dst_var)
    write_src_sig_gitignore()      # fix the src_sig ignore (scripts/ tracked)
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

# RETIRED: the shared samples.7z payload from Google Drive.  binexec moved
# to Zenodo, and the email fallback that was its last consumer is commented
# out below -- so nothing calls this and no dataset touches Drive any more.
# Kept commented rather than deleted: it is the only record of how the
# pre-Zenodo layout was assembled.
#
# _samples_ready = False
#
#
# def ensure_samples_deployed():
#     global _samples_ready
#     if _samples_ready:
#         return
#     samples_7z = os.path.join(TMP_DIR, "samples.7z")
#     print("  download samples.7z")
#     gdrive_download(SAMPLES_ID, samples_7z)
#     print("  extract + deploy samples")
#     extract_7z(samples_7z, EXTRACT_DIR)
#     deploy_samples(EXTRACT_DIR)
#     _samples_ready = True


# ---- binexec (CentOS binaries) -------------------------------------

# Empty the binexec target dirs (kept).
def clean_binexec():
    empty_dir(os.path.join(SAMPLES_DIR, "binexec_merged128k"))
    empty_dir(os.path.join(SAMPLES_DIR, "merge_records"))


# Fetch the corpus from Zenodo, then run the binexec merge.
def install_dataset_binexec():
    install_binexec_from_zenodo(verify_all=_VERIFY_ALL)
    # install_binexec_from_gdrive()        # superseded by Zenodo
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
# RETIRED: the Google Drive fallback for the Enron corpus.  It called
# ensure_samples_deployed(), which did NOT check EMAIL_TREE_DIGEST -- that
# gate exists only on the CMU path -- so a CMU outage silently produced an
# unverified corpus from a non-archival host that logs downloads to the file
# owner.  Enron is public, stable since 2015 and widely mirrored, so a hard
# failure is the honest outcome.
# def install_email_from_samples7z():
#     ensure_samples_deployed()
#     write_email_readme()


# Prefer the CMU source; fall back to samples.7z only when CMU is
# unreachable or its download/verify fails.
def install_dataset_email():
    # CMU is now the ONLY source: the Drive fallback was retired because it
    # bypassed EMAIL_TREE_DIGEST.  Fail loudly rather than half-install --
    # a missing corpus is obvious, an unverified one is not.
    if not cmu_email_available():
        raise RuntimeError(
            "the CMU Enron source is unreachable (%s) and the Google Drive "
            "fallback has been retired because it bypassed the "
            "EMAIL_TREE_DIGEST check. Retry later, or fetch the tarball by "
            "hand and place maildir/ at %s (sha256 of the sorted tree "
            "manifest must equal %s)."
            % (ENRON_URL, EMAIL_MAILDIR, EMAIL_TREE_DIGEST))
    install_email_from_cmu()


# ---- dna (chr17 / sig_c21 variants) --------------------------------

# Empty the dna target dirs (kept).  chr17_samples under samples/ is a
# symlink into chr17_variants; UNLINK it (never empty_dir -- that would
# follow the link and delete the real payload).  chr17_variants holds
# the real chr17_samples, so emptying it wipes the corpus.
def clean_dna():
    global _CHR17_SNAP
    _CHR17_SNAP = snapshot_chr17_scripts()   # BEFORE the empty_dir below
    link = os.path.join(SAMPLES_DIR, "chr17_samples")
    if os.path.islink(link):
        os.remove(link)
    elif os.path.isdir(link):              # legacy real dir from old layout
        shutil.rmtree(link)
    elif os.path.exists(link):
        os.remove(link)
    empty_dir(os.path.join(SRC_SIG_DIR, "chr17_variants"))


# Download + extract bora_dna.7z from Zenodo and deploy chr17_variants.
def install_dataset_dna():
    dna_7z = os.path.join(TMP_DIR, "bora_dna.7z")
    print("  download bora_dna.7z from Zenodo (%s)" % DNA_DOI)
    http_download(DNA_URL, dna_7z)
    got = sha256_file(dna_7z)
    if got != DNA_SHA256:
        raise RuntimeError(
            "bora_dna.7z sha256 mismatch:\n  got      %s\n  expected %s"
            % (got, DNA_SHA256))
    print("    sha256 OK")
    print("  extract bora_dna.7z")
    extract_7z(dna_7z, EXTRACT_DIR)
    deploy_chr17(EXTRACT_DIR)
    restore_chr17_scripts(_CHR17_SNAP)     # after the archive lands
    if _SKIP_REEF_BUILD:
        print("  SKIP reef build (--skip-reef-build). Build it before the")
        print("       Reef baseline:  cd %s && \\" % REEF_DIR)
        print("       cargo build --release --features metrics")
    else:
        build_reef()
        verify_reef_binary()
    print("  NOTE: Reef's commitment file (~4.3 GB) is NOT shipped;")
    print("        eval_reef.py regenerates it on first run.")
    print("        See reef/UPSTREAM.txt (upstream commit + our patch).")


# def install_dataset_dna_from_gdrive():   # superseded by the Zenodo path
#     sig_7z = os.path.join(TMP_DIR, "sig_c21.7z")
#     gdrive_download(SIG_C21_ID, sig_7z)
#     extract_7z(sig_7z, EXTRACT_DIR)
#     deploy_chr17(EXTRACT_DIR)


# Registry in menu order: (key, label, est. installed GB, clean, install).
DATASETS = [
    ("email",   "email (Enron)",          3.8,
     clean_email,   install_dataset_email),
    # 0.43 GB installed. Reef's commitment (~4.3 GB) and reef/target/ are
    # built on first eval run, so the on-disk total grows well past this.
    ("dna",     "dna (chr17 variants)",   0.43,
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
        description="Install bora data into ./data.")
    ap.add_argument("--data", choices=["all"] + keys,
                    help="non-interactive dataset selection")
    ap.add_argument("--toolchain", action="store_true",
                    help="install Rust 1.76 + system build deps, then "
                         "exit (unless --data is also given)")
    ap.add_argument("--verify", action="store_true",
                    help="binexec: check all 2702 files against "
                         "manifest.list after download (the archive's "
                         "own sha256 is always checked)")
    ap.add_argument("--skip-reef-build", action="store_true",
                    help="dna: deploy the corpus but do NOT run "
                         "`cargo build` for Reef (the baseline binary will "
                         "be missing until you build it by hand)")
    args = ap.parse_args()

    global _VERIFY_ALL, _SKIP_REEF_BUILD
    _VERIFY_ALL = args.verify
    _SKIP_REEF_BUILD = args.skip_reef_build

    # Before anything else: needs no toolchain, no network and no dataset
    # selection, and data/debug + data/paper_data + data/src_sig/clamav
    # fixtures are inputs the eval path reads regardless of which corpus is
    # installed (e.g. DatasetSpec CLAM's sig_file is one of them).  No
    # clean_* function touches these paths, so restoring once here is not
    # undone by the loop below.
    restore_bigfiles()

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
