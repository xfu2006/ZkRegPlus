#!/usr/bin/env python3
# ---------------------------------------------------------------------
# INSTALL.py  --  one-shot data installer for bora.
#
# Downloads + extracts data into data/.  The email dataset (Enron) is
# fetched from the CMU source and placed under data/samples/email/src/
# maildir; CMU is the ONLY source -- the samples.7z fallback was retired
# because it bypassed EMAIL_TREE_DIGEST, so an unreachable CMU host is a
# hard failure, never a silent unverified corpus.  The binexec corpus
# comes from its Zenodo
# deposit (DOI 10.5281/zenodo.21909549), which also carries the licence
# texts and the per-file manifest; the chr17 (dna) corpus comes from its own
# Zenodo deposit (DOI 10.5281/zenodo.21911045).  Both are sha256-verified.
# All scratch lives under /tmp/bora_install and is removed on completion.
#
# The paper_data entry is not a corpus either: it fetches the recorded
# run logs behind the paper's tables from their Zenodo deposit (DOI
# 10.5281/zenodo.22057943), keeps the .tgz beside data/paper_data/ as a
# backup, and clears the derived extracted/ caches and figs/*.tex so
# PAPER_DATA.py's "generate list of figures" rebuilds them from
# scratch.  It builds no PDF itself.
#
# The zombie entry is not a corpus: it clones the NSDI'24 Zombie baseline
# (gitignored, unlicensed upstream) and installs the extra apt/pip/rustup
# deps its CirC build needs.  PAPER_DATA.py's zombie leaf fails without it.
#
# Run from anywhere:
#   python3 INSTALL.py             menu: ALL / email / dna / binexec /
#                                  zombie / paper_data
#   python3 INSTALL.py --data all  non-interactive
#                                  (all|email|dna|binexec|zombie|
#                                   paper_data)
#
# NOTE: authored and manually reviewed/tested by the paper authors.
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
# data/ root holds only README.md and .gitignore; everything else
# lives in a subfolder so a reviewer opening data/ sees directories,
# not a pile of loose files.
DATA_SCRIPTS_DIR = os.path.join(DATA_DIR, "scripts")
PAPER_BACKUP_DIR = os.path.join(DATA_DIR, "paper_data_backup")
BIGFILES_DIR     = os.path.join(DATA_DIR, "bigfiles")
CACHE_MAIN  = os.path.join(DATA_DIR, "cache", "main")
TMP_DIR     = "/tmp/bora_install"                 # all scratch (item 4)
EXTRACT_DIR = os.path.join(TMP_DIR, "extract")

# ---- Google Drive ids (RETIRED -- nothing is fetched from Drive) ----
# Drive now serves NOTHING: binexec and dna moved to Zenodo (DOI-pinned,
# sha256-verified, free of Drive's download logging), and the email
# fallback that was Drive's last consumer is retired too.
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
# (incl. lld, required by the fused-ld link), p7zip, the texlive subset
# PAPER_DATA.py's figs item needs, and the rustup-managed
# 1.76.0 toolchain pinned by ./rust-toolchain.  Idempotent; needs sudo
# for apt.
# =====================================================================

APT_PACKAGES = [
    "build-essential", "lld", "pkg-config", "libssl-dev",
    "curl", "git", "p7zip-full", "python3-pip",
    # PAPER_DATA.py's "figs" item compiles list_figures.tex with
    # pdflatex (run_figs, twice for refs).  Unlike the zombie deps this
    # is NOT gated on a dataset: figs is a top-level menu item, so every
    # install can reach it.  The split is MEASURED with kpsewhich +
    # dpkg -S, not guessed; the CM fonts the PDF embeds come from
    # texlive-base, which texlive-latex-base already depends on.
    "texlive-latex-base",         # pdflatex, geometry, amsmath, hyperref
    "texlive-latex-recommended",  # booktabs
    "texlive-pictures",           # tikz, pgfplots
]
RUST_VERSION = "1.76.0"

# The .sty files list_figures.tex loads.  texlive-latex-recommended and
# texlive-pictures ship no binary, so `which` cannot see them and only
# kpsewhich answers -- the same trap have_header() covers for the -dev
# packages.  A package added above without a probe here is dead code:
# ensure_toolchain() skips the apt step whenever its probe says present.
LATEX_STYS = ("geometry.sty", "booktabs.sty", "amsmath.sty",
              "tikz.sty", "pgfplots.sty", "hyperref.sty")

# ---- zombie (NSDI'24 baseline) build prerequisites ------------------
# Kept OUT of APT_PACKAGES / install_rust deliberately: these are needed
# only by the zombie dataset, and the pinned nightly alone is ~1.5 GB, so
# an email-or-dna install must not pay for them.  ensure_toolchain()
# installs them when "zombie" is in the selection, and nothing else does.
#
# SOURCE OF TRUTH is the DEPS table in
# data/src_sig/ms_dlp/scripts/download_zombie.py (see its lines 48-71).
# check_zombie_dep_drift() re-reads that table at install time and warns
# if it has gained a package this list does not carry -- the lists cannot
# silently diverge.  cvc4 and coinor-* live in Ubuntu "universe", enabled
# by default on 24.04 server images.
ZOMBIE_APT_PACKAGES = [
    "libgmp-dev",        # TestRegex links -lgmpxx -lgmp
    "libmpfr-dev",       # CirC gmp-mpfr-sys system-libs build
    "libmpc-dev",        # CirC gmp-mpfr-sys system-libs build
    "cvc4",              # CirC SMT backend
    "coinor-cbc",        # CirC ILP backend
    "coinor-libcbc-dev",
]
ZOMBIE_NIGHTLY = "nightly-2023-02-01"   # pinned by circ/rust-toolchain.toml
ZOMBIE_PIP     = "tqdm==4.63.0"         # circ driver.py
# apt packages the downloader hints that APT_PACKAGES supplies indirectly,
# so the drift check does not flag them.  python3-pip depends on python3.
_APT_IMPLIED = ("python3",)


# Run argv, echoing it; raise on non-zero.
def run_cmd(argv):
    print("  $ " + " ".join(argv))
    subprocess.run(argv, check=True)


# Install apt build deps (lld is required by the fused-ld link).
def install_apt_deps():
    sudo = [] if os.geteuid() == 0 else ["sudo"]
    run_cmd(sudo + ["apt-get", "update"])
    run_cmd(sudo + ["apt-get", "install", "-y"] + APT_PACKAGES)


# Install the zombie-only apt deps.  Runs its own `apt-get update`: this
# can fire when apt_tools_present() was already True, so install_apt_deps
# (the only other updater) never ran, and a fresh instance with a stale or
# empty package cache would fail with "Unable to locate package".
def install_zombie_apt_deps():
    sudo = [] if os.geteuid() == 0 else ["sudo"]
    run_cmd(sudo + ["apt-get", "update"])
    run_cmd(sudo + ["apt-get", "install", "-y"] + ZOMBIE_APT_PACKAGES)


# pip-install gdown (Ubuntu 24 is PEP-668 managed -> retry w/ override).
# NO LIVE CALLER: gdown backed only gdrive_download, which has no live
# caller either (see its comment).  Kept so re-enabling a retired Drive
# path stays a one-line change; nothing on the reproduction path pays
# for this install any more.
def install_pip_deps():
    try:
        run_cmd([sys.executable, "-m", "pip", "install", "--user",
                 "gdown"])
    except subprocess.CalledProcessError:
        run_cmd([sys.executable, "-m", "pip", "install", "--user",
                 "--break-system-packages", "gdown"])


# pip-install circ's tqdm pin (same PEP-668 retry as gdown).
def install_zombie_pip_deps():
    try:
        run_cmd([sys.executable, "-m", "pip", "install", "--user",
                 ZOMBIE_PIP])
    except subprocess.CalledProcessError:
        run_cmd([sys.executable, "-m", "pip", "install", "--user",
                 "--break-system-packages", ZOMBIE_PIP])


# Install the nightly circ pins.  rustup would fetch it lazily on the
# first cargo build in that tree, but that build happens INSIDE a timed
# PAPER_DATA leaf -- pull it here so a network failure surfaces at install
# time instead of corrupting a measurement.  Callers run install_rust()
# first, so rustup exists; the guard covers a direct call.
def install_zombie_rust():
    rustup = shutil.which("rustup") or \
        os.path.join(os.path.expanduser("~/.cargo/bin"), "rustup")
    if not os.path.isfile(rustup) and shutil.which("rustup") is None:
        raise RuntimeError(
            "rustup not found; run `python3 scripts/INSTALL.py --toolchain` "
            "first, or `source ~/.cargo/env` in this shell")
    run_cmd([rustup, "toolchain", "install", ZOMBIE_NIGHTLY])


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
# with_zombie adds the baseline's extra apt/pip/rustup deps; main() sets
# it from --data, so `--toolchain` alone still installs only the base.
def install_toolchain(with_zombie=False):
    print("=== install toolchain (Rust %s + build deps) ==="
          % RUST_VERSION)
    install_apt_deps()
    install_rust()
    if with_zombie:
        print("=== zombie baseline build deps (rust %s) ==="
              % ZOMBIE_NIGHTLY)
        install_zombie_apt_deps()
        install_zombie_pip_deps()
        install_zombie_rust()
    print("toolchain ready -- build with:")
    print('  RUSTFLAGS="-C link-args=-fuse-ld=lld -Awarnings" '
          "cargo build --release")


# True if every binary the apt packages provide is already on PATH.
# True if every LATEX_STYS file is on the TeX search path.  kpsewhich
# prints one path per file it finds and nothing for the rest, so the
# line count is the test; it lives in texlive-binaries, which arrives
# with texlive-latex-base, hence the which() guard for a bare box.
def have_latex_stys():
    if shutil.which("kpsewhich") is None:
        return False
    try:
        p = subprocess.run(["kpsewhich"] + list(LATEX_STYS),
                           capture_output=True, text=True, timeout=60)
    except (OSError, subprocess.TimeoutExpired):
        return False
    return len(p.stdout.split()) >= len(LATEX_STYS)


def apt_tools_present():
    need = ("ld.lld", "7za", "cc", "pkg-config", "git", "curl",
            "pdflatex")
    return (all(shutil.which(b) is not None for b in need)
            and have_latex_stys())


# True if <header> compiles.  Same probe download_zombie.py:have_header
# uses -- the three -dev packages ship no binary, so `which` cannot see
# them and only a compile answers the question.
def have_header(header):
    if shutil.which("g++") is None:
        return False
    src = "#include <%s>\nint main(){ return 0; }\n" % header
    try:
        p = subprocess.run(["g++", "-x", "c++", "-fsyntax-only", "-"],
                           input=src, capture_output=True, text=True,
                           timeout=30)
        return p.returncode == 0
    except (OSError, subprocess.TimeoutExpired):
        return False


# True if every ZOMBIE_APT_PACKAGES payload is usable.  This probe MUST
# track that list: ensure_toolchain() skips the apt step when its probe
# says present, so a package added there without a probe here is never
# installed on a box that already satisfies apt_tools_present().
def zombie_apt_present():
    if not all(shutil.which(b) is not None for b in ("cvc4", "cbc")):
        return False
    return all(have_header(h)
               for h in ("gmpxx.h", "mpfr.h", "mpc.h"))


# True if the gdown python module imports.
# NO LIVE CALLER: ensure_toolchain() stopped gating on this once the
# last Drive consumer was retired.
def have_gdown():
    try:
        import gdown  # noqa: F401
        return True
    except ImportError:
        return False


# True if circ's tqdm imports.
def have_tqdm():
    try:
        import tqdm  # noqa: F401
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


# True if rustup has the nightly circ pins.
def have_zombie_rust():
    rustup = shutil.which("rustup") or \
        os.path.join(os.path.expanduser("~/.cargo/bin"), "rustup")
    if not os.path.isfile(rustup) and shutil.which("rustup") is None:
        return False
    try:
        out = subprocess.run([rustup, "toolchain", "list"],
                             capture_output=True, text=True, check=True)
        return ZOMBIE_NIGHTLY in out.stdout
    except (subprocess.CalledProcessError, FileNotFoundError):
        return False


# Default gate: install only the tools that are missing (idempotent).
# selected is the dataset key list main() resolved; the zombie deps are
# probed and installed only when that baseline is actually being set up.
def ensure_toolchain(selected=()):
    want_z = "zombie" in selected
    ok_apt, ok_rust = apt_tools_present(), have_rust()
    ok_z_apt = zombie_apt_present() if want_z else True
    ok_z_pip = have_tqdm() if want_z else True
    ok_z_rust = have_zombie_rust() if want_z else True
    if (ok_apt and ok_rust
            and ok_z_apt and ok_z_pip and ok_z_rust):
        print("toolchain present (apt deps, rust %s%s)."
              % (RUST_VERSION,
                 ", zombie deps, rust " + ZOMBIE_NIGHTLY if want_z else ""))
        return
    print("=== ensure toolchain (installing missing tools) ===")
    if not ok_apt:
        install_apt_deps()
    if not ok_rust:
        install_rust()
    if not ok_z_apt:
        install_zombie_apt_deps()
    if not ok_z_pip:
        install_zombie_pip_deps()
    if not ok_z_rust:
        install_zombie_rust()


# =====================================================================
# download tooling + filesystem helpers
# =====================================================================

# Download a Google Drive file to dest (skips if already present).
# NO LIVE CALLER: binexec and dna moved to Zenodo (http_download +
# sha256) and the email fallback is retired; kept only so the retired
# paths below stay readable.  Accepts either a bare file id (as
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
# Names that must survive any wipe: version-controlled, shipped in no
# archive, and not regenerable. chr17_variants/scripts was destroyed this
# way in ad2f76d4 (deploy_chr17 wipes the dir; the Zenodo dna archive
# carries corpora only) and restored in 9d47d38b.
PROTECTED_NAMES = {"scripts", ".gitignore", ".gitkeep"}


def empty_dir(d, keep=()):
    os.makedirs(d, exist_ok=True)
    skip = PROTECTED_NAMES | set(keep)
    for n in os.listdir(d):
        if n in skip:
            continue
        p = os.path.join(d, n)
        if os.path.isdir(p) and not os.path.islink(p):
            shutil.rmtree(p)
        else:
            os.remove(p)


# Delete every child of d except .gitkeep (the tracked dir marker).
def keep_only_gitkeep(d):
    for n in os.listdir(d):
        if n == ".gitkeep":
            continue
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
BINEXEC_DOC    = os.path.join(MANIFEST_DIR, "DATASET_BINEXEC.md")

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

# ---- paper_data (recorded paper runs) Zenodo deposit ----------------
# PAPER_DATA_DOI is the CONCEPT doi (cite this; it follows the newest
# version); PAPER_DATA_URL pins the version record so the bytes cannot
# move under PAPER_DATA_SHA256.  The archive carries ONLY the two raw
# run-log folders plus a README -- no scripts, no figs -- so the
# project's own generators under run_data/scripts/ are what run.
PAPER_DATA_DOI    = "https://doi.org/10.5281/zenodo.22057943"
PAPER_DATA_URL    = ("https://zenodo.org/records/22057944/files/"
                     "bora_paper_data.tgz?download=1")
PAPER_DATA_SHA256 = ("851bf9434c450af2696a2add9e55189764f3f4d6e"
                     "8f4607bd5dda77aefab7bb0")
# The .tgz stays HERE, not in TMP_DIR: cleanup_temp() wipes TMP_DIR on
# exit, and this copy is the offline backup of data/paper_data/.  It
# lives in its own folder (with a README) so that a reviewer browsing
# data/ can tell the backup apart from the results themselves.
PAPER_DATA_TGZ    = os.path.join(PAPER_BACKUP_DIR, "bora_paper_data.tgz")
PAPER_RUN_DATA    = os.path.join(DATA_DIR, "paper_data", "run_data")
PAPER_RAW_DATA    = os.path.join(PAPER_RUN_DATA, "data", "raw_data")
PAPER_FIGS_DIR    = os.path.join(PAPER_RUN_DATA, "figs")
# Whitelist: only these members are unpacked, so a future revision of
# the archive can never write into run_data/scripts/ or the code base.
PAPER_DATA_PREFIX = "paper_data/run_data/data/raw_data/"
PAPER_DATA_README = "BORA_PAPER_DATA_README.txt"

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
BIGFILES_PACK = os.path.join(BIGFILES_DIR, "bigfiles.tar.xz")
BIGFILES_SUMS = os.path.join(BIGFILES_DIR, "bigfiles.sha256")

# ---- zombie (NSDI'24 baseline) tree ---------------------------------
# A gitignored upstream clone, not an archive we deploy: the repo carries
# no licence ("all rights reserved"), so it is fetched per-machine and
# never redistributed in this tree.  download_zombie.py owns the clone.
MS_DLP_DIR      = os.path.join(SRC_SIG_DIR, "ms_dlp")
ZOMBIE_DIR      = os.path.join(MS_DLP_DIR, "zombie")
ZOMBIE_REGEX    = os.path.join(ZOMBIE_DIR, "regex")
ZOMBIE_CIRC     = os.path.join(ZOMBIE_DIR, "circ")
ZOMBIE_UPSTREAM = os.path.join(ZOMBIE_DIR, "UPSTREAM.txt")
ZOMBIE_DOWNLOAD = os.path.join(MS_DLP_DIR, "scripts", "download_zombie.py")

# Set by main() from --verify / --skip-reef-build / --force-zombie /
# --build-zombie; the DATASETS registry
# calls install functions with no arguments, so flags travel as module state.
_VERIFY_ALL = False
_SKIP_REEF_BUILD = False
_FORCE_ZOMBIE = False
_BUILD_ZOMBIE = False


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

# Parse data/bigfiles/bigfiles.sha256 -> (pack_digest, {repo-rel: digest}).
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


# Restore the 13 oversized fixtures from data/bigfiles/bigfiles.tar.xz.
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
    shutil.copy2(os.path.join(DATA_SCRIPTS_DIR, "gen_data.py"),
                 os.path.join(SAMPLES_DIR, "gen_data.py"))
    empty_dir(BINEXEC_DIR)
    move_children(os.path.join(root, "samples"), BINEXEC_DIR)
    # DATASET_BINEXEC.md is TRACKED and now lives inside manifest/, so it
    # has to survive this wipe.  The shutil.move below rewrites it from
    # the archive's README.md anyway, but keeping it means an install that
    # fails in between can never leave the tree missing a committed file.
    for src, dst, keep in (
            (os.path.join(root, "licenses"), LICENSES_DIR, ()),
            (os.path.join(root, "manifest"), MANIFEST_DIR,
             (os.path.basename(BINEXEC_DOC),))):
        empty_dir(dst, keep=keep)
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
    # overwrite it with the corrected master under data/scripts/ (-100KiB
    # headroom) so install_binexec runs the right version, not the archived
    # one.
    shutil.copy2(os.path.join(DATA_SCRIPTS_DIR, "gen_data.py"),
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


# CMU is the only source.  An unreachable host raises rather than
# falling back -- see the retired install_email_from_samples7z above.
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


# ---- zombie (NSDI'24 baseline) -------------------------------------

# Re-read download_zombie.py's DEPS table and warn if it now asks for
# something this script does not install.  Textual, not an import: that
# module chdir()s and pulls in ms_dlp/scripts/common.py, neither of which
# should happen as a side effect of a dep check.  Warns rather than
# raises -- an upstream edit to a hint string must not abort an install,
# and the downloader prints its own MISS report moments later.
def check_zombie_dep_drift():
    import re
    try:
        with open(ZOMBIE_DOWNLOAD) as f:
            src = f.read()
    except OSError:
        return
    known = set(APT_PACKAGES) | set(ZOMBIE_APT_PACKAGES) | set(_APT_IMPLIED)
    want = set()
    for hint in re.findall(r'"apt install ([^"]+)"', src):
        want.update(hint.split())
    missing = sorted(want - known)
    if missing:
        print("  WARN: download_zombie.py now hints apt package(s) this "
              "script does not install: %s" % ", ".join(missing))
        print("        add them to ZOMBIE_APT_PACKAGES.")
    m = re.search(r'RUST_NIGHTLY\s*=\s*"([^"]+)"', src)
    if m and m.group(1) != ZOMBIE_NIGHTLY:
        print("  WARN: nightly pin drifted -- downloader %s, this script %s"
              % (m.group(1), ZOMBIE_NIGHTLY))
    m = re.search(r'"pip install (tqdm==[0-9.]+)"', src)
    if m and m.group(1) != ZOMBIE_PIP:
        print("  WARN: tqdm pin drifted -- downloader %s, this script %s"
              % (m.group(1), ZOMBIE_PIP))


# Short upstream commit recorded by the last clone, for the skip message.
def zombie_commit():
    try:
        with open(ZOMBIE_UPSTREAM) as f:
            for line in f:
                if line.startswith("commit:"):
                    return line.split(":", 1)[1].strip()[:12] or "unknown"
    except OSError:
        pass
    return "unknown"


# No-op by design.  download_zombie.py rmtree()s zombie/ itself before
# cloning, so a clean_* wipe here would only add a second destructive
# path -- and one that runs even when install_dataset_zombie() decides to
# keep the existing tree.  Present to keep the DATASETS 5-tuple shape.
def clean_zombie():
    pass


# Confirm the clone left what run_zombie.py actually opens.  Checked, not
# assumed: download_zombie.py exits 0 on a clone whose build step was
# skipped, and a missing subtree would otherwise surface mid-evaluation.
def verify_zombie_tree():
    for p in (ZOMBIE_REGEX, ZOMBIE_CIRC):
        if not os.path.isdir(p):
            raise RuntimeError(
                "zombie clone left no %s; run_zombie.py needs it" % p)
    print("    zombie tree OK: upstream commit %s" % zombie_commit())


# Clone the Zombie baseline via download_zombie.py.
#
# Skips when the tree is already there.  download_zombie.py clones the
# DEFAULT BRANCH and records HEAD only afterwards, so re-cloning can move
# the baseline to a different upstream commit than UPSTREAM.txt reports --
# silently changing what the paper compares against.  Keeping the pinned
# tree is the safe default; --force-zombie re-clones.
#
# No build here, unlike build_reef().  That one runs at install time
# because eval_reef.py REFUSES to run without target/release/reef;
# run_zombie.py instead builds TestRegex and its out-of-workspace circ
# copy on demand (ensure_testregex / ensure_zombie_built), so the clone is
# sufficient and a ~30 min CirC build stays opt-in via --build-zombie.
def install_dataset_zombie():
    check_zombie_dep_drift()
    if os.path.isdir(ZOMBIE_REGEX) and not _FORCE_ZOMBIE:
        print("  zombie/ already present (upstream commit %s) -- kept."
              % zombie_commit())
        print("    re-cloning tracks the default branch and could move the")
        print("    baseline commit; pass --force-zombie to do it anyway.")
        return
    if not os.path.isfile(ZOMBIE_DOWNLOAD):
        raise RuntimeError("missing %s (expected in the repo)"
                           % ZOMBIE_DOWNLOAD)
    argv = [sys.executable, "-u", ZOMBIE_DOWNLOAD]
    if _BUILD_ZOMBIE:
        argv.append("--verify-build")
    print("  clone Zombie (upstream is unlicensed: local research use,")
    print("        do not redistribute -- zombie/ stays git-ignored)")
    run_cmd_in(argv, os.path.dirname(ZOMBIE_DOWNLOAD))
    verify_zombie_tree()
    if not _BUILD_ZOMBIE:
        print("  NOTE: TestRegex + circ are built on first use by")
        print("        run_zombie.py; pass --build-zombie to do it now.")


# =====================================================================
# paper_data  (the recorded run logs behind the paper's tables)
# =====================================================================

# Empty every target the paper_data install writes, plus the two derived
# caches and the LaTeX fragments they feed.  Every step is guarded on
# isdir(): a fresh checkout has no extracted/ tree, so absence is normal
# and never an error.
#
# figs/*.tex is cleared ON PURPOSE.  RUNALL.sh treats a failing
# generator as non-fatal, so a fragment left in place would keep its
# committed content and the rebuilt PDF would still show the paper's
# numbers with nothing having regenerated them.  Deleting them turns
# that silent false pass into a missing file.  Restore with
# `git checkout -- data/paper_data/run_data/figs/`.
def clean_paper_data():
    for name in ("jet1tb", "any_server"):
        d = os.path.join(PAPER_RAW_DATA, name)
        if os.path.isdir(d):
            keep_only_gitkeep(d)
    for d in (os.path.join(PAPER_RAW_DATA, "extracted"),
              os.path.join(PAPER_RAW_DATA, "jet1tb", "extracted")):
        shutil.rmtree(d, ignore_errors=True)
    if os.path.isdir(PAPER_FIGS_DIR):
        for n in sorted(os.listdir(PAPER_FIGS_DIR)):
            if n.endswith(".tex"):
                os.remove(os.path.join(PAPER_FIGS_DIR, n))


# F3 guard.  clean_paper_data() deletes figs/*.tex ON PURPOSE (see above),
# and those fragments are git-TRACKED -- the only tracked files any clean_*
# removes.  Snapshot them first so a FAILED install does not leave the
# working tree short of tracked files with nothing installed in exchange.
# Deliberately NOT restored on success: that would undo the design, which
# is to turn a silently-stale fragment into a missing file.
def snapshot_paper_figs():
    if not os.path.isdir(PAPER_FIGS_DIR):
        return None
    snap = os.path.join(TMP_DIR, "paper_figs")
    shutil.rmtree(snap, ignore_errors=True)
    os.makedirs(snap)
    n = 0
    for name in sorted(os.listdir(PAPER_FIGS_DIR)):
        if name.endswith(".tex"):
            shutil.copy2(os.path.join(PAPER_FIGS_DIR, name),
                         os.path.join(snap, name))
            n += 1
    print("  saved %d figs/*.tex fragment(s) (restored only on failure)" % n)
    return snap


def restore_paper_figs(snap):
    if snap is None or not os.path.isdir(snap):
        return
    os.makedirs(PAPER_FIGS_DIR, exist_ok=True)
    n = 0
    for name in sorted(os.listdir(snap)):
        shutil.copy2(os.path.join(snap, name),
                     os.path.join(PAPER_FIGS_DIR, name))
        n += 1
    print("  install FAILED -- restored %d figs/*.tex fragment(s)" % n)


# Download the Zenodo archive, verify it, keep it as the backup copy,
# and unpack the two raw-run folders.  The archive carries the full
# relative path, so it expands straight into data/.  No PDF is built
# here -- that is PAPER_DATA.py's "generate list of figures".
def install_dataset_paper_data():
    os.makedirs(DATA_DIR, exist_ok=True)
    os.makedirs(PAPER_BACKUP_DIR, exist_ok=True)
    print("  download bora_paper_data.tgz (37 MB) <- %s"
          % PAPER_DATA_DOI)
    http_download(PAPER_DATA_URL, PAPER_DATA_TGZ)
    got = sha256_file(PAPER_DATA_TGZ)
    if got != PAPER_DATA_SHA256:
        os.remove(PAPER_DATA_TGZ)
        raise RuntimeError("archive digest mismatch:\n  expected %s\n"
                           "  got      %s" % (PAPER_DATA_SHA256, got))
    print("    archive sha256 OK")

    # The archive carries the run folders under paper_data/..., which
    # expand straight into data/.  Its top-level README describes the
    # TARBALL, not the results, so it is unpacked next to the tarball in
    # paper_data_backup/ instead of landing loose in data/.
    def _extract(tf, dest, members):
        try:
            tf.extractall(dest, members=members, filter="data")
        except TypeError:
            tf.extractall(dest, members=members)   # py < 3.12

    with tarfile.open(PAPER_DATA_TGZ, "r:gz") as tf:
        members, readme, n = [], [], 0
        for m in tf.getmembers():
            name = os.path.normpath(m.name)
            anc = m.isdir() and PAPER_DATA_PREFIX.startswith(name + "/")
            if name == PAPER_DATA_README:
                readme.append(m)
                continue
            if not (name.startswith(PAPER_DATA_PREFIX) or anc):
                raise RuntimeError("archive member outside the "
                                   "paper_data tree: %r" % m.name)
            members.append(m)
            if m.isfile():
                n += 1
        _extract(tf, DATA_DIR, members)
        if readme:
            _extract(tf, PAPER_BACKUP_DIR, readme)
    print("    %d file(s) -> %s" % (n, PAPER_RAW_DATA))
    print("    backup tgz  -> %s" % PAPER_DATA_TGZ)
    if readme:
        print("    tgz README  -> %s"
              % os.path.join(PAPER_BACKUP_DIR, PAPER_DATA_README))
    print("    next: python3 scripts/PAPER_DATA.py --run figs")


# Registry in menu order: (key, label, est. installed GB, clean, install).
# F3.  A REAL --verify: inspect what is already installed and report.
# Reads only -- no download, no clean_*, no install_*, no deletion.  The
# old --verify was not a mode at all: it set _VERIFY_ALL and fell through
# into the install loop, which with a non-tty stdin selected ALL and
# reinstalled every dataset, deleting tracked figs/*.tex on the way.
def verify_installed():
    print("\n" + "=" * 64)
    print("  verify installed data (read-only)")
    print("=" * 64)
    checks = [
        ("email (Enron)",        EMAIL_DIR),
        ("dna (chr17 scripts)",  CHR17_SCRIPTS),
        ("binexec corpus",       BINEXEC_DIR),
        ("binexec manifest",     MANIFEST_DIR),
        ("zombie clone",         ZOMBIE_DIR),
        ("paper_data raw runs",  PAPER_RAW_DATA),
    ]
    missing = []
    for label, path in checks:
        if os.path.isdir(path) and os.listdir(path):
            print("  OK      %-22s present" % label)
        else:
            missing.append(label)
            print("  ABSENT  %-22s (install it with --data)" % label)

    mlist = os.path.join(MANIFEST_DIR, "manifest.list")
    if os.path.isdir(BINEXEC_DIR) and os.path.isfile(mlist):
        print("  verify binexec against manifest.list")
        try:
            verify_manifest(BINEXEC_DIR, mlist)
        except RuntimeError as exc:
            print("  FAIL    binexec: %s" % exc)
            return 1
    else:
        print("  skip    binexec digests (corpus or manifest.list absent)")

    n_figs = 0
    if os.path.isdir(PAPER_FIGS_DIR):
        n_figs = len([n for n in os.listdir(PAPER_FIGS_DIR)
                      if n.endswith(".tex")])
    print("  info    figs/*.tex fragments present: %d" % n_figs)

    if missing:
        print("  info    %d dataset(s) not installed: %s"
              % (len(missing), ", ".join(missing)))
    print("  verify complete -- nothing downloaded, deleted or rebuilt")
    return 0


DATASETS = [
    ("email",   "email (Enron)",          3.8,
     clean_email,   install_dataset_email),
    # 0.43 GB installed. Reef's commitment (~4.3 GB) and reef/target/ are
    # built on first eval run, so the on-disk total grows well past this.
    ("dna",     "dna (chr17 variants)",   0.43,
     clean_dna,     install_dataset_dna),
    ("binexec", "binexec (CentOS bins)",  1.5,
     clean_binexec, install_dataset_binexec),
    # APPENDED, never inserted: the interactive menu numbers options from
    # the registry order, so putting zombie anywhere else would renumber
    # email/dna/binexec out from under anyone following the README.
    # 0.04 GB for the clone; run_zombie.py's TestRegex + out-of-workspace
    # circ copy add several GB under /tmp at evaluation time, not here.
    ("zombie",  "zombie (NSDI'24)",       0.04,
     clean_zombie,  install_dataset_zombie),
    # APPENDED, never inserted (same reason as zombie above): the menu
    # numbers options from this order.  0.05 GB of recorded run logs --
    # the raw inputs behind every table and figure in the paper.
    ("paper_data", "paper_data (recorded runs)", 0.05,
     clean_paper_data, install_dataset_paper_data),
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
    # Do NOT fall through to all_keys.  The install loop runs clean_fn()
    # BEFORE install_fn(), so escalating an unrecognized answer to ALL
    # wipes datasets the reviewer never asked about -- clean_email()
    # alone rmtree()s 3.8 GB -- and then re-downloads 5.8 GB.  An empty
    # answer or "1" still means ALL: that is the advertised default.  A
    # typo is not consent, so it aborts having changed nothing.
    sys.exit("unrecognized choice %r; nothing was installed.\n"
             "  valid: 1 or 'all', 2-%d, or a name (%s)"
             % (choice, len(DATASETS) + 1,
                ", ".join(d[0] for d in DATASETS)))


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
                    help="VERIFY-ONLY MODE: report what is installed and "
                         "digest-check the binexec corpus, then exit. "
                         "Downloads nothing, deletes nothing, installs "
                         "nothing.")
    ap.add_argument("--verify-download", action="store_true",
                    help="binexec: during an INSTALL, check all 2702 files "
                         "against manifest.list after download (the "
                         "archive's own sha256 is always checked)")
    ap.add_argument("--skip-reef-build", action="store_true",
                    help="dna: deploy the corpus but do NOT run "
                         "`cargo build` for Reef (the baseline binary will "
                         "be missing until you build it by hand)")
    ap.add_argument("--force-zombie", action="store_true",
                    help="zombie: re-clone even when zombie/ is already "
                         "present (the clone follows the default branch, "
                         "so this can move the baseline commit)")
    ap.add_argument("--build-zombie", action="store_true",
                    help="zombie: also compile TestRegex + circ now "
                         "instead of on first use (slow); implies "
                         "--force-zombie, since the downloader can only "
                         "build a tree it just cloned")
    args = ap.parse_args()

    global _VERIFY_ALL, _SKIP_REEF_BUILD, _FORCE_ZOMBIE, _BUILD_ZOMBIE
    _VERIFY_ALL = args.verify_download
    _SKIP_REEF_BUILD = args.skip_reef_build
    _BUILD_ZOMBIE = args.build_zombie
    _FORCE_ZOMBIE = args.force_zombie or args.build_zombie

    # Before anything else: needs no toolchain, no network and no dataset
    # selection, and data/debug + data/paper_data + data/src_sig/clamav
    # fixtures are inputs the eval path reads regardless of which corpus is
    # installed (e.g. DatasetSpec CLAM's sig_file is one of them).  No
    # clean_* function touches these paths, so restoring once here is not
    # undone by the loop below.
    restore_bigfiles()

    # F3: verify-only exits HERE -- before select_datasets(), so a non-tty
    # run can no longer escalate to "install ALL", and before
    # ensure_toolchain(), since verifying needs no compiler.
    if args.verify:
        sys.exit(verify_installed())

    if args.toolchain:
        # --toolchain runs BEFORE the dataset selection, so the only
        # signal for the zombie extras is --data.  Bare --toolchain stays
        # base-only; the extras land in ensure_toolchain() below if the
        # menu later picks zombie.
        install_toolchain(with_zombie=args.data in ("all", "zombie"))
        if not args.data:
            return

    if args.data:
        selected = keys if args.data == "all" else [args.data]
    else:
        selected = select_datasets()

    ensure_toolchain(selected)                    # install missing tools

    os.makedirs(TMP_DIR, exist_ok=True)
    os.makedirs(CACHE_MAIN, exist_ok=True)        # ensure (never wiped)
    by_key = {d[0]: d for d in DATASETS}
    try:
        for key in selected:
            _, label, _gb, clean_fn, install_fn = by_key[key]
            print("=== install %s ===" % label)
            figs_snap = (snapshot_paper_figs() if key == "paper_data"
                         else None)
            clean_fn()                            # empty targets (item 4)
            try:
                install_fn()
            except BaseException:
                restore_paper_figs(figs_snap)
                raise
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
