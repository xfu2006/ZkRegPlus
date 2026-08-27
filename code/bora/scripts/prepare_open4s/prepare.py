#!/usr/bin/env python3
"""
prepare.py -- build, publish and inspect the anonymous artifact snapshot for
anonymous.4open.science.

USENIX Security '27 Cycle 1, tasks T902 (snapshot repo) and T903 (mint URL).

WHAT IT DOES
    Produces an identity-scrubbed copy of the BORA artifact as a fresh git
    repository with ONE squashed commit under a neutral identity, walks you
    action-by-action through the manual GitHub / 4open setup, and then
    re-inspects the result at two checkpoints: what GitHub received, and what
    the 4open mirror actually serves.

WHAT IT NEVER DOES
    - It never writes to your real repository.  Automated steps read through
      `git archive` and write only inside the staging directory.
    - It never copies the working tree.  The snapshot comes from
      `git archive HEAD:code/bora`, so untracked and gitignored files (which
      do contain absolute /home/... paths) cannot leak in.
    - It never pushes, mints or publishes anything.  Those are yours.

USAGE
    python3 scripts/prepare_open4s/prepare.py               # interactive
    python3 scripts/prepare_open4s/prepare.py --list
    python3 scripts/prepare_open4s/prepare.py --from pack
    python3 scripts/prepare_open4s/prepare.py --only checkmirror \\
            --zip ~/Downloads/bora_sec27.zip
    python3 scripts/prepare_open4s/prepare.py --yes          # no pauses

    Once the repo exists and the 4open ID is minted, publishing a change is
    one command -- it rebuilds, force-pushes, waits out 4open's hourly poll
    and re-inspects what the mirror then serves:

    python3 scripts/prepare_open4s/prepare.py --update
    python3 scripts/prepare_open4s/prepare.py --update --resume  # after a quit

Requires only the Python standard library (>= 3.6) and `git` on PATH.
"""

import argparse
import datetime
import gzip
import hashlib
import io
import json
import lzma
import os
import re
import shutil
import subprocess
import sys
import tarfile
import tempfile
import textwrap
import time
import zipfile

# ---------------------------------------------------------------------------
# CONFIGURATION -- everything policy-ish lives here so it is greppable.
# ---------------------------------------------------------------------------

# The artifact is rooted at code/bora, NOT at the git root.  INSTALL.py:32
# ("this file lives in scripts/, so the repo root is one level up") fixes this.
# Re-rooting is also what drops LOG, .gitmodules (which carries a bitbucket
# username), git_check.sh and the root .gitignore, with no prune rule needed.
SOURCE_SUBDIR = "code/bora"

BRANCH = "artifact-sec27"

# The ID is already cited in the paper at src/apdx_open_sci.tex:16.  It is not
# a preference; it must match character for character.
OPEN4S_ID = "bora_sec27"
OPEN4S_URL = "https://anonymous.4open.science/r/%s" % OPEN4S_ID

# Scratch space for the mirror check.  The downloaded ZIP is copied here and
# expanded here, then both go away together, so a full second copy of the
# artifact never lingers in /tmp under a random mkdtemp name nobody remembers.
#
# ONLY CHECK_DIR is ever deleted.  WORK_DIR is this project's own scratch root
# and holds gigabytes of sweep logs (/tmp/bora/scale_dlp and friends), so
# cleanup must never be pointed at WORK_DIR itself.
WORK_DIR = "/tmp/bora"
CHECK_DIR = os.path.join(WORK_DIR, "open4s_check")

# 4open re-reads the branch at most hourly.  Checking sooner downloads the
# PREVIOUS tree and diffs it against the manifest that was just rewritten, so
# the failure looks like hundreds of corrupted files rather than "too early".
#
# TWO hours, not one.  The hour is only the POLL interval -- the floor before
# 4open even notices the new tip.  On top of it sits a fetch and a full
# re-anonymization pass over a multi-GB repository, and the ZIP endpoint may
# serve an already-built archive from cache.  Waiting exactly one hour budgets
# for the poll and nothing else; the wait costs only wall-clock, while checking
# early costs a confusing failure and a second download.
MIRROR_LAG_SECONDS = 7200

# Identity used for the single squashed commit -- visible in `git log` on the
# mirror, so it must not resolve to a real person.
NEUTRAL_NAME = "Anonymous Author"
NEUTRAL_EMAIL = "anonymous@example.com"

# Fixed commit timestamp.  A real one leaks a timezone (hence a rough
# longitude); a fixed UTC one leaks nothing.
NEUTRAL_DATE = "2026-08-22T12:00:00+0000"

# The same instant as an epoch, for stamping tar headers in the pack.  Derived
# rather than hardcoded so the two can never drift apart.
NEUTRAL_EPOCH = int(datetime.datetime.strptime(
    NEUTRAL_DATE, "%Y-%m-%dT%H:%M:%S%z").timestamp())

# Deleted after export.
#   attic/      313 tracked files, 221 of them vendored noname/ark-noname with
#               no licence file and no `license` field: no redistribution grant.
#   *.swp/.swo  vim swap files embed the editing user's name AND hostname.
#               These two are TRACKED and binary, so 4open's redaction terms
#               (text only) could never scrub them.
#   scripts/prepare_open4s
#               THIS TOOL. It must never ship inside the artifact it builds:
#               REDACTION_TERMS below is a literal list of the author's name,
#               GitHub and Bitbucket handles and institution, and the README
#               names the build hostname. Publishing the scrubber inside the
#               thing it scrubs hands reviewers exactly what it exists to
#               hide. (Found by the tool flagging itself, once these files
#               were committed -- the identity scan is the only reason this
#               did not ship.)
PRUNE_PATHS = [
    "attic",
    "scripts/prepare_open4s",
    # Deferred-defect list.  It lives at the REPO ROOT (../../TODO.md),
    # outside SOURCE_SUBDIR, so `git archive HEAD:code/bora` cannot reach
    # it and this entry is a no-op today -- step_prune just logs "absent
    # (already clean)".  It is here as defence in depth: the file names
    # known bugs and their probabilities, so it must never ship, and if
    # anyone ever moves it beside the code this rule catches it.
    "TODO.md",
    # 37 MB offline backup of data/paper_data/, far over 4open's 8 MB
    # ceiling and too big to fit the bigfiles pack.  INSTALL.py
    # re-downloads it from the pinned Zenodo record when it is absent
    # (install_dataset_paper_data), so pruning it costs a reviewer
    # nothing.  data/paper_data_backup/README.md is NOT pruned: it stays
    # to explain what the folder holds and where the bytes come from.
    "data/paper_data_backup/bora_paper_data.tgz",
    "vendor/sonobe_mod/.rust-toolchain.swp",
    "vendor/sonobe_mod/folding-schemes/src/folding/foldpot/.circuits_super.rs.swo",
    # Dead-code folder (188 KB, 5 superseded .rs files) plus two
    # developer compile scripts. None is referenced by any build: the
    # workspace compiles the module tree via mod.rs, and the two .sh
    # files are personal cargo-invocation notebooks. A reviewer opening
    # a folder literally named TO_REMOVE reads it as untidiness.
    "vendor/sonobe_mod/folding-schemes/src/folding/foldpot/TO_REMOVE",
    "vendor/sonobe_mod/folding-schemes/src/folding/foldpot/compile.sh",
    "vendor/sonobe_mod/folding-schemes/src/folding/foldpot/two_compile.sh",
    # 508,614-line ranking of Enron messages by PII-pattern hit count,
    # keyed by real maildir path.  Sorted descending, so line 1 names the
    # highest-PII message in the corpus -- a pointer the public corpus
    # does not itself provide.  Nothing reads it: `grep -rI rank_email`
    # over the tree returns zero hits; it is a leftover of the Zombie
    # comparison run.
    "data/src_sig/ms_dlp/docs/rank_email_regex_zombie_international.txt.tgz",
    # Nested tar-in-a-tar whose INNER header carries the packing account
    # name.  Orphan: no reader anywhere in the tree, and the only thing
    # that names its payload (data/debug/full_dlp_sample/runcfg_failscan.
    # json) is itself unread.  Pruning beats scrubbing -- a file that does
    # not ship cannot leak.
    "data/src_sig/ms_dlp/docs/enron_list.tar.tgz",
    # Orphan twin of the _international list below: zero code readers (the
    # Rust CLEAN_TGZ const names only the _international one).  It carries
    # BOTH a dirty tar header and a "# dataset: /home/<user>/..." line in
    # its member content, so pruning removes two hits at once.
    "data/src_sig/ms_dlp/docs/clean_email_list_email_regex_zombie.txt.tgz",
    # The two survivors of the same Enron cleanup that already prunes
    # enron_list.tar.tgz above.  Nothing reads either: stats_helper.rs
    # only WRITES *_clean_enron_list.txt, and the two runcfgs that name
    # the uncompressed .txt are themselves unread.  Both carry a dirty
    # tar header, so pruning also drops two step_scrub dependencies.
    "data/src_sig/ms_dlp/docs/enron_list/full_clean_enron_list.txt.tgz",
    "data/src_sig/ms_dlp/docs/enron_list/pass_clean_enron_list.txt.tgz",
    # Four data/debug fixtures with no reader anywhere in the tree
    # (audited 2026-08-27).  They were in PACK_MEMBERS only because they
    # exceed 4open's 8 MB ceiling -- i.e. they were being compressed and
    # shipped for their own sake.  pass_/accept_needs_rank.tsv appear
    # solely as `report_out` WRITE targets in runcfg_{pass,accept}scan.
    # json; binexec5.dat's only mention in the whole tree was the packing
    # list itself; discharge_main_binexec.dat is a captured console log
    # (22,910 lines of "[job 0] LOG1: ...") sitting in a report dir that
    # zkp_driver.rs:2371 overwrites.  Removed from PACK_MEMBERS in the
    # same change -- a pruned path must never stay in the pack list.
    "data/debug/full_dlp_sample/config/pass_needs_rank.tsv",
    "data/debug/full_dlp_sample/config/accept_needs_rank.tsv",
    "data/debug/small_email/config/binexec5.dat",
    "data/debug/small_data_set2/config_dfa/discharge_main_binexec.dat",
]

# Pruned wherever they appear.  Deliberately only vim swap files.  Tracked
# *.orig / *.bak files are NOT all fixtures: data/debug/full_dlp_sample/
# scan_exp.dat.bak and src_sig/clamav/new_src/main.ldb.original are real
# inputs, so a blanket *.bak / *.orig rule here would silently drop them.
# The paper_data/run_data/scripts/eval/*.bak-before-* editor backups that
# used to need a human decision were deleted from the tree on 2026-08-26.
PRUNE_SUFFIXES = (".swp", ".swo", ".swn")

# 4open.science refuses to serve files larger than this.
SIZE_LIMIT = 8 * 1024 * 1024

# ---------------------------------------------------------------------------
# THE BIG-FILE PACK
#
# ORDER IS LOAD-BEARING.  Five of these are byte-identical copies of the same
# 11.11 MB ClamAV signature database.  LZMA collapses duplicates only inside
# one dictionary window (64 MB at preset 9), so the five must sit ADJACENT.
# Measured on the real tree:
#
#     tar.gz, any order .................... 30.94 MB  (gzip window is 32 KB;
#                                                       it can never dedupe)
#     tar.xz, alphabetical order ............ 8.67 MB  (still over the limit)
#     tar.xz, this order, preset 9|EXTREME .. 3.50 MB  (fits, 2.3x margin)
#
# Do NOT replace this with a glob or a sort.  It silently regresses past 8 MB
# and the failure surfaces only on the published mirror.
# ---------------------------------------------------------------------------
PACK_MEMBERS = [
    # --- the five identical copies, kept together ---
    "data/src_sig/clamav/categories/main.dat",
    "data/paper_data/clamav/config/main.dat",
    "data/debug/full_clamav/config/main.dat",
    "data/debug/full_data_set/config/main.dat",
    "data/debug/full_par_set/config/main.dat",
    # --- near-identical siblings, next in line ---
    "data/src_sig/clamav/new_src/main.ldb",
    "data/src_sig/clamav/new_src/main.ldb.original",
    "data/src_sig/clamav/categories/pm_reg.dat",
    # --- the Enron-corpus path indexes, mutually similar ---
    # file_needs_rank.tsv stays: build_scan500.py:5 and
    # numa_probe/build_np_corpus.py:46 both read it.  Its three former
    # neighbours here (pass_/accept_needs_rank.tsv, binexec5.dat) and the
    # captured discharge_main_binexec.dat log had no reader at all and
    # moved to PRUNE_PATHS on 2026-08-27; the pack shrinks accordingly, so
    # the 3.50 MB figure measured above predates that removal.
    "data/debug/full_dlp_sample/config/file_needs_rank.tsv",
]

# data/ root holds only README.md and .gitignore, so the pack and its
# digest list get their own folder.  step_pack makedirs() the parent.
PACK_PATH = "data/bigfiles/bigfiles.tar.xz"
PACK_SHA_PATH = "data/bigfiles/bigfiles.sha256"

GITIGNORE_BLOCK_HEADER = """
# ---------------------------------------------------------------------
# Restored by scripts/INSTALL.py from data/bigfiles/bigfiles.tar.xz.
#
# anonymous.4open.science refuses to serve any file over 8 MB, so the 9
# fixtures below ship inside one 3.0 MB xz archive instead of as loose
# files.  They are byte-identical to what the archive restores -- nothing
# is regenerated or re-encoded.  Same pattern as licenses/ above.
# ---------------------------------------------------------------------"""

# Identity strings that must not appear anywhere, in text OR binary.  4open
# auto-anonymizes only owner/org/repo, and only in text files.
IDENTITY_PATTERNS = [b"xiang", b"hofstra", b"xfu20", b"/home/", b"thinkpad",
                     b"fu.tex"]

# A hit is forgiven only when one of these appears in the window AROUND it.
# Context beats filename: a real /home/xiang added to an already-forgiven file
# would still be caught.
BENIGN_CONTEXTS = [
    # Two clamav READMEs cite an example path scrubbed to "anon" long ago:
    # "/home/anon/Desktop/NewResearch/Projects/ZkregPlus/...".
    b"/home/anon/",
]
CONTEXT_BEFORE = 40
CONTEXT_AFTER = 60

# Files whose NAME says "tar".  Suffix, not content, decides: a file named
# like an archive that will not open is a scan failure, never a silent pass.
ARCHIVE_SUFFIXES = (".tgz", ".tar.gz", ".tar", ".tar.xz", ".txz", ".tar.bz2")

# enron_list.tar.tgz held a tar inside a tar, so one level is not enough.
# Reaching the cap with an unexpanded inner archive is reported as a hit.
NEST_DEPTH_CAP = 3

# Member text rewritten by step_scrub, keyed by staging-relative archive.
# These are provenance comments that record the absolute path the file was
# generated from, which embeds the author's home directory.  The sole
# reader, load_email_list() in zkregplus/src/zkp_driver.rs, skips every line
# beginning with '#', so the value is inert -- but it must stay a comment.
# A pattern that matches nothing is a hard error, not a no-op: a silently
# skipped fix would ship the leak while reporting success.
CONTENT_FIXES = {
    "data/src_sig/ms_dlp/docs/"
    "clean_email_list_email_regex_zombie_international.txt.tgz": [
        (rb"(?m)^# dataset: .*$", b"# dataset: data/samples/email"),
    ],
}

# Paste into 4open's "Terms to redact" box.
REDACTION_TERMS = ["xiang", "Xiang", "Xiang Fu", "xfu2006", "xfu2009",
                   "hofstra", "Hofstra", "/home/xiang"]

# Where the Rust DatasetSpec consts live.  Parsed, never built -- the fields
# needed are plain &'static str literals.
RUST_DRIVER = "crates/zkregplus/src/bora_data_driver.rs"

# Prefixes populated by INSTALL.py at install time (Zenodo binexec, Zenodo dna,
# CMU Enron).  A required path under one of these is "expected but
# unverifiable without a real install", not a gap.
INSTALL_PROVIDED_ROOTS = [
    "data/samples/",
    "data/src_sig/chr17_variants/",
    "data/cache/",
    # bora_paper_data.tgz is pruned from the snapshot (PRUNE_PATHS): it is
    # 36.5 MB, over SIZE_LIMIT, and cannot join the pack.  INSTALL.py
    # re-downloads it from the pinned Zenodo record, so a required path
    # under here is "expected but unverifiable", not a gap.
    "data/paper_data_backup/",
]


# ---------------------------------------------------------------------------
# output helpers
# ---------------------------------------------------------------------------

class C:
    B = "\033[1m"
    G = "\033[32m"
    Y = "\033[33m"
    R = "\033[31m"
    D = "\033[2m"
    X = "\033[0m"

    @classmethod
    def off(cls):
        cls.B = cls.G = cls.Y = cls.R = cls.D = cls.X = ""


def hdr(text):
    print("\n" + C.B + "=" * 72 + C.X)
    print(C.B + text + C.X)
    print(C.B + "=" * 72 + C.X)


def ok(t):
    print("  " + C.G + "OK  " + C.X + t)


def warn(t):
    print("  " + C.Y + "WARN" + C.X + " " + t)


def bad(t):
    print("  " + C.R + "FAIL" + C.X + " " + t)


def die(t):
    bad(t)
    sys.exit(1)


def info(t):
    print("       " + C.D + t + C.X)


def mb(n):
    return "%.2f MB" % (n / 1048576.0)


def human_delta(seconds):
    seconds = int(max(0, seconds))
    m, s = divmod(seconds, 60)
    h, m = divmod(m, 60)
    if h:
        return "%dh %02dm" % (h, m)
    if m:
        return "%dm %02ds" % (m, s)
    return "%ds" % s


def check_dir(sub=""):
    """A path inside CHECK_DIR, created on demand."""
    p = os.path.join(CHECK_DIR, sub) if sub else CHECK_DIR
    if not os.path.isdir(p):
        os.makedirs(p)
    return p


def clean_check_dir():
    """Remove CHECK_DIR -- and never WORK_DIR, which is not ours to delete."""
    if os.path.isdir(CHECK_DIR):
        shutil.rmtree(CHECK_DIR, ignore_errors=True)
        ok("cleaned %s" % CHECK_DIR)


def ask(prompt, auto_yes, default=""):
    """Free-text prompt; returns default under --yes."""
    if auto_yes:
        return default
    try:
        return input("  " + C.B + prompt + C.X + " ").strip() or default
    except EOFError:
        return default


def confirm(prompt, auto_yes):
    if auto_yes:
        print("  " + C.D + "(--yes) " + prompt + " -> continuing" + C.X)
        return
    try:
        r = input("\n  " + C.B + prompt + C.X + " [Enter=yes, q=quit] ").strip().lower()
    except EOFError:
        return
    if r in ("q", "quit", "n", "no"):
        print("  stopped.")
        sys.exit(0)


def action(idx, total, title, body, auto_yes):
    """One manual action, shown alone and acknowledged before the next.

    Manual steps are deliberately NOT printed as one wall of text: you should
    never be reading ahead of what you are doing.
    """
    print("\n  " + C.Y + ("-- action %d of %d " % (idx, total)).ljust(70, "-") + C.X)
    print("  " + C.B + title + C.X)
    for line in textwrap.dedent(body).strip("\n").split("\n"):
        print("    " + line)
    if not auto_yes:
        try:
            input("\n  " + C.D + "[Enter when done]" + C.X + " ")
        except EOFError:
            pass


# ---------------------------------------------------------------------------
# git / fs helpers
# ---------------------------------------------------------------------------

def git(args, cwd, check=True, env=None):
    r = subprocess.run(["git"] + args, cwd=cwd, env=env,
                       stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    if check and r.returncode != 0:
        die("git %s failed: %s" % (" ".join(args),
                                   r.stderr.decode("utf-8", "replace").strip()))
    return r.stdout.decode("utf-8", "replace").strip()


def walk_files(root):
    """(abs, rel) for regular files.  Symlinks are not followed or returned."""
    for dirpath, dirnames, filenames in os.walk(root):
        if ".git" in dirnames:
            dirnames.remove(".git")
        for name in filenames:
            p = os.path.join(dirpath, name)
            if not os.path.islink(p):
                yield p, os.path.relpath(p, root)


def walk_links(root):
    for dirpath, dirnames, filenames in os.walk(root):
        if ".git" in dirnames:
            dirnames.remove(".git")
        for name in dirnames + filenames:
            p = os.path.join(dirpath, name)
            if os.path.islink(p):
                yield p, os.path.relpath(p, root)


def deref_symlinks(stage):
    """Replace every symlink with a real copy of whatever it points at.

    4open neither follows symlinks nor drops them: it serves each one as a
    TEXT FILE whose contents are the link path.  Measured on the live mirror
    2026-08-13, the 1.45 MB DLP fixture arrived as 68 bytes reading
    "../../../paper_data/dlp/cfg/regex_pat/main_data_dlp_internationl.dat",
    and every per-curve LICENSE-MIT as 14 bytes reading "../LICENSE-MIT".

    That is worse than dropping them.  The path still exists, so a
    completeness check comparing recorded paths passes while the content is
    garbage -- and the manifest stores None as a symlink's size, so the size
    comparison has nothing to catch it with either.  Inlining is the only
    fix that survives the proxy.

    Called AFTER prune deliberately: a link into a pruned path must fail
    loudly here rather than silently restore what prune just deleted.
    """
    root = os.path.realpath(stage)
    # Materialise the list before mutating the tree -- walk_links is a
    # generator over os.walk, and swapping a link for a real directory
    # underneath it would change what the walk sees mid-iteration.
    links = sorted(walk_links(stage), key=lambda t: t[1])
    n_file = n_dir = added = 0
    for p, rel in links:
        target = os.path.realpath(p)
        if target != root and not target.startswith(root + os.sep):
            die("symlink escapes the artifact: %s -> %s\n"
                "       inlining it would pull in content from outside the "
                "exported tree" % (rel, os.readlink(p)))
        if not os.path.exists(target):
            die("broken symlink: %s -> %s\n"
                "       target missing (pruned?), so it cannot be inlined"
                % (rel, os.readlink(p)))
        os.unlink(p)
        if os.path.isdir(target):
            # symlinks=False resolves any nested links into real files too.
            shutil.copytree(target, p, symlinks=False)
            n_dir += 1
            added += sum(os.path.getsize(fp) for fp, _ in walk_files(p))
        else:
            shutil.copy2(target, p)
            n_file += 1
            added += os.path.getsize(p)
    left = [r for _, r in walk_links(stage)]
    if left:
        die("%d symlink(s) survived inlining, e.g. %s" % (len(left), left[0]))
    if n_file or n_dir:
        ok("inlined %d symlink(s) as real files (%d dir), +%s"
           % (n_file + n_dir, n_dir, mb(added)))
    else:
        info("no symlinks to inline")


def sha256_file(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for c in iter(lambda: f.read(1 << 20), b""):
            h.update(c)
    return h.hexdigest()


def identity_hits(blob, label):
    """(hits, forgiven) for one blob.  A hit is (label, pattern, snippet).

    Split out of inspect_tree so the same rules -- including BENIGN_CONTEXTS
    -- apply to bytes that are not loose files on disk, notably the members
    and headers inside the xz pack.
    """
    hits, forgiven = [], 0
    low = blob.lower()
    for pat in IDENTITY_PATTERNS:
        start = 0
        while True:
            i = low.find(pat, start)
            if i < 0:
                break
            start = i + 1
            win = low[max(0, i - CONTEXT_BEFORE):i + len(pat) + CONTEXT_AFTER]
            if any(b in win for b in BENIGN_CONTEXTS):
                forgiven += 1
                continue
            hits.append((label, pat.decode(),
                         win.decode("utf-8", "replace").replace("\n", " ")))
    return hits, forgiven


def archive_identity_hits(path, rel, depth=0, blob=None):
    """(hits, forgiven, opened) for one tar archive, headers included.

    identity_hits() reads raw bytes, so compression hides everything inside
    an archive: the member CONTENTS, and the tar HEADERS, which record the
    packing user by NAME.  "xiang/xiang" shipped in the published snapshot
    exactly that way (see neutral()); the pack got a hand-written special
    case afterwards, but every other .tgz in the tree stayed unscanned.
    This is that special case, generalised, so the class cannot recur.

    Returns opened=False when the bytes are not a readable tar.  The caller
    decides what that means -- for a file matching ARCHIVE_SUFFIXES it is a
    failure, because an archive we cannot see into is precisely the hole.
    """
    hits, forgiven = [], 0
    try:
        if blob is None:
            tf = tarfile.open(path, "r:*")
        else:
            tf = tarfile.open(fileobj=io.BytesIO(blob), mode="r:*")
    except Exception:
        return [], 0, False
    # Opening only parses the first header.  A truncated or corrupt archive
    # opens cleanly and then raises on the first read(), so the walk needs the
    # same guard: report opened=False and let the caller fail the run, rather
    # than dying with a traceback or -- worse -- returning "no hits found" for
    # an archive nobody could actually look inside.
    try:
        for mem in tf:
            head = "%s %s %s" % (mem.name, mem.uname, mem.gname)
            h, g = identity_hits(head.encode(),
                                 "%s!%s [tar header]" % (rel, mem.name))
            hits += h
            forgiven += g
            if not mem.isreg():
                continue
            src = tf.extractfile(mem)
            if src is None:
                continue
            data = src.read()
            h, g = identity_hits(data, "%s!%s" % (rel, mem.name))
            hits += h
            forgiven += g
            if not mem.name.endswith(ARCHIVE_SUFFIXES):
                continue
            label = "%s!%s" % (rel, mem.name)
            if depth + 1 >= NEST_DEPTH_CAP:
                hits.append((label, "nested-archive",
                             "nested deeper than %d -- NOT scanned"
                             % NEST_DEPTH_CAP))
                continue
            ih, ig, iopened = archive_identity_hits(path, label, depth + 1,
                                                    blob=data)
            if not iopened:
                hits.append((label, "nested-archive",
                             "named like a tar but could not be opened"))
            hits += ih
            forgiven += ig
    except Exception:
        return hits, forgiven, False
    finally:
        tf.close()
    return hits, forgiven, True


def neutral(ti):
    """Strip the packer's identity and the wall clock from one tar header.

    tar records the owning user and group by NAME.  Left alone these read
    "xiang/xiang" -- which `tar tvf` prints on every line and INSTALL.py
    restores.  A raw byte search cannot see it once the archive is
    compressed; this shipped in the published snapshot before it was found
    by hand, 2026-08-13.  archive_identity_hits() is the detector for the
    same bug; this is the fix.

    Fixing mtime too makes archives byte-identical across exports.  `git
    archive HEAD:<subdir>` archives a TREE, which carries no commit
    timestamp, so it stamps the current time -- without this the pack, and
    therefore the snapshot commit, changes on every single run.
    """
    ti.uid = ti.gid = 0
    ti.uname = ti.gname = ""
    ti.mtime = NEUTRAL_EPOCH
    return ti


def extract_all(tf, path):
    """extractall with an explicit filter where the runtime supports one.

    3.12 deprecates the filterless call, 3.14 makes it an error.  "tar" rather
    than "data" because it preserves the executable bit that several shipped
    scripts rely on; it still blocks absolute paths and ../ traversal.
    """
    try:
        tf.extractall(path, filter="tar")
    except TypeError:                       # Python < 3.12
        tf.extractall(path)


# ---------------------------------------------------------------------------
# Rust DatasetSpec parsing
#
# PAPER_DATA.py:1144-1146 says the six Rust leaves declare no required_files
# because "the Rust leaves assert on their own config/corpus paths, which live
# in DatasetSpec".  DatasetSpec is Rust, so this reads it there rather than
# transcribing the paths into Python where they would silently drift.
# ---------------------------------------------------------------------------

def _strip_line_comments(src):
    """Remove // comments without touching // inside string literals."""
    out, i, n, in_str = [], 0, len(src), False
    while i < n:
        c = src[i]
        if in_str:
            if c == "\\":
                out.append(src[i:i + 2])
                i += 2
                continue
            if c == '"':
                in_str = False
            out.append(c)
            i += 1
            continue
        if c == '"':
            in_str = True
            out.append(c)
            i += 1
            continue
        if c == "/" and i + 1 < n and src[i + 1] == "/":
            while i < n and src[i] != "\n":
                i += 1
            continue
        out.append(c)
        i += 1
    return "".join(out)


def parse_dataset_specs(rust_path):
    """{name: {config_dir, sig_file, master_sources, scale_sources}}.

    Raises RuntimeError rather than under-reporting: a silent partial parse
    would turn into a falsely-green readiness report.
    """
    if not os.path.isfile(rust_path):
        raise RuntimeError("Rust driver not found: %s" % rust_path)
    clean = _strip_line_comments(
        open(rust_path, encoding="utf-8", errors="replace").read())

    specs = {}
    for m in re.finditer(
            r"pub const (\w+)\s*:\s*DatasetSpec\s*=\s*DatasetSpec\s*\{", clean):
        name, start = m.group(1), m.end()
        depth, i = 1, start
        while i < len(clean) and depth:
            if clean[i] == "{":
                depth += 1
            elif clean[i] == "}":
                depth -= 1
            i += 1
        if depth:
            raise RuntimeError("unbalanced braces in const %s" % name)
        body = clean[start:i - 1]

        def scalar(field, specs=specs):
            mm = re.search(field + r'\s*:\s*"([^"]*)"', body)
            if mm:
                return mm.group(1)
            mm = re.search(field + r'\s*:\s*(\w+)\.(\w+)\s*,', body)
            if mm:
                ref = specs.get(mm.group(1))
                return ref.get(mm.group(2)) if ref else None
            return None

        def array(field):
            mm = re.search(field + r'\s*:\s*&\s*\[(.*?)\]', body, re.S)
            # NOTE: `is None` matters -- `scale_sources: &[]` is a legitimate
            # empty list (DNA has no scale sweep), and an empty list is falsy.
            # Conflating the two would hide a real parse failure.
            return None if mm is None else re.findall(r'"([^"]*)"', mm.group(1))

        spec = {
            "config_dir": scalar("config_dir"),
            "sig_file": scalar("sig_file"),
            "master_sources": array("master_sources"),
            "scale_sources": array("scale_sources"),
        }
        missing = [k for k, v in spec.items() if v is None]
        if missing:
            raise RuntimeError(
                "const %s: could not parse %s -- the Rust probably stopped "
                "using plain string literals (concat!(), a helper fn, ...). "
                "Fix this parser rather than trusting a partial result."
                % (name, ", ".join(missing)))
        specs[name] = spec

    if len(specs) < 3:
        raise RuntimeError(
            "expected at least 3 DatasetSpec consts (DLP, DNA, CLAM), found %d "
            "-- refusing to report readiness from a partial parse" % len(specs))
    return specs


def rust_required_paths(root):
    """[(leaf, repo-relative path)] for the Rust-driven leaves."""
    specs = parse_dataset_specs(os.path.join(root, RUST_DRIVER))
    out = []
    for name, s in sorted(specs.items()):
        out.append((name.lower(), s["config_dir"] + "/" + s["sig_file"]))
        for p in s["master_sources"] + s["scale_sources"]:
            out.append((name.lower(), p))
    return out, specs


def python_required_paths(root, timeout=120):
    """[(leaf, path)] from PAPER_DATA.py's own required_files declarations.

    Imported in a SUBPROCESS: PAPER_DATA.py is 5,330 lines and this may run
    against a tree downloaded from the mirror, so a hang or a hard exit must
    not take the checker with it.  Returns (paths, note).
    """
    pd = os.path.join(root, "scripts", "PAPER_DATA.py")
    if not os.path.isfile(pd):
        return [], "scripts/PAPER_DATA.py absent -- skipped"
    helper = textwrap.dedent("""
        import importlib.util, json, sys, os
        path = sys.argv[1]
        spec = importlib.util.spec_from_file_location("pd", path)
        m = importlib.util.module_from_spec(spec)
        sys.modules["pd"] = m          # it self-references; register pre-exec
        spec.loader.exec_module(m)
        out = []
        for key, js in getattr(m, "JOB_SPECS", {}).items():
            fn = getattr(js, "required_files", None)
            if not fn:
                continue
            for mode in ("dry", "full"):
                try:
                    for p in (fn(mode) or []):
                        out.append([key, p])
                except Exception:
                    pass
        print(json.dumps({"paths": out,
                          "leaves": list(getattr(m, "JOB_SPECS", {}))}))
    """)
    # -B / PYTHONDONTWRITEBYTECODE are NOT hygiene, they are correctness.
    # Importing PAPER_DATA.py makes CPython write scripts/__pycache__/*.pyc
    # NEXT TO THE IMPORTED FILE, i.e. inside the tree under inspection: the
    # check would mutate its own subject, the .pyc would be swept into the
    # commit by `git add -A -f`, and -- worst -- .pyc files embed the absolute
    # source path, so a stage dir under $HOME would bake /home/<user>/... into
    # a file created AFTER the anonymity scan had already passed.
    env = dict(os.environ, PYTHONDONTWRITEBYTECODE="1")
    try:
        r = subprocess.run([sys.executable, "-B", "-c", helper, pd],
                           cwd=os.path.dirname(pd), stdout=subprocess.PIPE,
                           stderr=subprocess.PIPE, timeout=timeout, env=env)
    except subprocess.TimeoutExpired:
        return [], "PAPER_DATA.py import timed out -- skipped"
    if r.returncode != 0:
        return [], ("PAPER_DATA.py import failed -- skipped (%s)"
                    % r.stderr.decode("utf-8", "replace").strip().split("\n")[-1][:90])
    try:
        data = json.loads(r.stdout.decode("utf-8", "replace").strip().split("\n")[-1])
    except Exception:
        return [], "PAPER_DATA.py produced unparseable output -- skipped"

    paths, seen = [], set()
    for key, p in data["paths"]:
        rel = os.path.relpath(p, root) if os.path.isabs(p) else p
        if (key, rel) not in seen:
            seen.add((key, rel))
            paths.append((key, rel))
    return paths, "%d of %d JOB_SPECS leaves declare required_files" % (
        len({k for k, _ in paths}), len(data["leaves"]))


# ---------------------------------------------------------------------------
# THE REUSABLE INSPECTION  (requirement [b])
#
# Runs against any tree: the staging dir, a clone of the pushed GitHub repo, or
# an extracted 4open ZIP.  Returns a list of failure strings; empty == clean.
# ---------------------------------------------------------------------------

def inspect_tree(root, label, manifest=None, expect_pack_sha=None,
                 require_entry_points=True):
    hdr("INSPECTION -- %s" % label)
    info("root: %s" % root)
    failures = []

    files = list(walk_files(root))
    links = list(walk_links(root))
    total = sum(os.path.getsize(p) for p, _ in files)
    info("%d files + %d symlinks, %s" % (len(files), len(links), mb(total)))

    # --- (2) file size limit ------------------------------------------------
    over = [(r, os.path.getsize(p)) for p, r in files
            if os.path.getsize(p) > SIZE_LIMIT]
    if over:
        for r, s in sorted(over, key=lambda t: -t[1]):
            print("       %s  %s" % (mb(s).rjust(9), r))
        failures.append("%d file(s) exceed %s" % (len(over), mb(SIZE_LIMIT)))
    else:
        big = max(((os.path.getsize(p), r) for p, r in files), default=(0, "-"))
        ok("size: nothing over %s (largest %s %s)"
           % (mb(SIZE_LIMIT), mb(big[0]), big[1]))

    # --- (1) anonymity ------------------------------------------------------
    # Every file is scanned raw, and every file NAMED like a tar is opened
    # as well.  Compression hides both member contents and tar headers from
    # the raw pass, so an unopened archive is an unscanned archive.  The
    # pack used to be the only one opened, by a hand-written arm here; it is
    # now just one more ARCHIVE_SUFFIXES match, which is what stops the next
    # .tgz from slipping through the way these did.
    hits, forgiven = [], 0
    n_arch = 0
    for p, r in files:
        try:
            with open(p, "rb") as f:
                blob = f.read()
        except OSError:
            continue
        h, g = identity_hits(blob, r)
        hits += h
        forgiven += g
        if not r.replace(os.sep, "/").endswith(ARCHIVE_SUFFIXES):
            continue
        ah, ag, opened = archive_identity_hits(p, r)
        hits += ah
        forgiven += ag
        if opened:
            n_arch += 1
        else:
            failures.append("%s is named like an archive but could not be "
                            "opened for the identity scan" % r)
    if hits:
        shown = set()
        for r, pat, snip in hits:
            if (r, pat) in shown:
                continue
            shown.add((r, pat))
            if len(shown) > 20:
                break
            print("       %-10s %s" % (pat, r))
            print("       %-10s %s" % ("", snip[:110]))
        if len(hits) > 20:
            info("... and %d more hit(s)" % (len(hits) - 20))
        info("if a hit is harmless, add its surrounding text to "
             "BENIGN_CONTEXTS -- do not remove the pattern")
        failures.append("%d identity hit(s)" % len(hits))
    else:
        ok("anonymity: clean across %d files%s (%s)"
           % (len(files),
              " + %d archive(s) opened, members and headers included"
              % n_arch if n_arch else "",
              ", ".join(p.decode() for p in IDENTITY_PATTERNS)))
        if forgiven:
            info("%d occurrence(s) matched BENIGN_CONTEXTS and were forgiven"
                 % forgiven)

    # --- stray VCS / editor metadata ---------------------------------------
    # .gitignore/.gitkeep/.gitattributes are ordinary files here.  .gitmodules
    # records submodule URLs -- which is how a bitbucket username reached the
    # tracked tree -- and a nested .git would carry full author history.
    # __pycache__ is in here because .pyc files embed the absolute path of the
    # source they were compiled from, and nothing in the artifact needs them.
    strays = [r for _, r in files
              if os.path.basename(r) == ".gitmodules"
              or ".git/" in (r.replace(os.sep, "/") + "/")
              or "__pycache__/" in (r.replace(os.sep, "/") + "/")
              or r.endswith(PRUNE_SUFFIXES)]
    if strays:
        for r in strays[:20]:
            print("       %s" % r)
        failures.append("%d stray VCS/editor/bytecode file(s)" % len(strays))
    else:
        ok("no .gitmodules, nested .git, __pycache__, or editor swap files")

    # --- symlinks -----------------------------------------------------------
    unsafe = []
    for p, r in links:
        t = os.readlink(p)
        if os.path.isabs(t):
            unsafe.append((r, t, "absolute"))
        elif not os.path.abspath(
                os.path.normpath(os.path.join(os.path.dirname(p), t))
        ).startswith(os.path.abspath(root)):
            unsafe.append((r, t, "escapes"))
    if unsafe:
        for r, t, why in unsafe[:20]:
            print("       %-9s %s -> %s" % (why, r, t))
        failures.append("%d unsafe symlink(s)" % len(unsafe))
    elif links:
        # Since step_prune inlines them, a symlink here means the tree was
        # built by an older prepare.py -- 4open would serve each one as a
        # text file holding the link path, so they must not ship.
        warn("symlinks: %d present -- step_prune should have inlined these; "
             "4open would serve them as text stubs" % len(links))
    else:
        ok("symlinks: none (inlined at export, so the proxy cannot stub them)")

    dangling = [r for p, r in links if not os.path.exists(p)]
    if dangling:
        for r in dangling[:5]:
            warn("dangling symlink: %s" % r)

    # --- pack integrity -----------------------------------------------------
    pack_abs = os.path.join(root, PACK_PATH)
    if os.path.isfile(pack_abs):
        got = sha256_file(pack_abs)
        if expect_pack_sha and got != expect_pack_sha:
            bad("pack sha256 MISMATCH")
            info("expected %s" % expect_pack_sha)
            info("got      %s" % got)
            failures.append("pack altered in transit -- every restored fixture "
                            "would be wrong")
        else:
            try:
                with tarfile.open(pack_abs, "r:xz") as tf:
                    names = tf.getnames()
                if sorted(names) != sorted(PACK_MEMBERS):
                    failures.append("pack member list differs from PACK_MEMBERS")
                    bad("pack holds %d members, expected %d"
                        % (len(names), len(PACK_MEMBERS)))
                else:
                    ok("pack: readable, %d members, sha256 %s"
                       % (len(names), got[:16] + ("  (matches)" if expect_pack_sha else "")))
            except Exception as exc:
                failures.append("pack unreadable: %s" % exc)
                bad("pack unreadable: %s" % exc)
    else:
        failures.append("%s missing" % PACK_PATH)
        bad("%s missing -- 13 fixtures cannot be restored" % PACK_PATH)

    # --- (3) PAPER_DATA.py readiness ---------------------------------------
    try:
        rust_paths, specs = rust_required_paths(root)
        rust_note = "%d DatasetSpec consts parsed (%s)" % (
            len(specs), ", ".join(sorted(specs)))
    except RuntimeError as exc:
        rust_paths, rust_note = [], None
        failures.append("DatasetSpec parse failed: %s" % exc)
        bad("DatasetSpec parse failed: %s" % exc)

    py_paths, py_note = python_required_paths(root)
    required = rust_paths + py_paths

    if required:
        buckets = {"snapshot": [], "pack": [], "install": [], "gap": []}
        for leaf, rel in required:
            if os.path.exists(os.path.join(root, rel)):
                buckets["snapshot"].append((leaf, rel))
            elif rel in PACK_MEMBERS:
                buckets["pack"].append((leaf, rel))
            elif any(rel.startswith(x) for x in INSTALL_PROVIDED_ROOTS):
                buckets["install"].append((leaf, rel))
            else:
                buckets["gap"].append((leaf, rel))
        if rust_note:
            info("rust:   %s" % rust_note)
        info("python: %s" % py_note)
        ok("readiness: %d required input(s) -- %d present, %d in pack, "
           "%d from INSTALL.py download"
           % (len(required), len(buckets["snapshot"]), len(buckets["pack"]),
              len(buckets["install"])))
        for leaf, rel in buckets["pack"]:
            info("via pack:    [%s] %s" % (leaf, rel))
        for leaf, rel in buckets["install"]:
            info("via install: [%s] %s" % (leaf, rel))
        if buckets["gap"]:
            for leaf, rel in buckets["gap"]:
                print("       [%-10s] %s" % (leaf, rel))
            failures.append("%d required input(s) unaccounted for"
                            % len(buckets["gap"]))
        else:
            ok("readiness: no unaccounted inputs")
        info("NOTE: 'from INSTALL.py download' is accounted for, NOT verified. "
             "Only a real install proves those corpora arrive intact.")

    # --- completeness vs the recorded manifest ------------------------------
    if manifest:
        have = {r: os.path.getsize(p) for p, r in files}
        have.update({r: None for _, r in links})
        want = manifest["files"]
        missing = sorted(set(want) - set(have))
        added = sorted(set(have) - set(want))
        changed = [r for r in set(want) & set(have)
                   if want[r] is not None and have[r] is not None
                   and want[r] != have[r]]
        if missing:
            for r in missing[:20]:
                print("       missing  %s" % r)
            if len(missing) > 20:
                info("... and %d more missing" % (len(missing) - 20))
            failures.append("%d file(s) missing vs the published snapshot"
                            % len(missing))
        if changed:
            for r in changed[:10]:
                print("       resized  %s (%s -> %s)"
                      % (r, want[r], have[r]))
            failures.append("%d file(s) changed size" % len(changed))
        if added:
            info("%d file(s) present here but not in the snapshot "
                 "(e.g. mirror-added metadata)" % len(added))
            for r in added[:5]:
                info("  added: %s" % r)
        if not missing and not changed:
            ok("completeness: all %d recorded entries present, sizes match"
               % len(want))

    print()
    if failures:
        for f in failures:
            bad(f)
    else:
        ok("ALL CHECKS PASSED -- %s" % label)
    return failures


# ---------------------------------------------------------------------------
# steps
# ---------------------------------------------------------------------------

def step_preflight(ctx):
    hdr("STEP 1/13  preflight")
    if sys.version_info < (3, 6):
        die("Python 3.6+ required")
    ok("Python %d.%d" % sys.version_info[:2])
    if not shutil.which("git"):
        die("git not found on PATH")
    ok("git " + git(["--version"], ctx["repo"]).replace("git version ", ""))
    try:
        lzma.LZMACompressor(preset=9 | lzma.PRESET_EXTREME)
        ok("lzma available (preset 9|EXTREME) -- no external xz needed")
    except Exception as exc:
        die("Python lzma unusable: %s" % exc)

    lock = os.path.join(ctx["repo"], ".git", "index.lock")
    if os.path.exists(lock):
        die("%s exists -- another git process is running. Finish or kill it; "
            "do NOT delete the lock while a git process is alive." % lock)
    ok("no .git/index.lock")

    ctx["head"] = git(["rev-parse", "HEAD"], ctx["repo"])
    ok("HEAD %s  %s" % (ctx["head"][:12],
                        git(["log", "-1", "--pretty=%s"], ctx["repo"])))

    dirty = git(["status", "--porcelain"], ctx["repo"])
    if dirty:
        lines = dirty.split("\n")
        warn("working tree has %d modified/untracked path(s)" % len(lines))
        info("the snapshot comes from HEAD, so these are NOT included")
        for l in lines[:10]:
            info("  " + l)
    else:
        ok("working tree clean")

    git(["rev-parse", "HEAD:%s" % SOURCE_SUBDIR], ctx["repo"])
    ok("HEAD:%s resolves -- artifact rooted there" % SOURCE_SUBDIR)
    info("staging: %s" % ctx["stage"])
    info("manifest: %s" % ctx["manifest_path"])


def step_export(ctx):
    hdr("STEP 2/13  export tracked tree from git")
    stage = ctx["stage"]
    if os.path.exists(stage):
        shutil.rmtree(stage)
    os.makedirs(stage)
    proc = subprocess.Popen(["git", "archive", "HEAD:%s" % SOURCE_SUBDIR],
                            cwd=ctx["repo"], stdout=subprocess.PIPE)
    with tarfile.open(fileobj=proc.stdout, mode="r|") as tf:
        extract_all(tf, stage)
    proc.stdout.close()
    if proc.wait() != 0:
        die("git archive failed")
    files = list(walk_files(stage))
    ok("exported %d files + %d symlinks, %s"
       % (len(files), sum(1 for _ in walk_links(stage)),
          mb(sum(os.path.getsize(p) for p, _ in files))))
    info("source: git archive HEAD:%s (never the working tree)" % SOURCE_SUBDIR)
    info("dropped by re-rooting: LOG, .gitmodules, git_check.sh, root .gitignore")


def step_prune(ctx):
    hdr("STEP 3/13  prune non-shippable paths, inline symlinks")
    stage = ctx["stage"]
    n_files = n_bytes = 0
    for rel in PRUNE_PATHS:
        p = os.path.join(stage, rel)
        if not os.path.exists(p) and not os.path.islink(p):
            info("absent (already clean): %s" % rel)
            continue
        if os.path.isdir(p) and not os.path.islink(p):
            n = b = 0
            for fp, _ in walk_files(p):
                n += 1
                b += os.path.getsize(fp)
            shutil.rmtree(p)
            n_files += n
            n_bytes += b
            ok("removed dir  %-56s %d files, %s" % (rel, n, mb(b)))
        else:
            b = 0 if os.path.islink(p) else os.path.getsize(p)
            os.remove(p)
            n_files += 1
            n_bytes += b
            ok("removed file %-56s %s" % (rel, mb(b)))
    extra = [(p, r) for p, r in walk_files(stage) if r.endswith(PRUNE_SUFFIXES)]
    for p, r in extra:
        n_bytes += os.path.getsize(p)
        n_files += 1
        os.remove(p)
        ok("removed swap %s" % r)
    if not extra:
        ok("no further editor swap files found")

    # Belt and braces: .pyc files embed the absolute path they were compiled
    # from. git archive never exports them (they are gitignored), so anything
    # here was created locally -- see the -B note in python_required_paths.
    pyc = 0
    for dirpath, dirnames, _ in list(os.walk(stage)):
        if "__pycache__" in dirnames:
            d = os.path.join(dirpath, "__pycache__")
            for fp, _ in walk_files(d):
                n_bytes += os.path.getsize(fp)
                pyc += 1
            shutil.rmtree(d)
            dirnames.remove("__pycache__")
    n_files += pyc
    ok("removed %d __pycache__ file(s)" % pyc)
    print()
    info("pruned %d files, %s" % (n_files, mb(n_bytes)))
    print()
    deref_symlinks(stage)


def step_scrub(ctx):
    hdr("STEP 4/13  neutralise identity inside shipped archives")
    stage = ctx["stage"]

    # Rebuild each archive in a temp dir OUTSIDE the stage, then rename it
    # into place.  Writing in place would leave a truncated archive behind
    # if this died mid-write, and a temp dir inside the stage would be
    # committed wholesale by step_initrepo's `git add -A -f`.
    tmp = tempfile.mkdtemp(prefix="bora_scrub_",
                           dir=os.path.dirname(os.path.abspath(stage)))
    n_arch = n_hdr = n_fix = 0
    try:
        for abs_path, rel in sorted(walk_files(stage), key=lambda t: t[1]):
            key = rel.replace(os.sep, "/")
            if not key.endswith(ARCHIVE_SUFFIXES):
                continue
            try:
                tf = tarfile.open(abs_path, "r:*")
            except Exception as exc:
                die("%s is named like an archive but will not open: %s"
                    % (rel, exc))
            members = []
            dirty = False
            with tf:
                for mem in tf:
                    data = b""
                    if mem.isreg():
                        src = tf.extractfile(mem)
                        data = src.read() if src is not None else b""
                    if mem.uname or mem.gname or mem.uid or mem.gid:
                        dirty = True
                    members.append((mem, data))
            # matched counts pattern hits (zero means the file changed shape
            # and the fix silently stopped working); changed counts hits that
            # actually altered bytes.  They differ on a re-run over an already
            # scrubbed tree, where the pattern still matches but rewrites the
            # line to what it already says -- that must stay a no-op, or every
            # export would differ and run_update could never report "nothing
            # to publish".
            fixes = CONTENT_FIXES.get(key, [])
            matched = changed = 0
            if fixes:
                for i, (mem, data) in enumerate(members):
                    before = data
                    for pat, repl in fixes:
                        data, k = re.subn(pat, repl, data)
                        matched += k
                    if data != before:
                        changed += 1
                    members[i] = (mem, data)
                if not matched:
                    die("CONTENT_FIXES for %s matched nothing -- the file "
                        "changed shape; fix the pattern rather than "
                        "shipping it unscrubbed" % key)
            if not dirty and not changed:
                continue

            out = os.path.join(tmp, os.path.basename(rel))
            # gzip's own header carries a name and an mtime that tarfile's
            # "w:gz" fills from the wall clock -- that alone would make every
            # export differ and defeat the no-op check in run_update.  Drive
            # the gzip layer directly so the bytes are reproducible.
            with open(out, "wb") as raw:
                gz = gzip.GzipFile(filename="", mtime=NEUTRAL_EPOCH,
                                   mode="wb", fileobj=raw, compresslevel=9)
                with gz:
                    with tarfile.open(fileobj=gz, mode="w",
                                      format=tarfile.PAX_FORMAT) as out_tf:
                        for mem, data in members:
                            ti = neutral(mem)
                            ti.size = len(data)
                            out_tf.addfile(ti, io.BytesIO(data))
            os.replace(out, abs_path)
            n_arch += 1
            n_hdr += len(members)
            n_fix += changed
            ok("rewrote %-58s %d member(s)%s"
               % (rel, len(members),
                  ", %d content fix(es)" % changed if changed else ""))
    finally:
        shutil.rmtree(tmp, ignore_errors=True)

    if not n_arch:
        info("no archive needed scrubbing")
    else:
        print()
        info("%d archive(s), %d header(s) neutralised, %d content fix(es)"
             % (n_arch, n_hdr, n_fix))
    info("step_verify re-opens every archive afterwards; that scan, not "
         "this step, is the gate")


def step_pack(ctx):
    hdr("STEP 5/13  pack oversized files into one archive")
    stage = ctx["stage"]
    missing = [m for m in PACK_MEMBERS
               if not os.path.isfile(os.path.join(stage, m))]
    if missing:
        die("pack member(s) missing from the export: %s" % ", ".join(missing))
    ok("all %d pack members present" % len(PACK_MEMBERS))

    strays = [(r, os.path.getsize(p)) for p, r in walk_files(stage)
              if os.path.getsize(p) > SIZE_LIMIT and r not in PACK_MEMBERS]
    if strays:
        for r, s in sorted(strays, key=lambda t: -t[1]):
            print("       %s  %s" % (mb(s).rjust(9), r))
        die("%d file(s) over %s are not in PACK_MEMBERS -- update the list "
            "(keep identical files adjacent!)" % (len(strays), mb(SIZE_LIMIT)))
    ok("no oversized file outside the member list")

    raw = sum(os.path.getsize(os.path.join(stage, m)) for m in PACK_MEMBERS)
    pack_abs = os.path.join(stage, PACK_PATH)
    os.makedirs(os.path.dirname(pack_abs), exist_ok=True)
    print()
    info("compressing %s with preset 9|EXTREME -- takes a few minutes" % mb(raw))
    info("member order is deliberate; see PACK_MEMBERS in this script")

    # neutral() is module-level: step_scrub applies the identical filter to
    # every other archive in the tree, and one implementation cannot drift.
    with tarfile.open(pack_abs, mode="w:xz",
                      preset=9 | lzma.PRESET_EXTREME) as tf:
        for m in PACK_MEMBERS:
            tf.add(os.path.join(stage, m), arcname=m, recursive=False,
                   filter=neutral)

    size = os.path.getsize(pack_abs)
    digest = sha256_file(pack_abs)
    ok("%s -> %s (%.0fx)" % (mb(raw), mb(size), raw / float(size)))
    ok("sha256 %s" % digest)
    if size > SIZE_LIMIT:
        die("pack is %s, over the %s limit -- check that the five identical "
            "main.dat copies are adjacent in PACK_MEMBERS"
            % (mb(size), mb(SIZE_LIMIT)))
    ok("fits with %.1fx margin" % (SIZE_LIMIT / float(size)))

    digests = {m: sha256_file(os.path.join(stage, m)) for m in PACK_MEMBERS}
    with tarfile.open(pack_abs, "r:xz") as tf:
        names = tf.getnames()
    if sorted(names) != sorted(PACK_MEMBERS):
        die("archive member list does not match PACK_MEMBERS")
    ok("archive contains exactly the %d expected members" % len(names))

    with open(os.path.join(stage, PACK_SHA_PATH), "w") as f:
        f.write("%s  %s\n" % (digest, os.path.basename(PACK_PATH)))
        for m in PACK_MEMBERS:
            f.write("%s  %s\n" % (digests[m], m))
    ok("wrote %s (pack + per-member digests)" % PACK_SHA_PATH)

    for m in PACK_MEMBERS:
        os.remove(os.path.join(stage, m))
    ok("removed the %d loose originals" % len(PACK_MEMBERS))

    with open(os.path.join(stage, "data", ".gitignore"), "a") as f:
        f.write("\n" + GITIGNORE_BLOCK_HEADER.strip("\n") + "\n")
        for m in PACK_MEMBERS:
            f.write(m[len("data/"):] + "\n")
    ok("appended %d restore targets to data/.gitignore" % len(PACK_MEMBERS))
    ctx["pack_sha"] = digest


def step_verify(ctx):
    hdr("STEP 6/13  inspect the staging tree")
    if inspect_tree(ctx["stage"], "staging tree",
                    expect_pack_sha=ctx.get("pack_sha")):
        die("verification failed -- fix the above before publishing")


def step_initrepo(ctx):
    hdr("STEP 7/13  initialise the snapshot repository")
    stage = ctx["stage"]
    if os.path.exists(os.path.join(stage, ".git")):
        shutil.rmtree(os.path.join(stage, ".git"))
    git(["init", "-q"], stage)
    git(["symbolic-ref", "HEAD", "refs/heads/%s" % BRANCH], stage)
    git(["config", "user.name", NEUTRAL_NAME], stage)
    git(["config", "user.email", NEUTRAL_EMAIL], stage)
    git(["config", "commit.gpgsign", "false"], stage)
    ok("git init, branch %s, identity %s <%s>"
       % (BRANCH, NEUTRAL_NAME, NEUTRAL_EMAIL))

    # -f is REQUIRED, not defensive.  In a fresh repo `git add -A` honours
    # .gitignore; in ZkregPlus these files survive only because ignore rules
    # never apply to already-tracked files.  Without -f, data/.gitignore's
    # "samples/*" silently drops data/samples/email/README.md, and any future
    # rule would drop more, with no warning at all.
    git(["add", "-A", "-f"], stage)

    env = dict(os.environ)
    env.update({"GIT_AUTHOR_NAME": NEUTRAL_NAME,
                "GIT_AUTHOR_EMAIL": NEUTRAL_EMAIL,
                "GIT_AUTHOR_DATE": NEUTRAL_DATE,
                "GIT_COMMITTER_NAME": NEUTRAL_NAME,
                "GIT_COMMITTER_EMAIL": NEUTRAL_EMAIL,
                "GIT_COMMITTER_DATE": NEUTRAL_DATE})
    git(["commit", "-q", "-m",
         "BORA artifact snapshot for anonymous review"], stage, env=env)

    sha = git(["rev-parse", "HEAD"], stage)
    count = git(["rev-list", "--count", "HEAD"], stage)
    ctx["snap_sha"] = sha
    ok("commit %s (history depth %s)" % (sha[:12], count))
    ok("recorded: %s" % git(["log", "-1", "--pretty=%an <%ae> / %cn <%ce> / %ad"],
                            stage))
    if count != "1":
        die("expected exactly 1 commit, found %s" % count)
    if git(["remote"], stage):
        die("snapshot repo already has a remote; it must have none yet")
    ok("no remote configured yet")

    # reconciliation: everything on disk must be in the commit
    on_disk = {r for _, r in walk_files(stage)} | {r for _, r in walk_links(stage)}
    committed = set(git(["ls-files"], stage).split("\n")) - {""}
    lost = sorted(on_disk - committed)
    if lost:
        for r in lost[:20]:
            bad("on disk but NOT committed: %s" % r)
        die("%d file(s) did not reach the commit" % len(lost))
    ok("reconciliation: all %d entries on disk are in the commit" % len(on_disk))


def step_manifest(ctx):
    hdr("STEP 8/13  record the local manifest")
    stage = ctx["stage"]
    files = {r: os.path.getsize(p) for p, r in walk_files(stage)}
    files.update({r: None for _, r in walk_links(stage)})   # None = symlink
    pack_abs = os.path.join(stage, PACK_PATH)
    data = {
        "snapshot_commit": ctx.get("snap_sha"),
        "source_head": ctx.get("head"),
        "branch": BRANCH,
        "pack_sha256": (sha256_file(pack_abs) if os.path.isfile(pack_abs)
                        else ctx.get("pack_sha")),
        "files": files,
    }
    # Keep the OUTGOING manifest before overwriting it.  If the mirror later
    # serves a tree matching this file rather than the new one, the mirror is
    # merely stale -- and that is the difference between "wait another hour"
    # and "the scrub failed", which the raw per-file diff cannot express.
    if os.path.isfile(ctx["manifest_path"]):
        shutil.copy2(ctx["manifest_path"], ctx["manifest_path"] + ".prev")
        info("previous manifest kept at %s.prev" % ctx["manifest_path"])

    with open(ctx["manifest_path"], "w") as f:
        json.dump(data, f, indent=1, sort_keys=True)
    ctx["pack_sha"] = data["pack_sha256"]
    ok("wrote %s (%d entries)" % (ctx["manifest_path"], len(files)))
    print()
    warn("KEEP THIS FILE. It is deliberately outside the artifact, so the "
         "completeness diff in steps 10 and 12 depends on it surviving.")
    if ctx["manifest_path"].startswith("/tmp/"):
        warn("it is under /tmp and will not survive a reboot -- consider "
             "re-running with --manifest ~/bora_open4s.manifest.json")


def step_github(ctx):
    hdr("STEP 9/13  MANUAL -- create the private GitHub repo and push")
    sha = ctx.get("snap_sha", "<run step 7 first>")
    stage = ctx["stage"]
    y = ctx["yes"]

    action(1, 4, "Create an empty PRIVATE repository", """
        Open https://github.com/new

          Visibility : PRIVATE
          Name       : anything -- 4open anonymizes owner/org/repo for you

        Do NOT tick "Add a README", ".gitignore" or "licence": the push must
        fast-forward onto an empty repo.

        Do NOT reuse ZkRegPlus. The snapshot must carry no history and no
        relation to your other repositories.
        """, y)

    action(2, 4, "Point the snapshot at it", """
        cd %s
        git remote add origin git@github.com:<you>/<repo>.git

        (HTTPS works too; whatever your git is already authenticated for.)
        """ % stage, y)

    action(3, 4, "Push the single commit", """
        git push -u origin %s

        Exactly one commit (%s) on branch %s.
        """ % (BRANCH, sha[:12], BRANCH), y)

    action(4, 4, "Eyeball it on github.com", """
        [ ] the branch shows ONE commit
        [ ] the author reads "%s"
        [ ] data/bigfiles/bigfiles.tar.xz is present, about 3.5 MB
        [ ] no file is over 8 MB

        Leave this repository in place. 4open does not copy your code -- it
        proxies it live, so deleting or locking the repo breaks the mirror
        mid-review.
        """ % NEUTRAL_NAME, y)

    url = ask("paste the repo URL for the next check (or Enter to skip):", y)
    if url:
        ctx["github_url"] = url


def step_checkpush(ctx):
    hdr("STEP 10/13  inspect what GitHub actually received")
    url = ctx.get("github_url") or ask(
        "GitHub repo URL to clone (Enter to skip this check):", ctx["yes"])
    if not url:
        warn("skipped -- no URL given")
        info("re-run later with: --only checkpush")
        return
    tmp = tempfile.mkdtemp(prefix="bora_pushcheck_")
    dest = os.path.join(tmp, "clone")
    info("cloning %s (branch %s)" % (url, BRANCH))
    r = subprocess.run(["git", "clone", "-q", "--depth", "1", "-b", BRANCH,
                        url, dest], stdout=subprocess.PIPE,
                       stderr=subprocess.PIPE)
    if r.returncode != 0:
        shutil.rmtree(tmp, ignore_errors=True)
        bad("clone failed: %s"
            % r.stderr.decode("utf-8", "replace").strip().split("\n")[-1])
        info("this check needs your own GitHub credentials in this shell "
             "(SSH key or gh token). Fix auth and re-run --only checkpush.")
        die("cannot verify the push")
    try:
        sha = git(["rev-parse", "HEAD"], dest)
        if ctx.get("snap_sha") and sha != ctx["snap_sha"]:
            warn("remote HEAD %s != local snapshot %s"
                 % (sha[:12], ctx["snap_sha"][:12]))
        else:
            ok("remote HEAD %s matches the snapshot commit" % sha[:12])
        failures = inspect_tree(dest, "clone of the pushed GitHub repo",
                                manifest=ctx.get("manifest"),
                                expect_pack_sha=ctx.get("pack_sha"))
        if failures:
            die("the pushed repo is not clean -- fix and force-push before minting")
    finally:
        shutil.rmtree(tmp, ignore_errors=True)


def step_fouropen(ctx):
    hdr("STEP 11/13  MANUAL -- mint the anonymous.4open.science URL")
    y = ctx["yes"]

    action(1, 6, "Open the anonymize form", """
        https://anonymous.4open.science

        Sign in with GitHub and authorise it to read the private repository
        you just pushed.

        IMPORTANT, and unverified: I could not confirm that 4open serves
        PRIVATE repos. If the form will not list or accept your private repo,
        STOP HERE and tell me -- do not make the repo public to work around
        it. Going public before the scrub is reviewed is the one irreversible
        mistake available at this stage.
        """, y)

    action(2, 6, "Set the repository ID -- this one is not a preference", """
        Anonymized repository ID : %s

        The paper already cites the resulting URL at
        src/apdx_open_sci.tex:16, and every %%T9xx marker has been stripped
        from the source, so nothing else will flag a mismatch. It must match
        character for character:

          %s
        """ % (OPEN4S_ID, OPEN4S_URL), y)

    action(3, 6, "Set branch and commit", """
        Branch : %s
        Commit : LEAVE BLANK

        Blank commit + auto-update is what lets the URL be final on 08-25
        while the content behind it keeps changing until 08-28.
        """ % BRANCH, y)

    action(4, 6, "Auto update ON, and never Redirect to GitHub", """
        Auto update        : ON   (hourly at most)
        Redirect to GitHub : NEVER select this -- it deanonymizes you

        Conference : SEC27
        """, y)

    action(5, 6, "Expiration -- pick the FURTHEST date offered", """
        Floor: it must outlast 2026-12-15 (shepherd approval can run that
        late). An early expiry means reviewers lose the artifact mid-cycle;
        an over-long one costs nothing, since you control retirement.

        Write down what you actually chose:  ______________
        """, y)

    action(6, 6, "Terms to redact -- one per line", """
%s

        Text only. Binaries are served verbatim, which is why the two vim
        swap files were deleted in step 3 rather than redacted.
        """ % "\n".join("          " + t for t in REDACTION_TERMS), y)


def tree_matches_manifest(root, manifest):
    """True when `root` reproduces `manifest` exactly -- same names, same sizes."""
    have = {r: os.path.getsize(p) for p, r in walk_files(root)}
    have.update({r: None for _, r in walk_links(root)})
    want = manifest.get("files") or {}
    if set(have) != set(want):
        return False
    return not [r for r in want
                if want[r] is not None and have[r] is not None
                and want[r] != have[r]]


def diagnose_stale(root, ctx):
    """Distinguish "the mirror has not refreshed" from "the scrub is broken".

    A mirror that has not re-polled serves the PREVIOUS tree, which the current
    manifest then reports as thousands of missing and changed files -- a wall of
    noise that reads exactly like catastrophic corruption.  Re-testing the same
    tree against the manifest saved just before the last rebuild collapses that
    into a one-line verdict, and only that comparison can tell the two apart.
    """
    prev_path = ctx["manifest_path"] + ".prev"
    if not os.path.isfile(prev_path):
        return
    try:
        with open(prev_path) as f:
            prev = json.load(f)
    except Exception as exc:
        warn("could not read %s: %s" % (prev_path, exc))
        return
    if not tree_matches_manifest(root, prev):
        return          # genuinely different from BOTH snapshots -- a real fault

    print()
    bad("STALE MIRROR -- this ZIP is the PREVIOUS snapshot %s, not the %s you"
        % ((prev.get("snapshot_commit") or "?")[:12],
           (ctx.get("snap_sha") or "?")[:12]))
    bad("just pushed.  Nothing above is a scrub failure.")
    info("The tree matches %s exactly, so 4open simply has not re-read the"
         % prev_path)
    info("branch yet. Wait, re-download, and check again.")
    if ctx.get("pushed_at"):
        info("pushed %s ago; allow %s in total."
             % (human_delta(time.time() - ctx["pushed_at"]),
                human_delta(MIRROR_LAG_SECONDS)))
    print()
    info("Re-download later, then check again with EITHER:")
    info("  --only checkmirror --zip <new file>   inspect now, no waiting")
    info("  --update --resume  --zip <new file>   wait out the clock first")
    info("Re-checking is free and repeatable: nothing is pushed or rebuilt.")


def check_mirror_zip(ctx, zip_path):
    """Expand a downloaded 4open ZIP under CHECK_DIR and inspect it.

    The ZIP is COPIED, not moved: the browser's download stays where the
    browser put it.  The copy and its expansion both live under CHECK_DIR and
    are deleted together on the way out, pass or fail.

    Returns the inspect_tree failure list.
    """
    zip_path = os.path.expanduser(zip_path)
    if not os.path.isfile(zip_path):
        die("no such file: %s" % zip_path)

    try:
        staged = os.path.join(check_dir(), os.path.basename(zip_path))
        if os.path.abspath(zip_path) != os.path.abspath(staged):
            shutil.copy2(zip_path, staged)
            info("copied the ZIP to %s (%s)" % (staged,
                                                mb(os.path.getsize(staged))))
        dest = check_dir("extracted")
        with zipfile.ZipFile(staged) as zf:
            zf.extractall(dest)
        ok("extracted into %s" % dest)

        # 4open may wrap everything in one top directory; descend if so.
        entries = [e for e in os.listdir(dest) if not e.startswith("__MACOSX")]
        root = dest
        if len(entries) == 1 and os.path.isdir(os.path.join(dest, entries[0])):
            root = os.path.join(dest, entries[0])
            info("descended into single top-level dir: %s" % entries[0])

        failures = inspect_tree(root, "4open mirror (downloaded ZIP)",
                                manifest=ctx.get("manifest"),
                                expect_pack_sha=ctx.get("pack_sha"))
        if failures:
            diagnose_stale(root, ctx)

        print()
        info("REMINDER: the mirror is a live proxy, not a copy. Any fix means")
        info("push to GitHub, wait for auto-update, re-download, re-check:")
        info("  --update                             rebuild, push, wait, check")
        info("  --only checkmirror --zip <file>      just re-check, no waiting")
        info("Do NOT re-mint to force a refresh -- you risk losing the ID.")
        return failures
    finally:
        clean_check_dir()
        if os.path.isfile(zip_path):
            info("your original download is untouched at %s" % zip_path)


def step_checkmirror(ctx):
    hdr("STEP 12/13  inspect what the 4open mirror actually serves")
    y = ctx["yes"]
    zip_path = ctx.get("zip")

    if not zip_path:
        print()
        info("Open %s in a browser and use its download button to get the" % OPEN4S_URL)
        info("anonymized ZIP. (curl cannot do this: 4open answers 403 to")
        info("non-browser agents, so an automated fetch is unreliable.)")
        zip_path = ask("path to the downloaded ZIP (Enter to skip):", y)
    if not zip_path:
        warn("skipped -- no ZIP given")
        info("re-run later with: --only checkmirror --zip <file>")
        return
    if check_mirror_zip(ctx, zip_path):
        die("the mirror is not clean")


def step_freeze(ctx):
    hdr("STEP 13/13  MANUAL -- the two lock-up dates")
    y = ctx["yes"]
    sha = ctx.get("snap_sha", "<the published commit>")

    action(1, 2, "2026-08-25 -- the URL is final", """
        Nothing to do on 4open, but from this date the ID cannot change:
        the submitted PDF cites %s

        Content may still change until 08-28. Auto update stays ON.
        """ % OPEN4S_URL, y)

    action(2, 2, "2026-08-28 -- freeze the content (task T913)", """
        Return to the 4open form for %s and set:

          Commit : %s

        Pinning the SHA is a harder freeze than switching auto-update off:
        it makes the mirror serve one immutable tree regardless of what the
        GitHub branch does afterwards.

        Then re-run one last time:
          --only checkmirror --zip <freshly downloaded ZIP>

        After this the artifact is frozen. USENIX allows no updates past the
        grace period; if something is genuinely broken, email
        sec27chairs@usenix.org rather than pushing silently.
        """ % (OPEN4S_ID, sha), y)


# ---------------------------------------------------------------------------
# --update: republish an already-minted mirror
#
# Steps 8 and 10 are one-time: the GitHub repo exists and the 4open ID is
# minted and cited in the paper.  Everything after that is a loop -- rebuild,
# replace the branch tip, wait out the poll interval, re-inspect -- and that
# loop is what this section automates.  The 4open ID, branch, auto-update flag
# and redaction terms are never touched; the mirror is a live proxy on BRANCH,
# so replacing the tip IS the update, and re-minting to "refresh" would put
# the ID the submitted PDF cites at risk.
# ---------------------------------------------------------------------------

def record_push_time(ctx):
    """Persist push time and repo URL so a later --resume can find them."""
    path = ctx["manifest_path"]
    try:
        with open(path) as f:
            data = json.load(f)
        data["pushed_at"] = ctx["pushed_at"]
        data["github_url"] = ctx.get("github_url")
        with open(path, "w") as f:
            json.dump(data, f, indent=1, sort_keys=True)
        ctx["manifest"] = data
    except Exception as exc:
        warn("could not record the push time in %s: %s" % (path, exc))
        info("--update --resume will not know when the hour started")


def push_snapshot(ctx):
    """Force-push the rebuilt snapshot over the published branch.

    --force is structural, not a convenience: step_initrepo builds a brand new
    repository with one squashed commit every time, so the new tip shares no
    ancestry with the published one and can never fast-forward.
    """
    hdr("UPDATE 2/3  force-push the rebuilt snapshot")
    stage = ctx["stage"]
    y = ctx["yes"]

    url = ctx.get("github_url") or ask(
        "GitHub repo URL to push to (Enter to abort):", y)
    if not url:
        die("no repo URL -- pass --repo-url, or answer the prompt")
    ctx["github_url"] = url

    # step_initrepo refuses to leave a remote behind, so this is normally a
    # fresh add; the remove keeps a re-run from tripping over a stale one.
    if git(["remote"], stage):
        git(["remote", "remove", "origin"], stage)
    git(["remote", "add", "origin", url], stage)
    ok("origin -> %s" % url)

    confirm("force-push %s to %s, replacing the published tree?" % (BRANCH, url),
            y)

    r = subprocess.run(["git", "push", "--force", "-u", "origin", BRANCH],
                       cwd=stage, stdout=subprocess.PIPE,
                       stderr=subprocess.PIPE)
    if r.returncode != 0:
        bad("push failed: %s"
            % r.stderr.decode("utf-8", "replace").strip().split("\n")[-1])
        info("this needs your own GitHub credentials in this shell (SSH key")
        info("or gh token). Fix auth and re-run --update.")
        die("cannot publish the rebuilt snapshot")
    ok("pushed %s to %s" % ((ctx.get("snap_sha") or "?")[:12], BRANCH))
    ctx["pushed_at"] = time.time()
    record_push_time(ctx)


def wait_for_mirror(ctx):
    """Hold until 4open can plausibly have re-read the branch."""
    pushed = ctx.get("pushed_at")
    if not pushed:
        warn("no recorded push time -- cannot tell whether the mirror is current")
        info("if you pushed less than %s ago, the check below will compare the"
             % human_delta(MIRROR_LAG_SECONDS))
        info("OLD tree against the NEW manifest and fail confusingly.")
        return
    ready = pushed + MIRROR_LAG_SECONDS
    if time.time() >= ready:
        ok("pushed %s ago -- the mirror has had time to re-read the branch"
           % human_delta(time.time() - pushed))
        return

    hdr("UPDATE 3/3  wait for the mirror to catch up")
    info("pushed at   %s" % time.strftime("%H:%M:%S", time.localtime(pushed)))
    info("ready after %s  (4open polls hourly at most)"
         % time.strftime("%H:%M:%S", time.localtime(ready)))
    print()
    info("Downloading before then gets the PREVIOUS tree, which is then diffed")
    info("against the manifest written minutes ago: the report is a wall of")
    info("bogus per-file differences, not a clear 'too early'.")

    if ctx["yes"]:
        warn("--yes: not waiting %s" % human_delta(ready - time.time()))
        return

    print()
    r = ask("[Enter] wait here (%s) / s = check now anyway / q = quit:"
            % human_delta(ready - time.time()), False)
    if r[:1].lower() == "q":
        print()
        info("Resume with:  --update --resume")
        sys.exit(0)
    if r[:1].lower() == "s":
        warn("checking early at your request -- expect noisy differences")
        return

    info("Ctrl-C is safe here: the push is done and nothing is half-written.")
    try:
        while True:
            left = ready - time.time()
            if left <= 0:
                break
            sys.stdout.write("\r  " + C.D + "waiting %-10s" % human_delta(left)
                             + C.X)
            sys.stdout.flush()
            time.sleep(min(30, left))
        sys.stdout.write("\r" + " " * 40 + "\r")
    except KeyboardInterrupt:
        print()
        info("interrupted -- resume with: --update --resume")
        sys.exit(0)
    ok("the mirror has had its hour")


def run_update(ctx, resume=False):
    """Rebuild, force-push, wait out the poll interval, re-inspect."""
    hdr("UPDATE  republish the artifact snapshot")
    info("The 4open ID, branch, auto-update flag and redaction terms are all")
    info("left alone. Only the branch tip moves.")

    if not resume:
        prev_sha = ctx.get("snap_sha")

        hdr("UPDATE 1/3  rebuild the snapshot")
        # Steps 1-8 verbatim.  export MUST be included: it is the only step
        # that recreates staging, and re-pruning an already-packed tree fails
        # in step 5 with "pack member(s) missing from the export".
        for name, _, fn in STEPS:
            if name == "github":
                break
            fn(ctx)
            if name == "manifest":
                with open(ctx["manifest_path"]) as f:
                    ctx["manifest"] = json.load(f)
                ctx["pack_sha"] = ctx["manifest"].get("pack_sha256")
            else:
                confirm("continue to next step?", ctx["yes"])

        new_sha = ctx.get("snap_sha")
        if prev_sha and new_sha == prev_sha:
            hdr("UPDATE  nothing to publish")
            ok("the snapshot commit is unchanged: %s" % new_sha[:12])
            info("Identity and timestamps are fixed constants, so an identical")
            info("tree reproduces an identical commit. The mirror already")
            info("serves this exact snapshot; nothing was pushed.")
            return
        if prev_sha:
            info("replacing published %s with %s"
                 % (prev_sha[:12], (new_sha or "?")[:12]))

        push_snapshot(ctx)
        step_checkpush(ctx)
    else:
        info("--resume: skipping rebuild and push")
        if not ctx.get("pushed_at"):
            warn("no push recorded in %s" % ctx["manifest_path"])

    wait_for_mirror(ctx)

    hdr("UPDATE  re-inspect what the mirror now serves")
    zip_path = ctx.get("zip")
    if not zip_path:
        print()
        info("Open %s in a browser and download the ZIP." % OPEN4S_URL)
        info("(curl cannot: 4open answers 403 to non-browser agents.)")
        zip_path = ask("path to the freshly downloaded ZIP (Enter to skip):",
                       ctx["yes"])
    if not zip_path:
        warn("skipped -- no ZIP given")
        info("finish later with: --update --resume --zip <file>")
        return
    if check_mirror_zip(ctx, zip_path):
        die("the refreshed mirror is not clean")
    ok("the mirror now serves snapshot %s" % (ctx.get("snap_sha") or "?")[:12])


STEPS = [
    ("preflight", "environment, git state, staging dir", step_preflight),
    ("export", "git archive HEAD:%s into staging" % SOURCE_SUBDIR, step_export),
    ("prune", "delete attic/ and swap files, inline symlinks", step_prune),
    ("scrub", "neutralise identity inside shipped archives", step_scrub),
    ("pack", "build data/bigfiles/bigfiles.tar.xz, drop originals", step_pack),
    ("verify", "inspect the staging tree", step_verify),
    ("initrepo", "git init + one squashed commit + reconciliation", step_initrepo),
    ("manifest", "record the local manifest", step_manifest),
    ("github", "MANUAL: create the private repo and push", step_github),
    ("checkpush", "clone back from GitHub and inspect", step_checkpush),
    ("fouropen", "MANUAL: mint the 4open URL", step_fouropen),
    ("checkmirror", "download the 4open ZIP and inspect", step_checkmirror),
    ("freeze", "MANUAL: 08-25 URL final, 08-28 pin the SHA", step_freeze),
]

MANUAL = {"github", "fouropen", "freeze"}


def main():
    ap = argparse.ArgumentParser(
        description="Build, publish and inspect the anonymous artifact snapshot.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=textwrap.dedent("""\
            Automated steps never touch your real repository: they read via
            `git archive` and write only inside the staging directory.
        """))
    ap.add_argument("--stage", default="/tmp/bora_open4s")
    ap.add_argument("--manifest", default=None,
                    help="local manifest path (default: <stage>.manifest.json)")
    ap.add_argument("--zip", default=None,
                    help="4open ZIP for the mirror check")
    ap.add_argument("--repo-url", default=None,
                    help="GitHub URL for the push check")
    ap.add_argument("--from", dest="start", metavar="STEP")
    ap.add_argument("--only", metavar="STEP")
    ap.add_argument("--update", action="store_true",
                    help="republish: rebuild, force-push, wait, re-check")
    ap.add_argument("--resume", action="store_true",
                    help="with --update: skip rebuild+push, just wait and check")
    ap.add_argument("--list", action="store_true")
    ap.add_argument("--yes", action="store_true", help="do not pause")
    ap.add_argument("--no-color", action="store_true")
    args = ap.parse_args()

    if args.no_color or not sys.stdout.isatty():
        C.off()

    names = [s[0] for s in STEPS]
    if args.list:
        print("steps:")
        for i, (n, d, _) in enumerate(STEPS, 1):
            print("  %2d. %-13s %s%s" % (i, n, d,
                                         " [MANUAL]" if n in MANUAL else ""))
        return

    if args.resume and not args.update:
        die("--resume only means anything with --update")
    if args.update and (args.only or args.start):
        die("--update runs its own sequence; drop --only/--from")

    selected = STEPS
    if args.only:
        if args.only not in names:
            die("unknown step %r (see --list)" % args.only)
        selected = [s for s in STEPS if s[0] == args.only]
    elif args.start:
        if args.start not in names:
            die("unknown step %r (see --list)" % args.start)
        selected = STEPS[names.index(args.start):]

    here = os.path.dirname(os.path.abspath(__file__))
    repo = git(["rev-parse", "--show-toplevel"], here)
    stage = os.path.abspath(args.stage)
    # step_export rmtree()s the stage before extracting into it, so a
    # stage inside the repo would delete tracked source.  Refuse here,
    # before any step runs.
    if stage == repo or stage.startswith(repo + os.sep):
        die("--stage must be outside the repo (%s): step_export "
            "deletes the stage directory before writing to it" % repo)
    ctx = {
        "repo": repo,
        "stage": stage,
        "manifest_path": os.path.abspath(args.manifest or (stage + ".manifest.json")),
        "zip": args.zip,
        "github_url": args.repo_url,
        "yes": args.yes,
    }

    # Later steps need the manifest recorded earlier; load it if present.
    if os.path.isfile(ctx["manifest_path"]):
        try:
            with open(ctx["manifest_path"]) as f:
                ctx["manifest"] = json.load(f)
            ctx["pack_sha"] = ctx["manifest"].get("pack_sha256")
            ctx["snap_sha"] = ctx["manifest"].get("snapshot_commit")
            ctx["pushed_at"] = ctx["manifest"].get("pushed_at")
            ctx["github_url"] = ctx["github_url"] or ctx["manifest"].get("github_url")
        except Exception as exc:
            warn("could not read manifest %s: %s" % (ctx["manifest_path"], exc))

    print(C.B + "\nBORA -> anonymous.4open.science" + C.X)
    print("  git repo : %s" % repo)
    print("  artifact : %s (re-rooted)" % SOURCE_SUBDIR)
    print("  staging  : %s" % stage)
    print("  manifest : %s%s" % (ctx["manifest_path"],
                                 "  (loaded)" if "manifest" in ctx else ""))
    if args.update:
        print("  mode     : --update%s" % (" --resume" if args.resume else ""))
    else:
        print("  steps    : %s" % ", ".join(s[0] for s in selected))
    if args.start and args.start != "preflight":
        info("resuming: earlier steps assumed already done in staging")

    if args.update:
        run_update(ctx, resume=args.resume)
        print()
        return

    for name, _, fn in selected:
        fn(ctx)
        if name != selected[-1][0]:
            confirm("continue to next step?", args.yes)
        if name == "manifest" and "manifest" not in ctx:
            with open(ctx["manifest_path"]) as f:
                ctx["manifest"] = json.load(f)

    hdr("done")
    if ctx.get("snap_sha"):
        print("  snapshot commit : %s" % ctx["snap_sha"])
    print("  staging dir     : %s" % stage)
    print("  manifest        : %s" % ctx["manifest_path"])
    print()


if __name__ == "__main__":
    main()
