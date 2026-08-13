#!/usr/bin/env python3
"""
prepare.py -- build the anonymous artifact snapshot for anonymous.4open.science.

USENIX Security '27 Cycle 1, tasks T902 (snapshot repo) and T903 (mint URL).

WHAT IT DOES
    Produces a self-contained, identity-scrubbed copy of the BORA artifact as a
    fresh git repository with ONE squashed commit under a neutral identity, then
    walks you through the manual GitHub / 4open.science setup.

WHAT IT NEVER DOES
    - It never writes to your real repository.  Every automated step reads from
      git and writes only into the staging directory.
    - It never copies the working tree.  The snapshot comes from
      `git archive HEAD:code/bora`, so untracked and gitignored files (which do
      contain absolute /home/... paths) cannot leak in.

USAGE
    python3 scripts/prepare_open4s/prepare.py              # interactive, all steps
    python3 scripts/prepare_open4s/prepare.py --list       # show the step list
    python3 scripts/prepare_open4s/prepare.py --from pack  # resume at a step
    python3 scripts/prepare_open4s/prepare.py --only verify
    python3 scripts/prepare_open4s/prepare.py --yes        # no confirmation prompts
    python3 scripts/prepare_open4s/prepare.py --stage /tmp/bora_snapshot

Requires only the Python standard library (>= 3.6) and `git` on PATH.
"""

import argparse
import hashlib
import lzma
import os
import shutil
import subprocess
import sys
import tarfile
import textwrap

# ---------------------------------------------------------------------------
# CONFIGURATION -- everything policy-ish lives here so it is greppable.
# ---------------------------------------------------------------------------

# The artifact is rooted at code/bora, NOT at the git root.  INSTALL.py:32
# ("this file lives in scripts/, so the repo root is one level up") fixes this,
# and re-rooting is also what drops LOG, .gitmodules (which carries a bitbucket
# username), git_check.sh and the root .gitignore without needing prune rules.
SOURCE_SUBDIR = "code/bora"

BRANCH = "artifact-sec27"

# Identity used for the single squashed commit.  It shows up in `git log` on
# the mirror, so it must not resolve to a real person.
NEUTRAL_NAME = "Anonymous Author"
NEUTRAL_EMAIL = "anonymous@example.com"

# Fixed commit timestamp.  A real timestamp leaks a timezone (and therefore a
# rough longitude); a fixed UTC one leaks nothing.  ISO-8601, +0000.
NEUTRAL_DATE = "2026-08-22T12:00:00+0000"

# Paths (relative to the artifact root) deleted after export.
#   attic/  -- 313 tracked files, 221 of them vendored noname/ark-noname with
#              NO licence file and no `license` field: no redistribution grant.
#   *.swp/.swo -- vim swap files embed the editing user's name AND hostname.
#              These two are TRACKED and are binary, so 4open's redaction
#              terms (text only) could never scrub them.
PRUNE_PATHS = [
    "attic",
    "vendor/sonobe_mod/.rust-toolchain.swp",
    "vendor/sonobe_mod/folding-schemes/src/folding/foldpot/.circuits_super.rs.swo",
]

# Any file matching these suffixes is pruned wherever it appears.  Restricted
# to vim swap files on purpose: tracked *.orig / *.bak files in this repo are
# real fixtures and scan clean.
PRUNE_SUFFIXES = (".swp", ".swo", ".swn")

# 4open.science refuses to serve files larger than this.
SIZE_LIMIT = 8 * 1024 * 1024

# ---------------------------------------------------------------------------
# THE BIG-FILE PACK
#
# ORDER IS LOAD-BEARING.  Five of these are byte-identical copies of the same
# 11.11 MB ClamAV signature database.  LZMA can only collapse duplicates that
# fall inside one dictionary window (64 MB at preset 9), so the five copies
# must sit ADJACENT in the archive.  Measured on the real tree:
#
#     tar.gz, any order .................... 30.94 MB   (gzip window is 32 KB,
#                                                        it can never dedupe)
#     tar.xz, alphabetical order ............ 8.67 MB   (still over the limit)
#     tar.xz, this order, preset 9|EXTREME .. 3.50 MB   (fits, 2.3x margin)
#
# Do NOT replace this list with a glob or a sort.  It silently regresses past
# the 8 MB limit and the failure only shows up on the mirror.
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
    "data/debug/full_dlp_sample/config/file_needs_rank.tsv",
    "data/debug/full_dlp_sample/config/pass_needs_rank.tsv",
    "data/debug/full_dlp_sample/config/accept_needs_rank.tsv",
    "data/debug/small_email/config/binexec5.dat",
    # --- a captured log ---
    "data/debug/small_data_set2/config_dfa/discharge_main_binexec.dat",
]

PACK_PATH = "data/bigfiles.tar.xz"
PACK_SHA_PATH = "data/bigfiles.sha256"

# Appended to data/.gitignore in the snapshot so the restored files do not show
# up as untracked noise in a reviewer's clone.  data/.gitignore already uses
# this idiom for licenses/ ("INSTALL.py restores verbatim ... so it is not kept
# in git").
GITIGNORE_BLOCK_HEADER = """
# ---------------------------------------------------------------------
# Restored by scripts/INSTALL.py from data/bigfiles.tar.xz.
#
# anonymous.4open.science refuses to serve any file over 8 MB, so the 13
# fixtures below ship inside one 3.5 MB xz archive instead of as loose
# files.  They are byte-identical to what the archive restores -- nothing
# is regenerated or re-encoded.  Same pattern as licenses/ above.
# ---------------------------------------------------------------------"""

# Identity strings that must not appear anywhere in the snapshot, in text OR
# binary.  4open auto-anonymizes only owner/org/repo, only in text files.
IDENTITY_PATTERNS = [b"xiang", b"hofstra", b"xfu20", b"/home/", b"thinkpad"]

# A hit is forgiven only when one of these byte strings appears in the window
# AROUND it.  Allowlisting by context rather than by filename matters: a real
# /home/xiang added to an already-forgiven file would still be caught.
#
# Grow this list rather than weakening IDENTITY_PATTERNS.  Known future
# candidates, should they ever reach the tracked tree: b"zh-xiang" (an ICU
# locale tag inside CentOS .so files) and "hofstra" occurring inside the public
# Enron corpus, which is about a mail author, not this paper's author.
BENIGN_CONTEXTS = [
    # Two clamav READMEs cite an example path that was scrubbed to "anon"
    # long ago: "/home/anon/Desktop/NewResearch/Projects/ZkregPlus/...".
    b"/home/anon/",
]

# Bytes of context shown for each hit, and searched for BENIGN_CONTEXTS.
CONTEXT_BEFORE = 40
CONTEXT_AFTER = 60

# Terms to paste into the 4open.science "Terms to redact" box.
REDACTION_TERMS = [
    "xiang",
    "Xiang",
    "Xiang Fu",
    "xfu2006",
    "xfu2009",
    "hofstra",
    "Hofstra",
    "/home/xiang",
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


def ok(text):
    print("  " + C.G + "OK  " + C.X + text)


def warn(text):
    print("  " + C.Y + "WARN" + C.X + " " + text)


def die(text):
    print("  " + C.R + "FAIL" + C.X + " " + text)
    sys.exit(1)


def info(text):
    print("       " + C.D + text + C.X)


def mb(n):
    return "%.2f MB" % (n / 1048576.0)


def manual(body):
    """Print a block of manual instructions inside a visible frame."""
    print(C.Y + "  +" + "-" * 68 + "+" + C.X)
    for line in body.strip("\n").split("\n"):
        print(C.Y + "  | " + C.X + line)
    print(C.Y + "  +" + "-" * 68 + "+" + C.X)


def confirm(prompt, auto_yes):
    if auto_yes:
        print("  " + C.D + "(--yes) " + prompt + " -> continuing" + C.X)
        return True
    try:
        reply = input("\n  " + C.B + prompt + C.X + " [Enter=yes, q=quit] ").strip().lower()
    except EOFError:
        return True
    if reply in ("q", "quit", "n", "no"):
        print("  stopped.")
        sys.exit(0)
    return True


# ---------------------------------------------------------------------------
# git helpers
# ---------------------------------------------------------------------------

def git(args, cwd, capture=True, check=True, env=None):
    full = ["git"] + args
    r = subprocess.run(full, cwd=cwd, env=env,
                       stdout=subprocess.PIPE if capture else None,
                       stderr=subprocess.PIPE if capture else None)
    if check and r.returncode != 0:
        msg = (r.stderr or b"").decode("utf-8", "replace").strip()
        die("git %s failed: %s" % (" ".join(args), msg))
    return (r.stdout or b"").decode("utf-8", "replace").strip()


def walk_files(root):
    """Yield (abs_path, rel_path) for regular files; symlinks are not followed."""
    for dirpath, dirnames, filenames in os.walk(root):
        dirnames[:] = [d for d in dirnames]
        for name in filenames:
            p = os.path.join(dirpath, name)
            if os.path.islink(p):
                continue
            yield p, os.path.relpath(p, root)


def walk_links(root):
    for dirpath, dirnames, filenames in os.walk(root):
        for name in dirnames + filenames:
            p = os.path.join(dirpath, name)
            if os.path.islink(p):
                yield p, os.path.relpath(p, root)


def extract_all(tf, path):
    """tf.extractall with an explicit filter where the runtime supports one.

    Python 3.12 deprecates the filterless call and 3.14 makes it an error.
    "tar" is used rather than "data" because it preserves the executable bit,
    which several shipped scripts rely on; it still blocks absolute paths and
    ../ traversal.
    """
    try:
        tf.extractall(path, filter="tar")
    except TypeError:                      # Python < 3.12
        tf.extractall(path)


def sha256_file(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


# ---------------------------------------------------------------------------
# steps
# ---------------------------------------------------------------------------

def step_preflight(ctx):
    hdr("STEP 1/9  preflight")

    if sys.version_info < (3, 6):
        die("Python 3.6+ required, found %d.%d" % sys.version_info[:2])
    ok("Python %d.%d" % sys.version_info[:2])

    if not shutil.which("git"):
        die("git not found on PATH")
    ok("git " + git(["--version"], ctx["repo"]).replace("git version ", ""))

    # tarfile must be able to write xz; it is stdlib but can be built without.
    try:
        lzma.LZMACompressor(preset=9 | lzma.PRESET_EXTREME)
        ok("lzma available (preset 9|EXTREME) -- no external xz needed")
    except Exception as exc:
        die("Python lzma unusable: %s" % exc)

    lock = os.path.join(ctx["repo"], ".git", "index.lock")
    if os.path.exists(lock):
        die("%s exists -- another git process is running. Finish or kill it "
            "first; do NOT delete the lock while a git process is alive." % lock)
    ok("no .git/index.lock")

    head = git(["rev-parse", "HEAD"], ctx["repo"])
    subject = git(["log", "-1", "--pretty=%s"], ctx["repo"])
    ctx["head"] = head
    ok("HEAD %s  %s" % (head[:12], subject))

    dirty = git(["status", "--porcelain"], ctx["repo"])
    if dirty:
        n = len(dirty.split("\n"))
        warn("working tree has %d modified/untracked path(s)." % n)
        info("The snapshot is exported from HEAD, so these are NOT included.")
        info("If any of them belong in the artifact, commit them first.")
        for line in dirty.split("\n")[:10]:
            info("  " + line)
    else:
        ok("working tree clean")

    # the source subtree must exist in HEAD, not merely on disk
    git(["rev-parse", "HEAD:%s" % SOURCE_SUBDIR], ctx["repo"])
    ok("HEAD:%s resolves -- artifact will be rooted there" % SOURCE_SUBDIR)

    if os.path.exists(ctx["stage"]):
        warn("staging dir exists and will be REPLACED: %s" % ctx["stage"])
    info("staging dir: %s" % ctx["stage"])


def step_export(ctx):
    hdr("STEP 2/9  export tracked tree from git")

    stage = ctx["stage"]
    if os.path.exists(stage):
        shutil.rmtree(stage)
    os.makedirs(stage)

    # `git archive HEAD:<subdir>` re-roots the archive at that subtree, which is
    # exactly the layout the artifact wants (scripts/INSTALL.py at the top).
    proc = subprocess.Popen(["git", "archive", "HEAD:%s" % SOURCE_SUBDIR],
                            cwd=ctx["repo"], stdout=subprocess.PIPE)
    with tarfile.open(fileobj=proc.stdout, mode="r|") as tf:
        extract_all(tf, stage)
    proc.stdout.close()
    if proc.wait() != 0:
        die("git archive failed")

    files = list(walk_files(stage))
    links = list(walk_links(stage))
    total = sum(os.path.getsize(p) for p, _ in files)
    ctx["exported"] = (len(files), len(links), total)
    ok("exported %d files + %d symlinks, %s" % (len(files), len(links), mb(total)))
    info("source: git archive HEAD:%s (never the working tree)" % SOURCE_SUBDIR)
    info("dropped by re-rooting: LOG, .gitmodules, git_check.sh, root .gitignore")


def step_prune(ctx):
    hdr("STEP 3/9  prune non-shippable paths")

    stage = ctx["stage"]
    removed_bytes = 0
    removed_files = 0

    for rel in PRUNE_PATHS:
        p = os.path.join(stage, rel)
        if not os.path.exists(p) and not os.path.islink(p):
            info("absent (already clean): %s" % rel)
            continue
        if os.path.isdir(p) and not os.path.islink(p):
            n = 0
            b = 0
            for fp, _ in walk_files(p):
                n += 1
                b += os.path.getsize(fp)
            shutil.rmtree(p)
            removed_files += n
            removed_bytes += b
            ok("removed dir  %-58s %d files, %s" % (rel, n, mb(b)))
        else:
            b = os.path.getsize(p) if not os.path.islink(p) else 0
            os.remove(p)
            removed_files += 1
            removed_bytes += b
            ok("removed file %-58s %s" % (rel, mb(b)))

    # sweep for any other editor swap file
    extra = [(p, r) for p, r in walk_files(stage) if r.endswith(PRUNE_SUFFIXES)]
    for p, r in extra:
        removed_bytes += os.path.getsize(p)
        removed_files += 1
        os.remove(p)
        ok("removed swap %s" % r)
    if not extra:
        ok("no further editor swap files found")

    ctx["pruned"] = (removed_files, removed_bytes)
    print()
    info("pruned %d files, %s" % (removed_files, mb(removed_bytes)))


def step_pack(ctx):
    hdr("STEP 4/9  pack oversized files into one archive")

    stage = ctx["stage"]

    missing = [m for m in PACK_MEMBERS
               if not os.path.isfile(os.path.join(stage, m))]
    if missing:
        die("pack member(s) missing from the export: %s" % ", ".join(missing))
    ok("all %d pack members present" % len(PACK_MEMBERS))

    # Anything else over the limit means the member list is stale.
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
    info("compressing %s with preset 9|EXTREME -- this takes several minutes." % mb(raw))
    info("member order is deliberate; see PACK_MEMBERS in this script.")

    # Explicit per-member add in list order.  tarfile's xz mode maps onto the
    # same LZMA2 encoder as `xz -9e`.
    with tarfile.open(pack_abs, mode="w:xz",
                      preset=9 | lzma.PRESET_EXTREME) as tf:
        for m in PACK_MEMBERS:
            tf.add(os.path.join(stage, m), arcname=m, recursive=False)

    size = os.path.getsize(pack_abs)
    digest = sha256_file(pack_abs)
    ratio = raw / float(size) if size else 0
    ok("%s -> %s (%.0fx)" % (mb(raw), mb(size), ratio))
    ok("sha256 %s" % digest)

    if size > SIZE_LIMIT:
        die("pack is %s, over the %s limit. Check that the five identical "
            "main.dat copies are adjacent in PACK_MEMBERS." % (mb(size), mb(SIZE_LIMIT)))
    ok("pack fits under the %s limit with %.1fx margin"
       % (mb(SIZE_LIMIT), SIZE_LIMIT / float(size)))

    # Verify the round trip BEFORE deleting the originals.
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
    ok("removed the %d loose originals from the snapshot" % len(PACK_MEMBERS))

    gi = os.path.join(stage, "data", ".gitignore")
    with open(gi, "a") as f:
        f.write("\n" + GITIGNORE_BLOCK_HEADER.strip("\n") + "\n")
        for m in PACK_MEMBERS:
            f.write(m[len("data/"):] + "\n")
    ok("appended %d restore targets to data/.gitignore" % len(PACK_MEMBERS))

    ctx["pack"] = (raw, size, digest)


def step_verify(ctx):
    hdr("STEP 5/9  verify the snapshot")

    stage = ctx["stage"]
    failures = []

    # --- size ---
    over = [(r, os.path.getsize(p)) for p, r in walk_files(stage)
            if os.path.getsize(p) > SIZE_LIMIT]
    if over:
        for r, s in over:
            print("       %s  %s" % (mb(s).rjust(9), r))
        failures.append("%d file(s) exceed %s" % (len(over), mb(SIZE_LIMIT)))
    else:
        biggest = max(((os.path.getsize(p), r) for p, r in walk_files(stage)),
                      default=(0, "-"))
        ok("no file over %s (largest: %s %s)"
           % (mb(SIZE_LIMIT), mb(biggest[0]), biggest[1]))

    # --- identity sweep, text AND binary ---
    # Binaries are included on purpose: 4open's redaction terms apply to text
    # only, so anything embedded in a binary reaches reviewers verbatim.
    hits = []
    forgiven = 0
    n_scanned = 0
    for p, r in walk_files(stage):
        try:
            with open(p, "rb") as f:
                blob = f.read()
        except OSError:
            continue
        n_scanned += 1
        low = blob.lower()
        for pat in IDENTITY_PATTERNS:
            start = 0
            while True:
                i = low.find(pat, start)
                if i < 0:
                    break
                start = i + 1
                window = low[max(0, i - CONTEXT_BEFORE): i + len(pat) + CONTEXT_AFTER]
                if any(b in window for b in BENIGN_CONTEXTS):
                    forgiven += 1
                    continue
                snippet = window.decode("utf-8", "replace").replace("\n", " ")
                hits.append((r, pat.decode(), snippet))
    if hits:
        seen = set()
        for r, pat, snip in hits:
            key = (r, pat)
            if key in seen:
                continue
            seen.add(key)
            if len(seen) > 25:
                break
            print("       %-10s %s" % (pat, r))
            print("       %-10s %s...%s" % ("", " " * 0, snip[:110]))
        if len(hits) > 25:
            info("... and %d more hit(s)" % (len(hits) - 25))
        info("if a hit is genuinely harmless, add its surrounding text to "
             "BENIGN_CONTEXTS -- do not remove the pattern")
        failures.append("%d identity hit(s)" % len(hits))
    else:
        ok("identity sweep clean across %d files (patterns: %s)"
           % (n_scanned, ", ".join(p.decode() for p in IDENTITY_PATTERNS)))
        if forgiven:
            info("%d occurrence(s) matched BENIGN_CONTEXTS and were forgiven"
                 % forgiven)

    # --- stray VCS / editor metadata ---
    # .gitignore / .gitkeep / .gitattributes are ordinary repo files here (19,
    # 8 and 1 of them respectively, all carrying no identity), so only the
    # genuinely dangerous shapes are flagged: .gitmodules records submodule
    # URLs -- which is how a bitbucket username reached the tracked tree -- and
    # a nested .git directory would carry full author history.
    strays = [r for _, r in walk_files(stage)
              if os.path.basename(r) == ".gitmodules"
              or ".git/" in r.replace(os.sep, "/") + "/"
              or r.endswith(PRUNE_SUFFIXES)]
    if strays:
        for r in strays:
            print("       %s" % r)
        failures.append("%d stray VCS/editor file(s)" % len(strays))
    else:
        n_keep = sum(1 for _, r in walk_files(stage)
                     if os.path.basename(r).startswith(".git"))
        ok("no .gitmodules, nested .git, or editor swap files "
           "(%d expected .gitignore/.gitkeep entries kept)" % n_keep)

    # --- symlinks must be relative and stay inside the tree ---
    bad_links = []
    for p, r in walk_links(stage):
        target = os.readlink(p)
        if os.path.isabs(target):
            bad_links.append((r, target, "absolute"))
            continue
        resolved = os.path.normpath(os.path.join(os.path.dirname(p), target))
        if not os.path.abspath(resolved).startswith(os.path.abspath(stage)):
            bad_links.append((r, target, "escapes tree"))
    n_links = sum(1 for _ in walk_links(stage))
    if bad_links:
        for r, t, why in bad_links:
            print("       %-8s %s -> %s" % (why, r, t))
        failures.append("%d unsafe symlink(s)" % len(bad_links))
    else:
        ok("all %d symlinks are relative and stay inside the tree" % n_links)

    dangling = [r for p, r in walk_links(stage) if not os.path.exists(p)]
    if dangling:
        for r in dangling[:10]:
            warn("dangling symlink: %s" % r)
        info("dangling links are not fatal, but check they are intentional")
    else:
        ok("no dangling symlinks")

    # --- entry point sanity ---
    for must in ("scripts/INSTALL.py", "README.md", "LICENSE", "Cargo.toml"):
        if os.path.exists(os.path.join(stage, must)):
            ok("present: %s" % must)
        else:
            failures.append("missing entry point: %s" % must)

    files = list(walk_files(stage))
    total = sum(os.path.getsize(p) for p, _ in files)
    print()
    info("snapshot: %d files + %d symlinks, %s"
         % (len(files), n_links, mb(total)))

    if failures:
        print()
        for f in failures:
            print("  " + C.R + "FAIL" + C.X + " " + f)
        die("verification failed -- fix the above before publishing")
    ok("ALL CHECKS PASSED")
    ctx["verified"] = (len(files), n_links, total)


def step_initrepo(ctx):
    hdr("STEP 6/9  initialise the snapshot repository")

    stage = ctx["stage"]
    if os.path.exists(os.path.join(stage, ".git")):
        shutil.rmtree(os.path.join(stage, ".git"))

    git(["init", "-q"], stage)
    git(["symbolic-ref", "HEAD", "refs/heads/%s" % BRANCH], stage)
    ok("git init, branch %s" % BRANCH)

    git(["config", "user.name", NEUTRAL_NAME], stage)
    git(["config", "user.email", NEUTRAL_EMAIL], stage)
    git(["config", "commit.gpgsign", "false"], stage)
    ok("identity: %s <%s>" % (NEUTRAL_NAME, NEUTRAL_EMAIL))

    git(["add", "-A"], stage)

    env = dict(os.environ)
    env.update({
        "GIT_AUTHOR_NAME": NEUTRAL_NAME,
        "GIT_AUTHOR_EMAIL": NEUTRAL_EMAIL,
        "GIT_AUTHOR_DATE": NEUTRAL_DATE,
        "GIT_COMMITTER_NAME": NEUTRAL_NAME,
        "GIT_COMMITTER_EMAIL": NEUTRAL_EMAIL,
        "GIT_COMMITTER_DATE": NEUTRAL_DATE,
    })
    git(["commit", "-q", "-m",
         "BORA artifact snapshot for anonymous review"], stage, env=env)

    sha = git(["rev-parse", "HEAD"], stage)
    count = git(["rev-list", "--count", "HEAD"], stage)
    who = git(["log", "-1", "--pretty=%an <%ae> / %cn <%ce> / %ad"], stage)
    ctx["snap_sha"] = sha

    ok("commit %s (history depth: %s)" % (sha[:12], count))
    ok("recorded identity: %s" % who)
    if count != "1":
        die("expected exactly 1 commit, found %s" % count)
    if not git(["remote"], stage) == "":
        die("snapshot repo has a remote configured; it must have none yet")
    ok("no remote configured yet (added manually in the next step)")

    print()
    info("snapshot ready at: %s" % stage)


def step_github(ctx):
    hdr("STEP 7/9  MANUAL -- create the private GitHub repo and push")

    stage = ctx["stage"]
    sha = ctx.get("snap_sha", "<run step 6 first>")

    manual("""
Create a NEW private repository on GitHub.  Do not reuse ZkRegPlus: the
snapshot must carry no history and no relation to your other repos.

  1. https://github.com/new
       Name        : anything (4open anonymizes owner/org/repo automatically)
       Visibility  : PRIVATE
       Do NOT add a README, .gitignore, or licence -- the push must be a
       fast-forward onto an empty repo.

  2. Push this snapshot (it has exactly one commit, %s):

       cd %s
       git remote add origin git@github.com:<you>/<repo>.git
       git push -u origin %s

  3. Confirm on github.com that the branch shows ONE commit, authored by
     "%s", and that no file exceeds 8 MB.
""" % (sha[:12], stage, BRANCH, NEUTRAL_NAME))

    info("Nothing is pushed automatically -- this step is yours.")


def step_4open(ctx):
    hdr("STEP 8/9  MANUAL -- mint the anonymous.4open.science URL")

    terms = "\n       ".join(REDACTION_TERMS)
    manual("""
Go to https://anonymous.4open.science and anonymize the repository you
just pushed.  The paper ALREADY cites the resulting URL at
src/apdx_open_sci.tex:16, so the ID below must match EXACTLY:

       Anonymized repository ID : bora-sec27
       Branch                   : %s
       Commit                   : (leave BLANK until 2026-08-28)
       Auto update              : ON
       Conference               : SEC27
       Expiration date          : after 2026-12-15
       Redirect to GitHub       : NEVER select this

  Terms to redact (one per line):

       %s

WHY these settings:
  * Commit blank + Auto update ON lets you keep fixing content through the
    08-28 freeze behind a URL that is already final on 08-25.
  * On 08-28, come back and PIN the commit SHA -- that is a harder freeze
    than merely switching auto-update off  (task T913).
  * Redaction covers TEXT only.  Binaries are served verbatim, which is why
    step 3 prunes the vim swap files instead of relying on this box.
""" % (BRANCH, terms))


def step_browsercheck(ctx):
    hdr("STEP 9/9  MANUAL -- verify in a real browser")

    manual("""
curl cannot answer this: 4open returns HTTP 403 to non-browser agents, so a
403 means both "not minted" and "minted but bot-blocked".  Open it yourself.

  [ ] https://anonymous.4open.science/r/bora-sec27 loads
  [ ] the URL matches src/apdx_open_sci.tex:16 character for character
  [ ] README.md renders and says "Authors: Anonymous"
  [ ] scripts/INSTALL.py is browsable
  [ ] data/bigfiles.tar.xz is listed and downloadable (it is under 8 MB)
  [ ] no file shows a "too large" placeholder
  [ ] symlinked paths resolve or degrade gracefully (56 of them; behaviour
      is undocumented, so eyeball a few under vendor/dependency/)
  [ ] search the mirror for "xiang" and "hofstra" -- expect zero results

If any of these fail, fix the source repo, push, and wait for auto update
(hourly maximum) rather than re-minting: re-minting risks losing the ID.
""")


STEPS = [
    ("preflight", "check environment, git state, and staging dir", step_preflight),
    ("export", "git archive HEAD:%s into staging" % SOURCE_SUBDIR, step_export),
    ("prune", "delete attic/ and editor swap files", step_prune),
    ("pack", "build data/bigfiles.tar.xz and drop the loose originals", step_pack),
    ("verify", "size, identity, symlink and entry-point checks", step_verify),
    ("initrepo", "git init + one squashed commit, neutral identity", step_initrepo),
    ("github", "MANUAL: create the private repo and push", step_github),
    ("4open", "MANUAL: mint the anonymous.4open.science URL", step_4open),
    ("browsercheck", "MANUAL: verify the live mirror", step_browsercheck),
]

MANUAL_STEPS = {"github", "4open", "browsercheck"}


def main():
    ap = argparse.ArgumentParser(
        description="Prepare the anonymous artifact snapshot for 4open.science.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=textwrap.dedent("""\
            The automated steps never touch your real repository: they read via
            `git archive` and write only inside the staging directory.
        """))
    ap.add_argument("--stage", default="/tmp/bora_open4s",
                    help="staging directory (default: /tmp/bora_open4s)")
    ap.add_argument("--from", dest="start", metavar="STEP",
                    help="start at this step name")
    ap.add_argument("--only", metavar="STEP", help="run just this step")
    ap.add_argument("--list", action="store_true", help="list steps and exit")
    ap.add_argument("--yes", action="store_true",
                    help="do not pause between steps")
    ap.add_argument("--no-color", action="store_true")
    args = ap.parse_args()

    if args.no_color or not sys.stdout.isatty():
        C.off()

    names = [s[0] for s in STEPS]
    if args.list:
        print("steps:")
        for i, (name, desc, _) in enumerate(STEPS, 1):
            tag = " [MANUAL]" if name in MANUAL_STEPS else ""
            print("  %d. %-13s %s%s" % (i, name, desc, tag))
        return

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

    ctx = {"repo": repo, "stage": os.path.abspath(args.stage)}

    print(C.B + "\nBORA -> anonymous.4open.science snapshot builder" + C.X)
    print("  git repo   : %s" % repo)
    print("  artifact   : %s (re-rooted)" % SOURCE_SUBDIR)
    print("  staging    : %s" % ctx["stage"])
    print("  steps      : %s" % ", ".join(s[0] for s in selected))

    if args.start and args.start != "preflight":
        info("resuming: earlier steps are assumed already done in staging")

    for name, _, fn in selected:
        fn(ctx)
        if name != selected[-1][0]:
            confirm("continue to next step?", args.yes)

    hdr("done")
    if "snap_sha" in ctx:
        print("  snapshot commit : %s" % ctx["snap_sha"])
    print("  staging dir     : %s" % ctx["stage"])
    print("\n  Remaining manual work is printed above. After 2026-08-28, pin the")
    print("  commit SHA on the 4open form to freeze the mirror (task T913).\n")


if __name__ == "__main__":
    main()
