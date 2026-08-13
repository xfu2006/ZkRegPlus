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

Requires only the Python standard library (>= 3.6) and `git` on PATH.
"""

import argparse
import hashlib
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

# Identity used for the single squashed commit -- visible in `git log` on the
# mirror, so it must not resolve to a real person.
NEUTRAL_NAME = "Anonymous Author"
NEUTRAL_EMAIL = "anonymous@example.com"

# Fixed commit timestamp.  A real one leaks a timezone (hence a rough
# longitude); a fixed UTC one leaks nothing.
NEUTRAL_DATE = "2026-08-22T12:00:00+0000"

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
    "vendor/sonobe_mod/.rust-toolchain.swp",
    "vendor/sonobe_mod/folding-schemes/src/folding/foldpot/.circuits_super.rs.swo",
]

# Pruned wherever they appear.  Deliberately only vim swap files: tracked
# *.orig / *.bak files in this repo are real fixtures and scan clean.
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
    "data/debug/full_dlp_sample/config/file_needs_rank.tsv",
    "data/debug/full_dlp_sample/config/pass_needs_rank.tsv",
    "data/debug/full_dlp_sample/config/accept_needs_rank.tsv",
    "data/debug/small_email/config/binexec5.dat",
    # --- a captured log ---
    "data/debug/small_data_set2/config_dfa/discharge_main_binexec.dat",
]

PACK_PATH = "data/bigfiles.tar.xz"
PACK_SHA_PATH = "data/bigfiles.sha256"

GITIGNORE_BLOCK_HEADER = """
# ---------------------------------------------------------------------
# Restored by scripts/INSTALL.py from data/bigfiles.tar.xz.
#
# anonymous.4open.science refuses to serve any file over 8 MB, so the 13
# fixtures below ship inside one 3.5 MB xz archive instead of as loose
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


def sha256_file(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for c in iter(lambda: f.read(1 << 20), b""):
            h.update(c)
    return h.hexdigest()


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

        def scalar(field):
            mm = re.search(field + r'\s*:\s*"([^"]*)"', body)
            return mm.group(1) if mm else None

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
    hits, forgiven = [], 0
    for p, r in files:
        try:
            with open(p, "rb") as f:
                blob = f.read()
        except OSError:
            continue
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
                hits.append((r, pat.decode(),
                             win.decode("utf-8", "replace").replace("\n", " ")))
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
        ok("anonymity: clean across %d files (%s)"
           % (len(files), ", ".join(p.decode() for p in IDENTITY_PATTERNS)))
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
        ok("symlinks: all %d relative and inside the tree" % len(links))
    else:
        warn("symlinks: none present "
             "(the snapshot has 55 -- if this is the mirror, 4open dropped them)")

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
    hdr("STEP 1/12  preflight")
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
    hdr("STEP 2/12  export tracked tree from git")
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
    hdr("STEP 3/12  prune non-shippable paths")
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


def step_pack(ctx):
    hdr("STEP 4/12  pack oversized files into one archive")
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

    with tarfile.open(pack_abs, mode="w:xz",
                      preset=9 | lzma.PRESET_EXTREME) as tf:
        for m in PACK_MEMBERS:
            tf.add(os.path.join(stage, m), arcname=m, recursive=False)

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
    hdr("STEP 5/12  inspect the staging tree")
    if inspect_tree(ctx["stage"], "staging tree",
                    expect_pack_sha=ctx.get("pack_sha")):
        die("verification failed -- fix the above before publishing")


def step_initrepo(ctx):
    hdr("STEP 6/12  initialise the snapshot repository")
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
    hdr("STEP 7/12  record the local manifest")
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
    with open(ctx["manifest_path"], "w") as f:
        json.dump(data, f, indent=1, sort_keys=True)
    ctx["pack_sha"] = data["pack_sha256"]
    ok("wrote %s (%d entries)" % (ctx["manifest_path"], len(files)))
    print()
    warn("KEEP THIS FILE. It is deliberately outside the artifact, so the "
         "completeness diff in steps 9 and 11 depends on it surviving.")
    if ctx["manifest_path"].startswith("/tmp/"):
        warn("it is under /tmp and will not survive a reboot -- consider "
             "re-running with --manifest ~/bora_open4s.manifest.json")


def step_github(ctx):
    hdr("STEP 8/12  MANUAL -- create the private GitHub repo and push")
    sha = ctx.get("snap_sha", "<run step 6 first>")
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
        [ ] data/bigfiles.tar.xz is present, about 3.5 MB
        [ ] no file is over 8 MB

        Leave this repository in place. 4open does not copy your code -- it
        proxies it live, so deleting or locking the repo breaks the mirror
        mid-review.
        """ % NEUTRAL_NAME, y)

    url = ask("paste the repo URL for the next check (or Enter to skip):", y)
    if url:
        ctx["github_url"] = url


def step_checkpush(ctx):
    hdr("STEP 9/12  inspect what GitHub actually received")
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
    hdr("STEP 10/12  MANUAL -- mint the anonymous.4open.science URL")
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


def step_checkmirror(ctx):
    hdr("STEP 11/12  inspect what the 4open mirror actually serves")
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
    zip_path = os.path.expanduser(zip_path)
    if not os.path.isfile(zip_path):
        die("no such file: %s" % zip_path)

    tmp = tempfile.mkdtemp(prefix="bora_mirrorcheck_")
    try:
        with zipfile.ZipFile(zip_path) as zf:
            zf.extractall(tmp)
        ok("extracted %s" % zip_path)
        # 4open may wrap everything in one top directory; descend if so.
        entries = [e for e in os.listdir(tmp) if not e.startswith("__MACOSX")]
        root = tmp
        if len(entries) == 1 and os.path.isdir(os.path.join(tmp, entries[0])):
            root = os.path.join(tmp, entries[0])
            info("descended into single top-level dir: %s" % entries[0])

        failures = inspect_tree(root, "4open mirror (downloaded ZIP)",
                                manifest=ctx.get("manifest"),
                                expect_pack_sha=ctx.get("pack_sha"))

        print()
        info("REMINDER: the mirror is a live proxy, not a copy. Any fix means")
        info("push to GitHub, wait for auto-update (hourly max), re-download,")
        info("and re-run: --only checkmirror --zip <new file>")
        info("Do NOT re-mint to force a refresh -- you risk losing the ID.")
        if failures:
            die("the mirror is not clean")
    finally:
        shutil.rmtree(tmp, ignore_errors=True)


def step_freeze(ctx):
    hdr("STEP 12/12  MANUAL -- the two lock-up dates")
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


STEPS = [
    ("preflight", "environment, git state, staging dir", step_preflight),
    ("export", "git archive HEAD:%s into staging" % SOURCE_SUBDIR, step_export),
    ("prune", "delete attic/ and editor swap files", step_prune),
    ("pack", "build data/bigfiles.tar.xz, drop loose originals", step_pack),
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
        except Exception as exc:
            warn("could not read manifest %s: %s" % (ctx["manifest_path"], exc))

    print(C.B + "\nBORA -> anonymous.4open.science" + C.X)
    print("  git repo : %s" % repo)
    print("  artifact : %s (re-rooted)" % SOURCE_SUBDIR)
    print("  staging  : %s" % stage)
    print("  manifest : %s%s" % (ctx["manifest_path"],
                                 "  (loaded)" if "manifest" in ctx else ""))
    print("  steps    : %s" % ", ".join(s[0] for s in selected))
    if args.start and args.start != "preflight":
        info("resuming: earlier steps assumed already done in staging")

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
