#!/usr/bin/env python3
"""Filesystem-wide search for the full_clam 8-job / 8-proof run log.

Walks a filesystem root (default "/") looking for prover dumps that match the
"successful full_clam" signature:
  - it is a full_clam run (mentions binexec / merged128k / full_clam),
  - all 8 jobs appear ([job 0]..[job 7]),
  - all 8 jobs reach "Verify Individual Proof" (8 completed proofs),
  - total wall ~60 h (from the mimalloc "elapsed : N s" line, else the span
    between the first and last timestamp in the file).

Scans plain text dumps (.txt/.log/.dat/.out and extensionless text) AND the
contents of archives (.tgz/.tar.gz/.tar/.gz/.zip; .7z/.zst if the optional
py7zr/zstandard modules are installed). Streams line-by-line so multi-hundred-MB
dumps are fine. Permission errors and unreadable files are skipped quietly.

Usage:
  python3 find_clam_8prf.py [root] [--min-proofs N] [--max-size-mb N]
                            [--out report.txt] [--all]

Examples:
  sudo python3 find_clam_8prf.py /                 # whole filesystem
  python3 find_clam_8prf.py /home --min-proofs 8   # just /home
Run with sudo to see root-owned files; without sudo it still scans everything
readable by you.
"""
import os
import re
import sys
import gzip
import tarfile
import zipfile
import argparse
import datetime as dt

# ---- markers (bytes, so we never choke on odd encodings) -------------------
JOB = re.compile(rb"\[job (\d+)\]")
VERIFY_IND = b"Verify Individual Proof"
VERIFY_BATCH = b"Verify Batch Proof"
DECIDER = b"MainDeciderCirtuit TOTAL"          # note: prover's spelling
CLAM = re.compile(rb"binexec|merged128k|full_clam")
ELAPSED = re.compile(rb"elapsed\s*:\s*([0-9.]+)\s*s")
TS = re.compile(rb"(20\d\d-\d\d-\d\d)[ T](\d\d:\d\d:\d\d)")

TEXT_EXT = (".txt", ".log", ".dat", ".out")
ARCH_TAR = (".tgz", ".tar.gz", ".tar", ".tbz2", ".tar.bz2", ".tar.xz")
# dirs that are pseudo-filesystems or pure noise -- never worth walking
SKIP_DIRS = {"/proc", "/sys", "/dev", "/run", "/snap",
             "/var/lib/docker", "/var/run"}
# name fragments of huge prover *data* caches (numbers/hex, never run logs)
CACHE_HINT = re.compile(r"(lkup|bundle_subsig|vec_sigs|dfa_crit|"
                        r"crit_igc|nibble|packed)\.txt$")


def parse_ts(b):
    try:
        d, t = b.group(1).decode(), b.group(2).decode()
        return dt.datetime.strptime(d + " " + t, "%Y-%m-%d %H:%M:%S")
    except Exception:
        return None


def scan_lines(it):
    """Fingerprint a byte-line iterator. Returns a dict or None if it shows
    no relevance at all (not clam, no jobs)."""
    jobs, verified, deciders = set(), set(), set()
    is_clam = False
    elapsed = None
    first_ts = last_ts = None
    for line in it:
        if not is_clam and CLAM.search(line):
            is_clam = True
        m = JOB.search(line)
        jid = int(m.group(1)) if m else None
        if jid is not None:
            jobs.add(jid)
            if VERIFY_IND in line:
                verified.add(jid)
            if DECIDER in line:
                deciders.add(jid)
        e = ELAPSED.search(line)
        if e:
            try:
                elapsed = float(e.group(1))
            except ValueError:
                pass
        t = TS.search(line)
        if t:
            ts = parse_ts(t)
            if ts:
                if first_ts is None:
                    first_ts = ts
                last_ts = ts
    if not is_clam and not jobs:
        return None
    span = None
    if first_ts and last_ts and last_ts >= first_ts:
        span = (last_ts - first_ts).total_seconds()
    wall = elapsed if elapsed is not None else span
    return dict(is_clam=is_clam, njobs=len(jobs), nverified=len(verified),
                ndecider=len(deciders), elapsed=elapsed, span=span,
                wall=wall, jobs=sorted(jobs), verified=sorted(verified))


def looks_text(path):
    """Cheap binary sniff: a NUL byte in the first 8 KB => treat as binary."""
    try:
        with open(path, "rb") as fh:
            return b"\x00" not in fh.read(8192)
    except OSError:
        return False


def iter_plain(path):
    with open(path, "rb") as fh:
        for line in fh:
            yield line


def iter_gz(path):
    with gzip.open(path, "rb") as fh:
        for line in fh:
            yield line


def fingerprint_path(path, size_cap):
    """Yield (member_label, result) for a path: itself if text, or each text
    member if it is an archive. Heavy-but-bounded; never raises."""
    low = path.lower()
    try:
        # --- tar archives (.tgz/.tar.gz/.tar/...) -----------------------
        if low.endswith(ARCH_TAR):
            with tarfile.open(path, "r:*") as tf:
                for mem in tf:
                    if not mem.isfile() or mem.size > size_cap:
                        continue
                    if not (mem.name.lower().endswith(TEXT_EXT)
                            or "." not in os.path.basename(mem.name)):
                        continue
                    f = tf.extractfile(mem)
                    if f is None:
                        continue
                    r = scan_lines(f)
                    if r:
                        yield path + "::" + mem.name, r
            return
        # --- single-file gzip (e.g. foo.log.gz) -------------------------
        if low.endswith(".gz"):
            r = scan_lines(iter_gz(path))
            if r:
                yield path, r
            return
        # --- zip --------------------------------------------------------
        if low.endswith(".zip"):
            with zipfile.ZipFile(path) as zf:
                for nm in zf.namelist():
                    info = zf.getinfo(nm)
                    if info.file_size > size_cap:
                        continue
                    with zf.open(nm) as f:
                        r = scan_lines(f)
                    if r:
                        yield path + "::" + nm, r
            return
        # --- optional .7z / .zst (only if libs present) -----------------
        if low.endswith(".7z"):
            try:
                import py7zr
            except ImportError:
                return
            with py7zr.SevenZipFile(path, "r") as z:
                for nm, bio in z.readall().items():
                    r = scan_lines(bio)
                    if r:
                        yield path + "::" + nm, r
            return
        if low.endswith(".zst"):
            try:
                import zstandard
            except ImportError:
                return
            with open(path, "rb") as fh:
                rd = zstandard.ZstdDecompressor().stream_reader(fh)
                r = scan_lines(iter(lambda: rd.readline(), b""))
            if r:
                yield path, r
            return
        # --- plain text -------------------------------------------------
        if low.endswith(TEXT_EXT) or looks_text(path):
            r = scan_lines(iter_plain(path))
            if r:
                yield path, r
    except (OSError, tarfile.TarError, zipfile.BadZipFile, EOFError,
            gzip.BadGzipFile, Exception):
        return


def is_archive(low):
    return (low.endswith(ARCH_TAR) or low.endswith(".gz")
            or low.endswith(".zip") or low.endswith(".7z")
            or low.endswith(".zst"))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("root", nargs="?", default="/")
    ap.add_argument("--min-proofs", type=int, default=8,
                    help="report dumps with >= this many verified jobs")
    ap.add_argument("--max-size-mb", type=int, default=2048,
                    help="skip files larger than this (default 2 GB)")
    ap.add_argument("--out", default="/tmp/find_clam_8prf_report.txt")
    ap.add_argument("--all", action="store_true",
                    help="also list every clam/job dump found, not just hits")
    args = ap.parse_args()
    size_cap = args.max_size_mb * 1024 * 1024

    hits, near, seen_clam = [], [], []
    scanned = 0
    t0 = dt.datetime.now()

    def out(*a):
        print(*a)
        rep.write(" ".join(str(x) for x in a) + "\n")

    rep = open(args.out, "w")
    out("# find_clam_8prf scan root=%s started=%s" % (args.root, t0))
    out("# target: full_clam, 8 jobs, >=%d verified proofs, ~60h wall\n"
        % args.min_proofs)

    for dpath, dirs, files in os.walk(args.root, onerror=lambda e: None):
        # prune pseudo-fs and noise
        if any(dpath == s or dpath.startswith(s + "/") for s in SKIP_DIRS):
            dirs[:] = []
            continue
        for name in files:
            p = os.path.join(dpath, name)
            low = name.lower()
            if CACHE_HINT.search(low):
                continue
            if not (low.endswith(TEXT_EXT) or is_archive(low)
                    or "." not in name):
                continue
            try:
                if os.path.islink(p) or os.path.getsize(p) > size_cap:
                    if not is_archive(low):
                        continue
            except OSError:
                continue
            for label, r in fingerprint_path(p, size_cap):
                scanned += 1
                if r["is_clam"]:
                    seen_clam.append((label, r))
                wall_h = (r["wall"] / 3600.0) if r["wall"] else None
                tag = "wall=%.1fh" % wall_h if wall_h else "wall=?"
                if r["is_clam"] and r["nverified"] >= args.min_proofs:
                    hits.append((label, r))
                    out("\n*** HIT *** %s" % label)
                    out("    jobs=%d verified=%d decider=%d %s"
                        % (r["njobs"], r["nverified"], r["ndecider"], tag))
                elif r["is_clam"] and r["nverified"] >= 4:
                    near.append((label, r))
            if scanned and scanned % 200 == 0:
                sys.stderr.write("  ...scanned %d candidate streams\r"
                                 % scanned)

    out("\n================ SUMMARY ================")
    out("streams scanned: %d   elapsed: %s"
        % (scanned, dt.datetime.now() - t0))
    out("HITS (clam, >=%d proofs): %d" % (args.min_proofs, len(hits)))
    for label, r in sorted(hits, key=lambda x: -(x[1]["wall"] or 0)):
        wh = (r["wall"] / 3600.0) if r["wall"] else 0
        out("  [%.1fh] verified=%d  %s" % (wh, r["nverified"], label))
    out("\nNEAR-MISSES (clam, 4-7 proofs): %d" % len(near))
    for label, r in sorted(near, key=lambda x: -x[1]["nverified"]):
        wh = (r["wall"] / 3600.0) if r["wall"] else 0
        out("  [%.1fh] verified=%d/%d  %s"
            % (wh, r["nverified"], r["njobs"], label))
    if args.all:
        out("\nALL clam/job dumps seen: %d" % len(seen_clam))
        for label, r in seen_clam:
            wh = (r["wall"] / 3600.0) if r["wall"] else 0
            out("  [%.1fh] jobs=%d verified=%d  %s"
                % (wh, r["njobs"], r["nverified"], label))
    out("\nreport written to %s" % args.out)
    rep.close()


if __name__ == "__main__":
    main()
