# ---------------------------------------------------------------------
# gen.py -- build the dlp_hard_set config from the paper DLP bundle.
#
# Author: Claude Code
# Note:   All code generated under the instructions of the paper
#         author, inspected block-by-block.
#
# Reads data/paper_data/dlp/ and data/samples/email/ STRICTLY READ-ONLY.
#
# WHY THESE SITs. Measuring the paper's own worst-NEEDS files (named in
# dlp/report/needs_dist_report.txt and dlp/cfg/config/needs_dist.txt)
# against every keyword in the DLP DB shows what actually makes them
# expensive: the winning keywords are SHORT COMMON SUBSTRINGS --
# 'tin' (413 hits, inside "waiting"/"printing"), 'sin' (385, inside
# "using"/"business"), 'PAN', 'nie', 'dea'. Each hit opens a .{0,300}
# proximity window the SDE must carry, so keyword density IS discharge
# density. We keep the five SITs owning those keywords: 110 real sig
# lines out of the DB's 9861, small enough to build fresh.
#
# Scan targets, same sig set, so easy vs hard differs ONLY in density:
#   scan_hard.dat -- the paper's worst-NEEDS Enron files
#   scan_easy.dat -- MEDIAN-density files from the same corpus, padded
#                    to the hard blob's byte count (a zero-hit pick
#                    would measure an empty Q_m, not an easy one)
#
# usage (from repo root):  python3 data/debug/dlp_hard_set/config/gen.py
# ---------------------------------------------------------------------

import os
import random
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", "..", "..", ".."))
DLP = os.path.join(ROOT, "data", "paper_data", "dlp")
DB = os.path.join(DLP, "cfg", "regex_pat",
                  "main_data_dlp_internationl.dat")
MAILDIR = os.path.join(ROOT, "data", "samples", "email", "src", "maildir")

# the five SITs whose keywords dominate the paper's worst files
SITS = [
    "us-individual-taxpayer-identification-number",
    "canada-social-insurance-number",
    "india-permanent-account-number",
    "spain-dni",
    "drug-enforcement-agency-number",
]
# hex-alphabet seed sig: hex_acdfa requires a complete 16-nibble
# alphabet, and proximity sigs alone do not supply one.
SEED = ("Win.Alphabet.SAMPLE-1;Engine:51-255,Target:1;0|1;"
        "09afcdeb1928374650123457890abcde;0123498765423afedc")




def decode(s):
    s = re.sub(r"\\x([0-9a-fA-F]{2})",
               lambda m: chr(int(m.group(1), 16)), s)
    return s.replace("\\", "")


def worst_files():
    """Enron files the paper reports as the NEEDS tail."""
    pats = set()
    for rep in (os.path.join(DLP, "report", "needs_dist_report.txt"),
                os.path.join(DLP, "cfg", "config", "needs_dist.txt")):
        if not os.path.exists(rep):
            continue
        txt = open(rep, errors="replace").read()
        for m in re.finditer(
                r"maildir/([A-Za-z-]+/[A-Za-z_]+/[0-9]+\.)", txt):
            pats.add(m.group(1))
    out = []
    for rel in sorted(pats):
        p = os.path.join(MAILDIR, rel)
        if os.path.exists(p):
            out.append(p)
    return out


META = set("[]{}()|?*+^$")


def keywords(sigs):
    """Literal keywords only. A .bwd sig leads with the NUMBER arm, so
    drop anything carrying regex metacharacters -- it is not a keyword
    and would score as a constant zero."""
    out = set()
    for ln in sigs:
        m = re.search(r";/(.*?)\.\{0,\d+\}", ln)
        if m:
            kw = decode(m.group(1)).strip()
            if len(kw) >= 3 and not (META & set(kw)):
                out.add(kw)
    return sorted(out)


def hits(path, kws):
    try:
        t = open(path, "rb").read().decode("latin-1")
    except OSError:
        return -1
    return sum(t.count(k) for k in kws)


def easy_files(kws, exclude, target_bytes):
    """Same corpus, MEDIAN keyword density -- a typical email, not a
    zero-hit outlier -- accumulated to the hard blob's size so the two
    cells differ in density and not in chunk count."""
    cands = []
    for person in sorted(os.listdir(MAILDIR))[:8]:
        base = os.path.join(MAILDIR, person)
        for root, _, files in os.walk(base):
            for f in sorted(files)[:20]:
                p = os.path.join(root, f)
                if p not in exclude and 1000 < os.path.getsize(p) < 40000:
                    cands.append(p)
    random.seed(0)
    random.shuffle(cands)
    cands = cands[:400]
    scored = sorted((hits(p, kws) * 1000 // max(1, os.path.getsize(p)), p)
                    for p in cands)
    mid = len(scored) // 2
    out, tot = [], 0
    for _, p in scored[mid:]:
        out.append(p)
        tot += os.path.getsize(p)
        if tot >= target_bytes:
            break
    return out


def rel(p):
    return os.path.relpath(p, ROOT)


def main():
    if not os.path.exists(DB):
        sys.exit("paper DLP bundle not found: %s" % DB)

    keep = re.compile("|".join("sit-defn-%s\\." % s for s in SITS))
    sigs = [ln.rstrip("\n") for ln in open(DB, errors="replace")
            if keep.search(ln)]
    sigs = [SEED] + sigs
    kws = keywords(sigs)

    hard = worst_files()
    hb = sum(os.path.getsize(p) for p in hard)
    easy = easy_files(kws, set(hard), hb)

    out = {
        "main.dat": sigs,
        "main_dfa.dat": [SEED.split(";", 1)[0]],
        "needs_ised.dat": [],
        "needs_ised_igc.dat": [],
        "scan_hard.dat": [rel(p) for p in hard],
        "scan_easy.dat": [rel(p) for p in easy],
    }
    for fname, lines in out.items():
        with open(os.path.join(HERE, fname), "w") as f:
            for ln in lines:
                f.write(ln + "\n")
        print("wrote %-20s %4d lines" % (fname, len(lines)))

    hb = sum(os.path.getsize(p) for p in hard)
    eb = sum(os.path.getsize(p) for p in easy)
    print("keywords: %s" % ", ".join(repr(k) for k in kws))
    print("hard: %d files %d B, %d keyword hits"
          % (len(hard), hb, sum(hits(p, kws) for p in hard)))
    print("easy: %d files %d B, %d keyword hits"
          % (len(easy), eb, sum(hits(p, kws) for p in easy)))


if __name__ == "__main__":
    main()
