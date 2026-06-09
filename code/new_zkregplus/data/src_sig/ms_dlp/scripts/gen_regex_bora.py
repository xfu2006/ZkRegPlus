# -------------------------------------------
# Creator: BORA Author. Implemented with Claude Code; reviewed by BORA author.
# Date: 06/08/2026
# Purpose: emit the per-(keyword, direction) proximity regexes consumed by
#          BORA from the SAME translated patterns/keywords that
#          gen_zombie_regex.py produces, so BORA and Zombie run on an
#          IDENTICAL regex set (apples-to-apples cost comparison, see the
#          §7.6 cost matrix). The ONLY difference from gen_zombie_regex is the
#          final assembly + I/O.
#
#          Zombie bakes the whole proximity policy into ONE regex per SIT,
#          both orders and all keywords combined:
#                (PAT.{0,N}KWS)|(KWS.{0,N}PAT),  KWS = (kw1|kw2|...)
#          BORA instead processes each keyword and each direction as its OWN
#          regex non-matching task, so for every SIT and every (kept) keyword
#          we emit TWO files:
#                regex_bora/<slug>/kw<NN>.fwd.regex   ->  KW.{0,N}PAT  (keyword first)
#                regex_bora/<slug>/kw<NN>.bwd.regex   ->  PAT.{0,N}KW  (pattern first)
#          plus the shared pure pattern  regex_bora/<slug>/pat.regex  and a
#          keywords.tsv mapping <NN> -> keyword for traceability.
#
#          PAT SPLITTING: when PAT is a top-level alternation (e.g. UK National
#          Insurance's two number layouts AB123456C and AB 12 34 56 C), each
#          branch is emitted as its OWN signature instead of one union sig, so a
#          k-way alternation yields k separate (fwd, bwd) pairs per keyword. Such
#          SITs carry a .p<MM> branch suffix:
#                regex_bora/<slug>/kw<NN>.p<MM>.fwd.regex / .bwd.regex
#                regex_bora/<slug>/pat.p<MM>.regex   (the branch pattern)
#          SITs whose PAT has no top-level alternation are unchanged (no suffix).
#          Only a GENUINE top-level alternation splits; a nested alternation
#          inside a group (e.g. an `(00|01|...)` prefix) is left intact. The split
#          is purely on assembly -- the keyword set and PAT text are still exactly
#          what gen_zombie_regex produces. See split_pat.
#
#          Everything upstream of the assembly is reused verbatim from
#          gen_zombie_regex (translation, per-SIT relaxations, prose/short
#          keyword filters, the Zombie compiler-limit approximation, the
#          connection-string syntax rebuild, the whitespace-delimiting of
#          keywords). KW is whitespace-flanked exactly as in
#          gen_zombie_regex.sit_to_regex (bare for the connection-string SITs).
#
#          Each generated regex is sanity-checked with Python `re.compile`
#          (the Zombie/BORA dialect is a strict subset of Python regex, so a
#          successful compile means well-formed). The pure pattern is also
#          run against the web-crawled positive samples via the reused
#          gen_zombie_regex.test_samples (re-based, engine-agnostic).
# -------------------------------------------

import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gen_zombie_regex as gz   # noqa: E402  (reused translation pipeline)
from common import gen_report_header  # noqa: E402

# --- configuration ---------------------------------------------------------
RECORDS_DIR = gz.RECORDS_DIR            # input : per-SIT specs (reused)
BORA_DIR    = "regex_bora"              # output: per-SIT subdirs of fwd/bwd files
MAIN_FULL   = os.path.join(BORA_DIR, "main_full.dat")  # ClamAV-format sig DB
DOCS_DIR    = gz.DOCS_DIR
LOG_FILE    = os.path.join(DOCS_DIR, "gen_regex_bora.log")

# Whitespace class flanking a delimited keyword -- identical to
# gen_zombie_regex.sit_to_regex (space, tab, LF, CR).
WS_CLASS = "[\\x20\\x09\\x0A\\x0D]"

# ClamAV logical signature with a single PCRE subsig for each (keyword, direction)
# policy. Layout per line:
#   <name>;Engine:81-255,Target:0;0;/<pcre>/s
# subsig 0 is the proximity regex as PCRE; the logical expression "0" requires it.
# NOTE: the PCRE subsig is emitted WITHOUT a leading "0" trigger ("/.../s", not
# "0/.../s") -- a trigger of "0" is known to overflow BORA's parser stack. The
# Zombie dialect is already valid PCRE (\xHH escapes, classes, {n,m}, alternation),
# so the regex body is used verbatim. Engine level >=81 is the PCRE floor; Target:0
# = any file (DLP docs are arbitrary text); flag 's' = dotall so the .{0,N}
# proximity gap spans newlines.
SIG_DESC   = "Engine:81-255,Target:0"
PCRE_FLAGS = "s"
SIG_PREFIX = "Dlp"

# Leading alphabet-coverage signature, emitted as the very first line of
# main_full.dat (same convention as chr17_variants/scripts/gen_bora_regex.py).
ALPHABET_SIG = ("Win.Alphabet.SAMPLE-1;Engine:51-255,Target:1;0|1;"
                "09afcdeb1928374650123457890abcde;0123498765423afedc")


# --- top-level PAT-alternation splitting -----------------------------------
def strip_outer_group(s):
    """If `s` is a single group enclosing the WHOLE pattern, return (inner, True);
    otherwise (s, False). Dialect-aware: [..] classes are atomic and \\-escapes
    are a 2-char unit, so a `)` inside a class or after an escape is ignored."""
    if not s.startswith("("):
        return s, False
    depth, in_class, i = 0, False, 0
    while i < len(s):
        c = s[i]
        if c == "\\" and i + 1 < len(s):
            i += 2
            continue
        if in_class:
            if c == "]":
                in_class = False
            i += 1
            continue
        if c == "[":
            in_class = True
        elif c == "(":
            depth += 1
        elif c == ")":
            depth -= 1
            if depth == 0:
                # matching close of the opening paren: peel only if it ends s.
                return (s[1:-1], True) if i == len(s) - 1 else (s, False)
        i += 1
    return s, False


def top_level_split(s, sep="|"):
    """Split `s` on `sep` at paren-depth 0 only, treating [..] classes as atomic
    and \\-escapes as a 2-char unit. Nested alternations stay intact."""
    parts, buf, depth, in_class, i = [], [], 0, False, 0
    while i < len(s):
        c = s[i]
        if c == "\\" and i + 1 < len(s):
            buf.append(s[i:i + 2])
            i += 2
            continue
        if in_class:
            buf.append(c)
            if c == "]":
                in_class = False
            i += 1
            continue
        if c == "[":
            in_class = True
        elif c == "(":
            depth += 1
        elif c == ")":
            depth -= 1
        elif c == sep and depth == 0:
            parts.append("".join(buf))
            buf = []
            i += 1
            continue
        buf.append(c)
        i += 1
    parts.append("".join(buf))
    return parts


def split_pat(pat):
    """Return PAT's top-level alternative branches (>=1). A GENUINE top-level
    alternation -- the whole PAT is `(A|B|...)` or `A|B|...` -- splits into its
    branches; anything else (incl. a nested `(00|01|...)` prefix group) returns
    [pat] unchanged."""
    core, _ = strip_outer_group(pat)
    parts = top_level_split(core)
    return parts if len(parts) > 1 else [pat]


# --- per-(keyword, PAT-branch, direction) assembly -------------------------
def sit_to_bora_regexes(proximity, pat, keywords, ws_delimit=True):
    """Split the proximity policy into one (forward, backward) pair per keyword
    PER top-level PAT branch (see split_pat): a top-level alternation in PAT
    becomes separate signatures rather than one union sig.

    Returns a list of dicts {idx, keyword, branches} where branches is a list of
    {pidx, fwd, bwd} with
        fwd = KW.{0,N}PAT_branch   (keyword first)   -- "forward"
        bwd = PAT_branch.{0,N}KW   (pattern first)   -- "backward"
    and KW is the keyword escaped into the dialect, whitespace-flanked when
    ws_delimit is set (mirrors gen_zombie_regex.sit_to_regex; bare for the
    connection-string context anchors). Empty when there are no keywords."""
    out = []
    n = str(proximity)
    branches = split_pat(pat)
    for i, kw in enumerate(keywords):
        ktok = (WS_CLASS + gz._esc(kw) + WS_CLASS) if ws_delimit else gz._esc(kw)
        bl = []
        for m, b in enumerate(branches):
            bl.append({
                "pidx": m,
                "fwd": "{k}.{{0,{n}}}{p}".format(k=ktok, n=n, p=b),
                "bwd": "{p}.{{0,{n}}}{k}".format(k=ktok, n=n, p=b),
            })
        out.append({"idx": i, "keyword": kw, "branches": bl})
    return out


def _compiles(regex):
    """True if `regex` is well-formed (the dialect is a strict subset of Python
    regex, so a successful compile == well-formed)."""
    try:
        re.compile(regex)
        return True
    except re.error:
        return False


def _stem(idx, pidx, n_branches):
    """File/sig stem for a (keyword idx, PAT-branch pidx). No .p<MM> suffix when
    the PAT is not split (n_branches == 1), so non-alternation SITs are unchanged."""
    return "kw%02d" % idx if n_branches == 1 else "kw%02d.p%02d" % (idx, pidx)


def build_sig(slug, stem, direction, pcre):
    """Wrap one (keyword, PAT-branch, direction) proximity regex as a ClamAV
    logical signature with a single PCRE subsig:
        Dlp.<slug>.<stem>.<dir>;Engine:81-255,Target:0;0;/<pcre>/s
    where <stem> is kw<NN> (unsplit PAT) or kw<NN>.p<MM> (split PAT branch). The
    proximity regex is subsig 0; the logical expression "0" requires it. We
    deliberately emit the PCRE subsig WITHOUT a leading "0" trigger (i.e. "/.../s",
    not "0/.../s"): a trigger of "0" is known to overflow BORA's parser stack."""
    name = "%s.%s.%s.%s" % (SIG_PREFIX, slug, stem, direction)
    return "%s;%s;0;/%s/%s" % (name, SIG_DESC, pcre, PCRE_FLAGS)


# --- I/O -------------------------------------------------------------------
def write_sit(slug, pat, pairs):
    """Write this SIT's outputs under BORA_DIR/<slug>/: the shared pat.regex, a
    pat.p<MM>.regex per top-level PAT branch when the PAT splits, a
    kw<NN>[.p<MM>].fwd/.bwd.regex per (keyword, branch), and keywords.tsv.
    Returns (n_files_written, [bad_compile_paths], [clamav_sig_lines], n_branches)
    -- one PCRE logical-signature line per (keyword, PAT-branch, direction)."""
    d = os.path.join(BORA_DIR, slug)
    os.makedirs(d, exist_ok=True)
    branches = split_pat(pat)
    nb = len(branches)
    bad, sigs = [], []
    with open(os.path.join(d, "pat.regex"), "w") as f:
        f.write(pat + "\n")
    n_files = 1
    if nb > 1:
        for m, b in enumerate(branches):
            with open(os.path.join(d, "pat.p%02d.regex" % m), "w") as f:
                f.write(b + "\n")
            n_files += 1
    with open(os.path.join(d, "keywords.tsv"), "w") as f:
        for p in pairs:
            f.write("%02d\t%s\n" % (p["idx"], p["keyword"]))
    for p in pairs:
        for br in p["branches"]:
            stem = _stem(p["idx"], br["pidx"], nb)
            for tag, rgx in (("fwd", br["fwd"]), ("bwd", br["bwd"])):
                name = "%s.%s.regex" % (stem, tag)
                with open(os.path.join(d, name), "w") as f:
                    f.write(rgx + "\n")
                n_files += 1
                if not _compiles(rgx):
                    bad.append(os.path.join(slug, name))
                sigs.append(build_sig(slug, stem, tag, rgx))
    return n_files, bad, sigs, nb


def write_main_full(sigs):
    """Write the ClamAV-format signature DB regex_bora/main_full.dat: the leading
    Win.Alphabet.SAMPLE-1 line followed by one PCRE logical signature per
    (keyword, direction). Returns the number of Dlp.* signatures written."""
    with open(MAIN_FULL, "w") as f:
        f.write(ALPHABET_SIG + "\n")
        f.write("\n".join(sigs) + "\n")
    return len(sigs)


# --- log -------------------------------------------------------------------
def write_log(rows):
    counts = {"OK": 0, "APPROX": 0, "SKIP": 0}
    for r in rows:
        counts[r["status"]] += 1
    with open(LOG_FILE, "w") as f:
        f.write(gen_report_header("ms_dlp pattern->BORA per-keyword regex log"))
        f.write("\n\n")
        f.write("outputs:\n")
        f.write("  %s/<slug>/pat.regex            (shared pure pattern)\n" % BORA_DIR)
        f.write("  %s/<slug>/pat.p<MM>.regex      (per top-level PAT branch, if split)\n" % BORA_DIR)
        f.write("  %s/<slug>/kw<NN>[.p<MM>].fwd.regex  (KW.{0,N}PAT_branch, keyword first)\n" % BORA_DIR)
        f.write("  %s/<slug>/kw<NN>[.p<MM>].bwd.regex  (PAT_branch.{0,N}KW, pattern first)\n" % BORA_DIR)
        f.write("  %s/<slug>/keywords.tsv         (<NN> -> keyword)\n" % BORA_DIR)
        f.write("  %s   (ClamAV-format PCRE sig DB: one logical\n" % MAIN_FULL)
        f.write("    signature per (keyword, PAT-branch, direction), led by Win.Alphabet.SAMPLE-1)\n\n")
        f.write("note: in %s the PCRE subsig is emitted WITHOUT a leading \"0\"\n"
                % MAIN_FULL)
        f.write("  trigger -- we write \"/<pcre>/s\", NOT \"0/<pcre>/s\". We\n")
        f.write("  SPECIFICALLY DO NOT generate the \"0\" trigger: it is known to\n")
        f.write("  overflow BORA's signature parser stack (a known issue).\n\n")
        f.write("note: PAT and keywords are produced by the SAME pipeline as\n")
        f.write("  gen_zombie_regex.py (identical translation, relaxations,\n")
        f.write("  prose/short-keyword filters, Zombie compiler-limit approx, and\n")
        f.write("  connection-string syntax rebuild), so the BORA and Zombie regex\n")
        f.write("  sets are identical -- only the assembly differs (per-keyword,\n")
        f.write("  per-direction here vs. one combined regex there). 'parse=OK'\n")
        f.write("  means every emitted regex compiled under Python re (the dialect\n")
        f.write("  is a strict subset). 'zombie-limit[...]' warnings carry over.\n\n")
        f.write("== PER-SIT RESULTS ==\n")
        tot_files = 0
        for r in rows:
            if r["status"] == "SKIP":
                f.write("[%-6s] %s\n" % (r["status"], r["slug"]))
                for w in r["warnings"]:
                    f.write("           - %s\n" % w)
                continue
            tot_files += r["files"]
            ptag = "  parse=OK" if not r["bad"] else "  parse=FAIL"
            samp = r.get("samples")
            stag = "  samples=%d/%d" % (samp[0], samp[1]) if samp else ""
            nb = r.get("branches", 1)
            btag = "  branches=%d" % nb if nb > 1 else ""
            f.write("[%-6s] %s  keywords=%d  files=%d%s%s%s\n"
                    % (r["status"], r["slug"], r["nkw"], r["files"],
                       btag, ptag, stag))
            for w in r["warnings"]:
                f.write("           - %s\n" % w)
            for b in r["bad"]:
                f.write("           ! did not compile: %s\n" % b)
            if samp:
                for s in samp[2]:
                    f.write("           ! sample not matched: %r\n" % s)
        s_pass = sum(r["samples"][0] for r in rows if r.get("samples"))
        s_tot = sum(r["samples"][1] for r in rows if r.get("samples"))
        z = sum(1 for r in rows
                if any("zombie-limit" in w for w in r.get("warnings", [])))
        f.write("\n== SUMMARY ==\n")
        f.write("total SITs:  %d\n" % len(rows))
        f.write("OK:          %d\n" % counts["OK"])
        f.write("APPROX:      %d\n" % counts["APPROX"])
        f.write("SKIP:        %d\n" % counts["SKIP"])
        n_split = sum(1 for r in rows if r.get("branches", 1) > 1)
        f.write("regex files: %d  (pat[.p<MM>] + 2 per kept keyword per PAT branch)\n"
                % tot_files)
        f.write("PAT-split SITs: %d  (top-level alternation -> per-branch sigs)\n"
                % n_split)
        f.write("zombie-limit approx: %d  (forced by Zombie compiler limits; see %s)\n"
                % (z, gz.LIMIT_LOG))
        f.write("samples:     %d/%d positive matches\n" % (s_pass, s_tot))
    return counts, tot_files, s_pass, s_tot


# -------------------------------------------
# MAIN
# -------------------------------------------
def main():
    # this script lives in scripts/, one level below ms_dlp/ (same convention
    # as gen_zombie_regex so the reused relative paths resolve).
    os.chdir(os.path.join(os.path.dirname(os.path.abspath(__file__)), os.pardir))
    os.makedirs(DOCS_DIR, exist_ok=True)
    gz.reset_dir(BORA_DIR)

    rows = []
    all_sigs = []
    for fname in sorted(os.listdir(RECORDS_DIR)):
        if not fname.endswith(".txt"):
            continue
        rec = gz.parse_sit(os.path.join(RECORDS_DIR, fname))
        pat, status, warns = gz.patterns_to_regex(rec["pattern"])
        if status == "untranslatable":
            # connection-string SITs rebuild PAT entirely from CONNSTRING_SYNTAX,
            # so an untranslatable prose pattern is irrelevant -- don't skip them.
            if rec["slug"] not in gz.CONNSTRING_SYNTAX:
                rows.append({"slug": rec["slug"], "status": "SKIP",
                             "warnings": warns})
                continue
            pat = ""        # discarded; approx_for_zombie sets the real PAT below
        pat = gz._relax(rec["slug"], pat, warns)
        rec["keywords"], dropped_kw = gz._filter_keywords(rec["keywords"])
        for d in dropped_kw:
            warns.append("dropped non-keyword line (prose/example leak): %r" % d)
        rec["keywords"], short_kw = gz._filter_short_keywords(rec["keywords"])
        for d in short_kw:
            warns.append("dropped short keyword (trimmed len < %d): %r"
                         % (gz.MIN_KEYWORD_LEN, d))
        # force the regex set to fit Zombie's compiler limits, identically to
        # gen_zombie_regex (so BORA's inputs match Zombie's exactly).
        pat, rec["keywords"], znotes = gz.approx_for_zombie(rec["slug"], pat,
                                                            rec["keywords"])
        warns.extend(znotes)
        if znotes and status == "exact":
            status = "approx"             # a Zombie-limit approximation was applied

        ws_delimit = rec["slug"] not in gz.CONNSTRING_SYNTAX
        pairs = sit_to_bora_regexes(rec["proximity"], pat, rec["keywords"],
                                    ws_delimit=ws_delimit)
        if not pairs:
            rows.append({"slug": rec["slug"], "status": "SKIP",
                         "warnings": warns + ["no keywords"]})
            continue
        n_files, bad, sigs, nb = write_sit(rec["slug"], pat, pairs)
        all_sigs.extend(sigs)
        rows.append({"slug": rec["slug"],
                     "status": "OK" if status == "exact" else "APPROX",
                     "warnings": warns, "nkw": len(pairs), "branches": nb,
                     "files": n_files, "bad": bad,
                     "samples": gz.test_samples(rec["slug"], pat)})

    n_sigs = write_main_full(all_sigs)
    counts, tot_files, s_pass, s_tot = write_log(rows)
    print("[gen] %s : SITs=%d OK=%d APPROX=%d SKIP=%d  files=%d  sigs=%d  "
          "samples=%d/%d"
          % (LOG_FILE, len(rows), counts["OK"], counts["APPROX"],
             counts["SKIP"], tot_files, n_sigs, s_pass, s_tot))


if __name__ == "__main__":
    main()
