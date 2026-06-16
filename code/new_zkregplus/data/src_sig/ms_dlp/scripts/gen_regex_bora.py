# -------------------------------------------
# Creator: BORA Author. Implemented with Claude Code; reviewed by BORA author.
# Date: 06/08/2026 (refactored 06/10/2026)
# Purpose: emit the per-(keyword, direction) proximity regexes consumed by BORA
#          from the SAME translated patterns/keywords/combos that
#          gen_zombie_regex.py produces, so BORA and Zombie run on an IDENTICAL
#          regex set (apples-to-apples cost comparison, see the §7.6 cost matrix).
#          The ONLY difference from gen_zombie_regex is the final assembly + I/O.
#
#          EVERYTHING upstream of assembly is reused VERBATIM from gen_zombie_regex
#          via gz.process_sit (translation, per-SIT relaxations, prose/short/
#          very-long keyword filters, the empty-keyword discard, the Zombie
#          compiler-limit fit + uncompilable-PAT discard, and the recursive
#          alternation EXPANSION into combos). gz owns the dialect scanners and
#          expand_pat; this file owns only the BORA assembly, ClamAV signatures,
#          and the log.
#
#          Zombie bakes one circuit per combo:  (combo.{0,N}KWS)|(KWS.{0,N}combo).
#          BORA instead processes each keyword and each direction as its OWN regex
#          non-matching task, so for every SIT, every kept keyword and every
#          expanded combo we emit TWO files:
#                regex_bora/<slug>/kw<NN>[.p<MM>].fwd.regex  ->  KW.{0,N}combo
#                regex_bora/<slug>/kw<NN>[.p<MM>].bwd.regex  ->  combo.{0,N}KW
#          where .p<MM> is the combo index, present only when the PAT expands to
#          >1 combo (single-combo SITs carry no suffix). Plus the per-combo
#          pat[.p<MM>].regex, a keywords.tsv, and a ClamAV-format main_full.dat.
#
#          TWO PASSES (same pipeline, different I/O dirs): the English batch
#          (raw_data_records -> regex_bora) and the international SUPERSET
#          (raw_data_records_international -> regex_bora_international). A sample
#          miss in the international pass auto-discards the SIT (reason=
#          samples-failed); in the English pass it is kept and surfaced (a miss
#          there is a regression).
#
#          Each generated regex is sanity-checked with Python re.compile (the
#          Zombie/BORA dialect is a strict subset). The pure pattern is verified
#          against web-crawled positive samples by the reused gz.test_samples
#          (any-combo: a sample matches the SIT iff it matches some combo).
# -------------------------------------------

import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gen_zombie_regex as gz   # noqa: E402  (reused translation+expansion pipeline)
from common import gen_report_header, get_ms_dlp_dir  # noqa: E402

# --- configuration ---------------------------------------------------------
DOCS_DIR = gz.DOCS_DIR

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


class Pass:
    """One generation pass: input records dir, output regex_bora dir, the
    matching positive-sample dir, and the log file. main_full.dat lives in the
    output dir."""
    def __init__(self, records, out_dir, sample_dir, log_file):
        self.records, self.out_dir = records, out_dir
        self.sample_dir, self.log_file = sample_dir, log_file

    @property
    def main_full(self):
        return os.path.join(self.out_dir, "main_full.dat")


PASS_ENGLISH = Pass(
    "raw_data_records", "regex_bora", "regex_pat_samples",
    os.path.join(DOCS_DIR, "gen_regex_bora.log"))
PASS_INTL = Pass(
    "raw_data_records_international", "regex_bora_international",
    "regex_pat_samples_international",
    os.path.join(DOCS_DIR, "gen_regex_bora_international.log"))


# --- per-(keyword, combo, direction) assembly ------------------------------
def sit_to_bora_regexes(proximity, combos, keywords):
    """One (forward, backward) pair per keyword PER expanded combo (see
    gz.expand_pat): a top-level alternation in PAT becomes separate combos rather
    than one union sig. Returns a list of dicts {idx, keyword, branches} where
    branches is a list of {pidx, fwd, bwd} with
        fwd = KW.{0,N}combo   (keyword first)   -- "forward"
        bwd = combo.{0,N}KW   (pattern first)   -- "backward"
    KW is the keyword escaped into the dialect and whitespace-flanked (mirrors
    gz.sit_to_regex). Empty when there are no keywords/combos."""
    out = []
    n = str(proximity)
    for i, kw in enumerate(keywords):
        ktok = WS_CLASS + gz._esc(kw) + WS_CLASS
        bl = []
        for m, combo in enumerate(combos):
            bl.append({
                "pidx": m,
                "fwd": "{k}.{{0,{n}}}{p}".format(k=ktok, n=n, p=combo),
                "bwd": "{p}.{{0,{n}}}{k}".format(k=ktok, n=n, p=combo),
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


def _stem(idx, pidx, n_combos):
    """File/sig stem for a (keyword idx, combo pidx). No .p<MM> suffix when the PAT
    does not expand (n_combos == 1), so non-alternation SITs are unchanged."""
    return "kw%02d" % idx if n_combos == 1 else "kw%02d.p%02d" % (idx, pidx)


def build_sig(slug, stem, direction, pcre):
    """Wrap one (keyword, combo, direction) proximity regex as a ClamAV logical
    signature with a single PCRE subsig:
        Dlp.<slug>.<stem>.<dir>;Engine:81-255,Target:0;0;/<pcre>/s
    The proximity regex is subsig 0; the logical expression "0" requires it. We
    deliberately emit the subsig WITHOUT a leading "0" trigger ("/.../s", not
    "0/.../s"): a trigger of "0" is known to overflow BORA's parser stack."""
    name = "%s.%s.%s.%s" % (SIG_PREFIX, slug, stem, direction)
    return "%s;%s;0;/%s/%s" % (name, SIG_DESC, pcre, PCRE_FLAGS)


# --- I/O -------------------------------------------------------------------
def write_sit(out_dir, res):
    """Write this SIT's outputs under out_dir/<slug>/: per-combo pat[.p<MM>].regex,
    kw<NN>[.p<MM>].fwd/.bwd.regex per (keyword, combo), and keywords.tsv. Returns
    (n_files, [bad_compile_paths], [clamav_sig_lines]) -- one PCRE logical sig per
    (keyword, combo, direction)."""
    slug, combos, kws = res["slug"], res["combos"], res["keywords"]
    d = os.path.join(out_dir, slug)
    os.makedirs(d, exist_ok=True)
    nb = len(combos)
    bad, sigs, n_files = [], [], 0

    # per-combo pure patterns
    if nb == 1:
        with open(os.path.join(d, "pat.regex"), "w") as f:
            f.write(combos[0] + "\n")
        n_files += 1
    else:
        for m, combo in enumerate(combos):
            with open(os.path.join(d, "pat.p%02d.regex" % m), "w") as f:
                f.write(combo + "\n")
            n_files += 1

    pairs = sit_to_bora_regexes(res["proximity"], combos, kws)
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
    return n_files, bad, sigs


def write_main_full(path, sigs):
    """Write the ClamAV-format signature DB: the leading Win.Alphabet.SAMPLE-1
    line followed by one PCRE logical signature per (keyword, combo, direction).
    Returns the number of Dlp.* signatures written."""
    with open(path, "w") as f:
        f.write(ALPHABET_SIG + "\n")
        if sigs:
            f.write("\n".join(sigs) + "\n")
    return len(sigs)


# --- log -------------------------------------------------------------------
def write_log(p, rows, n_sigs):
    """Itemized per-SIT log; same reason vocabulary as gen_zombie_regex (it all
    comes from gz.process_sit), so the two logs agree."""
    counts = {"OK": 0, "APPROX": 0, "SKIP": 0}
    for r in rows:
        counts[r["status"]] += 1
    with open(p.log_file, "w") as f:
        f.write(gen_report_header("ms_dlp pattern->BORA per-keyword regex log"))
        f.write("\n\n")
        f.write("input:   %s/\n" % p.records)
        f.write("outputs: %s/<slug>/pat[.p<MM>].regex            (per-combo pure pattern)\n"
                % p.out_dir)
        f.write("         %s/<slug>/kw<NN>[.p<MM>].fwd.regex      (KW.{0,N}combo)\n"
                % p.out_dir)
        f.write("         %s/<slug>/kw<NN>[.p<MM>].bwd.regex      (combo.{0,N}KW)\n"
                % p.out_dir)
        f.write("         %s/<slug>/keywords.tsv\n" % p.out_dir)
        f.write("         %s   (ClamAV-format PCRE sig DB; one sig per\n" % p.main_full)
        f.write("           (keyword, combo, direction), led by Win.Alphabet.SAMPLE-1)\n\n")
        f.write("note: PAT/keywords/combos come from the SAME pipeline as\n")
        f.write("  gen_zombie_regex.py (gz.process_sit), so the BORA and Zombie\n")
        f.write("  regex sets are identical -- only assembly differs (per-keyword,\n")
        f.write("  per-direction here vs. one combined circuit there). The PCRE subsig\n")
        f.write("  is emitted WITHOUT a leading \"0\" trigger (known to overflow BORA's\n")
        f.write("  parser stack). 'parse=OK' = every emitted regex compiled under\n")
        f.write("  Python re. Discard reasons: %s.\n\n"
                % ", ".join(gz.DISCARD_REASONS))
        f.write("== PER-SIT RESULTS ==\n")
        tot_files = 0
        for r in rows:
            if r["status"] == "SKIP":
                f.write("[SKIP  ] %s  reason=%s\n" % (r["slug"], r["reason"]))
                f.write("           - %s\n" % r["detail"])
                for w in r["warnings"]:
                    f.write("           - %s\n" % w)
                continue
            tot_files += r["n_files"]
            ptag = "parse=OK" if not r["bad"] else "parse=FAIL"
            samp = r.get("samples")
            stag = "  samples=%d/%d" % (samp[0], samp[1]) if samp else ""
            ctag = "  combos=%d" % len(r["combos"])
            if r["truncated"]:
                ctag += "/%d(trunc)" % r["n_total"]
            if r.get("compress"):
                ctag += "  compress=%s[%d->%d]" % (r["compress"]["kind"],
                          r["compress"]["before"], r["compress"]["after"])
            f.write("[%-6s] %s  keywords=%d%s  files=%d  %s%s\n"
                    % (r["status"], r["slug"], len(r["keywords"]), ctag,
                       r["n_files"], ptag, stag))
            for w in r["warnings"]:
                f.write("           - %s\n" % w)
            for b in r["bad"]:
                f.write("           ! did not compile: %s\n" % b)
            if samp:
                for s in samp[2]:
                    f.write("           ! sample not matched: %r\n" % s)
        s_pass = sum(r["samples"][0] for r in rows if r.get("samples"))
        s_tot = sum(r["samples"][1] for r in rows if r.get("samples"))
        n_combo = sum(len(r["combos"]) for r in rows if r["status"] != "SKIP")
        f.write("\n== DISCARDED BY REASON ==\n")
        for code in gz.DISCARD_REASONS:
            n = sum(1 for r in rows if r["status"] == "SKIP" and r["reason"] == code)
            f.write("  %-22s %d\n" % (code, n))
        f.write("\n== APPROXIMATED BY REASON ==\n")
        for code, mark in gz.APPROX_TAGS:
            n = sum(1 for r in rows if r["status"] != "SKIP"
                    and any(mark in w for w in r.get("warnings", [])))
            f.write("  %-22s %d\n" % (code, n))
        f.write("\n== SUMMARY ==\n")
        f.write("total SITs:  %d\n" % len(rows))
        f.write("OK:          %d\n" % counts["OK"])
        f.write("APPROX:      %d\n" % counts["APPROX"])
        f.write("SKIP:        %d\n" % counts["SKIP"])
        f.write("regex files: %d  (pat[.p<MM>] + 2 per kept keyword per combo)\n"
                % tot_files)
        f.write("combos:      %d total (one (fwd,bwd) pair per keyword each)\n" % n_combo)
        f.write("Dlp sigs:    %d  (in %s)\n" % (n_sigs, p.main_full))
        f.write("samples:     %d/%d positive matches\n" % (s_pass, s_tot))
    return counts, tot_files, s_pass, s_tot, n_combo


def run_pass(p, discard_on_sample_miss):
    """Run one pass: read p.records, run gz.process_sit per SIT, write per-(keyword,
    combo,direction) BORA regexes + sigs, log. discard_on_sample_miss=True
    (international) turns a sample miss into reason=samples-failed."""
    gz.reset_dir(p.out_dir)
    if not os.path.isdir(p.records):
        print("[gen] %s : records dir %s absent -- skipping pass"
              % (p.log_file, p.records))
        return
    rows, all_sigs = [], []
    for fname in sorted(os.listdir(p.records)):
        if not fname.endswith(".txt"):
            continue
        rec = gz.parse_sit(os.path.join(p.records, fname))
        res = gz.process_sit(rec, p.sample_dir)
        if res["status"] == "SKIP":
            rows.append(res)
            continue
        samp = res.get("samples")
        if discard_on_sample_miss and samp and samp[0] < samp[1]:
            rows.append(gz._skip(res["slug"], "samples-failed",
                                 "pattern matched only %d/%d web-verified samples -> "
                                 "discarded (international auto-discard policy)"
                                 % (samp[0], samp[1]), res["warnings"]))
            continue
        n_files, bad, sigs = write_sit(p.out_dir, res)
        all_sigs.extend(sigs)
        res["n_files"], res["bad"] = n_files, bad
        rows.append(res)
    n_sigs = write_main_full(p.main_full, all_sigs)
    counts, tot_files, s_pass, s_tot, n_combo = write_log(p, rows, n_sigs)
    print("[gen] %s : SITs=%d OK=%d APPROX=%d SKIP=%d  files=%d  combos=%d  "
          "sigs=%d  samples=%d/%d"
          % (p.log_file, len(rows), counts["OK"], counts["APPROX"],
             counts["SKIP"], tot_files, n_combo, n_sigs, s_pass, s_tot))


# -------------------------------------------
# MAIN
# -------------------------------------------
def main():
    # resolve all relative paths against the ms_dlp dir (never cwd / hardcoded).
    os.chdir(get_ms_dlp_dir())
    os.makedirs(DOCS_DIR, exist_ok=True)
    run_pass(PASS_ENGLISH, discard_on_sample_miss=False)
    run_pass(PASS_INTL, discard_on_sample_miss=True)


if __name__ == "__main__":
    main()
