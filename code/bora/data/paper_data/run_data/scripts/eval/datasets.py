#!/usr/bin/env python3
# ----------------------------------
# Designed by the paper author; function implementation by Claude Code 4.8.
# Code reviewed and audited by the author; the generated table was manually
# verified by the paper author.
# ----------------------------------
"""Generate the dataset characterization table for §7.2 (tab:datasets).

The three datasets are keyed by their paper labels -- ``Mal`` (malware
scanning, CentOS x ClamAV), ``Dna`` (genomics, chr17 x NCBI), and ``Dlp``
(email DLP, Enron x MS-DLP). Each label is emitted as a small-caps row stub
(``\\textsc{Mal}`` etc.), the same identifiers used throughout §7.6.

Reads:
  The Mal row is extracted live via ``common.extract_mal_dataset`` (ClamAV
  README/main.dat + binexec_merged128k); the Dna row via
  ``common.extract_dna_dataset`` (chr17_variants logs + reef_regex/); the Dlp
  row via ``common.extract_dlp_dataset`` (raw Enron maildir + MS-DLP
  regex_zombie_international/). All three rows are now live.

Writes:
  <paper_root>/figs/datasets.tex
"""

from __future__ import annotations

import os
import statistics
import sys
import tarfile
from dataclasses import dataclass
from pathlib import Path

# common.py lives in the parent scripts/ directory.
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from common import (get_paper_root, get_proj_root, extract_mal_dataset,
                    extract_dna_dataset, extract_dlp_dataset, dlp_patkws_bytes)


# ----------------------------- configuration -----------------------------

@dataclass(frozen=True)
class Dataset:
    """One corpus x ruleset pairing. ``label`` is the §7.6 row stub."""
    label: str          # Mal / Dna / Dlp -- emitted as \textsc{label}
    corpus: str         # document-corpus name
    docs: int           # document count
    nbytes: str         # total bytes, pre-unit (e.g. "4.7\\,GB")
    doc_size: str       # median doc size cell (math/literal LaTeX)
    ruleset: str        # ruleset name + version
    rules: int          # rule count
    regex_size: str     # on-disk size of the regex/signature set (LaTeX)
    rule_shape: str     # rule-shape description (LaTeX)


# All three rows (Mal, Dna, Dlp) are now built live in main() from their
# respective extractors; no static placeholder rows remain.


# ---------------------------- formatting ---------------------------------

def tex_int(n: int) -> str:
    """Render ``n`` with LaTeX-safe thousands separators (``38{,}889``)."""
    return f"{n:,}".replace(",", "{,}")


def fmt_bytes(n: int, mb_decimals: int = 0, kb_decimals: int = 0,
              gb_decimals: int = 1) -> str:
    """Render a byte count as a compact decimal-unit LaTeX cell (``765\\,MB``).

    ``gb_decimals`` / ``mb_decimals`` / ``kb_decimals`` set the precision of the
    GB / MB / KB units (defaults ``1`` / ``0`` / ``0``); e.g. ``gb_decimals=2``
    -> ``1.38\\,GB`` (so a 1.376\\,GB corpus is distinct from a 1.42\\,GB one)
    and ``kb_decimals=1`` -> ``1.5\\,KB`` (so a 1.5\\,KB median is not rounded
    to ``2\\,KB``).
    """
    if n >= 10 ** 9:
        return f"{n / 10 ** 9:.{gb_decimals}f}\\,GB"
    if n >= 10 ** 6:
        return f"{n / 10 ** 6:.{mb_decimals}f}\\,MB"
    if n >= 10 ** 3:
        return f"{n / 10 ** 3:.{kb_decimals}f}\\,KB"
    return f"{n}\\,B"


def fmt_size_mmm(mn: int, median: float, mx: int,
                 mb_decimals: int = 0, kb_decimals: int = 0) -> str:
    """Render a ``min / median / max`` doc-size cell (robust to heavy tails)."""
    return (f"{fmt_bytes(mn, mb_decimals, kb_decimals)} / "
            f"{fmt_bytes(int(median), mb_decimals, kb_decimals)} / "
            f"{fmt_bytes(mx, mb_decimals, kb_decimals)}")


def build_mal_dataset(d: dict) -> Dataset:
    """Assemble the live Mal row from ``extract_mal_dataset`` output."""
    rule_shape = (
        f"literal rich; {tex_int(d['subsigs'])} leaf subsigs "
        f"({tex_int(d['subsigs_pcre'])} PCRE); logical AND/OR combinations; "
        r"frequent bounded gaps \texttt{.\{n\}}; mostly unanchored, "
        r"implicit \texttt{.*\dots.*} shape"
    )
    return Dataset(
        label="Mal",
        corpus=f"CentOS {d['centos']}",
        docs=d["docs"],
        nbytes=fmt_bytes(d["total_bytes"]),
        doc_size=fmt_size_mmm(d["size_min"], d["size_median"], d["size_max"]),
        ruleset=f"ClamAV {d['clamav_version']}",
        rules=d["rules"],
        regex_size=fmt_bytes(d["ruleset_bytes"], mb_decimals=1),  # size of main.dat
        rule_shape=rule_shape,
    )


def build_dna_dataset(d: dict) -> Dataset:
    """Assemble the live Dna row from ``extract_dna_dataset`` output."""
    chrom = d["chromosome"]
    rule_shape = (
        r"anchored \texttt{\^{}.\{N\}}literal\texttt{.*}; "
        rf"len {tex_int(d['min_len'])}--{tex_int(d['max_len'])}\,chars "
        rf"(avg {d['avg_len']:.0f})"
    )
    assembly = d["assembly"].split(".")[0]   # GRCh38.p14 -> GRCh38
    return Dataset(
        label="Dna",
        corpus=rf"\shortstack[l]{{chr{chrom}\\({assembly})}}",
        docs=1,
        nbytes=fmt_bytes(d["doc_bytes"]),
        doc_size=r"---~(single)",
        ruleset=f"NCBI ClinVar (chr{chrom})",
        rules=d["rules"],
        regex_size=fmt_bytes(d["ruleset_bytes"], mb_decimals=1),
        rule_shape=rule_shape,
    )


def build_dlp_dataset(d: dict) -> Dataset:
    """Assemble the live Dlp row from ``extract_dlp_dataset`` output."""
    gap = str(d["gap"])
    # Keyword-proximity disjunction, both keyword orders, with kw subscripts:
    #   (kw_1|...|kw_n).{0,N}re | re.{0,N}(kw_1|...|kw_n)
    kw = r"(kw\textsubscript{1}|\ldots|kw\textsubscript{n})"
    # Tie the disjunction bar to the following branch (``|~re``) so a wrap in
    # the narrow p-column breaks *before* it -- the bar never sits alone on a
    # line; the continuation reads ``| re.{0,N}(...)``.
    # \allowbreak lets the narrow p-column wrap the disjunction group away from
    # the following bounded-gap token, so neither monospace chunk overflows.
    shape_tt = (f"{kw}\\allowbreak.\\{{0,{gap}\\}}re "
                f"|~re.\\{{0,{gap}\\}}\\allowbreak{kw}")
    rule_shape = r"keyword-proximity: \texttt{" + shape_tt + "}"
    return Dataset(
        label="Dlp",
        corpus=r"\shortstack[l]{Enron\\Email}",
        docs=d["docs"],
        # 2-decimal GB so the 1.38\,GB clean corpus reads distinct from the
        # 1.42\,GB raw maildir (both round to 1.4\,GB at one decimal).
        nbytes=fmt_bytes(d["total_bytes"], gb_decimals=2),
        # raw maildir is heavy-tailed (398\,B .. ~1.9\,MB); show sub-KB/MB.
        doc_size=fmt_size_mmm(d["size_min"], d["size_median"], d["size_max"],
                              mb_decimals=1, kb_decimals=1),
        ruleset="MS-DLP (SIT)",
        rules=d["rules"],
        regex_size=fmt_bytes(d["ruleset_bytes"]),
        rule_shape=rule_shape,
    )


def dlp_step1_corpus(paper_root: Path, proj_root: Path) -> dict:
    """Measure the step-1 (RE2-screened) clean Dlp corpus from ``corpus.tgz``.

    The step-1 clean set is the union of ``passed_clean_email.txt`` and
    ``failed_clean_email.txt`` inside ``data/raw_data/any_server/corpus.tgz``
    (corpus.tgz is machine-independent, so it lives under any_server/; these are
    the step-2 pass/fail split; their union is the step-1 RE2-clean corpus,
    509,612 paths -- matching corpus.stat). NOT steps 2-3 (BORA-side
    approximation pruning); ``final_enron_list.txt.tgz`` is unused.

    Each listed path is relative to ``proj_root``. The two member lists are
    extracted to ``/tmp/bora`` and removed afterward. Sizes are measured over
    the actual email files (paths under ``maildir/``); the 2 non-email repo
    metadata entries (.gitignore, README.md) are excluded. Returns
    docs/total_bytes/size_min/size_median/size_max.
    """
    tgz = paper_root / "data" / "raw_data" / "any_server" / "corpus.tgz"
    members = ["passed_clean_email.txt", "failed_clean_email.txt"]
    workdir = Path("/tmp/bora")
    workdir.mkdir(parents=True, exist_ok=True)
    extracted: list[Path] = []
    try:
        with tarfile.open(tgz) as tf:
            for m in members:
                tf.extract(m, path=workdir)
                extracted.append(workdir / m)
        rels: list[str] = []
        seen: set[str] = set()
        for f in extracted:
            for line in f.read_text().splitlines():
                p = line.strip()
                if p and "maildir/" in p and p not in seen:
                    seen.add(p)
                    rels.append(p)
        sizes = sorted(os.path.getsize(proj_root / p) for p in rels)
        if not sizes:
            raise RuntimeError("dlp_step1_corpus: no email files resolved "
                               f"under {proj_root}")
        return {
            "docs": len(sizes),
            "total_bytes": sum(sizes),
            "size_min": sizes[0],
            "size_median": statistics.median(sizes),
            "size_max": sizes[-1],
        }
    finally:
        for f in extracted:
            f.unlink(missing_ok=True)
        try:                       # drop /tmp/bora only if we left it empty
            workdir.rmdir()
        except OSError:
            pass


# --------------------------- table builder -------------------------------

def build_row(d: Dataset) -> str:
    return (
        f"    \\textsc{{{d.label}}} & {d.corpus} & {tex_int(d.docs)} & "
        f"{d.nbytes} & {d.doc_size}\n"
        f"        & {d.ruleset} & {tex_int(d.rules)} & {d.regex_size}\n"
        f"        & {d.rule_shape} \\\\"
    )


def dna_drop_note(d: dict) -> str:
    """Render the Dna variant-drop provenance as a LaTeX comment block.

    Documents, in the generated table, where the §7.2 "65 dropped" footnote
    numbers come from, so they can be re-checked against the live log.
    """
    reasons = "; ".join(
        f"{n} {r}" for r, n in sorted(d["skip_reasons"].items(),
                                      key=lambda kv: (-kv[1], kv[0])))
    return (
        f"% Dna drop provenance (source of the 65 dropped: {d['skip_log']}):\n"
        f"%   {d['n_processed']} pathogenic/likely-pathogenic chr17 variants "
        f"processed; {d['n_skipped']} skipped ({reasons}); "
        f"{d['n_kept']} kept = Rules cell.\n")


def build_table(datasets: list[Dataset], dna_note: str = "") -> str:
    body = "\n".join(build_row(d) for d in datasets)

    return dna_note + r"""% Auto-generated by data/scripts/eval/datasets.py -- do not edit by hand.
% Dataset characterization table for §7.2 (tab:datasets).
% All three rows are auto-extracted from the project corpus: Mal from ClamAV
% main.dat + binexec_merged128k, Dna from chr17_variants, Dlp from the raw
% Enron maildir + MS-DLP regex_zombie/. Locked layout:
% label stub outside both groups; two \multicolumn spans (Document corpus |
% Regex set); descriptive only -- NO tier (CP/SDE/DFA) columns, NO PCRE column.
%
% CentOS version: the table reports the neutral "CentOS 7" only. Binary
% provenance in the corpus points to the CentOS 7.9 update stream -- bundled
% shared objects carry the RPM dist tag el7_9 (e.g. ...base.el7_9.1.so) and
% the kernel is the 3.10.0-1160 series (shipped with 7.9). \cite{Zkreg} cited
% CentOS 7.1, and no /etc/centos-release or ISO is on disk to settle the
% minor version, so we leave it at "CentOS 7" rather than commit to 7.1 or 7.9.
\begin{table*}[t]
  \centering
  \footnotesize
  \caption{Evaluation datasets: \textsc{Mal} (malware scanning), \textsc{Dna}
  (genomic variants), and \textsc{Dlp} (e-mail DLP). The \emph{Rule shape}
  column summarizes the form and variety of the regexes.}
  \label{tab:datasets}
  \begin{tabular}{@{}l l r r l l r r p{3.2cm}@{}}
    \toprule
     & \multicolumn{4}{c}{Document corpus}
       & \multicolumn{4}{c}{Regex set} \\
    \cmidrule(lr){2-5} \cmidrule(lr){6-9}
     & Corpus & Docs & Size & Per-doc (min/med/max)
       & Ruleset (ver.) & Rules & Size & Rule shape \\
    \midrule
""" + body + r"""
    \bottomrule
  \end{tabular}
\end{table*}
"""


# --------------------------------- main ----------------------------------

def main() -> None:
    root = get_paper_root()
    figs = root / "figs"
    figs.mkdir(exist_ok=True)

    proj = get_proj_root()
    mal = build_mal_dataset(extract_mal_dataset(proj))
    dna_raw = extract_dna_dataset(proj)
    dna = build_dna_dataset(dna_raw)
    # Dlp row: use the full international SIT set (regex_zombie_international).
    dlp_regex_dir = proj / "data" / "src_sig" / "ms_dlp" / "regex_zombie_international"
    dlp_raw = extract_dlp_dataset(proj, regex_dir=dlp_regex_dir)
    # Report the regex size on the pattern-byte basis (pat_len+kws_len per
    # instance, each sub-pattern counted once) -- the accurate cost-driver
    # measure -- not the on-disk .regex size, which doubles each sub-pattern
    # for the bidirectional proximity form. Mal/Dna keep on-disk file sizes.
    dlp_raw["ruleset_bytes"] = dlp_patkws_bytes()
    # Override corpus count/size/per-doc stats with the step-1 (RE2-screened)
    # clean corpus -- the emails actually evaluated -- computed from the real
    # files listed in corpus.tgz, resolved under proj (get_proj_root()).
    dlp_raw.update(dlp_step1_corpus(root, proj))
    dlp = build_dlp_dataset(dlp_raw)
    datasets = [mal, dna, dlp]

    tex = build_table(datasets, dna_note=dna_drop_note(dna_raw))
    out = figs / "datasets.tex"
    out.write_text(tex)
    print(f"wrote {out}")


if __name__ == "__main__":
    main()
