#!/usr/bin/env python3
# ----------------------------------
# Designed by the paper author; function implementation by Claude Code 4.8.
# Code reviewed and audited by the author; the generated table was manually
# verified by the paper author.
# ----------------------------------
"""Generate the consolidated main-body comparison table (tab:compare-all).

One row per dataset (\\textsc{Mal}/\\textsc{Dna}/\\textsc{Dlp}, keyed to
tab:datasets -- no size columns, to avoid overlap), one column per system
(Zombie / Reef / BORA) plus BORA's speedup over each.

Every cell is sourced from the SAME extractors that feed Table 1
(eval/datasets.py), Table 3 (eval/dna_reef_bora.py), and Table 4
(eval/gen_zombie_table.py), so the numbers cannot drift from those tables:

  Zombie (all)  -- unit cost u (zombie_totals) * corpus * regex set, exactly
                   as tab:compare-zombie-bora projects it.
  Reef Dna      -- parse_reef_log (Table 3's own parser): Estimate1 (as-impl,
                   sum of count*mean) and Estimate2 (count*min_mean floor).
  Reef Mal/Dlp  -- optimistic projection: Reef's cheapest measured per-run cost
                   on Dna (min bucket mean = the proj_512k floor, same value as
                   Table 3's Estimate2 floor) * rule count * corpus length.
  BORA Mal/Dna  -- bora_cost_breakdown (net = 8-job sum for Mal, single for Dna;
                   wall = slowest job).

Cells with no audited source yet are emitted as ``??`` by returning None from
the corresponding cost function (currently none -- all three datasets have a
BORA dump; Dlp temporarily reuses the full_dna run while its real dump
regenerates on the server).

Reads (server-specific files under data/raw_data/<SERVER_TO_USE>/):
  run_zombie_regex_zombie_international.log
  reef_sample_run.log
  full_clam.tgz   (8-job full ClamAV)
  full_dna.tgz    (single-job full DNA)
  full_dlp.tgz    (Dlp; currently a copy of the full_dna run)
  + dataset corpora / regex sets via the common extractors (same as tab:datasets)

Writes:
  <paper_root>/figs/compare_all.tex
"""

from __future__ import annotations

import sys
from pathlib import Path

# common.py lives in the parent scripts/ directory; dna_reef_bora.py is a
# sibling in this eval/ directory (we reuse its Reef-log parser verbatim).
_HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(_HERE.parent))
sys.path.insert(0, str(_HERE))
from common import (get_paper_root, zombie_totals, zombie_regex_bytes,
                    dataset_corpus_bytes, dataset_rule_count,
                    bora_cost_breakdown, resolve_server_dump, server_file)
from dna_reef_bora import parse_reef_log, BUCKETS


# ----------------------------- configuration -----------------------------

UNIT_STR_LEN = 2000   # Zombie unit cost taken at 2k (~ BORA folding step size)

# Server-specific run logs / dumps (resolved via SERVER_TO_USE).
ZOMBIE_LOG = "run_zombie_regex_zombie_international.log"
REEF_LOG = "reef_sample_run.log"

PLACEHOLDER = "??"

# (row label, dataset key, BORA dump filename | None if no BORA data yet).
# Dlp temporarily reuses the full_dna run (the real Dlp dump is regenerating on
# the server); full_dlp.tgz currently holds full_dna data -- see
# check_data_server.py's task-name check, which flags this.
DATASETS = [
    ("\\textsc{Mal}", "mal", "full_clam.tgz"),
    ("\\textsc{Dna}", "dna", "full_dna.tgz"),
    ("\\textsc{Dlp}", "dlp", "full_dlp.tgz"),
]


# ------------------------------- formatting ------------------------------

def fmt_human(seconds: float) -> str:
    """Compact wall-clock label (min / hr / d / yr) -- matches the sibling
    generators so Zombie/Reef cells read the same as Tables 3 and 4."""
    if seconds < 3600:
        return f"{seconds / 60:.1f}\\,min"
    if seconds < 86400 * 2:
        return f"{seconds / 3600:.2f}\\,hr"
    if seconds < 86400 * 730:
        return f"{seconds / 86400:.1f}\\,d"
    yr = seconds / 31557600
    if yr >= 1e6:
        return f"{yr / 1e6:.1f}\\,Myr"
    if yr >= 1e4:
        return f"{yr:,.0f}".replace(",", "{,}") + r"\,yr"
    return f"{yr:.1f}\\,yr"


def fmt_hr(seconds: float) -> str:
    """BORA cells are always shown in hours (net compute, not wall-clock time),
    as in tab:compare-zombie-bora -- e.g. 344.95 hr for the 8-job Mal sum."""
    return f"{seconds / 3600:.2f}\\,hr"


def fmt_speed(x: float) -> str:
    """Speedup factor as a ``$...$`` cell. Small factors get LaTeX thousands
    separators (``$4{,}241\\times$``); large ones use an M/B suffix
    (``$125\\text{M}\\times$``) so the cell stays compact."""
    if x >= 1e9:
        return f"${x / 1e9:,.0f}".replace(",", "{,}") + r"\text{B}\times$"
    if x >= 1e6:
        return f"${x / 1e6:,.0f}".replace(",", "{,}") + r"\text{M}\times$"
    return f"${x:,.0f}".replace(",", "{,}") + r"\times$"


def star(cell: str) -> str:
    """Append a projection marker $^{*}$ inside a ``$...$`` math cell."""
    return cell[:-1] + r"^{*}$"


def fmt_sci(x: float, sig: int = 2) -> str:
    """Format ``x`` as ``a \\times 10^{b}`` (no surrounding $), for the caption
    unit cost -- mirrors the sibling generators' fmt_sci."""
    exp = int(f"{x:.6e}".split("e")[1])
    mant = x / (10 ** exp)
    return f"{mant:.{sig}f} \\times 10^{{{exp}}}"


# ------------------------------- cost cells ------------------------------
# Each function returns seconds (or a dict of seconds), or None when there is
# no audited source -- None renders as ``??``.

def zombie_cost(key: str, unit: float) -> float:
    """Projected Zombie cost (s): unit u * corpus bytes * regex-set bytes.
    Reuses the SAME extractors as tab:compare-zombie-bora."""
    return unit * dataset_corpus_bytes(key) * zombie_regex_bytes(key)


def reef_data() -> dict:
    """Parse the Reef Dna log once (Table 3's parser) and derive the values
    reused across rows: the measured Dna Estimate1/Estimate2 and the cheapest
    per-run cost (min bucket mean = the proj_512k floor) that drives the
    Mal/Dlp projection."""
    b = parse_reef_log(server_file(REEF_LOG))
    count = sum(b[k]["count"] for k in BUCKETS)
    min_step = min(b[k]["mean"] for k in BUCKETS)
    return {
        "min_step": min_step,                                  # s, proj_512k floor
        "dna_e1": sum(b[k]["count"] * b[k]["mean"] for k in BUCKETS),
        "dna_e2": count * min_step,
    }


def reef_cost(key: str, rd: dict) -> dict:
    """Reef cost for a dataset.

    Dna is measured -> {'kind': 'measured', 'e1':.., 'e2':..}. Mal/Dlp have no
    measured Reef run, so they are projected optimistically as the cheapest
    measured Dna per-run cost (rd['min_step']) times the rule count times the
    corpus length -> {'kind': 'projected', 'value':..}. All three sub-values
    (corpus, rule count, min_step) come from the same extractors as Tables 1/3.
    """
    if key == "dna":
        return {"kind": "measured", "e1": rd["dna_e1"], "e2": rd["dna_e2"]}
    value = rd["min_step"] * dataset_rule_count(key) * dataset_corpus_bytes(key)
    return {"kind": "projected", "value": value}


def bora_cost(key: str, dump: str | None) -> dict | None:
    """BORA net/wall cost for a dataset, or None if no run yet.

    Returns the bora_cost_breakdown dict {n_jobs, net, wall} (seconds) when a
    dump exists; None for datasets without a BORA run (currently Dlp).
    """
    if dump is not None:
        return bora_cost_breakdown(resolve_server_dump(dump))
    return _bora_cost_dlp(key)


def _bora_cost_dlp(key: str) -> dict | None:
    """BORA cost on Dlp -- UNKNOWN (no BORA DLP run yet).

    Fill in once the run lands: return bora_cost_breakdown(<dlp dump>). Left
    empty so the BORA \\textsc{Dlp} cell (and its two speedups) render ``??``.
    """
    return None


# ------------------------------ row rendering ----------------------------

def render_row(label: str, key: str, dump: str | None, unit: float,
               rd: dict, notes: list) -> str:
    """Render one table row; append any caption notes (e.g. the Mal job sum)."""
    z = zombie_cost(key, unit)
    r = reef_cost(key, rd)
    b = bora_cost(key, dump)

    z_cell = fmt_human(z)

    if r["kind"] == "measured":
        r_cell = f"{fmt_human(r['e1'])} ({fmt_human(r['e2'])}$^{{*}}$)"
    else:
        r_cell = f"{fmt_human(r['value'])}$^{{*}}$"

    if b is not None:
        b_cell = fmt_hr(b["net"])
        if b["n_jobs"] > 1:
            notes.append((label, b["n_jobs"], b["wall"] / 3600))
    else:
        b_cell = PLACEHOLDER

    # Speedup vs Zombie: Est. Zombie / BORA net.
    vz_cell = fmt_speed(z / b["net"]) if b is not None else PLACEHOLDER

    # Speedup vs Reef: Reef cost / BORA net (Estimate1 with the Estimate2 floor
    # in parens for the measured Dna row; single projected factor otherwise).
    if b is not None:
        if r["kind"] == "measured":
            vr_cell = (f"{fmt_speed(r['e1'] / b['net'])} "
                       f"({star(fmt_speed(r['e2'] / b['net']))})")
        else:
            vr_cell = star(fmt_speed(r["value"] / b["net"]))
    else:
        vr_cell = PLACEHOLDER

    return (f"    {label} & {z_cell} & {r_cell} & {b_cell} "
            f"& {vz_cell} & {vr_cell} \\\\")


# ------------------------------- table build -----------------------------

def fmt_job_note(notes: list) -> str:
    """Fold the per-dataset multi-job notes into one sentence.

    This caption rides a full-width float at the top of a page, so every
    line it costs is two lines of body text against the 13-page limit.
    Datasets with differing job counts fall back to one sentence each,
    since a single sentence cannot then state the count unambiguously.
    Wall-clock time (notes[*][2]) is computed but not printed here since
    it is not one of the table's columns.
    """
    if not notes:
        return ""
    if len({n for _, n, _ in notes}) != 1:
        return "".join(
            f" {lab} BORA is the total net cost summed over ${n}$ parallel"
            f" jobs."
            for lab, n, _ in notes)
    n_jobs = notes[0][1]
    if len(notes) == 1:
        lab = notes[0][0]
        return (f" {lab} BORA is the total net cost summed over ${n_jobs}$"
                f" parallel jobs.")
    labs = ", ".join(lab for lab, _, _ in notes[:-1]) + f" and {notes[-1][0]}"
    return (f" {labs} BORA costs are net totals summed over ${n_jobs}$"
            f" parallel jobs.")


def build_table(unit: float, rd: dict) -> str:
    notes: list = []
    rows = [render_row(label, key, dump, unit, rd, notes)
            for (label, key, dump) in DATASETS]
    note_tex = fmt_job_note(notes)
    # Only explain the placeholder when one is actually rendered.
    ph_tex = (r""" Cells shown as ``""" + PLACEHOLDER + r"""'' have no
  audited measurement yet.""") if any(PLACEHOLDER in r for r in rows) else ""
    unit_str = fmt_sci(unit, sig=4)

    return r"""% Auto-generated by data/scripts/eval/gen_compare_all.py -- do not edit by hand.
% Consolidated Zombie / Reef / BORA comparison across all three datasets,
% keyed by tag to tab:datasets (no size columns, to avoid overlap). Replaces
% the main-body role of tab:compare-zombie-bora.
%
% Provenance (all cells reuse the Table 1/3/4 extractors -- see module docstring):
%   Zombie (all):  u (zombie_totals @ """ + f"{UNIT_STR_LEN}" + r""" B) * corpus * regex set.
%   Reef Dna:      parse_reef_log -- Estimate1 (as-impl) / Estimate2 (floor).
%   Reef Mal/Dlp:  cheapest measured Dna per-run cost * rule count * corpus.
%   BORA all:      bora_cost_breakdown net (8-job sum / single); wall = slowest.
%                  Dlp temporarily reuses the full_dna run (real dump pending).
\begin{table*}[t]
  \centering
  \small
  \caption{End-to-end prover cost of Zombie~\cite{Zombie23},
  Reef~\cite{Reef}, and BORA on the three datasets of
  Table~\ref{tab:datasets}. Zombie costs are projected from the unit cost
  $u=""" + unit_str + r"""$~s\,B$^{-2}$ (Table~\ref{tab:zombie-data}).
  Values marked $^{*}$ are projected from Reef's cheapest measured
  per-run cost on \textsc{Dna} ($""" + f"{rd['min_step']:.2f}" + r"""$\,s, the \texttt{proj\_512k}
  bucket): the \textsc{Dna} floor as that cost per signature, and Reef
  \textsc{Mal}/\textsc{Dlp} as that cost per signature per corpus byte
  (Table~\ref{tab:dna-reef-bora}); the \textsc{Dna} cells pair Reef's
  as-implemented cost with that floor in parentheses.""" \
        + note_tex + ph_tex + r"""}
  \label{tab:compare-all}
  \begin{tabular}{l r r r r r}
    \toprule
    Dataset & Zombie & Reef & BORA
      & \multicolumn{2}{c}{Speedup} \\
    \cmidrule(lr){5-6}
    & & & & vs Zombie & vs Reef \\
    \midrule
""" + "\n".join(rows) + r"""
    \bottomrule
  \end{tabular}
\end{table*}
"""


# --------------------------------- main ----------------------------------

def main() -> None:
    root = get_paper_root()
    figs = root / "figs"
    figs.mkdir(exist_ok=True)

    unit = zombie_totals(server_file(ZOMBIE_LOG), UNIT_STR_LEN)["unit_cost"]
    rd = reef_data()

    out = figs / "compare_all.tex"
    out.write_text(build_table(unit, rd))
    print(f"wrote {out}")


if __name__ == "__main__":
    main()
