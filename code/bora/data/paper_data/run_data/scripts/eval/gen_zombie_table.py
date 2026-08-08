#!/usr/bin/env python3
# ----------------------------------
# Designed by the paper author; function implementation by Claude Code 4.8.
# Code reviewed and audited by the author; the generated tables were manually
# verified by the paper author.
# ----------------------------------
"""Generate the two Zombie tables for section 7.7 (Zombie comparison).

Reads (server-specific files under data/raw_data/<SERVER_TO_USE>/):
  run_zombie_regex_zombie_international.log
  full_clam.tgz   (8-job full ClamAV)
  full_dna.tgz    (single-job full DNA)
  full_dlp.tgz    (Dlp; currently a copy of the full_dna run)
  + the dataset corpora / regex sets via the common extractors (same sources
    as eval/datasets.py, so the sizes agree with tab:datasets).

Writes:
  <paper_root>/figs/zombie_data.tex          (Table A: Zombie measured totals)
  <paper_root>/figs/compare_zombie_bora.tex  (Table B: projection vs BORA)
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

# common.py lives in the parent scripts/ directory.
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from common import (get_paper_root, zombie_totals, zombie_regex_bytes,
                    dataset_corpus_bytes, bora_cost_breakdown,
                    resolve_server_dump, server_file)


# ----------------------------- configuration -----------------------------

# Table A's rows are DATA-DRIVEN (see _detect_str_lens): a real full run
# writes the log with VEC_SIZE=[1000,2000,4000], but a dry-run sweep
# (dry_run_zombie.py) uses a smaller VEC_SIZE like [700,800,1000] -- this
# reads whichever lengths are actually in the log, not a hardcoded guess.
UNIT_STR_LEN = 2000   # unit cost taken at 2k (~ BORA folding step size);
                       # ALWAYS shown/used even on a dry-run log lacking a
                       # real 2000B block (interpolated from 1000B then --
                       # see _linear_interp).

_STR_LEN_HDR = re.compile(r"== STR_LENGTH = (\d+) ==")


def _detect_str_lens(log_file) -> list:
    """Every STR_LENGTH this log has a real block for, sorted ascending."""
    text = Path(log_file).read_text()
    lens = sorted({int(m.group(1)) for m in _STR_LEN_HDR.finditer(text)})
    if not lens:
        raise RuntimeError(f"{log_file}: no STR_LENGTH blocks found")
    return lens


ZOMBIE_LOG = "run_zombie_regex_zombie_international.log"  # server-specific

# (label, dataset key, BORA dump filename | None if no BORA data yet).
# Server-specific dumps, resolved via SERVER_TO_USE. Dlp temporarily reuses the
# full_dna run (real Dlp dump regenerating on the server); full_dlp.tgz holds
# full_dna data for now -- check_data_server.py's task-name check flags this.
DATASETS = [
    ("\\textsc{Mal} (ClamAV)", "mal", "full_clam.tgz"),
    ("\\textsc{Dna} (chr17)",  "dna", "full_dna.tgz"),
    ("\\textsc{Dlp} (Enron)",  "dlp", "full_dlp.tgz"),
]


# ---------------------------- formatting ---------------------------------

def fmt_sci(x: float, sig: int = 2) -> str:
    """Format ``x`` as $a \\times 10^{b}$ in LaTeX math mode."""
    if x == 0:
        return "$0$"
    exp = int(f"{x:.6e}".split("e")[1])
    mant = x / (10 ** exp)
    return f"${mant:.{sig}f} \\times 10^{{{exp}}}$"


def fmt_human(seconds: float) -> str:
    """Compact wall-clock label (min / hr / d / yr)."""
    if seconds < 3600:
        return f"{seconds / 60:.1f}\\,min"
    if seconds < 86400 * 2:
        return f"{seconds / 3600:.2f}\\,hr"
    if seconds < 86400 * 730:
        return f"{seconds / 86400:.1f}\\,d"
    return f"{seconds / 31557600:.1f}\\,yr"


def fmt_bytes(n: int) -> str:
    """Compact byte size label (KB / MB / GB), decimal units."""
    if n < 1e6:
        return f"{n / 1e3:.1f}\\,KB"
    if n < 1e9:
        return f"{n / 1e6:.1f}\\,MB"
    return f"{n / 1e9:.2f}\\,GB"


# --------------------------- Table A: Zombie -----------------------------

def build_table_a(rows: list) -> str:
    """Zombie measured totals per string length + derived unit cost.
    Rows flagged ``interpolated`` (see _linear_interp) get a dagger mark
    and the caption grows an explanatory note."""
    regex_total = rows[0]["total_regex_bytes"]   # constant across blocks
    any_interp = any(r.get("interpolated") for r in rows)

    body = []
    for r in rows:
        mark = r"$^\dagger$" if r.get("interpolated") else ""
        body.append(
            f"    {r['str_len']:,}{mark} & {r['total_r1cs']:,} & "
            f"{r['total_prove_s']:.1f} & {r['total_verify_s']:.1f} & "
            f"{r['total_proof_bytes'] / 1e6:.2f} \\\\"
        )

    units = " / ".join(fmt_sci(r["unit_cost"]) for r in rows)
    lens = " / ".join(f"{r['str_len']:,}" for r in rows)

    interp_note = ""
    if any_interp:
        interp_note = r""" Rows marked $^\dagger$ have no real
  measurement at that length in this log (e.g.\ a dry-run sweep with a
  smaller \texttt{VEC\_SIZE}) -- all four totals are linearly
  interpolated from the 1{,}000\,B row, under a linear-growth
  assumption matching Zombie's per-byte circuit complexity; treat them
  as illustrative, not measured."""

    return r"""% Auto-generated by data/scripts/eval/gen_zombie_table.py
% Source: data/raw_data/""" + ZOMBIE_LOG + r"""
%
% Per-block totals over all 'ok' international SIT regex instances. The unit cost
% u = (total prove time) / (L_T * total regex bytes) is the price of one
% input-byte x one regex-byte; it is reused in tab:compare-zombie-bora to
% project the full Mal/Dna/Dlp corpora. Rows are whichever STR_LENGTHs are
% actually in the log (see _detect_str_lens); if UNIT_STR_LEN=2000 isn't
% among them (e.g. a dry-run sweep), it's linearly interpolated from the
% 1000B row -- see _linear_interp() -- and marked with a dagger.
\begin{table*}[t]
  \centering
  \small
  \caption{Zombie prover cost on the MS-DLP international SIT rules
  (Spartan NIZK, two-pattern proximity circuit), totalled over all
  """ + f"{rows[0]['n']}" + r""" regex instances (the """ + \
        f"{rows[0]['n_rules']}" + r""" \textsc{Sit} rules of
  Table~\ref{tab:datasets}, expanded into their comb variants) at each
  scanned document length $L_T$. The total regex size (sum of pattern $+$
  keyword bytes over all instances, each sub-pattern counted once) is fixed
  at """ + f"{regex_total:,}" + r"""\,B. The last row
  derives the unit cost $u = t_{\text{prove}} / (L_T \cdot \sum s)$ in seconds
  per (input-byte $\times$ regex-byte).""" + interp_note + r"""}
  \label{tab:zombie-data}
  \begin{tabular}{r r r r r}
    \toprule
    $L_T$ (B) & Total constraints & Prove (s) & Verify (s) & Proof (MB) \\
    \midrule
""" + "\n".join(body) + r"""
    \midrule
    \multicolumn{5}{l}{Unit $u = t/(L_T\cdot\sum s)$ at $L_T=""" + \
        f"{lens}" + r"""$: $""" + units.replace("$", "") + \
        r"""$ s\,B$^{-2}$} \\
    \bottomrule
  \end{tabular}
\end{table*}
"""


# ------------------------ Table B: project vs BORA -----------------------

def build_table_b(unit: float, rows: list,
                   unit_interpolated: bool = False) -> str:
    """Project the Zombie unit cost across datasets and compare with BORA.
    ``unit_interpolated`` flags that ``unit`` itself came from a
    linearly-interpolated row (see build_table_a), not a real
    measurement at UNIT_STR_LEN."""
    body = []
    notes = []
    if unit_interpolated:
        notes.append(
            r"$\bar u$ itself is linearly interpolated (see "
            r"Table~\ref{tab:zombie-data}'s $\dagger$ note): this log has "
            r"no real measurement at $L_T=" + f"{UNIT_STR_LEN:,}" +
            r"$, e.g.\ a dry-run sweep.")
    for label, key, dump in rows:
        corpus = dataset_corpus_bytes(key)
        regex = zombie_regex_bytes(key)
        est = unit * corpus * regex
        if dump is not None:
            b = bora_cost_breakdown(resolve_server_dump(dump))
            bora_cell = f"{fmt_sci(b['net'])} ({b['net'] / 3600:.2f}\\,hr)"
            speed = f"$\\approx {est / b['net']:,.0f}\\times$"
            if b["n_jobs"] > 1:
                notes.append(
                    f"The {label} BORA cost ${b['net'] / 3600:.2f}$\\,hr is the "
                    f"total over its ${b['n_jobs']}$ parallel jobs; the "
                    f"wall-clock time is ${b['wall'] / 3600:.2f}$\\,hr (the "
                    f"slowest job)."
                )
        else:
            bora_cell = "--- (no data)"
            speed = "---"
        body.append(
            f"    {label} & {fmt_bytes(corpus)} & {fmt_bytes(regex)} & "
            f"{fmt_sci(est)} ({fmt_human(est)}) & {bora_cell} & {speed} \\\\"
        )

    note_tex = (" " + " ".join(notes)) if notes else ""

    return r"""% Auto-generated by data/scripts/eval/gen_zombie_table.py
% Sources (server-specific, under data/raw_data/<SERVER_TO_USE>/):
%   full_clam.tgz  (BORA full ClamAV, 8-job sum)
%   full_dna.tgz   (BORA full DNA, single job)
%   full_dlp.tgz   (BORA Dlp; currently a copy of the full_dna run)
%   dataset corpus + regex sizes via common extractors (same as tab:datasets)
%
% Est. Zombie = u * (corpus bytes) * (regex-set bytes), the full doc x regex
% cross product, with u the """ + f"{UNIT_STR_LEN}" + r"""-byte unit cost from
% tab:zombie-data (closest to BORA's folding step size). This UNDER-estimates
% Zombie at MB-scale documents (Spartan prove is super-linear in constraints),
% so it is charitable to Zombie. BORA = phase-1 main-circuit folding net
% (bora_net_cost): single-job DNA, 8-job sum for ClamAV. Dlp temporarily
% reuses the full_dna run (its real dump is regenerating on the server).
\begin{table*}[t]
  \centering
  \small
  \caption{Projected Zombie cost (unit $\bar u =
  """ + fmt_sci(unit).replace("$", "") + r"""$ s\,B$^{-2}$, taken at $L_T=""" + \
        f"{UNIT_STR_LEN:,}" + r"""$) vs.\ BORA's net main-circuit folding
  cost. $\text{Est.\ Zombie} = \bar u \cdot (\text{corpus})\cdot
  (\text{regex set})$, a full document~$\times$~regex cross product. Regex-set
  size is on-disk rule-file bytes for \textsc{Mal}/\textsc{Dna}; for
  \textsc{Dlp} it is the pattern$+$keyword bytes fed to the circuit (the
  on-disk \texttt{.regex} doubles each sub-pattern for the bidirectional
  proximity form).""" + note_tex + r"""}
  \label{tab:compare-zombie-bora}
  \begin{tabular}{l r r r r r}
    \toprule
    Dataset & Corpus & Regex set & Est.\ Zombie & BORA (net) & Speedup \\
    \midrule
""" + "\n".join(body) + r"""
    \bottomrule
  \end{tabular}
\end{table*}
"""


def _linear_interp(base: dict, target_len: int) -> dict:
    """Build a str_len=target_len row from ``base`` by scaling every raw
    total by target_len/base['str_len'], under a linear-growth
    assumption (matches Zombie's per-byte circuit complexity). Used
    ONLY as a fallback when the log has no real block for target_len --
    e.g. a dry-run sweep whose VEC_SIZE doesn't cover the real
    [1000,2000,4000]. unit_cost is left as base's: since prove_s and
    str_len scale by the same factor, u = prove_s/(str_len*regex) is
    exactly invariant under this assumption, not merely approximated."""
    factor = target_len / base["str_len"]
    return {
        "str_len": target_len,
        "n": base["n"],
        "n_rules": base["n_rules"],
        "total_regex_bytes": base["total_regex_bytes"],
        "total_r1cs": round(base["total_r1cs"] * factor),
        "total_prove_s": base["total_prove_s"] * factor,
        "total_verify_s": base["total_verify_s"] * factor,
        "total_proof_bytes": round(base["total_proof_bytes"] * factor),
        "unit_cost": base["unit_cost"],
        "interpolated": True,
    }


# --------------------------------- main ----------------------------------

def main() -> None:
    root = get_paper_root()
    figs = root / "figs"
    figs.mkdir(exist_ok=True)

    log = server_file(ZOMBIE_LOG)
    lens = _detect_str_lens(log)   # real e.g. [1000,2000,4000], or a
                                    # dry-run's e.g. [700,800,1000]
    zrows = [zombie_totals(log, n) for n in lens]

    unit_row = next((r for r in zrows if r["str_len"] == UNIT_STR_LEN), None)
    if unit_row is None:
        # UNIT_STR_LEN has no real block (e.g. this dry-run's smaller
        # VEC_SIZE) -- BORA's projection still needs a value at exactly
        # this length, so interpolate from the 1000B row specifically
        # (both real and dry-run logs always measure 1000B).
        base = next(r for r in zrows if r["str_len"] == 1000)
        unit_row = _linear_interp(base, UNIT_STR_LEN)
        zrows = sorted(zrows + [unit_row], key=lambda r: r["str_len"])
    unit = unit_row["unit_cost"]

    (figs / "zombie_data.tex").write_text(build_table_a(zrows))
    print(f"wrote {figs / 'zombie_data.tex'}")

    (figs / "compare_zombie_bora.tex").write_text(build_table_b(
        unit, DATASETS, unit_interpolated=unit_row.get("interpolated", False)))
    print(f"wrote {figs / 'compare_zombie_bora.tex'}")


if __name__ == "__main__":
    main()
