#!/usr/bin/env python3
# ----------------------------------
# Designed by the paper author; function implementation by Claude Code 4.8.
# Code reviewed and audited by the author; the generated table was manually
# verified by the paper author.
# ----------------------------------
"""Generate the lookup-table composition table for §7.4 (tab:lkup).

Reads:
  <paper_root>/data/raw_data/any_server/lookup_stats.dat -- the
  collect_lookup_stats report (per-dataset per-source lookup breakdown;
  Mal/Dna/Dlp blocks).

Writes:
  <paper_root>/figs/lookup.tex -- a self-contained booktabs table: the five
  lookup categories x three datasets, each cell = entries (millions) and %
  of that dataset's populated entries, plus a TOTAL row (entries only; the
  table capacity varies per dataset, so no %-of-capacity is shown) and a
  #signatures row.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

# common.py lives in the parent scripts/ directory.
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from common import get_paper_root, any_server_file

DATASETS = ["Mal", "Dna", "Dlp"]    # column order (matches §7.6 stubs)

# Per-dataset correction to the reported #signatures. Dna's sig DB carries one
# extra alphabet/helper rule that is not a disease variant, so subtract 1.
SIG_ADJUST = {"Dna": -1}

# category -> (LaTeX component label, purpose blurb). Order = table rows.
CATS = [
    ("range",      r"range table$^\dagger$", "range proof e.g. for pattern distance"),
    ("AC-DFA(CP)", r"AC-DFA / CP",           "transition rules"),
    # The SDE block is dominated (~98%) by the bag-of-words AC-DFA over all
    # subsig keywords (add_bundle_subsig_to_lkup -> add_acdfa_to_lkup, ~18
    # entries/state x 6.4M states for Mal); the step/info stores are a sliver.
    ("SDE",        r"SDE",                   "subsig keyword AC-DFA + step distance bounds"),
    ("DFA",        r"DFA",                   "transition rules"),
    ("sig-DB",     r"sig-DB",                "DNF combinations / tri-logic truth table"),
]
CAT_KEYS = {c[0] for c in CATS}

# a source row: "  <cat> <source> <entries> <pct>"
_ROW = re.compile(r"^\s+(\S+)\s+(\w+)\s+(\d+)\s+[\d.]+\s*$")
_HDR = re.compile(r"Lookup Composition:\s+(\w+)")
_SIG = re.compile(r"#sigs\s*:\s*(\d+)\s+range2_bit\s*:\s*(\d+)")
# "#DFAs in lkup: 45 (... | sig_dfa 35)" -- count of per-subsig DFAs folded
# into the lookup (the DFA / hard-rule tier). Zero for Dna/Dlp.
_NDFA = re.compile(r"sig_dfa\s+(\d+)")


def parse(dump: str) -> dict[str, dict]:
    """Return {dataset: {'cat': {name: entries}, 'sigs', 'r2', 'ndfa'}}."""
    out: dict[str, dict] = {}
    cur = None
    for line in dump.splitlines():
        h = _HDR.search(line)
        if h:
            cur = h.group(1)
            out[cur] = {"cat": {k: 0 for k in CAT_KEYS}, "sigs": 0, "r2": 0,
                        "ndfa": 0}
            continue
        if cur is None:
            continue
        s = _SIG.search(line)
        if s:
            out[cur]["sigs"] = int(s.group(1))
            out[cur]["r2"] = int(s.group(2))
            continue
        if "#DFAs in lkup" in line:
            d = _NDFA.search(line)
            if d:
                out[cur]["ndfa"] = int(d.group(1))
            continue
        m = _ROW.match(line)
        if m and m.group(1) in CAT_KEYS:
            out[cur]["cat"][m.group(1)] += int(m.group(3))
    # sanity: every dataset must be present with a non-zero total.
    for d in DATASETS:
        if d not in out or sum(out[d]["cat"].values()) == 0:
            raise RuntimeError(f"parse: missing/empty block for {d}")
    return out


def _m(n: int) -> str:       # entries -> millions, 1 decimal
    return f"{n / 1e6:.1f}"


def _pct(n: int, tot: int) -> str:
    return f"{100.0 * n / tot:.1f}" if tot else "0.0"


def build_table(data: dict[str, dict]) -> str:
    tot = {d: sum(data[d]["cat"].values()) for d in DATASETS}

    # DFA row label carries the per-dataset count of folded per-subsig DFAs
    # (Mal/Dna/Dlp), so column 1 reads e.g. "DFA (35/0/0)".
    ndfa = "/".join(str(data[d]["ndfa"]) for d in DATASETS)

    rows = []
    for key, label, purpose in CATS:
        if key == "DFA":
            label = f"{label} ({ndfa})"
        body = " & ".join(
            f"{_m(data[d]['cat'][key])} & {_pct(data[d]['cat'][key], tot[d])}"
            for d in DATASETS)
        rows.append(f"{label} & {purpose} & {body} \\\\")

    # entries only -- the table capacity varies per dataset, so a
    # %-of-capacity figure would be misleading.
    total_row = "TOTAL populated & & " + " & ".join(
        f"\\multicolumn{{2}}{{c}}{{{_m(tot[d])}}}" for d in DATASETS) + r" \\"
    sig_row = r"\#signatures & & " + " & ".join(
        f"\\multicolumn{{2}}{{c}}{{{data[d]['sigs'] + SIG_ADJUST.get(d, 0):,}}}"
        for d in DATASETS) + r" \\"
    r2 = " / ".join(str(data[d]["r2"]) for d in DATASETS)

    return "\n".join([
        # table* spans both columns; such floats cannot be [H]-pinned, so
        # [t] floats it to a page top near §7.4 (the paper preamble loads
        # stfloats, which also permits [b]).
        r"\begin{table*}[t]",
        r"\centering",
        r"\small",
        r"\setlength{\tabcolsep}{4pt}",
        r"\begin{tabular}{@{}ll rr rr rr@{}}",
        r"\toprule",
        r" & & \multicolumn{2}{c}{\textsc{Mal}} & "
        r"\multicolumn{2}{c}{\textsc{Dna}} & \multicolumn{2}{c}{\textsc{Dlp}} \\",
        r"\cmidrule(lr){3-4}\cmidrule(lr){5-6}\cmidrule(lr){7-8}",
        r"Component & Purpose & M & \% & M & \% & M & \% \\",
        r"\midrule",
        *rows,
        r"\midrule",
        total_row,
        sig_row,
        r"\bottomrule",
        r"\end{tabular}",
        r"\caption{Lookup-table composition across datasets. Column "
        r"\emph{M} is millions of entries. Each \% is of "
        r"that dataset's populated entries. "
        r"$^\dagger$range table $=2^{\text{range2\_bit}}$ "
        f"({r2} for \\textsc{{Mal}}/\\textsc{{Dna}}/\\textsc{{Dlp}}), sized by "
        r"the maximum document offset. The "
        r"$(\cdot/\cdot/\cdot)$ after \emph{DFA} is the number of "
        r"DFAs folded in for rules that frequently fail SDE, per dataset.",
        r"BORA re-writes \ttt{(kw1|...kwn).\{0,N\}pat} in \textsc{Dlp} to "
        r"disjunction of $n$ rules for improved SDE accuracy, thus expanding from $136$ to $9861$.}",
        r"\label{tbl:lkup}",
        r"\end{table*}",
        "",
    ])


def main() -> None:
    root = get_paper_root()
    dump = any_server_file("lookup_stats.dat").read_text()
    out = root / "figs" / "lookup.tex"
    out.write_text(build_table(parse(dump)))
    print(f"wrote {out}")


if __name__ == "__main__":
    main()
