#!/usr/bin/env python3
# ----------------------------------
# Designed by the paper author; function implementation by Claude Code 4.8.
# Code reviewed and audited by the author; the generated figure was manually
# verified by the paper author.
# ----------------------------------
"""Generate the data fragments for the §6.3 approximation-effectiveness tables.

Reads:
  <paper_root>/data/raw_data/any_server/eval_effective.txt -- the tier-discharge
  dump from collect_assess_tier_data() in zkregplus/src/zkp_driver.rs.

Writes:
  <paper_root>/figs/effectiveness_tab.tex       -- Table 2 body: pair-level
                                                   (Mal/Dna/Dlp), 3 rows
  <paper_root>/figs/effectiveness_size.tex      -- Table 5 body: Mal by size,
                                                   4 merged rows
  <paper_root>/figs/effectiveness_size_dlp.tex  -- Table 6 body: Dlp by size,
                                                   4 merged rows
The Table 2 body is \\input by figs/fig_effectiveness.fig; the two by-size
bodies moved to the appendix and are \\input by src/apdx_eval_data.tex
(layout + captions hand-kept in both).

The per-bucket lines carry raw tier *counts* ("cp: <count> (<pct>%)"), so the
size tables merge buckets by summing counts and recomputing the percentages
(NOT by averaging per-bucket percentages, which would mis-weight the sparse
large-file buckets).
"""
from __future__ import annotations

import re
import sys
from pathlib import Path

# common.py lives in the parent scripts/ directory.
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from common import get_paper_root, any_server_file

ORDER = ["Mal", "Dna", "Dlp"]
TIERS = ("cp", "sde", "dfa", "fail")


# ------------------------------ parsing ----------------------------------
def _pct(line: str, key: str) -> float:
    """Read the percentage from a 'key: N (P%)' field."""
    return float(re.search(rf"{key}: \d+ \(([\d.]+)%\)", line).group(1))


def _count(line: str, key: str) -> int:
    """Read the raw integer count from a 'key: N (P%)' field."""
    return int(re.search(rf"{key}: (\d+) \(", line).group(1))


def parse(dump: str):
    """Return (datasets, size_buckets).

    datasets:     {label: {pairs, files, total_sigs, cp.., <tier>_n, <tier>}}
                  where <tier> is the percentage and <tier>_n the raw count.
    size_buckets: {label: [bucket, ...]} for Mal and Dlp, each bucket
                  {flen, files, total_sigs, <tier>_n, <tier>}, sorted by flen.
    """
    datasets: dict = {}
    size_buckets: dict = {"Mal": [], "Dlp": []}
    cur = None            # ("ds", label) | ("bk", label, flen)
    files = total_sigs = 0
    for ln in dump.splitlines():
        if m := re.match(r"=== Data for (\w+) ===", ln):
            cur = ("ds", m.group(1))
        elif m := re.match(r"=== Filesize data for (\w+) -- flen=(\d+)", ln):
            cur = ("bk", m.group(1), int(m.group(2)))
        elif ln.startswith("total_sigs:") and cur:
            total_sigs = int(re.search(r"total_sigs: (\d+)", ln).group(1))
            files = int(re.search(r"files: (\d+)", ln).group(1))
            if cur[0] == "ds":
                datasets[cur[1]] = {
                    "pairs": int(re.search(r"total_pairs: (\d+)", ln).group(1)),
                    "files": files, "total_sigs": total_sigs}
        elif ln.startswith("cp: ") and cur:
            pcts = {k: _pct(ln, k) for k in TIERS}
            cnts = {f"{k}_n": _count(ln, k) for k in TIERS}
            if cur[0] == "ds":
                datasets[cur[1]].update(pcts | cnts)
            else:
                size_buckets[cur[1]].append(
                    {"flen": cur[2], "files": files, "total_sigs": total_sigs,
                     **pcts, **cnts})
            cur = None
    for label in size_buckets:
        size_buckets[label].sort(key=lambda b: b["flen"])
    return datasets, size_buckets


# ---------------------------- merging ------------------------------------
def merge_to_4(buckets: list) -> list:
    """Group the sorted flen buckets into 4 contiguous bins on the log-size
    axis, choosing bin boundaries so each bin holds a roughly equal *file
    count* (not an equal count of flen buckets), summing raw tier counts and
    recomputing percentages from the merged totals.

    File counts are extremely skewed across flen buckets (a handful of
    large-file buckets can hold single-digit file counts), so splitting by
    equal number of flen buckets leaves the tail bins backed by only a few
    dozen files -- too little data for their percentages to be meaningful,
    which manifests as sampling noise (e.g. a percentage that bounces back up
    a bin before resuming its trend). Splitting by cumulative file count
    keeps every bin's sample size comparable and the reported trend
    representative of the underlying data instead of small-sample noise.

    Returns [{flen_lo, flen_hi, files, cp.., <tier>}] (4 entries, or fewer if
    <4 buckets exist)."""
    n = len(buckets)
    k = min(4, n)
    total_files = sum(b["files"] for b in buckets)
    groups, idx, cum = [], 0, 0
    for g in range(k):
        remaining = k - g
        if remaining == 1:
            grp = buckets[idx:]
        else:
            target = total_files * (g + 1) / k
            grp, j, local_cum = [], idx, cum
            while j < n:
                grp.append(buckets[j])
                local_cum += buckets[j]["files"]
                j += 1
                # Stop once this group reaches its target share, as long as
                # enough buckets remain for every later group to be non-empty.
                if local_cum >= target and (n - j) >= (remaining - 1):
                    break
            idx, cum = j, local_cum
        groups.append(grp)
    out = []
    for grp in groups:
        files = sum(b["files"] for b in grp)
        total_sigs = grp[0]["total_sigs"]
        pairs = total_sigs * files
        cnts = {k: sum(b[f"{k}_n"] for b in grp) for k in TIERS}
        # The four tiers partition the pair space exactly -- catch any
        # parse/merge bug at the count level (the strong, exact check).
        assert sum(cnts.values()) == pairs, (
            grp[0]["flen"], grp[-1]["flen"], cnts, pairs)
        pcts = {k: 100.0 * cnts[k] / pairs for k in TIERS}
        # ... and the recomputed ratios sum to 1 (float-level restatement).
        assert abs(sum(pcts.values()) - 100.0) < 1e-9, (
            grp[0]["flen"], grp[-1]["flen"], pcts)
        out.append({"flen_lo": grp[0]["flen"], "flen_hi": grp[-1]["flen"],
                    "files": files, **pcts})
    return out


# ---------------------------- formatting ---------------------------------
def sci(n: int) -> str:
    """Integer -> '$a.bb\\times10^{c}$' (matches dna_reef_bora.tex style)."""
    e = len(str(n)) - 1
    return f"${n / 10 ** e:.2f}\\times10^{{{e}}}$"


def pct(p: float) -> str:
    """At least 4 decimals (the dump's own precision); add more only if a
    nonzero value would still print as 0.0000 or a sub-100 value as 100.0000."""
    for nd in (4, 5, 6):
        s = f"{p:.{nd}f}"
        if float(s) == 0.0 and p > 0:
            continue
        if float(s) == 100.0 and p < 100:
            continue
        return s
    return f"{p:.6f}"


def _cells(*pcts: float) -> str:
    return " & ".join(f"${pct(p)}\\%$" for p in pcts)


def build_table(datasets: dict) -> str:
    rows = []
    for label in ORDER:
        d = datasets[label]
        rows.append(f"\\textsc{{{label}}} & {sci(d['pairs'])} & "
                    f"{_cells(d['cp'], d['sde'], d['dfa'])} \\\\")
    # Emit the closing \hline here so the last row's \\ and the rule sit in
    # the SAME file -- \input'ing a tabular body that ends in \\ right before
    # an outer \hline triggers "Misplaced \noalign" across the file boundary.
    return "\n".join(rows) + "\n\\hline\n"


def size_label(lo: int, hi: int) -> str:
    """Bin [flen_lo, flen_hi] -> byte-range span '$2^{16}$--$2^{19}$'
    (size in [2^(flen_lo-1), 2^flen_hi))."""
    return f"$2^{{{lo - 1}}}$--$2^{{{hi}}}$"


def build_size_table(buckets: list) -> str:
    """Tiers by file size, merged into 4 log-even bins. Owns its closing
    \\hline (see build_table note on the \\input boundary)."""
    rows = []
    for b in merge_to_4(buckets):
        rows.append(f"{size_label(b['flen_lo'], b['flen_hi'])} & {b['files']} "
                    f"& {_cells(b['cp'], b['sde'], b['dfa'])} \\\\")
    return "\n".join(rows) + "\n\\hline\n"


def main() -> None:
    root = get_paper_root()
    dump = any_server_file("eval_effective.txt").read_text()
    datasets, size_buckets = parse(dump)
    figs = root / "figs"
    outputs = {
        "effectiveness_tab.tex": build_table(datasets),
        "effectiveness_size.tex": build_size_table(size_buckets["Mal"]),
        "effectiveness_size_dlp.tex": build_size_table(size_buckets["Dlp"]),
    }
    for name, text in outputs.items():
        (figs / name).write_text(text)
        print(f"wrote {figs / name}")


if __name__ == "__main__":
    main()
