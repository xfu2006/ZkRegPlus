#!/usr/bin/env python3
# ----------------------------------
# Designed by the paper author; function implementation by Claude Code 4.8.
# Code reviewed and audited by the author; the generated figure was manually
# verified by the paper author.
# ----------------------------------
"""Generate the combined regex-set scalability figure for App. C.3, Figure 8
(fig:scale-regex).

Merges the former gen_scale.py (ClamAV) and gen_scale_dlp.py (MS-DLP) into one
two-column ``figure*`` with a 2x2 grid: columns are datasets (ClamAV | MS-DLP),
rows are metrics (absolute per-step R1CS / net R1CS per rule-byte). One caption,
one label.

For each rule count ``N`` (per-fraction run log ``log_<N>.txt.tgz``, each a
collect_scale_data round) we extract two *per-step* metrics:
  - circuit size : share-weighted R1CS over the folding circuits
                   (reuses gen_component_cost.parse_log), and
  - proof time   : median ``prove_step`` duration, paircycle steps excluded
                   (parsed but not plotted here; kept for parity / auditing).
Lookup-table share is excluded (one-time, amortized).

NO HARD-CODED MEASUREMENTS: every number printed in the figure or caption is
derived from the parsed logs -- floors, ruleset totals, per-rule densities, and
the Zombie comparison (read live from the Zombie measurement log). The two
qualitative tags ``dense``/``sparse`` are descriptors, not measurements. Whole-
document byte sizes are intentionally NOT shown: they are not present in the run
logs, so printing them would be a hard-coded number.

DLP detail carried over: the DLP fold uses config-gated catchable-CapErr bump
retries, so a round may print SEVERAL ``==== COST circN ...`` blocks (one per
fold attempt), the earlier ones FAILED. We therefore ask parse_log for the
LAST block per circuit id (dedup="last"); the converged fold is emitted last.
This is a no-op for ClamAV (one block per id) so it is applied uniformly.

Difficulty is a rule x document property, so each dataset is swept over two
corpora: a dense one whose anchors recur (SDE saturates) and a sparse one
(CP / floor). The contrast is the SDE effect on per-step circuit size; the
saturation itself is reported in the run log, not plotted.

Reads : <paper_root>/data/raw_data/any_server/scale_data_{gdb,readelf}.tgz
        <paper_root>/data/raw_data/any_server/scale_data_dlp_{6,2}.tgz
        (machine-independent sweeps; unbundled under data/raw_data/extracted/)
Writes: <paper_root>/figs/scale.tex   (label fig:scale-regex)
"""

from __future__ import annotations

import re
import statistics
import sys
import tarfile
from pathlib import Path

# common.py lives in the parent scripts/ directory; gen_component_cost is a
# sibling we reuse for the per-circuit R1CS / share / input-byte parsing.
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from common import (get_paper_root, extract_tgz, any_server_file,
                    zombie_totals, server_file, _ZOMBIE_LOG)
from gen_component_cost import parse_log as parse_cost, _PAIRCYCLE

# Each dataset: ruleset name (for x-label / caption), the LaTeX corpus title,
# an ordered map of corpus key -> (bundle, legend label, marker style), and
# whether to attach the Zombie comparison sentence. Bundle labels "6"/"2" for
# DLP are the maildir message numbers (email1=message 6 dense, email2=message 2
# sparse). dense/sparse are qualitative tags, not measurements.
DATASETS = [
    {
        "key": "clamav",
        "ruleset": r"\textsc{ClamAV}",
        # curves sit high near the floor -> legend in the empty lower-left.
        "legend_at": "(0.03,0.04)", "legend_anchor": "south west",
        "series": {
            "gdb": ("scale_data_gdb.tgz", r"gdb (dense)", "mark=*, thick"),
            "readelf": ("scale_data_readelf.tgz", r"readelf (sparse)",
                        "mark=square*, thick, densely dashed"),
        },
        "zombie": False,
    },
    {
        "key": "dlp",
        "ruleset": r"\textsc{MS-DLP}",
        # curves rise from the floor -> legend in the empty upper-left.
        "legend_at": "(0.03,0.96)", "legend_anchor": "north west",
        "series": {
            "email1": ("scale_data_dlp_6.tgz", r"email1 (dense)",
                       "mark=*, thick"),
            "email2": ("scale_data_dlp_2.tgz", r"email2 (sparse)",
                       "mark=square*, thick, densely dashed"),
        },
        "zombie": True,
    },
]

_FRAC = re.compile(r"log_(\d+)")
_PSTEP = re.compile(
    r"prove_step cost: i: \d+, circ_id: \d+, stmt_len: (\d+), "
    r"wtns size: \d+\s+([\d.]+)\s*(ns|us|µs|ms|s)\b")
_UNIT_MS = {"ns": 1e-6, "us": 1e-3, "µs": 1e-3, "ms": 1.0, "s": 1e3}

PR_SCALE = 1e3   # display net density in 1e-3 R1CS/(rule.byte)
# Zombie comparison is measured on a fixed-length input string; this selects
# which Zombie run (by input length) to read from the Zombie log -- it is a
# comparison parameter, not data extracted from the BORA scale logs.
ZOMBIE_STR_LEN = 2000


def per_step_metrics(text: str) -> tuple[float, float, int]:
    """(share-weighted per-step R1CS, median per-step proof ms, input bytes).

    Dedup COST blocks to the LAST per circuit id: bump retries emit one COST
    block per fold attempt and the earlier ones FAILED with CapErr; only the
    last converged. No-op where there is one block per id (ClamAV, and the
    DLP sparse sweep)."""
    info = parse_cost(text, dedup="last")
    r1cs = sum(info["shares"][c["id"]] * c["total"] for c in info["circuits"])

    pc = _PAIRCYCLE.search(text)
    pc_stmt = int(pc.group(1)) if pc else None
    durs = [float(v) * _UNIT_MS[u]
            for stmt, v, u in _PSTEP.findall(text)
            if pc_stmt is None or int(stmt) != pc_stmt]
    if not durs:
        raise RuntimeError("no main prove_step durations found")
    return r1cs, statistics.median(durs), info["input_bytes"]


def collect(bundle: Path, work: Path) -> list[tuple[int, float, float, int]]:
    """Unbundle log_<N>.txt.tgz files; return sorted [(N, r1cs, ms, inbytes)]."""
    work.mkdir(parents=True, exist_ok=True)
    with tarfile.open(bundle, "r:gz") as tf:
        tf.extractall(work)
    points = []
    for inner in sorted(work.glob("log_*.tgz")):
        m = _FRAC.search(inner.name)
        if not m:
            continue
        log = extract_tgz(inner, work)
        r1cs, ms, inb = per_step_metrics(log.read_text())
        points.append((int(m.group(1)), r1cs, ms, inb))
    if not points:
        raise RuntimeError(f"no log_<N>.txt.tgz members found in {bundle}")
    points.sort()
    return points


def _net_density(pts, floor):
    """Net R1CS per (rule x input byte), in 1e-3 units; floor point skipped."""
    return [(n, (r - floor) / (n * inb) * PR_SCALE)
            for n, r, _, inb in pts if n > 1]


def _panel(dataset: dict, show_ylabel: bool = True) -> tuple[list[str], dict]:
    """Build one dataset's two stacked panels (abs + net density) as a minipage.

    Returns (minipage_lines, stats) where stats carries the derived numbers the
    shared caption needs (floor, total, per-corpus peak/final density)."""
    series = dataset["series"]
    total = max(n for _, _, pts in series.values() for n, _, _, _ in pts)
    floor = min(pts[0][1] for _, _, pts in series.values())

    abs_lines, pr_lines = [], []
    max_abs = max_pr = 0.0
    corpus_stats = {}
    for key, (label, marker, pts) in series.items():
        abs_c = "".join(f"({n / total * 100:.1f},{r / 1e6:.3f})"
                        for n, r, _, _ in pts)
        abs_lines.append(rf"  \addplot[{marker}] coordinates {{{abs_c}}};")
        abs_lines.append(rf"  \addlegendentry{{{label}}}")
        dens = _net_density(pts, floor)
        pr_c = "".join(f"({n / total * 100:.1f},{v:.3f})" for n, v in dens)
        pr_lines.append(rf"  \addplot[{marker}] coordinates {{{pr_c}}};")
        max_abs = max(max_abs, max(r / 1e6 for _, r, _, _ in pts))
        if dens:
            max_pr = max(max_pr, max(v for _, v in dens))
            vals = [v for _, v in dens]
            # Caption endpoints: quote the SWEEP, first sampled step -> full
            # set, not peak -> final.  Peak->final describes only the
            # descending tail and reads as amortization even where the net
            # movement is upward (ClamAV gdb runs 0.45 -> 0.76 over the sweep
            # but 0.94 -> 0.76 from its peak).  Start at the first >=10% step:
            # the sub-1% points are single-rule-scale probes (email1's is
            # 0.000, email2's 323.59) and are far too noisy to headline.
            steps = [v for n, v in dens if n / total >= 0.095]
            corpus_stats[key] = (label, steps[0], steps[-1])

    floor_m = f"{floor / 1e6:.2f}"
    abs_lines.append(rf"  \addplot[gray, densely dotted, thick] coordinates "
                     rf"{{(0,{floor_m})(100,{floor_m})}};")
    abs_lines.append(r"  \addlegendentry{single-rule floor}")
    ymax1 = f"{1.12 * max_abs:.0f}" if max_abs >= 1 else f"{1.12 * max_abs:.2f}"
    ymax2 = f"{1.25 * max_pr:.1f}" if max_pr > 0 else "1.0"

    # The two datasets share each row's quantity, so the y-axis annotation is
    # drawn once (left column only); the right column keeps its own ticks since
    # the scales differ. Labels are split onto two lines so the (long) bottom
    # label does not overrun the short axis. ylabel style centers the stack.
    ystyle = r"ylabel style={font=\small, align=center}, "
    yl_top = (r"ylabel={R1CS\,/\,step\\($\times10^{6}$)}, " + ystyle
              if show_ylabel else "")
    # Keep each label line shorter than the (shorter) bottom plot area, else a
    # rotated label longer than the axis makes pgfplots expand the panel
    # vertically and inflate the inter-box gap on the labelled (left) column.
    yl_bot = (r"ylabel={net R1CS per\\rule$\cdot$byte\\($\times10^{-3}$)}, "
              + ystyle if show_ylabel else "")
    # Right column (no ylabel): its top panel has single-digit ticks while the
    # bottom has wide ones (e.g. "1,000"). Reserve a common label width and
    # right-align so the two panels' plot boxes line up and the top digits sit
    # under the bottom's units digit. Left column keeps its natural widths.
    ytick_style = ("" if show_ylabel
                   else r"yticklabel style={text width=2.6em, align=right}, ")

    xaxis = "xmin=-3, xmax=105, xtick={0,10,20,30,40,50,60,70,80,90,100}"
    # Both panels live in ONE tikzpicture with scale only axis: the plot box is
    # exactly PLOT_H tall and the bottom axis is pinned PLOT_GAP below the top
    # axis. Geometry is then independent of label width, so the two columns are
    # vertically identical (same box height, same inter-box gap) by construction.
    # 0.74 (not 0.80): leaves room for the y-axis label + tick labels so the
    # whole picture fits inside the \columnwidth minipage (no overfull \hbox).
    PLOT_W = r"0.74\columnwidth"
    PLOT_H = "2.6cm"
    PLOT_GAP = "0.5cm"
    lines = [
        r"\begin{minipage}[t]{\columnwidth}",
        r"\centering",
        rf"{{\small {dataset['ruleset']}}}\par",
        # Pin the picture baseline to the top plot box's top-left corner so both
        # columns align there regardless of how far their labels hang below.
        r"\begin{tikzpicture}[baseline=(ptop.north west)]",
        r"% --- top: absolute per-step circuit size ---",
        r"\begin{axis}[",
        rf"    name=ptop, scale only axis, width={PLOT_W}, height={PLOT_H},",
        rf"    {xaxis}, xticklabels={{}},",
        rf"    ymin=0, ymax={ymax1}, {yl_top}{ytick_style}",
        r"    tick label style={font=\small}, label style={font=\small},",
        rf"    legend style={{font=\footnotesize, at={{{dataset['legend_at']}}}, "
        rf"anchor={dataset['legend_anchor']}, draw=none, fill=none, "
        r"row sep=-2pt}, legend cell align=left]",
        *abs_lines,
        r"\end{axis}",
        r"% --- bottom: net R1CS per rule-byte (amortization) ---",
        r"\begin{axis}[",
        rf"    name=pbot, scale only axis, width={PLOT_W}, height={PLOT_H},",
        rf"    at={{(ptop.south west)}}, anchor=north west, yshift=-{PLOT_GAP},",
        rf"    {xaxis},",
        rf"    xlabel={{\% of {dataset['ruleset']} ruleset}},",
        rf"    ymin=0, ymax={ymax2}, {yl_bot}{ytick_style}",
        r"    tick label style={font=\small}, label style={font=\small}]",
        *pr_lines,
        r"\end{axis}",
        r"\end{tikzpicture}",
        r"\end{minipage}",
    ]
    stats = {
        "floor_m": floor_m,
        "total": total,          # ruleset size (int), for the Zombie per-rule-byte calc
        "total_tex": f"{total:,}".replace(",", "{,}"),
        "corpus": corpus_stats,   # key -> (label, peak, final) in 1e-3 units
    }
    return lines, stats


def _corpus_phrase(corpus_stats: dict) -> str:
    """`A to B (x) and C to D (y)` over the corpora, derived.

    A is the first sampled step (>=10% of the ruleset), B the full set."""
    frags = []
    for _, (label, first, final) in corpus_stats.items():
        # label like "gdb (dense)" -> bare token for \ttt{}
        tok = label.split(" ")[0]
        frags.append(rf"${first:.2f}\times10^{{-3}}$ to ${final:.2f}\times10^{{-3}}$ "
                     rf"(\ttt{{{tok}}})")
    return " and ".join(frags)


def build_figure(datasets: list[tuple[dict, list, dict]]) -> str:
    """datasets: ordered [(dataset, panel_lines, stats), ...]."""
    body = []
    for i, (_, panel_lines, _) in enumerate(datasets):
        body.extend(panel_lines)
        if i + 1 < len(datasets):
            body.append(r"\hfill")

    # Caption numbers, all derived above.
    clam = next(s for d, _, s in datasets if d["key"] == "clamav")
    dlp = next(s for d, _, s in datasets if d["key"] == "dlp")
    clam_phrase = _corpus_phrase(clam["corpus"])
    dlp_phrase = _corpus_phrase(dlp["corpus"])

    # Zombie comparison on the SAME DLP ruleset, read live from the Zombie log.
    # Report per rule-byte (total R1CS / input length / ruleset size) so the unit
    # matches the figure's delta and the in-text comparison; the ruleset size is
    # the BORA MS-DLP rule count, the same total plotted on the DLP x-axis.
    z = zombie_totals(server_file(_ZOMBIE_LOG), ZOMBIE_STR_LEN,
                      allow_nearest=True)
    z_r1cs_tex = f"{z['total_r1cs']:,}".replace(",", "{,}")
    z_prb_tex = f"{z['total_r1cs'] / z['str_len'] / dlp['total']:.2f}"  # R1CS/rule-byte

    caption = (
        rf"\caption{{Ruleset-size scalability (input fixed), per folding step, "
        rf"on \textsc{{ClamAV}} (left) and \textsc{{MS-DLP}} (right). "
        rf"\emph{{Top:}} absolute circuit size with "
        rf"the single-rule framework floor (dotted; ${clam['floor_m']}$\,M R1CS "
        rf"for \textsc{{ClamAV}}, ${dlp['floor_m']}$\,M for \textsc{{MS-DLP}}); "
        rf"growing the ruleset to the full ${clam['total_tex']}$ (\textsc{{ClamAV}}) "
        rf"/ ${dlp['total_tex']}$ (\textsc{{MS-DLP}}) rules grows the circuit far "
        rf"slower than the rule count. \emph{{Bottom:}} net circuit cost "
        rf"\emph{{per rule per input byte}}---"
        rf"cumulative R1CS above the floor divided by cumulative rule count times "
        rf"per-step input length---moving from {clam_phrase} R1CS per rule-byte "
        rf"(\textsc{{ClamAV}}) and {dlp_phrase} R1CS per rule-byte "
        rf"(\textsc{{MS-DLP}}) between $10\%$ of the ruleset and the full "
        rf"set. For the "
        rf"same \textsc{{MS-DLP}} ruleset, \textsc{{Zombie}} emits ${z_r1cs_tex}$ "
        rf"R1CS in total; dividing by the ${z['str_len']}$-byte input and the "
        rf"same ${dlp['total_tex']}$ rules gives $\sim$${z_prb_tex}$ R1CS per "
        rf"rule-byte, the same normalization applied to BORA.}}")

    return "\n".join([
        r"% GENERATED by data/scripts/eval/gen_scale_all.py -- do not edit.",
        r"% Q4 scalability in regex-set size (input fixed), per folding step.",
        r"% Two-column figure*: columns = datasets (ClamAV | MS-DLP), rows =",
        r"% metrics (top: absolute R1CS with single-rule floor; bottom: net R1CS",
        r"% per rule-byte). One curve per corpus (dense / sparse). Lookup share",
        r"% excluded (one-time, amortized). All numbers derived from logs.",
        r"\begin{figure*}[t]",
        r"\centering",
        *body,
        caption,
        r"\label{fig:scale-regex}",
        r"\end{figure*}",
        "",
    ])


def main() -> None:
    root = get_paper_root()
    raw = root / "data" / "raw_data"

    built = []
    for di, dataset in enumerate(DATASETS):
        resolved = {}
        for key, (bundle, label, marker) in dataset["series"].items():
            try:
                path = any_server_file(bundle)
            except Exception as e:
                print(f"  SKIP {dataset['key']}/{key}: bundle not found ({e})")
                continue
            work = raw / "extracted" / f"scale_{key}"
            pts = collect(path, work)
            resolved[key] = (label, marker, pts)
            print(f"  {dataset['key']}/{key}: {len(pts)} points "
                  f"{[n for n, _, _, _ in pts]}")
        if not resolved:
            print(f"  SKIP dataset {dataset['key']}: no bundles found")
            continue
        ds = {**dataset, "series": resolved}
        panel_lines, stats = _panel(ds, show_ylabel=(di == 0))
        built.append((ds, panel_lines, stats))

    if not built:
        raise SystemExit("no scale bundles found; run the sweeps first")

    out = root / "figs" / "scale.tex"
    out.write_text(build_figure(built))
    print(f"wrote {out}")


if __name__ == "__main__":
    main()
