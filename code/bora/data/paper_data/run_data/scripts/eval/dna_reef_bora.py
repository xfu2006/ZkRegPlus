#!/usr/bin/env python3
# ----------------------------------
# Designed by the paper author; function implementation by Claude Code 4.7.
# Code reviewed and audited by the author; the generated table was manually
# verified by the paper author.
# ----------------------------------
"""Generate the Reef per-bucket vs BORA comparison table for chr17 x NCBI.

Reads (server-specific, under data/raw_data/<SERVER_TO_USE>/):
  reef_sample_run.log
  full_dna.tgz

Writes:
  <paper_root>/figs/dna_reef_bora.tex
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

# common.py lives in the parent scripts/ directory.
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from common import get_paper_root, get_cost, resolve_server_dump, server_file


# ----------------------------- configuration -----------------------------

BUCKETS = ["non_projectable", "proj_512k", "proj_2M", "proj_4M",
           "proj_8M", "proj_16M"]

# Display labels with LaTeX-safe underscores.
BUCKET_TEX = {b: b.replace("_", r"\_") for b in BUCKETS}


# ------------------------------ parsers ----------------------------------

def parse_reef_log(path: Path) -> dict:
    """Return {bucket: {count, share, mean, std, ...}} from reef log."""
    text = path.read_text()
    n_runs = len(re.findall(r"^# Reef non-match sample run\s*$", text,
                            re.MULTILINE))
    if n_runs != 1:
        raise RuntimeError(
            f"parse_reef_log: expected exactly 1 run, found {n_runs}. "
            f"A concatenated log silently yields the LAST run's numbers.")
    out: dict[str, dict] = {b: {} for b in BUCKETS}

    pop_re = re.compile(
        r"^\s*(" + "|".join(BUCKETS) + r")\s+(\d+)\s+([\d.]+)%",
        re.MULTILINE,
    )
    for m in pop_re.finditer(text):
        out[m.group(1)].update(
            count=int(m.group(2)), share=float(m.group(3))
        )

    block_re = re.compile(
        r"\[(" + "|".join(BUCKETS) + r")\]"
        r".*?net_cost\(s\):\s*"
        r"n=(\d+)\s+min=([\d.]+)\s+max=([\d.]+)"
        r"\s+mean=([\d.]+)\s+std=([\d.]+)",
        re.DOTALL,
    )
    for m in block_re.finditer(text):
        out[m.group(1)].update(
            n=int(m.group(2)),
            min=float(m.group(3)),
            max=float(m.group(4)),
            mean=float(m.group(5)),
            std=float(m.group(6)),
        )

    missing = [b for b in BUCKETS if "count" not in out[b] or "mean" not in out[b]]
    if missing:
        raise RuntimeError(f"parse_reef_log: incomplete buckets: {missing}")
    return out


def bora_main_folding_cost(path: Path) -> float:
    """BORA prover cost (seconds) = total Phase 1 main-folding time.

    Delegates parsing to ``common.get_cost`` and aborts unless the dump is a
    single job (the chr17 run is one batched job).
    """
    per_job, agg = get_cost(path)
    if len(per_job) != 1:
        raise RuntimeError(
            f"bora_main_folding_cost: expected exactly 1 job, found "
            f"{len(per_job)}: {[r['job'] for r in per_job]}")
    total = agg["phase1_main_folding"]["total"]
    if total is None:
        raise RuntimeError("bora_main_folding_cost: no phase1_main_folding data")
    return total


# ---------------------------- formatting ---------------------------------

def fmt_sci(x: float, sig: int = 3) -> str:
    """Format ``x`` as $a \\times 10^{b}$ in LaTeX math mode."""
    if x == 0:
        return "$0$"
    exp = int(f"{x:.6e}".split("e")[1])
    mant = x / (10 ** exp)
    return f"${mant:.{sig}f} \\times 10^{{{exp}}}$"


def fmt_human(seconds: float) -> str:
    """Compact wall-clock label (min / hr / d)."""
    if seconds < 3600:
        return f"{seconds / 60:.1f}\\,min"
    if seconds < 86400 * 2:
        return f"{seconds / 3600:.2f}\\,hr"
    return f"{seconds / 86400:.2f}\\,d"


# --------------------------- table builder -------------------------------

def build_table(buckets: dict, bora_cost: float) -> str:
    min_mean = min(buckets[b]["mean"] for b in BUCKETS)

    bucket_rows = []
    for b in BUCKETS:
        rec = buckets[b]
        est1 = rec["count"] * rec["mean"]
        est2 = rec["count"] * min_mean
        bucket_rows.append(
            f"    {BUCKET_TEX[b]} & {rec['count']:>6,} & "
            f"${rec['mean']:.2f} \\pm {rec['std']:.2f}$ & "
            f"{fmt_sci(est1)} & {fmt_sci(est2)} \\\\"
        )

    reef_count = sum(buckets[b]["count"] for b in BUCKETS)
    reef_est1 = sum(buckets[b]["count"] * buckets[b]["mean"] for b in BUCKETS)
    reef_est2 = reef_count * min_mean

    speedup1 = reef_est1 / bora_cost
    speedup2 = reef_est2 / bora_cost

    reef_row = (
        f"    \\textbf{{Reef TOTAL}} & \\textbf{{{reef_count:,}}} & --- & "
        f"\\textbf{{{fmt_sci(reef_est1)}}} ({fmt_human(reef_est1)}) & "
        f"\\textbf{{{fmt_sci(reef_est2)}}} ({fmt_human(reef_est2)}) \\\\"
    )

    bora_row = (
        f"    \\textbf{{BORA}} & \\textbf{{{reef_count:,}}} & "
        f"--- (single batched run) & "
        f"\\textbf{{{fmt_sci(bora_cost)}}} ({fmt_human(bora_cost)}) "
        f"--- $\\approx {speedup1:.0f}\\times$ faster & "
        f"\\textbf{{{fmt_sci(bora_cost)}}} ({fmt_human(bora_cost)}) "
        f"--- $\\approx {speedup2:.2f}\\times$ faster \\\\"
    )

    body = "\n".join(bucket_rows + ["    \\midrule", reef_row, bora_row])

    return r"""% Auto-generated by data/scripts/eval/dna_reef_bora.py
% Sources (server-specific, under data/raw_data/<SERVER_TO_USE>/):
%   reef_sample_run.log
%   full_dna.tgz
%
% Why the consistency / evaluation proof (pi_poly -- the Hyrax opening of the
% document polynomial commitment) is NOT charged into net:
%   Reef's released code computes one such opening per (doc, regex) pair,
%   because its Fiat-Shamir evaluation point q_r is derived from each regex's
%   own proof transcript. That cost is, however, amortizable: a single
%   Fiat-Shamir challenge can be derived over the ENTIRE regex set, so the
%   document commitment need be opened only ONCE for the whole batch rather
%   than once per regex. We therefore treat it as a one-time per-document
%   cost (like the commitment load and SNARK setup) and exclude it from the
%   per-regex net, for both Reef and BORA.
\begin{table*}[!b]
  \centering
  \small
  \caption{Reef per-bucket cost vs.\ BORA on chr17~$\times$~NCBI (27{,}500
  regexes). Both systems are compared on the \emph{net} step-folding cost
  only, excluding commitment, setup, and IVC proof compression, for
  a fair comparison.
  For Reef, net $=$ witness generation $+$
  Nova prove $+$ SAFA solve (\texttt{fa\_solver}); it excludes the fixed
  floor (the 4.3\,GB commitment load, SNARK setup, consistency proof, and
  related one-time costs). For BORA, net $=$ the Phase~1 circuit selection
  and non-deterministic advice generation, and Phase~2 main-folding step
  cost, excluding the Groth16 IVC proof compression as well as setup and
  commitment. Estimate1 uses each bucket's measured per-run mean times its
  population count; Estimate2 uses the minimum measured per-run mean
  (proj\_512k) times bucket count as a counterfactual floor. Each per-run
  mean is over $n=10$ sampled runs; $\pm$ is their population s.d.}
  \label{tab:dna-reef-bora}
  \setlength{\tabcolsep}{3pt}
  \begin{tabular}{l r r r r}
    \toprule
    Bucket & Count & Per-run net cost (s) & Estimate1 (s) & Estimate2 (s) \\
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

    buckets = parse_reef_log(server_file("reef_sample_run.log"))
    bora_dump = resolve_server_dump("full_dna.tgz")
    bora_cost = bora_main_folding_cost(bora_dump)

    tex = build_table(buckets, bora_cost)
    out = figs / "dna_reef_bora.tex"
    out.write_text(tex)
    print(f"wrote {out}")


if __name__ == "__main__":
    main()
