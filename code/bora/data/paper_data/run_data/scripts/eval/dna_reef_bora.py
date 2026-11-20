#!/usr/bin/env python3
# ----------------------------------
# Designed by the paper author; function implementation by Claude Code 4.7.
# Code reviewed and audited by the author; the generated table was manually
# verified by the paper author.
# ----------------------------------
"""Generate the Reef per-bucket vs BORA comparison table for chr17 x NCBI.

Reads (ALL_T1020, W807 g):
  data/raw_data/jet1tb/reef_sample_run.log   (Reef, whatever the server)
  data/raw_data/<SERVER_TO_USE>/full_dna.tgz  (BORA)

Writes:
  <paper_root>/figs/dna_reef_bora.tex
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

# common.py lives in the parent scripts/ directory.
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from common import (get_cost, resolve_server_dump, reef_file, fig_dir,
                    server_file,
                    source_line, MISSING)


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

def reef_total(buckets: dict) -> tuple:
    """(runs, seconds): the sum of every measured Reef run (n x mean)."""
    return (sum(buckets[b]["n"] for b in BUCKETS),
            sum(buckets[b]["n"] * buckets[b]["mean"] for b in BUCKETS))


def build_table(buckets, bora_cost) -> str:
    """ALL_T1020 (W204.2): measured cells only, no Estimate1/2, no factor.
    ``buckets`` / ``bora_cost`` are None when their log is missing."""
    rows = []
    if buckets is None:
        rows.append(rf"    Reef & \multicolumn{{4}}{{r}}{{{MISSING}}} \\")
    else:
        for b in BUCKETS:
            r = buckets[b]
            rows.append(
                f"    {BUCKET_TEX[b]} & {r['count']:,} & {r['n']} & "
                f"${r['mean']:.2f} \\pm {r['std']:.2f}$ & "
                f"{fmt_sci(r['n'] * r['mean'])} \\\\")
        n, t = reef_total(buckets)
        rows += [r"    \midrule",
                 f"    \\textbf{{Reef, measured runs}} & --- & {n} & --- & "
                 f"\\textbf{{{fmt_sci(t)}}} ({fmt_human(t)}) \\\\"]
    bora = (rf"\textbf{{{fmt_sci(bora_cost)}}} ({fmt_human(bora_cost)})"
            if bora_cost is not None else MISSING)
    n_rules = sum(buckets[b]["count"] for b in BUCKETS) if buckets else None
    rules = f"{n_rules:,}" if n_rules else MISSING   # the same regex set
    # Caption regex count, from the Reef log (was a fixed 27,500).
    rules_tex = f"{n_rules:,}".replace(",", "{,}") if n_rules else MISSING
    rows.append(f"    \\textbf{{BORA, all rules}} & {rules} & --- & --- & "
                f"{bora} \\\\")
    body = "\n".join(rows)

    return r"""% Auto-generated by data/scripts/eval/dna_reef_bora.py
""" + source_line(reef_file(), server_file("full_dna.tgz")) + r"""
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
  \caption{Reef per-bucket cost vs.\ BORA on chr17~$\times$~NCBI (""" + rules_tex + r"""
  regexes). Both systems are compared on the \emph{net} step-folding cost
  only, excluding commitment, setup, and IVC proof compression, for
  a fair comparison.
  For Reef, net $=$ witness generation $+$
  Nova prove $+$ SAFA solve (\texttt{fa\_solver}); it excludes the fixed
  floor (the commitment load, SNARK setup, consistency proof, and
  related one-time costs). For BORA, net $=$ the Phase~1 circuit selection
  and non-deterministic advice generation, and Phase~2 main-folding step
  cost, excluding the Groth16 IVC proof compression as well as setup and
  commitment. \emph{Count} is each bucket's population; Reef ran $n$
  sampled rules per bucket, and \emph{Measured} sums those runs. Each
  per-run mean is over the $n$ runs; $\pm$ is their population s.d.
  BORA proves all """ + rules_tex + r""" rules in one batched run.}
  \label{tab:dna-reef-bora}
  \setlength{\tabcolsep}{3pt}
  \begin{tabular}{l r r r r}
    \toprule
    Bucket & Count & $n$ & Per-run net (s) & Measured net (s) \\
    \midrule
""" + body + r"""
    \bottomrule
  \end{tabular}
\end{table*}
"""


# --------------------------------- main ----------------------------------

def _try(what, fn, *args):
    """fn(*args), or None (printed as MISSING) when its log is absent."""
    try:
        return fn(*args)
    except (OSError, RuntimeError) as e:
        print(f"MISSING {what}: {e}")
        return None


def main() -> None:
    figs = fig_dir()
    buckets = _try("Reef log", lambda: parse_reef_log(reef_file()))
    bora_cost = _try("BORA Dna dump", lambda: bora_main_folding_cost(
        resolve_server_dump("full_dna.tgz")))

    tex = build_table(buckets, bora_cost)
    out = figs / "dna_reef_bora.tex"
    out.write_text(tex)
    print(f"wrote {out}")


if __name__ == "__main__":
    main()
