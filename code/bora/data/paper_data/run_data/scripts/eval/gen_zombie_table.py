#!/usr/bin/env python3
# ----------------------------------
# Designed by the paper author; function implementation by Claude Code 4.8.
# Code reviewed and audited by the author; the generated tables were manually
# verified by the paper author.
# ----------------------------------
"""Generate the Zombie same-sample table (tab:zombie-data, App. F; W210).

ALL_T1020 (W807 d, OD19): one row per arm L_T (1/2/4 KB). R1CS and proof
size come from the Zombie sweep log (they do not depend on the e-mail);
prove and verify time come from the same-sample run on the fixed 32 e-mails
per arm (same_zombie.py, D5). The u row and the projection table
(compare_zombie_bora.tex) are gone (W206, W807 e).

Reads (server-specific, under data/raw_data/<SERVER_TO_USE>/):
  run_zombie_regex_zombie_international.log   (sweep: R1CS, proof bytes)
  same_zombie_regex_zombie_international.tsv  (D5: accepted proofs)
Writes:
  <fig_dir>/zombie_data.tex
"""

from __future__ import annotations

import csv
import sys
import tarfile
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from common import (zombie_totals, zombie_str_lens, server_file, fig_dir,
                    source_line, MISSING, get_proj_root)

ARMS = [1000, 2000, 4000]
ZOMBIE_LOG = "run_zombie_regex_zombie_international.log"
SAME_TSV = "same_zombie_regex_zombie_international.tsv"
# ALL_T1020 Q5a (owner 11/19): the arm mix is recomputed from the paper's
# Dlp run list (tracked) and the installed e-mail files.
RUN_LIST = "data/paper_data/dlp/cfg/jobs/final_enron_list.txt.tgz"


def arm_mix():
    """{arm: share} of the paper's Dlp run e-mails of at most 4,000 B, each
    counted in the smallest arm that holds it. None when the list or an
    e-mail file is missing."""
    root, n = get_proj_root(), dict.fromkeys(ARMS, 0)
    try:
        with tarfile.open(root / RUN_LIST) as t:
            names = t.extractfile(t.getmember("final_enron_list.txt")
                                  ).read().decode().splitlines()
        for p in (x.strip() for x in names):
            if "/maildir/" in p:
                size = (root / p).stat().st_size
                arm = next((a for a in ARMS if size <= a), None)
                if arm:
                    n[arm] += 1
    except (OSError, KeyError, tarfile.TarError) as e:
        print(f"MISSING arm mix: {e}")
        return None
    tot = sum(n.values())
    return {a: n[a] / tot for a in ARMS} if tot else None


def same_sample(path) -> dict:
    """{arm: {emails, proofs, prove_s, verify_s}} over accepted proofs; a
    retried (unit, e-mail) proof counts once. Per-e-mail values = the
    e-mail's accepted proofs summed, mean over e-mails. {} when the TSV is
    missing (D5 not run yet) or a cell does not parse."""
    try:
        with open(path) as f:
            rows = {(int(r["size"]), r["unit"], r["email_id"]): r
                    for r in csv.DictReader(f, delimiter="\t")
                    if r.get("accepted") == "1"}
        for r in rows.values():               # parse once; a bad cell = no D5
            r["prove_ms"] = float(r["prove_ms"])
            r["verify_ms"] = float(r["verify_ms"] or 0)
    except (OSError, ValueError) as e:
        print(f"MISSING same-sample TSV (D5): {e}")
        return {}
    out = {}
    for arm in ARMS:
        rs = [r for (size, _, _), r in rows.items() if size == arm]
        mails = {r["email_id"] for r in rs}
        if mails:
            out[arm] = {
                "emails": len(mails), "proofs": len(rs),
                "prove_s": sum(r["prove_ms"] for r in rs)
                / 1000 / len(mails),
                "verify_s": sum(r["verify_ms"] for r in rs)
                / 1000 / len(mails)}
    return out


def build_table(sweep: dict, same: dict, mix=None) -> str:
    """Two 5-column blocks: compile (sweep log) for every swept arm, then
    same-sample timing (D5) for every timed arm. A missing arm is omitted
    from its own block only (OD39 a, W807 d)."""
    rows = []
    for arm in ARMS:
        z = sweep.get(arm)
        if z is None:
            rows.append(f"% OMITTED compile arm {arm} (OD39 a): no sweep block")
            continue
        rows.append(f"    {arm:,} & {z['n']} & {z['total_r1cs']:,} & "
                    f"{z['total_r1cs'] / arm:,.0f} & "
                    f"{z['total_proof_bytes'] / 1e6:.2f} \\\\")
    if not sweep:
        rows.append(rf"    \multicolumn{{5}}{{l}}{{{MISSING} sweep log}} \\")
    full = set(same) >= set(ARMS) and bool(mix)        # OD39 a
    if same:
        rows += [r"    \midrule",
                 r"    $L_T$ (B) & E-mails & Proofs & Prove/e-mail (s) & "
                 r"Verify/e-mail (s) \\",
                 r"    \midrule"]
        for arm in ARMS:
            s = same.get(arm)
            if s is None:
                rows.append(f"% OMITTED timing arm {arm} (OD39 a): not in D5")
                continue
            rows.append(f"    {arm:,} & {s['emails']} & {s['proofs']:,} & "
                        f"{s['prove_s']:.1f} & {s['verify_s']:.1f} \\\\")
        if full:
            pw = [sum(mix[a] * same[a][k] for a in ARMS)
                  for k in ("prove_s", "verify_s")]
            rows.append(r"    \midrule")
            rows.append(rf"    \multicolumn{{3}}{{l}}{{Population-weighted "
                        rf"mean (derived)}} & {pw[0]:.1f} & {pw[1]:.1f} \\")
    return "\n".join([
        r"% Auto-generated by data/scripts/eval/gen_zombie_table.py",
        source_line(server_file(ZOMBIE_LOG), server_file(SAME_TSV)),
        r"\begin{table*}[t]",
        r"  \centering",
        r"  \small",
        r"  \caption{Zombie prover cost on the \textsc{MS-DLP} international",
        r"  SIT rules (Spartan NIZK, two-pattern proximity circuit), per",
        r"  scanned length $L_T$. R1CS and proof size are summed over the"
        + (r" regex instances. Prove and verify time are measured on the"
           r" same random Enron e-mails BORA proves, summed over each"
           r" e-mail's accepted proofs and averaged over the e-mails."
           if same else r" regex instances.")
        + (r" The derived row weights the per-arm means by the arm mix ("
           + "/".join(rf"{100 * mix[a]:.1f}\%" for a in ARMS)
           + r" of the \textsc{Dlp} e-mails of at most 4\,KB)."
           if full else "") + "}",                       # OD39 a
        r"  \label{tab:zombie-data}",
        r"  \begin{tabular}{rrrrr}",
        r"    \toprule",
        r"    $L_T$ (B) & Instances & R1CS & R1CS/B & Proof (MB) \\",
        r"    \midrule",
        *rows,
        r"    \bottomrule",
        r"  \end{tabular}",
        r"\end{table*}",
        "",
    ])


def main() -> None:
    sweep = {}
    try:
        log = server_file(ZOMBIE_LOG)
        for arm in ARMS:
            if arm in zombie_str_lens(log):
                sweep[arm] = zombie_totals(log, arm)
    except (OSError, RuntimeError) as e:
        print(f"MISSING Zombie sweep log: {e}")
    out = fig_dir() / "zombie_data.tex"
    same = same_sample(server_file(SAME_TSV))
    mix = arm_mix() if set(same) >= set(ARMS) else None
    out.write_text(build_table(sweep, same, mix))
    print(f"wrote {out}")


if __name__ == "__main__":
    main()
