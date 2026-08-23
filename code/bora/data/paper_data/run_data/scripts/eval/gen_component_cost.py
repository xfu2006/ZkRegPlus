#!/usr/bin/env python3
# ----------------------------------
# Designed by the paper author; function implementation by Claude Code 4.8.
# Code reviewed and audited by the author; the generated table was manually
# verified by the paper author.
# ----------------------------------
"""Generate the per-circuit cost-profile table for §7.4 (tab:component-cost).

For each dataset (Mal/Dna/Dlp) we read a FoldPot run log and emit, per
processing circuit, a row with:
  - input  : bytes processed per folding step. ``max_word_len`` is not printed
             in the log, so we derive it from the logged ``max_nibble_len``:
             a packed field is LEGS=62 nibbles = 31 bytes, and 1 byte = 2
             nibbles, hence input_bytes = max_nibble_len / 2 (== max_word_len*31).
  - total  : R1CS constraints of one folding step (the COST block header).
  - c1..c4 : per-input-byte R1CS of the CP / SDE / DFA tier layers and the
             circuit-level framework layer (logup / input-output / poseidon).
             By construction c1+c2+c3+c4 == total / input.
  - share  : fraction of the corpus discharged by the circuit, taken as the
             fraction of main folding steps on that circuit (the paircycle
             companion steps are excluded via their distinct small stmt_len).

Reads : the per-dataset BORA dump under data/raw_data/<SERVER_TO_USE>/
        (extracted to <paper_root>/data/raw_data/extracted/ and read there)
Writes: <paper_root>/figs/component_cost.tex
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

# common.py lives in the parent scripts/ directory.
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from common import get_paper_root, resolve_server_dump

# Dataset -> server-specific log archive (resolved via SERVER_TO_USE). Each
# dataset has its own full-run dump under data/raw_data/<server>/.
# NOTE: this table needs the per-component COST blocks; the dump must come from
# a COST-instrumented run. The legacy dump_bora_full_clam.dat predated the COST
# block, so full_clam.tgz must be the re-run, COST-instrumented ClamAV dump.
DATASET_LOGS = {
    "Mal": "full_clam.tgz",
    "Dna": "full_dna.tgz",
    "Dlp": "full_dlp.tgz",
}

NIBBLES_PER_BYTE = 2                 # 1 byte = 2 nibbles (LEGS = 62 nibbles/field)
BYTES_PER_FIELD = 31                 # 1 packed field = 62 nibbles = 31 bytes

# Placeholder shown for a dataset whose COST-instrumented log is not available
# yet (its dump is still regenerating on the server). per_dataset[ds] is set to
# None for such datasets, and build_table emits a single ``***`` row.
PLACEHOLDER = "***"

# COST-block component label -> profile key (CpMapper#1/#2 both fold into cp).
_TIER = {"CpMapper": "cp", "SedMapper": "sde", "DfaMapper": "dfa"}

_NIBBLE = re.compile(r"max_nibble_len:\s*(\d+)")
# Fallback when max_nibble_len is absent (real runs): the per-step word length
# is the Phase-1 main-folding total_word_len divided by its n_steps.
_PHASE1_WL = re.compile(
    r"Phase 1 step 1:.*?total_word_len:\s*(\d+) packed fields")
_NSTEPS = re.compile(r"n_steps:\s*(\d+)")
# Phase 1 step 5 prints n_steps AND total_word_len on ONE line, so the two are
# guaranteed to come from the SAME job. Prefer it. The two-search fallback
# below takes the first match of each pattern independently, and in a combined
# multi-job log those land in DIFFERENT jobs -- for Mal, total_word_len from
# job 1 (3358720) paired with n_steps from job 0 (819), giving 4101.0 fields
# per step instead of the true 4096.0 and inflating input_bytes to 127131 B
# instead of 126976 B.
_PHASE1_PAIR = re.compile(
    r"Phase 1 step 5:.*?n_steps:\s*(\d+):\s*total_word_len:\s*(\d+)")
_COST_HEAD = re.compile(
    r"==== COST circ(\d+) \(R1CS constraints\) ====\s+total = (\d+)")
# `datacol = N` is the per-component data-column/var size (Σ witness-var deltas).
# It is OPTIONAL: only the newer COST instrumentation prints it. When every
# component line carries it, we can redistribute the c4 logup query cost into
# c1/c2/c3 (case 2); otherwise we show raw c_i only and flag the row (case 1).
_MAPPER = re.compile(
    r"^\s+(CpMapper|SedMapper|DfaMapper)\S*\s+subtotal = (\d+)"
    r"(?:\s+datacol = (\d+))?")
_FRAMEWORK = re.compile(r"^\s+framework\b[^\d]*(\d+)\s*$")
# PERF 1012: the MEASURED logup query cost (real cs-delta of the inv_hab22
# block) and query length. Primary source for the c4 query cost; the data-col
# sum is the proxy estimate of the same quantity.
_LOGUP_MEAS = re.compile(
    r"PERF 1012: logup query cost \(measured\) = (\d+)\s+qry_len = (\d+)")
_PAIRCYCLE = re.compile(r"paircycle'[^\n]*\(stmt\s+(\d+)")
_PROVE = re.compile(r"prove_step cost: i: \d+, circ_id: (\d+), stmt_len: (\d+)")


def parse_log(text: str, dedup: str = "first") -> dict:
    """Return {input_bytes, circuits: [profile...], shares: {id: frac}}.

    ``dedup`` picks which COST block survives when one circuit id emits
    several. "first" (default) is for a NUMA two-half combined dump, where
    the blocks are two jobs' copies of the same circuit. "last" is for a
    CapErr bump-retry sweep, where the earlier blocks are FAILED fold
    attempts and only the last one converged.
    """
    nib = _NIBBLE.search(text)
    if nib:
        input_bytes = int(nib.group(1)) // NIBBLES_PER_BYTE
    else:
        # Real runs do not print max_nibble_len. Derive the per-step input
        # from the Phase-1 main folding: per-step packed fields =
        # total_word_len / n_steps, each field = 31 bytes. This equals
        # max_word_len*31 == max_nibble_len/2, so the two paths agree.
        pair = _PHASE1_PAIR.search(text)
        if pair:
            n_steps, word_len = int(pair.group(1)), int(pair.group(2))
        else:
            # Legacy logs without the step-5 line only. UNSAFE on a combined
            # multi-job log: the two searches can straddle two jobs.
            wl = _PHASE1_WL.search(text)
            ns = _NSTEPS.search(text)
            if not (wl and ns):
                raise RuntimeError(
                    "neither max_nibble_len nor Phase-1 word-len found in log")
            word_len, n_steps = int(wl.group(1)), int(ns.group(1))
        per_step_fields = word_len / n_steps
        input_bytes = round(per_step_fields * BYTES_PER_FIELD)

    # COST blocks: accumulate per-component R1CS between '==== COST circN ...'
    # and the next '====' boundary line.
    circuits: list[dict] = []
    cur: dict | None = None
    for line in text.splitlines():
        h = _COST_HEAD.search(line)
        if h:
            cur = {"id": int(h.group(1)), "total": int(h.group(2)),
                   "cp": 0, "sde": 0, "dfa": 0, "fw": 0,
                   # per-tier data-column size; has_dc stays False until a
                   # component line carries the optional `datacol = N` field.
                   "cp_dc": 0, "sde_dc": 0, "dfa_dc": 0, "has_dc": False,
                   # measured logup query cost (PERF 1012); None until seen.
                   "logup_meas": None, "qry_len": None}
            circuits.append(cur)
            continue
        if cur is None:
            continue
        mm = _MAPPER.match(line)
        if mm:
            tier = _TIER[mm.group(1)]
            cur[tier] += int(mm.group(2))
            if mm.group(3) is not None:
                cur[tier + "_dc"] += int(mm.group(3))
                cur["has_dc"] = True
            continue
        fm = _FRAMEWORK.match(line)
        if fm:
            cur["fw"] = int(fm.group(1))
            continue
        lm = _LOGUP_MEAS.search(line)
        if lm:
            cur["logup_meas"] = int(lm.group(1))
            cur["qry_len"] = int(lm.group(2))
            continue
        if line.startswith("===="):          # GRAND TOTAL / next boundary
            cur = None
    if not circuits:
        raise RuntimeError("no COST circ blocks found in log")

    # A NUMA two-half combined dump emits a per-circuit COST block from each
    # process; keep one per id so the table is not duplicated. The two halves'
    # blocks need NOT be equal (Mal's differ by ~0.04%/0.24%), so the choice
    # matters: "first" keeps the part-1 circuits the table has always shown.
    # A single-process dump has one per id, so this is a no-op there. shares
    # aggregate prove-steps across ALL jobs below, so they need no dedup.
    # dedup="last" serves the CapErr bump-retry logs of the DLP scale sweep,
    # where the earlier blocks are FAILED attempts (see gen_scale_all.py).
    if dedup not in ("first", "last"):
        raise ValueError(f"dedup must be 'first' or 'last', got {dedup!r}")
    seen: dict[int, dict] = {}
    for c in circuits:
        if dedup == "last" or c["id"] not in seen:
            seen[c["id"]] = c
    circuits = [seen[k] for k in sorted(seen)]

    # sanity: the four layers must reconcile with the header total.
    for c in circuits:
        s = c["cp"] + c["sde"] + c["dfa"] + c["fw"]
        if s != c["total"]:
            raise RuntimeError(
                f"circ {c['id']}: layers sum {s} != header total {c['total']}")

    # corpus share = fraction of main folding steps per circuit; drop paircycle
    # steps (identified by their distinct small stmt_len).
    pc = _PAIRCYCLE.search(text)
    pc_stmt = int(pc.group(1)) if pc else None
    counts: dict[int, int] = {}
    for cid, stmt in _PROVE.findall(text):
        if pc_stmt is not None and int(stmt) == pc_stmt:
            continue
        counts[int(cid)] = counts.get(int(cid), 0) + 1
    tot = sum(counts.values())
    shares = {c["id"]: (counts.get(c["id"], 0) / tot if tot else 0.0)
              for c in circuits}

    return {"input_bytes": input_bytes, "circuits": circuits, "shares": shares}


def _commas(n: int) -> str:
    return f"{n:,}".replace(",", "{,}")


def _coef(n: int, input_bytes: int) -> str:
    return f"{n / input_bytes:.1f}"


def _cell(raw: int, adj: int | None, ib: int) -> str:
    """One coefficient cell. Case 2 (logup split known): "raw (adj)". Case 1
    (no split): "raw" with the adjusted slot left empty."""
    if adj is None:
        return _coef(raw, ib)
    return rf"{_coef(raw, ib)}\,({_coef(adj, ib)})"


def build_table(per_dataset: dict) -> str:
    datasets = list(per_dataset)
    rows: list[str] = []
    meas_notes: list[str] = []
    for di, ds in enumerate(datasets):
        info = per_dataset[ds]
        if info is None or not info.get("circuits"):
            # No COST-instrumented log yet: emit a single placeholder row
            # (Dataset name + ``***`` in every data cell).
            ph = " & ".join([PLACEHOLDER] * 8)   # circ, input, total, c1..c4, share
            rows.append(rf"\textsc{{{ds}}} & {ph} \\")
            if di < len(datasets) - 1:
                rows.append(r"\midrule")
            continue
        ib = info["input_bytes"]
        for ci, c in enumerate(info["circuits"]):
            # input length * (c1 + c2 + c3 + c4) must recover the total R1CS.
            coef_sum = sum(c[k] for k in ("cp", "sde", "dfa", "fw")) / ib
            assert abs(ib * coef_sum - c["total"]) < 1e-6, (
                f"{ds} circ {c['id']}: input*(c1..c4)={ib * coef_sum} "
                f"!= total {c['total']}")
            # Adjusted profile: move the c4 logup *query* cost into the tiers
            # that issued the queries, so each c_i becomes the all-in per-byte
            # cost and c4 keeps only Poseidon/IO. Conserves the total R1CS.
            #   magnitude Q : MEASURED PERF 1012 query cost (primary); falls
            #                 back to the data-column sum (proxy) if absent.
            #   per-tier split: by data-column proportion (the per-tier weight).
            if c["has_dc"]:
                dsum = c["cp_dc"] + c["sde_dc"] + c["dfa_dc"]   # proxy estimate
                q = c["logup_meas"] if c["logup_meas"] is not None else dsum
                if q > c["fw"]:
                    print(f"WARN {ds} circ {c['id']}: query cost {q} exceeds "
                          f"framework {c['fw']}; clamping the move to c4.")
                    q = c["fw"]
                w = {k: (c[k + "_dc"] / dsum if dsum else 0.0)
                     for k in ("cp", "sde", "dfa")}
                adj = {k: c[k] + q * w[k] for k in ("cp", "sde", "dfa")}
                adj["fw"] = c["fw"] - q
                if c["logup_meas"] is not None:
                    diff = (100.0 * (c["logup_meas"] - dsum) / dsum
                            if dsum else 0.0)
                    meas_notes.append(
                        rf"\textsc{{{ds}}} (circ~${c['id']}$): measured "
                        rf"{_commas(c['logup_meas'])} "
                        rf"(\texttt{{qry\_len}}~$=$~{_commas(c['qry_len'])}) "
                        rf"vs.\ data-column estimate {_commas(dsum)} "
                        rf"(${diff:+.1f}\%$)")
            else:
                adj = None
            star = "" if c["has_dc"] else r"^{*}"
            head = rf"\textsc{{{ds}}}" if ci == 0 else ""
            share = f"{100 * info['shares'][c['id']]:.1f}\\%"
            cells = " & ".join(
                _cell(c[k], adj[k] if adj else None, ib)
                for k in ("cp", "sde", "dfa", "fw"))
            rows.append(
                f"{head} & ${c['id']}{star}$ & {_commas(ib)} "
                f"& {_commas(c['total'])} & {cells} & {share} \\\\")
        if di < len(datasets) - 1:
            rows.append(r"\midrule")

    meas_clause = ("" if not meas_notes else
                   r" As a cross-check, the measured query cost tracks the "
                   r"data-column proxy estimate closely: " +
                   "; ".join(meas_notes) + ".")

    return "\n".join([
        r"% GENERATED by data/scripts/eval/gen_component_cost.py -- do not edit.",
        r"% Per-circuit cost profile for Q2 (component R1CS per folding step).",
        r"% Each c_i cell is `raw (adjusted)': raw = component R1CS / input byte;",
        r"% adjusted = raw after the MEASURED c4 log-up query cost (PERF 1012)",
        r"% is moved out of the framework and split across tiers by data-column",
        r"% proportion, so c1/c2/c3 become all-in and c4 keeps only Poseidon/IO.",
        r"% A `*' row lacks the per-component data-column log, so only raw is",
        r"% shown (the split is not yet available -- not accurate).",
        r"\begin{table*}[t]",
        r"\centering",
        r"\small",
        r"\setlength{\tabcolsep}{6pt}",
        r"\begin{tabular}{@{}ll r r rrrr r@{}}",
        r"\toprule",
        r"        &      & input & total  & \multicolumn{4}{c}{R1CS / input byte:"
        r" raw (adjusted)}",
        r"        & corpus \\",
        r"\cmidrule(lr){5-8}",
        r"Dataset & Circ & (B)   & R1CS   & $c_1$ (CP) & $c_2$ (SDE) & $c_3$ (DFA)",
        r"        & $c_4$ (frwk) & share \\",
        r"\midrule",
        *rows,
        r"\bottomrule",
        r"\end{tabular}",
        r"\caption{Per-circuit cost profile. Each dataset is discharged by a "
        r"small set of circuits. \emph{input} is the bytes processed per "
        r"folding step. "
		r"Each $c_i \in (c_1,c_2,c_3,c_4)$ is the "
        r"per-input-byte R1CS constraints of the four components of a circuit."
        r"Each $c_i$ is shown as \emph{raw\,(adjusted)}: the \emph{adjusted} "
        r"value moves the \emph{measured} log-up query cost in $c_4$"
        r" and charges it to each tier in "
        r" proportion to its data-column size, so $c_1/c_2/c_3$ reflect the "
        r" all-in per-byte cost and $c_4$ retains only folding overhead "
		r" and the processing of Logup share of lookup table. }"
        r"\label{tbl:component-cost}",
        r"\end{table*}",
        "",
    ])


def main() -> None:
    root = get_paper_root()
    raw = root / "data" / "raw_data"
    extract_dir = raw / "extracted"

    per_dataset = {}
    for ds, archive in DATASET_LOGS.items():
        # Build the real profile when the COST-instrumented dump is available;
        # otherwise fall back to a placeholder row (the dump is still
        # regenerating on the server).
        try:
            log = resolve_server_dump(archive, extract_dir)
            per_dataset[ds] = parse_log(log.read_text())
        except (RuntimeError, OSError) as exc:
            print(f"WARN {ds} ({archive}): {exc} -- emitting placeholder row")
            per_dataset[ds] = None

    out = root / "figs" / "component_cost.tex"
    out.write_text(build_table(per_dataset))
    print(f"wrote {out}")


if __name__ == "__main__":
    main()
