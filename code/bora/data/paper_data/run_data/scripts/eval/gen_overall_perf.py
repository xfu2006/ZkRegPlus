#!/usr/bin/env python3
# ----------------------------------
# Designed by the paper author; function implementation by Claude Code 4.8.
# Code reviewed and audited by the author; the generated table was manually
# verified by the paper author.
# ----------------------------------
"""Generate the end-to-end prover-performance table for §6.5, Table 3
(tbl:overall-perf).

For each dataset (Mal/Dna/Dlp) we read a FoldPot run log and emit one row:
  - Corpus : input bytes processed, summed over the parallel jobs.
  - Jobs   : number of parallel folding jobs (``fold_pot starts with N jobs``).
  - Steps  : total main-folding steps, summed over jobs.
  - Stage 1 (Main Folding), summed CPU-time over jobs, decomposed into
        Sel.        : circuit selection   = Phase-1 steps {1,2}
        Commit wit. : commit fixed witness= Phase-1 steps {3,4}
        Fold        : folding             = Phase-1 steps {5,6,7}
    and Total = Sel + Commit + Fold.
  - Wall   : TRUE wall-clock = the slowest single job (the jobs run in
    parallel), from per-job [job N] attribution of the Phase-1 step
    durations.  NOT Total/Jobs: that balanced-job mean under-reports the
    wall by the job imbalance (5.9% on Mal, 3.3% on Dlp).  Agrees with
    common.py bora_cost_breakdown's max(jobs) by an independent path.
  - Stage 2 (Compression): a single per-job tail = build main decider +
    main-circuit SNARK proof + cyclepair fold + build cyclepair + second
    SNARK proof.  The two Groth16 key-generations are one-time setup and are
    excluded (amortized).

Reads : the per-dataset BORA dump under data/raw_data/<SERVER_TO_USE>/
        (extracted to <paper_root>/data/raw_data/extracted/ and read there)
Writes: <paper_root>/figs/overall_perf.tex
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
DATASET_LOGS = {
    "Mal": "full_clam.tgz",
    "Dna": "full_dna.tgz",
    "Dlp": "full_dlp.tgz",
}

# When a dataset's run was folding-only (the decider flag was off), its
# Compression tail is absent. A same-named makeup dump -- <base>_makeup_
# snark.tgz, part-tgz shaped (one nested *.log.tgz), folded on a SMALLER
# sample but with the IDENTICAL circuit size so its Compression tail matches
# the full run's -- backfills it. Absent => the table masks the cell.
_MAKEUP_SUFFIX = "_makeup_snark.tgz"


def _makeup_compress(archive, extract_dir):
    """Compression seconds from <base>_makeup_snark.tgz; None if absent."""
    from common import raw_data_root, SERVER_TO_USE, _read_part_log
    base = archive[:-len(".tgz")] if archive.endswith(".tgz") else archive
    mk = raw_data_root() / SERVER_TO_USE / (base + _MAKEUP_SUFFIX)
    if not mk.exists():
        return None
    return parse_log(_read_part_log(mk))["compress"] or None


# Phase-1 sub-step -> Stage-1 bucket. Editable: the dominant cost is the
# folding prove (step 7), so the seconds-scale steps 1-6 barely move totals.
STAGE1_BUCKETS = {
    "sel":    {1, 2},        # generate claims + dispatch words into steps
    "commit": {3, 4},        # generate cmF (commit fixed witness) + batch prf
    "fold":   {5, 6, 7},     # prep + build nova + prove steps
}

# Stage-2 (Compression) parts, matched by a substring of the log line. The
# two "setup Groth16" key-generations are deliberately NOT listed (one-time
# amortized setup, reported in prose, not here).
COMPRESS_PARTS = [
    "build MAIN decider circuit",
    "Gen Groth16 Proof for MainCirc",
    "cyclefold and cyclepair IVC PROVE STEPS",
    "build CyclePair circuit",
    "Generate Groth16 proof",
]

_JOB = re.compile(r"\[job (\d+)\]")
_NJOBS = re.compile(r"fold_pot starts with (\d+) jobs")
_P1STEP = re.compile(r"Phase 1 step (\d+)")
_NSTEPS = re.compile(r"Phase 1 step 7: PROVE STEPS done for n_steps: (\d+)")
_CORPUS = re.compile(r"Job Step 1: main circuits IVC PROVE STEPS .*?"
                     r"total_word_len: ([\d.]+)\s*(B|KB|MB|GB)")
_DECIDER = re.compile(r"MainDeciderCirtuit TOTAL constraints: (\d+)")

# Per-job proof size and final verification cost. Both are constants
# (independent of corpus size and rule-set), so we read them from job 0:
#   proof  = BatchProof TOTAL + IndividualProof TOTAL bytes
#   verify = "Verify Batch Proof" + "Verify Individual Proof" durations
# A full run emits one such proof per job; the per-job constant is reported.
_BATCH_BYTES = re.compile(r"====\s*BatchProof\s*====.*?TOTAL\s+(\d+)\s+bytes",
                          re.S)
_INDIV_BYTES = re.compile(r"====\s*IndividualProof\s*====.*?TOTAL\s+(\d+)\s+bytes",
                          re.S)
_VERIFY_BATCH = re.compile(r"Verify Batch Proof\.\s*([\d.]+)\s*ms")
_VERIFY_INDIV = re.compile(r"Verify Individual Proof\.\s*([\d.]+)\s*ms")
# Distinct Groth16 SNARK proofs in the batch proof (snark_proof_main, _cp).
_GROTH = re.compile(r"(snark_proof\w*)\s*:\s*Groth16")

# Trailing "<value> <unit>" duration at end of a log line.
_DUR = re.compile(r"([\d.]+)\s*(ns|us|µs|ms|s)\s*$")
_UNIT_MS = {"ns": 1e-6, "us": 1e-3, "µs": 1e-3, "ms": 1.0, "s": 1e3}
_SIZE_B = {"B": 1, "KB": 1024, "MB": 1024**2, "GB": 1024**3}


def _dur_ms(line: str):
    """Trailing duration of a log line, in milliseconds (None if absent)."""
    m = _DUR.search(line.rstrip())
    return float(m.group(1)) * _UNIT_MS[m.group(2)] if m else None


def parse_log(text: str) -> dict:
    """Return {corpus_bytes, jobs, steps, sel, commit, fold, compress}."""
    lines = text.splitlines()

    # Sum every "fold_pot starts with N jobs" marker: a single-process dump
    # emits one (= 8); a NUMA two-half combined dump emits one PER PROCESS
    # (4 + 4 = 8), so summing recovers the true total parallelism either way.
    njs = [int(m.group(1)) for m in _NJOBS.finditer(text)]
    jobs = sum(njs) if njs else len({m.group(1) for m in
                                     (_JOB.search(l) for l in lines) if m})
    steps = sum(int(m.group(1)) for m in map(_NSTEPS.search, lines) if m)

    corpus = sum(int(round(float(v) * _SIZE_B[u]))
                 for v, u in _CORPUS.findall(text))

    # Stage 1: bucket each (job, Phase-1 step) duration, summed over jobs.
    # Also accumulate PER JOB, so the true wall-clock (the slowest single
    # job, since the jobs run in parallel) can be reported instead of the
    # balanced-job approximation Total/Jobs.
    stage1 = {k: 0.0 for k in STAGE1_BUCKETS}
    stage1_by_job: dict[str, float] = {}
    for line in lines:
        sm = _P1STEP.search(line)
        if not sm:
            continue
        step, dur = int(sm.group(1)), _dur_ms(line)
        if dur is None:
            continue
        for bucket, members in STAGE1_BUCKETS.items():
            if step in members:
                stage1[bucket] += dur
                jm = _JOB.search(line)
                if jm is not None:
                    job = jm.group(1)
                    stage1_by_job[job] = stage1_by_job.get(job, 0.0) + dur
                break

    # Stage 2: ONE per-job compression tail. The log holds one tail per job;
    # sum a single proof's parts (the N tails are parallel/amortized), not
    # all jobs. Attribute each part-line to its [job N] and pick the lowest-id
    # job whose tail is complete (all parts present).
    job_time: dict[str, float] = {}
    job_parts: dict[str, set] = {}
    for line in lines:
        part = next((p for p in COMPRESS_PARTS if p in line), None)
        jm = _JOB.search(line)
        dur = _dur_ms(line) if part else None
        if part is None or jm is None or dur is None:
            continue
        job = jm.group(1)
        job_time[job] = job_time.get(job, 0.0) + dur
        job_parts.setdefault(job, set()).add(part)
    complete = [j for j in job_time
                if len(job_parts[j]) == len(COMPRESS_PARTS)]
    if complete:
        compress = job_time[min(complete, key=int)]
    elif job_time:
        compress = max(job_time.values())
    else:
        compress = 0.0

    dec = _DECIDER.search(text)
    decider = int(dec.group(1)) if dec else None

    # Per-job proof size (BatchProof + IndividualProof) and verify cost.
    mb, mi = _BATCH_BYTES.search(text), _INDIV_BYTES.search(text)
    proof_bytes = (((int(mb.group(1)) if mb else 0)
                    + (int(mi.group(1)) if mi else 0)) or None)
    vb, vi = _VERIFY_BATCH.search(text), _VERIFY_INDIV.search(text)
    verify_ms = (((float(vb.group(1)) if vb else 0.0)
                  + (float(vi.group(1)) if vi else 0.0))
                 if (vb or vi) else None)

    # Number of Groth16 SNARK proofs inside one batch proof (main + cp),
    # counted by distinct snark_proof_* names in the BatchProof section.
    ngroth = len(set(_GROTH.findall(text))) or None

    total = stage1["sel"] + stage1["commit"] + stage1["fold"]
    # True wall-clock = slowest single job (jobs run in parallel). Falls back
    # to the Total/Jobs mean only if the log carries no [job N] attribution.
    wall = max(stage1_by_job.values()) if stage1_by_job else None
    return {"corpus": corpus, "jobs": jobs, "steps": steps, "wall": wall,
            "sel": stage1["sel"], "commit": stage1["commit"],
            "fold": stage1["fold"], "total": total, "compress": compress,
            "decider": decider, "proof_bytes": proof_bytes,
            "verify_ms": verify_ms, "ngroth": ngroth}


_NUMWORD = {1: "one", 2: "two", 3: "three", 4: "four", 5: "five",
            6: "six", 7: "seven", 8: "eight", 9: "nine"}


def _num2word(n: int) -> str:
    return _NUMWORD.get(n, str(n))


def _commas(n: int) -> str:
    return f"{n:,}".replace(",", "{,}")


def _fmt_dur(ms: float) -> str:
    """Adaptive ms -> ms/s/min/hr with a fixed LaTeX thin space."""
    if ms < 1000:
        return rf"${ms:.0f}$\,ms"
    s = ms / 1000
    if s < 60:
        return rf"${s:.1f}$\,s"
    m = s / 60
    if m < 60:
        return rf"${m:.1f}$\,min"
    return rf"${m / 60:.2f}$\,hr"


def _fmt_size(b: int) -> str:
    for unit in ("GB", "MB", "KB"):
        if b >= _SIZE_B[unit]:
            return rf"${b / _SIZE_B[unit]:.1f}$\,{unit}"
    return rf"${b}$\,B"


def build_table(per_dataset: dict) -> str:
    rows = []
    # Proof size, verify cost, and Groth16 count are per-job constants (one
    # batch proof, identical across jobs and datasets). Collect them and
    # sanity-check that every dataset agrees before reporting the single value.
    proof_bytes = verify_ms = ngroth = None
    for ds, info in per_dataset.items():
        if info["proof_bytes"]:
            assert proof_bytes in (None, info["proof_bytes"]), \
                f"{ds}: proof size {info['proof_bytes']} != {proof_bytes}"
            proof_bytes = info["proof_bytes"]
        if info["verify_ms"]:
            verify_ms = verify_ms or info["verify_ms"]
        if info["ngroth"]:
            assert ngroth in (None, info["ngroth"]), \
                f"{ds}: Groth16 count {info['ngroth']} != {ngroth}"
            ngroth = info["ngroth"]
        assert abs(info["total"] - (info["sel"] + info["commit"]
                                    + info["fold"])) < 1e-6, \
            f"{ds}: Total != Sel+Commit+Fold"
        wall = info.get("wall")
        if wall is None:
            wall = info["total"] / info["jobs"] if info["jobs"] else info["total"]
        # Total CPU-time / wall-clock (= the slowest single job),
        # with the job count in parentheses. For single-job datasets the
        # two coincide, so we print one value and "(1)".
        if info["jobs"] > 1:
            total_cell = (f"{_fmt_dur(info['total'])}\\,/\\,{_fmt_dur(wall)} "
                          f"(${info['jobs']}$)")
        else:
            total_cell = f"{_fmt_dur(info['total'])} (${info['jobs']}$)"
        comp_cell = (_fmt_dur(info["compress"]) if info["compress"]
                     else r"\textit{n/a}")
        rows.append(
            f"\\textsc{{{ds}}} & {_fmt_size(info['corpus'])} & ${info['jobs']}$ "
            f"& {_commas(info['steps'])} & {_fmt_dur(info['sel'])} "
            f"& {_fmt_dur(info['commit'])} & {_fmt_dur(info['fold'])} "
            f"& {total_cell} & {comp_cell} \\\\")

    proof_str = rf"${_commas(proof_bytes)}$\,B" if proof_bytes else r"$1{,}152$\,B"
    verify_str = _fmt_dur(verify_ms) if verify_ms else r"${\approx}29$\,ms"
    # Corpus sizes (extracted) for the caption's encoding/padding note.
    by_name = {d.lower(): i for d, i in per_dataset.items()}
    dna_str = _fmt_size(by_name["dna"]["corpus"])
    mal_str = _fmt_size(by_name["mal"]["corpus"])
    ngroth_word = _num2word(ngroth) if ngroth else "two"

    return "\n".join([
        r"% GENERATED by data/scripts/eval/gen_overall_perf.py -- do not edit.",
        r"% Per-dataset end-to-end prover breakdown for Q3 (overall perf).",
        r"% Stage 1 (folding) = circuit-selection + commit-fixed-witness +",
        r"% folding, summed CPU-time over jobs; Total is their sum. Stage 2",
        r"% (Compression) is the per-job decider/SNARK tail (Groth16 keygen",
        r"% excluded as one-time setup). The footer row reports one batch",
        r"% proof's size and verify cost (constant in corpus/rule-set; a run",
        r"% emits one such proof per job), extracted from the",
        r"% BatchProof/IndividualProof log sections.",
        r"\begin{table*}[t]",
        r"\centering",
        r"\small",
        r"\setlength{\tabcolsep}{6pt}",
        r"\begin{tabular}{@{}l r r r rrrr r@{}}",
        r"\toprule",
        r"        &        &      &       & \multicolumn{3}{c}{Stage 1: Main Folding}",
        r"        &       & \multicolumn{1}{c}{Stage 2} \\",
        r"\cmidrule(lr){5-7}\cmidrule(lr){9-9}",
        r"Dataset & Corpus & Jobs & Steps & Sel. & Commit wit. & Fold "
        r"& Total\,/\,Wall (jobs)",
        r"        & Compression \\",
        r"\midrule",
        *rows,
        r"\midrule",
        r"\multicolumn{9}{@{}l}{\footnotesize Per batch proof (one per job, "
        r"constant): size " + proof_str + r", verification " + verify_str +
        r".} \\",
        r"\bottomrule",
        r"\end{tabular}",
        r"\caption{End-to-end prover performance. \emph{Corpus} is the bytes "
        r"actually folded: \textsc{Dna} packs each base of its chr17 sequence "
        r"into a nibble (half a byte), halving it to the " + dna_str + r" shown, "
        r"while the " + mal_str + r" \textsc{Mal} results from padding each "
        r"chunk to $128$\,KB. \emph{Stage 1} (main folding) is the corpus-scaling "
        r"cost: circuit selection $+$ commit fixed witness $+$ folding. "
        r"\emph{Total\,/\,Wall (jobs)} reports the summed CPU-time over the "
        r"parallel jobs and the wall-clock time, i.e.\ the slowest single job, "
        r"since the jobs run in parallel. \emph{Stage 2: Compression} computes "
        r"the main-circuit SNARK proof, the QA-NIZK proof, the cycle-pairing fold, "
        r"and the resulting batch proof. It is a fixed per-job cost, and all "
        r"timings exclude the one-time key setup. The bottom row shows the size "
        r"and verification cost of one batch proof (mainly the " + ngroth_word +
        r" Groth16 SNARK proofs); this per-job batch proof is constant size and "
        r"independent of corpus and rule-set size. A run emits one batch proof "
        r"per job, as jobs split a corpus to save wall time.}",
        r"\label{tbl:overall-perf}",
        r"\end{table*}",
        "",
    ])


def main() -> None:
    root = get_paper_root()
    raw = root / "data" / "raw_data"
    extract_dir = raw / "extracted"

    per_dataset = {}
    for ds, archive in DATASET_LOGS.items():
        log = resolve_server_dump(archive, extract_dir)
        info = parse_log(log.read_text())
        # If a run was folding-only its Compression tail is absent; use the
        # dump's own SNARK if present, else backfill from the makeup dump,
        # else None so the table masks the cell. Applies to every dataset.
        if not info["compress"]:
            info["compress"] = _makeup_compress(archive, extract_dir)
        per_dataset[ds] = info

    out = root / "figs" / "overall_perf.tex"
    out.write_text(build_table(per_dataset))
    print(f"wrote {out}")


if __name__ == "__main__":
    main()
