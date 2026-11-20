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
  - Stage 2 (Compression): the per-job tail = build main decider +
    main-circuit SNARK proof + cyclepair fold + build cyclepair + second
    SNARK proof (+ KZG openings and batch-proof assembly when logged).
    The two Groth16 key-generations are one-time setup and are excluded.
    Cell = per-job mean / total over all jobs (ALL_T1025).
  - End-to-end wall (ALL_T1025): first fold start to last proof, minus the
    one-time setup (FoldPot steps 1-3, every Groth16 key-generation).

Reads : the per-dataset BORA dump under data/raw_data/<SERVER_TO_USE>/
        (extracted to <paper_root>/data/raw_data/extracted/ and read there)
Writes: <paper_root>/figs/overall_perf.tex
"""

from __future__ import annotations

import calendar
import re
import sys
import time
from pathlib import Path

# common.py lives in the parent scripts/ directory.
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from common import (resolve_server_dump, raw_data_root, fig_dir, server_file,
                    source_line, MISSING)
from gen_component_cost import parse_log as parse_cost

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
# ALL_T1025: later code also logs these per-job tail parts; summed when
# present, not required (the August logs lack the KZG lines).
COMPRESS_OPTIONAL = [
    "KZG open + D_1",
    "KZG open + D_2",
    "Assmeble Batch Proof",      # sic, as the log spells it
]

# ALL_T1025: end-to-end wall.  A dump is one or more process logs, each
# opening with a "# <date> <time> host=... label=..." header.
_HEADER = re.compile(r"^# \d{4}-\d\d-\d\d \d\d:\d\d:\d\d", re.M)
SELF_COVER_MARK = "fold: dummy self-cover:"   # PAPER_DATA.py: retry marker
_FOLD_START = re.compile(r"fold_pot starts with \d+ jobs")
_DATETIME = re.compile(r"^datetime : (\d{4}-\d\d-\d\d \d\d:\d\d:\d\d) (\S+)\s*$",
                       re.M)
_ALL_JOBS = re.compile(r"=== ALL JOBS === ([\d.]+)\s*ms")
_FP_STEP = re.compile(r"PERF 1005: FoldPot:? Step ([0-3]):")
_BARE_MS = re.compile(r"^\s*([\d.]+)\s*ms\s*$")
_G16_SETUP = "setup Groth16"
_P1_DONE = "Phase 1 step 7: PROVE STEPS done"

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


def _segments(text: str) -> list:
    """ALL_T1025: one text per process log (split at the "# <date>" header),
    each cut to its last fold attempt: a self-cover retry re-runs fold_pot
    after SELF_COVER_MARK, so only the text after the last mark counts (as
    PAPER_DATA.py's verdict does).  Text with no header is one process.
    A headerless prefix without a fold is dropped; a process log without a
    fold is kept, so the total and E2E print MISSING for a half-run dump."""
    cuts = [m.start() for m in _HEADER.finditer(text)]
    if not cuts or cuts[0] != 0:
        cuts = [0] + cuts
    segs = [text[a:b] for a, b in zip(cuts, cuts[1:] + [len(text)])]
    if len(segs) > 1 and not _HEADER.match(segs[0]) \
            and not _FOLD_START.search(segs[0]):
        segs = segs[1:]
    return [s[s.rfind(SELF_COVER_MARK):] if SELF_COVER_MARK in s else s
            for s in segs]


def _stage1_by_job(seg_lines: list) -> dict:
    """{job id: summed Stage-1 ms} for one process."""
    out: dict[str, float] = {}
    for line in seg_lines:
        sm, jm = _P1STEP.search(line), _JOB.search(line)
        if not sm or not jm:
            continue
        dur = _dur_ms(line)
        if dur is not None and any(int(sm.group(1)) in m
                                   for m in STAGE1_BUCKETS.values()):
            out[jm.group(1)] = out.get(jm.group(1), 0.0) + dur
    return out


def _foldpot_setup(seg_lines: list) -> tuple:
    """(step-0 ms, steps 1-3 ms) of one process.  Step 3's duration sits on
    the first bare "<n> ms" line after its label."""
    step0 = setup = 0.0
    for i, line in enumerate(seg_lines):
        m = _FP_STEP.search(line)
        if not m:
            continue
        dur = _dur_ms(line)
        if dur is None:
            dur = next((float(b.group(1)) for b in
                        map(_BARE_MS.match, seg_lines[i + 1:i + 6]) if b), 0.0)
        if m.group(1) == "0":
            step0 += dur
        else:
            setup += dur
    return step0, setup


def _end_to_end(segs: list):
    """ALL_T1025: wall-clock ms from the first fold start to the last proof,
    minus the one-time setup, or None when the log cannot vouch for it.

    Per process p: F_p = the "datetime :" line printed right after "fold_pot
    starts" (the ALL JOBS timer starts just before it), all_p = ALL JOBS.
    The deciders run one at a time and only after every job has folded
    (part1 waits for part2's fold, part2 for part1's exit), so every Groth16
    key-generation G lies on the critical path, as do FoldPot steps 1-3 of
    the process whose fold ends last (q):
        E2E = max(F_p + all_p) - min(F_p) - S_q - G."""
    procs, tzs, g16 = [], set(), 0.0
    for seg in segs:
        fs = _FOLD_START.search(seg)
        dt = _DATETIME.search(seg, fs.end()) if fs else None
        al = _ALL_JOBS.search(seg, fs.end()) if fs else None
        if not dt or not al:               # also "epoch+Ns" datetime fallback
            return None
        # Guard: all folding before the first key-generation, else a setup
        # could overlap folding and subtracting it would over-count.
        first_g = seg.find(_G16_SETUP)
        if first_g >= 0 and seg.rfind(_P1_DONE) > first_g:
            return None
        lines = seg.splitlines()
        g16_ms = [_dur_ms(l) for l in lines if _G16_SETUP in l]
        if None in g16_ms:                 # an untimed setup cannot be removed
            return None
        g16 += sum(g16_ms)
        tzs.add(dt.group(2))
        f_ms = calendar.timegm(time.strptime(dt.group(1),
                                             "%Y-%m-%d %H:%M:%S")) * 1e3
        step0, setup = _foldpot_setup(lines)
        fold = max(_stage1_by_job(lines).values(), default=0.0)
        procs.append({"f": f_ms, "end": f_ms + float(al.group(1)),
                      "setup": setup, "foldend": f_ms + step0 + setup + fold})
    if not procs or len(tzs) != 1:          # one time zone (no DST change)
        return None
    q = max(procs, key=lambda p: p["foldend"])
    return (max(p["end"] for p in procs) - min(p["f"] for p in procs)
            - q["setup"] - g16)


def parse_log(text: str) -> dict:
    """Return {corpus_bytes, jobs, steps, sel, commit, fold, compress, ...}."""
    segs = _segments(text)
    text = "".join(segs)                   # ALL_T1025: last attempt only
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

    # Stage 1: bucket each Phase-1 step duration, summed over jobs.
    stage1 = {k: 0.0 for k in STAGE1_BUCKETS}
    for line in lines:
        sm = _P1STEP.search(line)
        dur = _dur_ms(line) if sm else None
        if dur is None:
            continue
        for bucket, members in STAGE1_BUCKETS.items():
            if int(sm.group(1)) in members:
                stage1[bucket] += dur
                break
    # True wall-clock = the slowest single job (jobs run in parallel), keyed
    # (process, job) so an un-renumbered part2 cannot merge with part1.
    seg_lines = [s.splitlines() for s in segs]
    stage1_by_job = {(i, j): v for i, sl in enumerate(seg_lines)
                     for j, v in _stage1_by_job(sl).items()}

    # Stage 2: the per-job compression tails.  Every job proves (T952) and
    # the deciders run one at a time, so the table reports the per-job mean
    # and the total over all jobs.  A tail is complete when it has every
    # required part; optional parts add to it when logged.
    job_time: dict[tuple, float] = {}
    job_parts: dict[tuple, set] = {}
    for i, sl in enumerate(seg_lines):
        for line in sl:
            part = next((p for p in COMPRESS_PARTS + COMPRESS_OPTIONAL
                         if p in line), None)
            jm = _JOB.search(line)
            dur = _dur_ms(line) if part else None
            if part is None or jm is None or dur is None:
                continue
            key = (i, jm.group(1))
            job_time[key] = job_time.get(key, 0.0) + dur
            job_parts.setdefault(key, set()).add(part)
    complete = [job_time[k] for k in job_time
                if set(COMPRESS_PARTS) <= job_parts[k]]
    # JET_T1026: no job with all parts -> 0.0, so the cell prints MISSING
    # (was the largest partial sum, which read as a real Stage 2 value).
    compress = sum(complete) / len(complete) if complete else 0.0
    all_proved = (bool(complete) and len(complete) == jobs
                  and all(_FOLD_START.search(s) for s in segs))
    compress_total = sum(complete) if all_proved else None
    # E2E counts every decider only when every job proved (an August-style
    # one-proof run would understate it).
    e2e = _end_to_end(segs) if all_proved else None

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
    wall = max(stage1_by_job.values()) if stage1_by_job else None
    return {"corpus": corpus, "jobs": jobs, "steps": steps, "wall": wall,
            "sel": stage1["sel"], "commit": stage1["commit"],
            "fold": stage1["fold"], "total": total, "compress": compress,
            "compress_total": compress_total, "e2e": e2e,
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
        if info is None:          # ALL_T1020 (W807 i): no dump, marked row
            rows.append(rf"\textsc{{{ds}}} & " + " & ".join([MISSING] * 9)
                        + r" \\")
            continue
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
        # Total CPU-time / wall-clock (= the slowest single job),
        # with the job count in parentheses. For single-job datasets the
        # two coincide, so we print one value and "(1)".
        if info["jobs"] > 1:
            total_cell = (f"{_fmt_dur(info['total'])}\\,/\\,"
                          f"{_fmt_dur(wall) if wall else MISSING} "
                          f"(${info['jobs']}$)")
        else:
            total_cell = f"{_fmt_dur(info['total'])} (${info['jobs']}$)"
        # ALL_T1025: per-job mean / total over all jobs; the total (and the
        # end-to-end wall) print MISSING unless every job proved.
        comp_cell = (_fmt_dur(info["compress"]) if info["compress"]
                     else r"\textit{n/a}")
        if info["jobs"] > 1 and info["compress"]:
            tot = info.get("compress_total")
            comp_cell += r"\,/\," + (_fmt_dur(tot) if tot else MISSING)
        e2e_cell = _fmt_dur(info["e2e"]) if info.get("e2e") else MISSING
        rows.append(
            f"\\textsc{{{ds}}} & {_fmt_size(info['corpus'])} & ${info['jobs']}$ "
            f"& {_commas(info['steps'])} & {_fmt_dur(info['sel'])} "
            f"& {_fmt_dur(info['commit'])} & {_fmt_dur(info['fold'])} "
            f"& {total_cell} & {comp_cell} & {e2e_cell} \\\\")

    # ALL_T1020 (W807 i): a value the logs lack prints MISSING, never a
    # hard-coded fallback.
    proof_str = rf"${_commas(proof_bytes)}$\,B" if proof_bytes else MISSING
    verify_str = _fmt_dur(verify_ms) if verify_ms else MISSING
    # Corpus sizes (extracted) for the caption's encoding/padding note.
    by_name = {d.lower(): i for d, i in per_dataset.items()}
    dna_str = (_fmt_size(by_name["dna"]["corpus"]) if by_name["dna"]
               else MISSING)
    mal_str = (_fmt_size(by_name["mal"]["corpus"]) if by_name["mal"]
               else MISSING)
    ngroth_word = _num2word(ngroth) if ngroth else MISSING
    # Mal per-step input (Table 8 "input"), from the log; was a fixed 128 KB.
    mal_step = by_name["mal"].get("step_bytes") if by_name["mal"] else None
    step_str = rf"${_commas(mal_step)}$\,B" if mal_step else MISSING

    return "\n".join([
        r"% GENERATED by data/scripts/eval/gen_overall_perf.py -- do not edit.",
        source_line(*map(server_file, DATASET_LOGS.values())),
        r"% Per-dataset end-to-end prover breakdown for Q3 (overall perf).",
        r"% Stage 1 (folding) = circuit-selection + commit-fixed-witness +",
        r"% folding, summed CPU-time over jobs; Total is their sum. Stage 2",
        r"% (Compression) is the per-job decider/SNARK tail, mean / total over",
        r"% jobs (Groth16 keygen excluded as one-time setup). End-to-end wall",
        r"% = first fold start to last proof, setup excluded (ALL_T1025).",
        r"% The footer row reports one batch",
        r"% proof's size and verify cost (constant in corpus/ruleset; a run",
        r"% emits one such proof per job), extracted from the",
        r"% BatchProof/IndividualProof log sections.",
        r"\begin{table*}[t]",
        r"\centering",
        r"\small",
        r"\setlength{\tabcolsep}{3.5pt}",   # ALL_T1025: 10 columns fit 7.0 in
        r"\begin{tabular}{@{}l r r r rrrr r r@{}}",
        r"\toprule",
        r"        &        &      &       & \multicolumn{4}{c}{Stage 1: Main Folding}",
        r"        & \multicolumn{1}{c}{Stage 2} & \\",
        r"\cmidrule(lr){5-8}\cmidrule(lr){9-9}",
        r"Dataset & Corpus & Jobs & Steps & Sel. & Commit wit. & Fold "
        r"& Total\,/\,Wall (jobs) & Compression & End-to-end \\",
        r"        &        &      &       &      &             &      "
        r"&                       & Per job\,/\,Total & wall \\",
        r"\midrule",
        *rows,
        r"\midrule",
        r"\multicolumn{10}{@{}l}{\footnotesize Per batch proof (one per job, "
        r"constant): size " + proof_str + r", verification " + verify_str +
        r".} \\",
        r"\bottomrule",
        r"\end{tabular}",
        r"\caption{End-to-end prover performance. \emph{Corpus} is the bytes "
        r"actually folded: \textsc{Dna} packs each base of its chr17 sequence "
        r"into a nibble (half a byte), halving it to the " + dna_str + r" shown, "
        r"while the " + mal_str + r" \textsc{Mal} results from padding each "
        r"chunk to " + step_str + r". \emph{Stage 1} (main folding) is the corpus-scaling "
        r"cost: circuit selection $+$ commit fixed witness $+$ folding. "
        r"\emph{Total\,/\,Wall (jobs)} reports the summed CPU-time over the "
        r"parallel jobs and the wall-clock time, i.e.\ the slowest single job, "
        r"since the jobs run in parallel. \emph{Stage 2: Compression} computes "
        r"the main-circuit SNARK proof, the QA-NIZK proof, the cycle-pairing fold, "
        r"and the resulting batch proof. It is a fixed per-job cost. The Stage 2 "
        r"column gives the per-job mean and, for multi-job runs, the total over all "
        r"jobs. The run proves every job, one decider at a time. "
        r"\emph{End-to-end wall} runs from the start of folding to the last "
        r"proof. All timings exclude the one-time circuit configuration search, "
        r"rule database build and key setup. The keys depend only on the "
        r"circuits, so one setup serves every run. The bottom row shows the size "
        r"and verification cost of one batch proof (mainly the " + ngroth_word +
        r" Groth16 SNARK proofs); this per-job batch proof is constant size and "
        r"independent of corpus and ruleset size. A run emits one batch proof "
        r"per job, as jobs split a corpus to save wall time.}",
        r"\label{tbl:overall-perf}",
        r"\end{table*}",
        "",
    ])


def main() -> None:
    extract_dir = raw_data_root() / "extracted"

    per_dataset = {}
    for ds, archive in DATASET_LOGS.items():
        try:
            log = resolve_server_dump(archive, extract_dir)
        except (OSError, RuntimeError) as e:
            print(f"MISSING {ds} ({archive}): {e}")
            per_dataset[ds] = None
            continue
        text = log.read_text()
        info = parse_log(text)
        try:                     # per-step input bytes (Table 8 "input")
            info["step_bytes"] = parse_cost(text)["input_bytes"]
        except (KeyError, TypeError, ValueError, AttributeError, RuntimeError, ZeroDivisionError):
            info["step_bytes"] = None
        # If a run was folding-only its Compression tail is absent; use the
        # dump's own SNARK if present, else backfill from the makeup dump,
        # else None so the table masks the cell. Applies to every dataset.
        if not info["compress"]:
            info["compress"] = _makeup_compress(archive, extract_dir)
        per_dataset[ds] = info

    out = fig_dir() / "overall_perf.tex"
    out.write_text(build_table(per_dataset))
    print(f"wrote {out}")


if __name__ == "__main__":
    main()
