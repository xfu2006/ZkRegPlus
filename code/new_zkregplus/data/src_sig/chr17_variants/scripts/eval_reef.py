# -----------------------------------
# Evaluate Reef (project) mode against the Chr17 (84MB) sequence
#   over the full reef_regex/ set (27k disease related variants on Chr17)
# Author: BORA Author framework set up and manual review of source code
#   and auditing of results
#         code (function body) filled by Claude Code 4.7
# -----------------------------------
#
# Anchoring & invocation facts (verified against the Reef source in ../reef):
#   * Each regex is `^.{N}LITERAL.*`; N (the "initial distance jump") is the
#     anchor offset. The whole experiment proves NON-MATCH (`-n`): the mutated
#     LITERAL is absent from the reference chr17, so Reef proves it does
#     not match.
#   * Projection (`-p`) only engages when Reef can name an *aligned
#     power-of-two* block [start,end) with start>0 that covers
#     [anchor, orig_doc_len); otherwise it falls back to the full padded
#     document. The exact selection loop is in
#     ../reef/src/backend/r1cs.rs:417-468; we replicate it byte-for-byte in
#     `_doc_subset()` below. The judgement "b_project" is precisely
#     "_doc_subset(anchor) is not None" (r1cs.rs:451: `if start == 0 { None }`).
#     We inserted one line of print statement into Reef to tell if the
#       the actual -p is applicable or not based on if doc_subset is None.
#       so that we can know about it when we run reef.
#   * The witness_generation cost is ~ n*log2(n) over the lookup table length n
#     (= projected chunk length when -p applies, else the full padded doc). See
#     paper reef.pdf 6.4 ("nlookup's prover incurs O(n) operations over F"); the
#     log factor comes from gen_eq_table + prover_mle_partial_eval. We calibrate
#     against a measured full-document point (832 s at n = 2^27).

import math
import os
import platform
import random
import re
import secrets
import statistics
import subprocess
import time

# --------------------------------
# PATHS / CONSTANTS
# --------------------------------
# Anchor the working directory one level above scripts/ (same convention as the
# other scripts in this project), regardless of where we are launched from.
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
REEF_BIN = os.path.join(ROOT, "reef", "target", "release", "reef")
DOC = os.path.join(ROOT, "chr17_samples", "NC_000017.11.reef.txt")
CMT = DOC + ".cmt"  # Reef's default commitment name is <doc>.cmt
REGEX_DIR = os.path.join(ROOT, "reef_regex")
DOCS_DIR = os.path.join(ROOT, "docs")  # generated logs go here
TMP_DIR = "/tmp/reef_exp"  # all temp files live here (random names)
def _next_pow2(x):
    return 1 << (x - 1).bit_length()


ORIG_DOC_LEN = os.path.getsize(DOC)  # 83,257,441 for chr17
N_PAD = _next_pow2(ORIG_DOC_LEN)  # padded table length, 2^27 for chr17

# Empirical cost-model constants (seconds). Calibrated from instrumented runs:
#   - FULL_WIT: measured full-document witness_generation_0 at n = N_PAD (2^27).
#   - FA_SOLVE / PROVE: ~flat across chunk size (the SAFA solve + Nova
#     prove step runs over the full document, not the projected chunk);
#     values are the measured magnitudes (fa_solver ~2.8-3.3 s,
#     prove_0 ~0.19 s).
FULL_WIT = 832.0
FA_SOLVE = 3.0
PROVE = 0.2

# Timer test-names (the CSV `test` column) that make up the "net" cost. By the
# agreed definition, net = witness_generation + prove + fa_solve ONLY (it
# excludes the fixed floor: commitment_read 4.3GB load, snark_setup,
# consistency_proof, fa_builder, r1cs_init). assess_variant's estimate uses the
# SAME definition so the +/- threshold gate is apples-to-apples.
_RE_WITNESS = re.compile(r"^witness_generation_\d+$")
_RE_PROVE = re.compile(r"^prove_\d+$")  # NB: excludes "prove+wit"
_FA_SOLVE_KEY = "fa_solver"

# Timers we expect Reef to emit on a --prove run (used to fill -1 on timeout).
EXPECTED_TIMERS = [
    "doc_read", "commitment_read", "regex_normalization", "fa_builder",
    "fa_solver", "r1cs_init", "constraint_generation", "witness_generation_0",
    "prove_0", "compressed_snark", "consistency_proof", "snark_setup",
    "prove+wit", "doc_transform",
]

# Per-component rows shown in the per-category summary. The starred set sums to
# total_net_time; the rest are the main fixed-floor components (constant across
# projection). Order: net constituents first, then floor.
_NET_COMPONENTS = {"witness_generation_0", "prove_0", "fa_solver"}
SUMMARY_COMPONENTS = [
    "witness_generation_0", "prove_0", "fa_solver",
    "consistency_proof", "commitment_read", "snark_setup", "fa_builder",
    "r1cs_init",
]

# Reproducible sampling.
RANDOM_SEED = 20260527


# --------------------------------
# COST MODEL HELPERS
# --------------------------------
def _wit_seconds(n):
    # n*log2(n) model, anchored at the measured full-doc point
    # (FULL_WIT @ N_PAD).
    return FULL_WIT * (n * math.log2(n)) / (N_PAD * math.log2(N_PAD))


def _doc_subset(real_start):
    # Faithful replica of ../reef/src/backend/r1cs.rs:417-468 (hybrid disabled).
    # Returns (start, end) of the projected aligned power-of-two chunk, or None
    # when Reef would fall back to the full document (start == 0).
    chunk_len = N_PAD // 2
    e = N_PAD
    s = 0
    end = e
    start = 0
    while e >= ORIG_DOC_LEN:
        end = e
        start = s
        s = 0
        while s + chunk_len <= real_start:
            s += chunk_len
        e = s + chunk_len
        chunk_len = chunk_len // 2
    # (the post-loop asserts in r1cs.rs hold by construction)
    if start == 0:
        return None
    return (start, end)


def _chunk_label(chunk_len):
    # Human-readable category name for a projected chunk length (power of two
    # bytes), or "non_projectable" when chunk_len is None.
    if chunk_len is None:
        return "non_projectable"
    kib = chunk_len // 1024
    if kib < 1024:
        return "proj_%dk" % kib
    return "proj_%dM" % (kib // 1024)


def _read_anchor(variant_name):
    # Parse N out of `^.{N}LITERAL.*` in reef_regex/<variant_name>.txt.
    path = os.path.join(REGEX_DIR, variant_name + ".txt")
    with open(path, "r") as f:
        rgx = f.read().strip()
    m = re.match(r"\^\.\{(\d+)\}", rgx)
    if not m:
        raise ValueError("regex for %s is not in ^.{N}... form: %r"
                         % (variant_name, rgx[:40]))
    return int(m.group(1)), rgx


# generate a string (multi-line typical key: val format)
# that presents the info of running machine: cores, cpu speed, RAM etc.
def gen_machine_config():
    lines = []
    uname = platform.uname()
    lines.append("os:              %s %s" % (uname.system, uname.release))
    lines.append("logical_cores:   %s" % (os.cpu_count() or "unknown"))

    # CPU model + max MHz from /proc/cpuinfo (Linux).
    model, mhz, physical = "unknown", "unknown", 0
    try:
        with open("/proc/cpuinfo") as f:
            for ln in f:
                if ln.startswith("model name") and model == "unknown":
                    model = ln.split(":", 1)[1].strip()
                elif ln.startswith("cpu MHz") and mhz == "unknown":
                    mhz = ln.split(":", 1)[1].strip()
                elif ln.startswith("processor"):
                    physical += 1
    except OSError:
        pass
    lines.append("cpu_model:       %s" % model)
    lines.append("cpu_mhz:         %s" % mhz)
    lines.append("cpu_count_proc:  %d" % physical)

    # Total RAM from /proc/meminfo (Linux).
    mem = "unknown"
    try:
        with open("/proc/meminfo") as f:
            for ln in f:
                if ln.startswith("MemTotal"):
                    kb = int(ln.split()[1])
                    mem = "%.1f GiB" % (kb / (1024.0 * 1024.0))
                    break
    except OSError:
        pass
    lines.append("ram_total:       %s" % mem)

    lines.append("doc:             %s (%d bytes, padded table %d = 2^%d)"
                 % (os.path.basename(DOC), ORIG_DOC_LEN, N_PAD,
                    N_PAD.bit_length() - 1))
    return "\n".join(lines)


# given variant based on its anchor point (initial distance jump)
# make an estimate of the following:
#   (1) b_project: if the -p option of Reef can apply. 
#   (2) estimate cost: explain the empirical model that the
#       witness_gen cost is nlog(n) over the length n of the chunk
#       the estimat cost include the net expense:
#            witness_generation + prove + fa_solve
def assess_variant(variant_name):
    anchor, rgx = _read_anchor(variant_name)
    ds = _doc_subset(anchor)
    b_project = ds is not None
    chunk_len = (ds[1] - ds[0]) if b_project else None
    # Cost table length: projected chunk when -p applies, else full padded doc.
    n = chunk_len if b_project else N_PAD
    est_net = _wit_seconds(n) + FA_SOLVE + PROVE
    return {
        "name": variant_name,
        "anchor": anchor,
        "b_project": b_project,
        # judgement: -p applies iff Reef's aligned-block selector yields start>0
        # (r1cs.rs:451 `if start == 0 { None }`); the block must cover
        # [anchor, orig_doc_len), which forces anchor >= N_PAD/2.
        "b_project_reason": (
            "aligned 2^k block [%d,%d), start>0, covers doc end"
            % (ds[0], ds[1])) if b_project
        else "no aligned block start>0 reaches doc end -> full doc",
        "chunk_len": chunk_len,
        "category": _chunk_label(chunk_len),
        # est_net = wit(n) + fa_solve + prove ;
        # wit(n) = FULL_WIT*(n*log2 n)/(N*log2 N)
        "est_net": est_net,
    }


# go over all regex in reef_regex/ folder, and categorize them as
# non_projetable:
# proj_512k
# proj_2M
# proj_4M
# proj_8M
# proj_16M
# -- note: if there are other categories, include them
# in each category: include a record about [variant_name, estimated_cost]
def gen_assessment():
    cats = {}
    names = sorted(n[:-4] for n in os.listdir(REGEX_DIR) if n.endswith(".txt"))
    for name in names:
        a = assess_variant(name)
        cats.setdefault(a["category"], []).append(a)
    # Stable, readable category ordering: non_projectable first, then projected
    # ascending by chunk length.
    def _key(cat):
        if cat == "non_projectable":
            return (0, 0)
        kib = int(re.match(r"proj_(\d+)([kM])", cat).group(1))
        unit = re.match(r"proj_(\d+)([kM])", cat).group(2)
        return (1, kib * (1024 if unit == "M" else 1) * 1024)
    return {c: cats[c] for c in sorted(cats, key=_key)}


# given the result of gen_assessment(), return a deterministically shuffled
# pool of ALL variants per category. seq_run_categories draws the first
# sample_size that pass the gates, pulling REPLACEMENTS from the tail of the
# same category's pool whenever a sample is discarded as a cost outlier. A
# full shuffled pool (rather than a fixed pick of k) is what makes the
# discard-and-resample possible while staying reproducible (RANDOM_SEED).
def gen_sample_pool():
    full = gen_assessment()
    rng = random.Random(RANDOM_SEED)
    out = {}
    for cat, entries in full.items():
        pool = list(entries)
        rng.shuffle(pool)
        out[cat] = pool
    return out


# --------------------------------
# REEF DRIVER (external tool)
# --------------------------------
# (1) verify the tool exists / is runnable before any invocation.
def verify_tool_existence(path=REEF_BIN):
    if not os.path.isfile(path):
        raise RuntimeError(
            "Reef binary not found: %s (build it: cd ../reef && "
            "cargo build --release --features metrics)" % path)
    if not os.access(path, os.X_OK):
        raise RuntimeError("Reef binary is not executable: %s" % path)
    return True


# (2) run the tool with an argv list (shell=False -> no injection surface).
# mode in {"prove","commit"}. Returns (returncode, log_path, timed_out, wall_s).
# The child's stdout+stderr are redirected to log_path (a file, not a PIPE) so
# large/long runs don't blow the buffer and partial output survives a timeout.
def run_reef(mode, doc, regex, metrics_path, proof_path, projections,
             negate, timeout):
    verify_tool_existence(REEF_BIN)
    if mode == "commit":
        args = [REEF_BIN, "--commit", "-d", doc, "--cmt-name", CMT,
                "--metrics", metrics_path]
    elif mode == "prove":
        args = [REEF_BIN, "--prove", "-d", doc, "--cmt-name", CMT,
                "--metrics", metrics_path, "--proof-name", proof_path,
                "-r", regex]
        if projections:
            args.append("-p")
        if negate:
            args.append("-n")
    else:
        raise ValueError("unknown mode: %r" % mode)
    args.append("dna")  # alphabet/config subcommand goes last

    log_path = os.path.join(TMP_DIR, "log_" + secrets.token_hex(8) + ".txt")
    timed_out = False
    start = time.monotonic()
    with open(log_path, "wb") as logf:
        try:
            cp = subprocess.run(args, stdout=logf, stderr=subprocess.STDOUT,
                                timeout=timeout)
            rc = cp.returncode
        except subprocess.TimeoutExpired:
            timed_out = True
            rc = None
    wall = time.monotonic() - start
    if timed_out:
        wall = float(timeout)
    return rc, log_path, timed_out, wall


def _parse_metrics_csv(metrics_path):
    # Reef writes CSV: type,component,test,value,metric_type. Keep runtime rows
    # (type R, metric μs) as seconds, keyed by the test name.
    import csv
    timings = {}
    if not os.path.exists(metrics_path):
        return timings
    with open(metrics_path, newline="") as f:
        for row in csv.DictReader(f):
            if row.get("type") == "R" and row.get("metric_type") == "μs":
                try:
                    timings[row["test"]] = int(row["value"]) / 1.0e6
                except (ValueError, KeyError):
                    pass
    return timings


def _net_from(timings):
    net = 0.0
    for k, v in timings.items():
        if v is None or v < 0:
            continue
        if _RE_WITNESS.match(k) or _RE_PROVE.match(k) or k == _FA_SOLVE_KEY:
            net += v
    return net


def _parse_proj(log_path):
    # Returns (applied: bool, real_chunk_len: int|None) from the REEF_PROJ line.
    applied, chunk = False, None
    try:
        with open(log_path, "r", errors="replace") as f:
            text = f.read()
    except OSError:
        return applied, chunk
    m = re.search(r"REEF_PROJ applied=(\d).*?chunk_len=(\d+)", text)
    if m:
        applied = m.group(1) == "1"
        chunk = int(m.group(2))
    return applied, chunk


def _cleanup(*paths):
    for p in paths:
        try:
            if p and os.path.exists(p):
                os.remove(p)
        except OSError:
            pass


# generate the commitment of the doc NC00017.0001
# so that later runs do not have to generate commitment again.
def setup():
    os.makedirs(TMP_DIR, exist_ok=True)
    verify_tool_existence(REEF_BIN)
    if os.path.exists(CMT) and os.path.getsize(CMT) > 0:
        print("setup: commitment present (%s, %.1f GiB) - skip --commit"
              % (CMT, os.path.getsize(CMT) / (1024.0 ** 3)))
        return
    print("setup: generating commitment for %s (one-time) ..." % DOC)
    metrics_path = os.path.join(
        TMP_DIR, "commit_" + secrets.token_hex(8) + ".csv")
    rc, log_path, timed_out, wall = run_reef(
        "commit", DOC, "", metrics_path, "", False, False,
        timeout=24 * 3600)
    _cleanup(metrics_path)
    if timed_out or rc != 0:
        raise RuntimeError(
            "commitment generation failed (rc=%s, log=%s)" % (rc, log_path))
    _cleanup(log_path)
    print("setup: commitment written to %s" % CMT)


# invoke reef up to time-out on the variant (non-match mode),
# try the best effort
# on -p, also take advantage of the fact that commitment to doc (NC00017)
# is already generated.
# return: [b_if_p_applied, a dictionary of all running results including
#    all timing available, in the running record add two columns:
#       total_net_time, and wall_time]
# for potential parallel run: make sure any temp files generated have
#   a random name. All temp files placed in /tmp/reef_exp/
# if timed out, set total_net_time and wall_time to the timeout
#   and all other attributes to -1 (meaning invalid)
def run_variant(variant_name, timeout):
    os.makedirs(TMP_DIR, exist_ok=True)
    _, rgx = _read_anchor(variant_name)
    tag = secrets.token_hex(8)
    metrics_path = os.path.join(TMP_DIR, "m_" + tag + ".csv")
    proof_path = os.path.join(TMP_DIR, "p_" + tag + ".proof")

    rc, log_path, timed_out, wall = run_reef(
        "prove", DOC, rgx, metrics_path, proof_path,
        projections=True, negate=True, timeout=timeout)

    # b_if_p_applied comes from the REEF_PROJ stdout line (flushed well
    # before the long witness phase, so it survives even a timed-out run).
    b_applied, real_chunk = _parse_proj(log_path)

    if timed_out:
        results = {t: -1 for t in EXPECTED_TIMERS}
        results["real_chunk_len"] = real_chunk if real_chunk is not None else -1
        results["total_net_time"] = float(timeout)
        results["wall_time"] = float(timeout)
        results["timed_out"] = True
        _cleanup(metrics_path, proof_path, log_path)
        return [b_applied, results]

    timings = _parse_metrics_csv(metrics_path)
    results = dict(timings)
    results["real_chunk_len"] = real_chunk if real_chunk is not None else -1
    results["total_net_time"] = _net_from(timings)
    results["wall_time"] = wall
    results["timed_out"] = False
    if rc != 0:
        # Finished but non-zero exit: flag it; keep whatever timings exist.
        results["returncode"] = rc
    _cleanup(metrics_path, proof_path, log_path)
    return [b_applied, results]


# pool is a per-category SHUFFLED list of all variants (gen_sample_pool).
# For each category we draw variants in pool order, running run_variant on
# each, until we have collected `sample_size` ACCEPTED samples (or the pool
# is exhausted).
#   - GATE 1 (projectability mismatch): the -p judgement is deterministic
#     from the model, so a disagreement means the replica is wrong -> hard
#     STOP the whole run.
#   - GATE 2 (cost outside est +/- threshold): treated as a per-sample
#     OUTLIER, not a model failure -- DISCARD that sample and draw ANOTHER
#     from the same category's pool, up to max_discard discards per category
#     before giving up (hard STOP). Timed-out-but-predicted-fast stays a hard
#     STOP (the estimate, not jitter, was wrong).
# Returns (accepted, discarded): two category->list-of-records dicts.
def seq_run_categories(pool, timeout, threshhold_perc, sample_size,
                       max_discard):
    out = {cat: [] for cat in pool}
    discarded = {cat: [] for cat in pool}
    stopped = False
    for cat, entries in pool.items():
        if stopped:
            break
        k_target = min(sample_size, len(entries))
        accepted = 0
        n_discard = 0
        attempt = 0
        for est in entries:
            if accepted >= k_target or stopped:
                break
            attempt += 1
            name = est["name"]
            b_applied, results = run_variant(name, timeout)
            rec = dict(est)
            rec["real_b_applied"] = b_applied
            rec["results"] = results

            to = results.get("timed_out", False)
            real_net = results["total_net_time"]
            print("[%-16s acc=%d/%d try=%d disc=%d] %s  est_net=%.1fs  "
                  "real_net=%.1fs  p_applied=%s(est %s)  timed_out=%s  chunk=%s"
                  % (cat, accepted, k_target, attempt, n_discard, name,
                     est["est_net"], real_net, b_applied, est["b_project"],
                     to, results.get("real_chunk_len")))

            # --- GATE 1: projectability must match the estimate (hard STOP) ---
            if b_applied != est["b_project"]:
                print("  STOP: projectability mismatch for %s "
                      "(real=%s, est=%s)" % (name, b_applied, est["b_project"]))
                out[cat].append(rec)
                stopped = True
                break

            # --- GATE 2: cost within estimate +/- threshold ---
            if to:
                # Timed out: a PASS iff we predicted it would exceed the
                # timeout; otherwise the estimate was wrong -> hard STOP.
                if est["est_net"] > timeout:
                    out[cat].append(rec)
                    accepted += 1
                    continue
                print("  STOP: %s timed out but est_net=%.1fs <= timeout=%ds"
                      % (name, est["est_net"], timeout))
                out[cat].append(rec)
                stopped = True
                break

            e = est["est_net"]
            # Projectable variants get a doubled tolerance: their net is tiny
            # (a few s to ~95 s) so fixed per-run jitter is a larger fraction,
            # whereas the ~835 s full-doc runs are dominated by the n*log n
            # witness term and track the model more tightly.
            eff_perc = threshhold_perc * (2 if est["b_project"] else 1)
            eff_thr = eff_perc / 100.0
            if e > 0 and abs(real_net - e) / e > eff_thr:
                # OUTLIER: discard this sample and try another from the pool.
                n_discard += 1
                rec["discard_reason"] = (
                    "real_net=%.1fs outside est=%.1fs +/-%d%%"
                    % (real_net, e, eff_perc))
                discarded[cat].append(rec)
                print("  DISCARD (%d/%d) %s: %s -- drawing another sample"
                      % (n_discard, max_discard, name, rec["discard_reason"]))
                if n_discard >= max_discard:
                    print("  STOP: %s exceeded max_discard=%d outliers"
                          % (cat, max_discard))
                    stopped = True
                    break
                continue

            # --- ACCEPTED ---
            out[cat].append(rec)
            accepted += 1

        if not stopped and accepted < k_target:
            print("  WARN: %s pool exhausted with only %d/%d accepted "
                  "(%d discarded)" % (cat, accepted, k_target, n_discard))
    return out, discarded


# One-block summary: counts of ALL reef regex per size category
# (non_projectable first, then projected chunks ascending), each with
# its share of the total and the est_net cost span. Driven by the
# gen_assessment output (EVERY variant, not just executed samples), so
# it reflects the whole reef_regex/ set.
def _format_category_breakdown(full_category):
    total = sum(len(v) for v in full_category.values())
    n_nonproj = len(full_category.get("non_projectable", []))
    n_proj = total - n_nonproj
    lines = []
    lines.append("all reef regex: %d total  (projectable=%d, "
                 "non_projectable=%d)" % (total, n_proj, n_nonproj))
    lines.append("  %-16s %8s %8s   %s"
                 % ("category", "count", "share",
                    "est_net s (min/mean/max)"))
    for cat, entries in full_category.items():
        nets = [a["est_net"] for a in entries]
        pct = (100.0 * len(entries) / total) if total else 0.0
        lines.append("  %-16s %8d %7.1f%%   %.1f / %.1f / %.1f"
                     % (cat, len(entries), pct,
                        min(nets), statistics.mean(nets), max(nets)))
    return "\n".join(lines)


# write the log which includes fo the seq_run_results:
# 0. machine config.
# 1. brief explaination of the categories and why doing so.
# 2. summary of each category (cat_name, net_cost (min, max, mean,
#    std_deviation), wall_time (min, max, mean, std_deviation)
# 3. for each category, one row per variant: (variant name, cost items
#    one by one, and estimate_net_cost)
# the input: (1) the sequential running result, (2) the full category info
#    of all variants, i.e., return of the gen_assessment
# also for full_cateory: display by category the list of all variants
#    and the estimate of cost
# generate two log files:
# reef_sample_run.log for seq_run_result
# variants_category.txt for full_category
# `discarded` (category -> list of outlier records) is reported in its own
# section so the resampling is transparent (which variants were dropped, why).
def write_log(seq_run_results, full_category, discarded=None):
    discarded = discarded or {}
    def _stats(vals):
        vals = [v for v in vals if v is not None]
        if not vals:
            return "n=0"
        mn, mx = min(vals), max(vals)
        mean = statistics.mean(vals)
        std = statistics.pstdev(vals) if len(vals) > 1 else 0.0
        return ("n=%d min=%.2f max=%.2f mean=%.2f std=%.2f"
                % (len(vals), mn, mx, mean, std))

    os.makedirs(DOCS_DIR, exist_ok=True)
    run_path = os.path.join(DOCS_DIR, "reef_sample_run.log")
    cat_path = os.path.join(DOCS_DIR, "variants_category.txt")

    all_recs = [r for recs in seq_run_results.values() for r in recs]
    total_wall = sum(r["results"]["wall_time"] for r in all_recs)

    # ---- reef_sample_run.log ----
    with open(run_path, "w") as f:
        f.write("# Reef non-match sample run\n")
        f.write("# generated: %s by scripts/eval_reef.py\n"
                % time.strftime("%Y-%m-%d %H:%M:%S"))
        f.write("# total run time: %.1f s (%.1f min)\n"
                % (total_wall, total_wall / 60.0))
        f.write("#\n")
        f.write("# how generated: eval_reef.py runs the Reef binary in\n")
        f.write("#   non-match mode (reef --prove -p -n ... dna) against the\n")
        f.write("#   prebuilt chr17 commitment, sampling up to %d variant(s)\n"
                % sample_size)
        f.write("#   per category. net = witness_generation + prove +\n")
        f.write("#   fa_solve. A sample whose measured cost leaves est\n")
        f.write("#   +/-%d%% (projectable +/-%d%%) is DISCARDED as an\n"
                % (threshold_perc, threshold_perc * 2))
        f.write("#   outlier and another is drawn from the same category\n")
        f.write("#   (up to max_discard=%d per category). The run STOPs\n"
                % max_discard)
        f.write("#   only if projectability disagrees with the estimate,\n")
        f.write("#   a fast-predicted sample times out, or max_discard is\n")
        f.write("#   exceeded. Discarded outliers are listed in section 4.\n\n")

        f.write("== ALL-REGEX BREAKDOWN BY SIZE CATEGORY "
                "(every variant) ==\n")
        f.write(_format_category_breakdown(full_category) + "\n\n")

        f.write("== 0. MACHINE CONFIG ==\n")
        f.write(gen_machine_config() + "\n\n")

        f.write("== 1. CATEGORIES (why) ==\n")
        f.write(
            "Variants are bucketed by whether Reef's `-p` projection\n"
            "engages and, if so, by the projected chunk length.\n"
            "Projection replaces the n=2^27 full-document nlookup\n"
            "table with an aligned 2^k chunk covering [anchor,\n"
            "doc_end); witness_generation (the prover bottleneck)\n"
            "scales ~ n*log2(n), so chunk length is the dominant cost\n"
            "axis. 'non_projectable' variants (anchor < N/2) keep the\n"
            "full n=2^27 table (~835 s each). Net cost =\n"
            "witness_generation + prove + fa_solve.\n\n")

        f.write("== 2. PER-CATEGORY SUMMARY (executed samples) ==\n")
        n_to_all = sum(1 for r in all_recs if r["results"].get("timed_out"))
        f.write("timed_out: %d of %d samples\n" % (n_to_all, len(all_recs)))
        for cat, recs in seq_run_results.items():
            nets = [r["results"]["total_net_time"] for r in recs]
            walls = [r["results"]["wall_time"] for r in recs]
            n_to = sum(1 for r in recs if r["results"].get("timed_out"))
            f.write("[%s]  samples=%d  timed_out=%d\n" % (cat, len(recs), n_to))
            f.write("   net_cost(s):  %s\n" % _stats(nets))
            f.write("   wall_time(s): %s\n" % _stats(walls))
            # component breakdown (* = sums into net_cost)
            for comp in SUMMARY_COMPONENTS:
                vals = [r["results"].get(comp) for r in recs]
                vals = [v for v in vals
                        if isinstance(v, (int, float)) and v >= 0]
                mark = "*" if comp in _NET_COMPONENTS else " "
                f.write("   %s %-20s %s\n" % (mark, comp, _stats(vals)))
        f.write("\n")

        f.write("== 3. PER-VARIANT ROWS (executed samples) ==\n")
        for cat, recs in seq_run_results.items():
            f.write("--- %s ---\n" % cat)
            for r in recs:
                res = r["results"]
                items = ", ".join(
                    "%s=%s" % (k, ("%.3f" % v if isinstance(v, float) else v))
                    for k, v in sorted(res.items()))
                f.write("  %s  est_net=%.2fs  real_p_applied=%s\n"
                        % (r["name"], r["est_net"], r["real_b_applied"]))
                f.write("      %s\n" % items)
        f.write("\n")

        f.write("== 4. DISCARDED OUTLIERS (resampled away) ==\n")
        n_disc_all = sum(len(v) for v in discarded.values())
        f.write("total discarded: %d\n" % n_disc_all)
        for cat, recs in discarded.items():
            if not recs:
                continue
            f.write("--- %s (%d discarded) ---\n" % (cat, len(recs)))
            for r in recs:
                res = r["results"]
                f.write("  %s  est_net=%.2fs  real_net=%.2fs  reason=%s\n"
                        % (r["name"], r["est_net"],
                           res.get("total_net_time", -1),
                           r.get("discard_reason", "?")))
        f.write("\n")

    # ---- variants_category.txt (full assessment of ALL variants) ----
    with open(cat_path, "w") as f:
        f.write("# Full categorization of all variants (estimated)\n")
        f.write("# generated: %s\n" % time.strftime("%Y-%m-%d %H:%M:%S"))
        f.write("# doc=%s (%d bytes, padded 2^%d)\n"
                % (os.path.basename(DOC), ORIG_DOC_LEN, N_PAD.bit_length() - 1))
        f.write("#\n")
        f.write("# est_net = estimated NET prover cost (seconds) =\n")
        f.write("#   witness_generation + prove + fa_solve (the\n")
        f.write("#   variant-dependent work; EXCLUDES the ~60 s fixed\n")
        f.write("#   floor: commitment_read, consistency_proof,\n")
        f.write("#   snark_setup, fa_builder, r1cs_init). Modeled as\n")
        f.write("#   wit(n) = 832*(n*log2 n)/(2^27*27) + ~3.2 s, with n\n")
        f.write("#   = projected chunk_len when -p applies, else 2^27.\n\n")
        total = sum(len(v) for v in full_category.values())
        f.write("category counts (of %d total):\n" % total)
        for cat, entries in full_category.items():
            f.write("  %-16s %6d\n" % (cat, len(entries)))
        f.write("\n")
        for cat, entries in full_category.items():
            f.write("--- %s (%d variants) ---\n" % (cat, len(entries)))
            for a in entries:
                f.write("  %s  anchor=%d  chunk_len=%s  est_net=%.2fs\n"
                        % (a["name"], a["anchor"], a["chunk_len"],
                           a["est_net"]))
            f.write("\n")

    print("wrote %s and %s" % (run_path, cat_path))
    return run_path, cat_path


# --------------------------------
# MAIN
# --------------------------------
timeout = 2000         # seconds
threshold_perc = 50    # 50%
sample_size = 10
max_discard = 30       # per category: outliers to resample past before STOP

if __name__ == "__main__":
    verify_tool_existence(REEF_BIN)
    setup()
    full_category = gen_assessment()
    print("assessed %d variants across %d categories: %s"
          % (sum(len(v) for v in full_category.values()),
             len(full_category),
             {c: len(v) for c, v in full_category.items()}))
    pool = gen_sample_pool()
    seq_run_results, discarded = seq_run_categories(
        pool, timeout, threshold_perc, sample_size, max_discard)
    write_log(seq_run_results, full_category, discarded)
