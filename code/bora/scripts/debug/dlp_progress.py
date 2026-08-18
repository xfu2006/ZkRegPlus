#!/usr/bin/env python3
"""full_dlp neo production meter: every stage and every hour scored
against the MEASURED legacy full_dlp run, then a completion forecast.
Read-only and PROBE-FREE -- it parses only PERF/PROGRESS markers a
production LOG3 run already emits.  Meant to be run from time to time,
not continuously: each invocation banks a sample and re-prints the
hourly comparison up to that moment."""

import json
import os
import re
import sys
import time

# ------------------------------------------------------------- inputs

# PAPER_DATA.py repoints these at the leaf now running: part1 (part_id
# 0, folding-only) and part2 (part_id 1, which also PROVES).  Both are
# read and merged; job ids are LOCAL to a part, so every key below
# carries the part index too.
DEFAULT_LOGS = ["/tmp/bora/CURRENT_JOB.log",
	"/tmp/bora/CURRENT_JOB_part2.log"]
# `PAPER_DATA.py --run full_run --items dlp` always launches 8 jobs
# (DLP_LEAF_ARGS["full"][3]) and resolve_process_model() splits them
# 4 + 4 across the two sockets of a multi-socket box.  So the job count
# is KNOWN, not inferred: a log whose jobs have not all logged yet must
# not be allowed to shrink the denominators.  --jobs N overrides.
DEFAULT_JOBS = 8
# incremental-scan checkpoint, written beside the first log.  Holds the
# byte offset consumed per log, every accumulator, and the banked
# samples that make the hourly table possible.
STATE_NAME = "dlp_progress.state.json"
# hours to ADD to this box's clock to get the owner's laptop clock.
# The server runs UTC; the laptop measured UTC-4 on 2026-08-17.
MY_OFFSET_H = float(os.environ.get("MY_OFFSET_H", "-4"))
# a log untouched this long, with no terminal marker, is suspect.
STALL_S = 45 * 60
# free memory below this many GB during phase 3 means the topology is
# heading for the OOM M101 warns about; the fix is numa_num=2.
MEM_FLOOR_GB = 50

# =====================================================================
# LEGACY REFERENCE.  Every number below was measured, not modelled.
#
# A. THE FOLD -- the 5.05 d production run, 8 jobs, two-half 4+4:
#    data/paper_data/run_data/data/raw_data/jet1tb/extracted/
#        full_dlp.combined.log            (741 MB, 6,680,998 lines)
#    part1 2026-07-11 21:07:58 jobs 0-3, finished in 436,316.03 s
#    part2 2026-07-11 21:23:04 jobs 4-7, finished in 414,194.18 s
#    box: 64 logical cpus, 961.1 GiB RAM, AMD EPYC-Milan @ 1996 MHz
#    ALL 8 jobs ran b_folding_only, so this run has NO decider.
#
# B. THE DECIDER -- run separately as a "makeup snark", 2026-07-17:
#    ~/tmp/bora/numa_dlp_run/makeup_snark/
#        paper_data_dlp_BUNDLE_20260717_000520.tgz -> part2 log
#    mode=full_dlp prod pct=1 jobs=8, wall 16,873.8 s.  Only 1% of the
#    corpus was folded, but it built the IDENTICAL production ladder
#    (cs1e 59,948,947, cols 357,827/721,868/4,313,676/29,308,137), and
#    decider cost is set by the ladder, not by the step count.  So its
#    phase-4 timings ARE the legacy full_dlp phase-4 reference.
# =====================================================================

# corpus, per job.  All 8 jobs got the same shape: 63,107 words,
# ~7,415,000 packed fields (219.23 MB), 115,862.5 fold steps mean
# (min 115,858, max 115,867).
LEG_WORDS = 63107
LEG_FIELDS = 7415168
LEG_STEPS = 115862.5
# packed fields per chunk (seg_word_len on the DLP/enron corpus).
SEG_WORD_LEN = 64

# per-job wall for each PERF 1007 Phase 1 step, seconds: mean over the
# 8 jobs, then the (min, max) spread across them.  Step 1 is staggered
# on purpose -- jobs enter it serially -- so its spread is not variance.
LEG_STEP = {
	1: (358.0, 141.0, 574.2),        # generate batch/ind claims
	2: (20034.4, 19837.3, 20240.5),  # dispatch w into steps = PHASE 1
	3: (28099.2, 27741.6, 28454.8),  # generate cmF          = PHASE 2
	4: (98.0, 94.4, 102.1),          # generate batch prf
	5: (0.001, 0.001, 0.001),        # prep for proving steps
	6: (146.5, 77.2, 218.8),         # build nova (cs1e-driven)
	7: (363889.1, 353547.3, 378922.2),  # PROVE STEPS       = PHASE 3
	8: (0.33, 0.28, 0.41),           # verify
}
LEG_STEP_NAME = {
	1: "gen batch/ind claims", 2: "dispatch w    (PHASE 1)",
	3: "generate cmF  (PHASE 2)", 4: "generate batch prf",
	5: "prep for proving steps", 6: "build nova",
	7: "PROVE STEPS   (PHASE 3)", 8: "verify",
}
# sum of steps 2..8, the per-job fold budget: 412,267.6 s = 114.52 hr.
LEG_JOB_TOTAL = 412267.6
# per-job fold wall from PERF 1006 Job Step 1, seconds, all 8 jobs:
# 401806 402771 403037 406399 417877 418135 422471 428514.  A PART ends
# with its SLOWEST job, which ran 3.9% over the mean -- that gap is why
# the part wall (436,316 s) exceeds the mean job's timeline.
LEG_JOB_FOLD = (412626.3, 401805.9, 428513.7)

# per-PART wall for the 5 PERF 1005 FoldPot steps, seconds
# (part1, part2).  Emitted by BOTH arms: they come from foldpot's own
# driver, which the neo path shares.  Step 3 has no timer of its own.
LEG_FP = {
	0: (113.759, 86.816),         # Load Keys and Pad Jobs
	1: (5.790, 5.758),            # build dummy stmt for all circs
	2: (391.105, 391.930),        # set up driver 1
	4: (428596.004, 406487.206),  # parallel jobs of folding + nark
}
LEG_FP_NAME = {
	0: "Load Keys and Pad Jobs", 1: "build dummy stmt",
	2: "set up driver 1", 4: "fold all jobs (+nark)",
}
LEG_ALL_JOBS = (429116.893, 406981.833)   # PERF 1005 === ALL JOBS ===

# per-PART wall for the 6 PERF WORKFLOW steps, seconds (part1, part2).
# LEGACY ONLY: "PERF WORKFLOW" is emitted from zkp_driver.rs, which the
# neo path never calls, so a neo run prints none of these.  Kept as the
# reference cost of the pre-fold stages -- the neo arm reaches the same
# milestones but does not time them.
LEG_WF = {
	1: (5553.2, 5550.8),      # load DB
	2: (0.2, 0.1),            # split jobs
	3: (42.9, 35.3),          # discharge full list
	4: (0.1, 0.1),            # NEEDS distribution
	5: (1321.9, 1333.9),      # capacity ladder = THE TUNER
	6: (429397.8, 407273.9),  # fold all jobs
}

# --- PHASE 4, the decider.  Source B above; the proving job only.
# (PERF 1006 Job Step index, label, seconds, MEM GB reported there).
LEG_DEC = [
	(2, "setup Groth16 (MainCirc)", 1033.484, 287),
	(3, "Gen Groth16 proof MainCirc", 1712.412, 284),
	(4, "cyclefold+cyclepair fold", 19.279, 284),
	(5, "build CyclePair circuit", 0.581, 284),
	(6, "setup Groth16 (CpCircuit)", 3054.051, 369),
	(7, "Generate Groth16 proof", 4516.955, 369),
]
# 10,336.8 s = 2.87 hr, peak 369 GB.  Verify Individual Proof adds 5 ms.
LEG_DEC_TOTAL = sum(x[2] for x in LEG_DEC)
LEG_MAIN_DECIDER_CS = 147372734    # *** MainDeciderCirtuit TOTAL ***
LEG_CYCLEPAIR_CS = 204080670       # *** CyclePairCirc TOTAL ***

# production ladder, R1CS A-matrix dims as PERF 1002 reports them.
# 1-based circ index.  NOT the "==== COST circN ====" cost-model
# totals, which over-count ~6x.
LEG_LADDER = {
	1: (357827, 290844),
	2: (721868, 570185),
	3: (4313676, 3155387),
	4: (29308137, 21231034),
}
LEG_CS1E = 59948947
LEG_TOTAL_W = 34701496
LEG_TOTAL_E = 25247450
LEG_MAX_PP = 29308137
# the side fold's single circuit (KEYS info n_circs: 1).
LEG_SIDE = (183775, 185119, 368891)

# ---- THE 08-16 FULL-SCALE NEO REFERENCE.  Same spec, same DB, same
# corpus, ratchet off (b_fold_only false for DLP), so this run must
# REPRODUCE it -- a divergence means the tree changed, not the data.
# Source: /tmp/bora/neo_run/speed/neo_pass1_0816.log, PERF 1002 + KEYS.
NEO_REF_LADDER = {
	1: (295516, 245348),
	2: (1942772, 1620648),
	3: (7920188, 6738718),
	4: (20453765, 17296201),
}
# (total_w, total_e, cs1e, max_pp) from that run's 4-circ KEYS info.
NEO_REF_KEYS = (30612229, 25900915, 56513145, 20453765)
# v5 walk occupancy in WORDS (not chunks) and the rung costs beside it.
# The occupancy doubles as the routing prior until phase 1 measures the
# real per-CHUNK mix: on the 512 GB run words read 91.67% on rung 1
# against 90.59% of chunks, so it is close but not identical.
NEO_REF_HIST = [462809, 34035, 6700, 1311]
NEO_REF_COSTS = [2054, 22168, 82472, 300288]

# routing mix in percent, low rung first, over ALL 926,900 chunks.
LEG_MIX = [24.6509, 70.4427, 4.6640, 0.2424]
# P_max.subsigs the full_dlp tuner settles on, both arms.
PROD_SUBSIGS = 18751
# rung count the ladder must reach.  3 means circ4 -- the tier that sets
# cs1e, decider size and peak RAM -- never appears and the run is void.
EXPECT_RUNGS = 4

# PHASE 1 (step 2), per job.  The per-word gap timers sum to 19,997 s,
# 99.8% of the 20,034 s step-2 wall, so PERF 1008 fully tiles phase 1.
LEG_P1_WORD_MEAN = 316.9   # ms/word, mean over all 504,856 words
LEG_P1_WORD_MED = 158.0    # ms/word, median (p90 574, p99 2444)
LEG_P1_WORDS_HR = 11343.0  # words/hr per job = 63107 / 20034.4 s
LEG_P1_MS_CHUNK = 172.9    # step-2 wall / chunks, per job

# PHASE 3 (step 7) per fold step, ms, means over all 926,900 steps.
# These four spans tile the step-7 wall to 0.12%: wall/n_steps =
# 3140.7 ms, spans sum to 3137.0 ms.
LEG_PROVE_MS = 2965.4   # PERF 1009 "prove_step cost for word_id"
LEG_ADV_MS = 111.0      # PERF 1009 "gen advice for word_id"
LEG_STMT_MS = 60.0      # PERF 1009 "gen stmt"
LEG_LKUP_MS = 0.699     # PERF 1009 "update lkup: share size"
LEG_STEP_WALL_MS = 3140.7   # step-7 wall per step, the ETA term
LEG_UNACCOUNTED_MS = 3.7    # wall minus the four spans
# the per-step terms that do NOT vary with rung: charged flat to every
# step of both arms, so they shift no share, only the totals.
FLAT_MS = LEG_STMT_MS + LEG_LKUP_MS + LEG_UNACCOUNTED_MS
# measured spans per rung before they outrank the fitted price.  Low
# enough to switch over early, high enough that one slow step cannot
# swing a rung's whole share.
MEAS_MIN = 30

# prove_step by ROUTED rung, ms: (n, mean, median, p90), low rung
# first.  Outer PERF 1009 span, joined to the rung via circ sel.
LEG_PROVE_RUNG = [
	(228489, 2138.7, 2016.0, 2481.0),
	(652933, 2716.6, 2612.0, 3145.0),
	(43231, 8837.0, 8544.0, 10017.0),
	(2247, 46335.2, 44577.0, 51880.0),
]
# gen advice by ROUTED rung, ms: (mean, median, p90).
LEG_ADV_RUNG = [
	(65.1, 47.0, 97.0), (100.4, 75.0, 149.0),
	(395.1, 332.0, 573.0), (2363.1, 2275.0, 2838.0),
]
# the INNER "-- prove_step cost: i:" span by circ_id (0-based == pci):
# (mean ms, median ms, stmt_len, wtns size).  Carries circ_id directly,
# so phase 3 buckets by rung with no join at all.
LEG_INNER_CIRC = [
	(1985.3, 1861.0, 132461, 198861),
	(2521.9, 2414.0, 299747, 449790),
	(8059.2, 7734.0, 1822059, 2733258),
	(42156.3, 40341.0, 12343537, 18515475),
]
# log-reported "Total RAM" at step 7, GB, one per job: 227 227 235 241
# 249 252 260 262.  The true peak runs higher -- quote
# PAPER_DATA_PEAK_RSS_GIB, not this.
LEG_RAM_GB = (227, 262, 244.1)
# mb_speed at step 7, MB/hr per job: 2.184 .. 2.341, mean 2.276.
LEG_MB_HR = (2.184, 2.341, 2.2757)

# ---- THE SHAPE OF EACH LONG STAGE.  Cumulative seconds a job spent to
# reach fraction 0.05, 0.10 ... 1.00 of that stage's work, averaged
# over the 8 jobs.  These matter enormously: PHASE 1 is SEVERELY
# front-loaded -- the corpus is ordered big-files-first, so the first 5%
# of words cost 26.3% of phase 1 (5.25x the linear rate).  Comparing an
# early neo cumulative mean against legacy's OVERALL mean would
# therefore condemn a perfectly healthy run.  Every projection below
# compares at the SAME fraction instead.
LEG_P1_CURVE = [5261, 7204, 8763, 9927, 10953, 11940, 12823, 13510,
	14108, 14680, 15266, 15834, 16389, 16941, 17463, 17981, 18491,
	18986, 19472, 19997]
# PHASE 3 is nearly linear (worst 1.13x at f=0.10, from the
# largest-circuit-first dispatch).
LEG_P3_CURVE = [19634, 41083, 59398, 77899, 96339, 114904, 133879,
	152345, 171861, 190442, 208139, 224725, 240539, 259705, 278878,
	297725, 315810, 333145, 349553, 363458]


def _build_tl():
	"""The legacy timeline: absolute seconds from process start for a
	MEAN job, stage by stage, as (label, t_start, t_end, shape curve).
	Accumulated from the constants above so the boundaries cannot drift
	out of step with them."""
	def mean2(p):
		return (p[0] + p[1]) / 2.0
	acc = [0.0]
	tl = []

	def add(label, dur, curve=None):
		tl.append((label, acc[0], acc[0] + dur, curve))
		acc[0] += dur
	add("setup: load DB", mean2(LEG_WF[1]))
	add("setup: split+discharge+NEEDS",
		mean2(LEG_WF[2]) + mean2(LEG_WF[3]) + mean2(LEG_WF[4]))
	add("ladder: capacity tuner", mean2(LEG_WF[5]))
	add("fold setup: keys+driver",
		mean2(LEG_FP[0]) + mean2(LEG_FP[1]) + mean2(LEG_FP[2]))
	add("phase 1 prep: step 1", LEG_STEP[1][0])
	add("PHASE 1: circ selection", LEG_STEP[2][0], LEG_P1_CURVE)
	add("PHASE 2: generate cmF", LEG_STEP[3][0])
	add("phase 3 prep: steps 4,5,6",
		LEG_STEP[4][0] + LEG_STEP[5][0] + LEG_STEP[6][0])
	add("PHASE 3: folding", LEG_STEP[7][0], LEG_P3_CURVE)
	add("phase 3 verify: step 8", LEG_STEP[8][0])
	add("PHASE 4: decider (part2)", LEG_DEC_TOTAL)
	return tl


LEG_TL = _build_tl()
# index of the decider stage; everything before it is what part1 does.
DEC_IDX = len(LEG_TL) - 1
# LEG_TL index of PHASE 1, the first stage neo times itself.  Anything
# before it is a legacy placeholder, so a comparison made there says
# nothing about the fold.
P1_IDX = 5
# the source string forecast() stamps on a stage neo never times.  Used
# to decide whether the run has produced ANY number of its own yet.
LEG_SRC = "legacy (neo does not time it)"
# mean-job wall WITHOUT the decider, and WITH it.
LEG_WALL_FOLD = LEG_TL[DEC_IDX][1]
LEG_WALL_ALL = LEG_TL[DEC_IDX][2]
# the measured part walls, for scale.  part1 436,316 s = 5.05 d is the
# referee.  It exceeds LEG_WALL_FOLD because a part ends with its
# SLOWEST job (see LEG_JOB_FOLD).
LEG_PART_WALL = (436316.03, 414194.18)
# which PERF 1007 step each small timeline stage is built from, so the
# forecast can substitute a measurement without a second lookup table.
TL_SMALL_STEPS = {4: [1], 7: [4, 5, 6], 9: [8]}

# ------------------------------------------------------------- regexes

# every marker below is emitted by an UNMODIFIED production LOG3 run;
# nothing here depends on a DEBUG probe.
RE_JOB = re.compile(r"^\[job (\d+)\]")
# per-circuit measured R1CS dims, emitted before the block's circs: N.
RE_CIRC = re.compile(
	r"PERF 1002 circ (\d+), r1cs cols: (\d+), rows: (\d+)")
# closes a preprocess block and states how many circuits it held.
RE_BLOCK = re.compile(
	r"preprocess\(\) Step 2: setup circ params\. circs: (\d+)")
# key/decider sizing for the block that just closed.
RE_KEYS = re.compile(
	r"KEYS info: n_circs: (\d+), total_w: (\d+), total_e: (\d+), "
	r"cs1e: (\d+), max_pp: (\d+)")
RE_DRIVER = re.compile(r"=== ZKP driver \(aggr\) starts ====")
# tuner verdict: rung count, occupancy histogram, the P_max top.
RE_GATE = re.compile(
	r"determine_config_aggr: (\d+) rungs, hist=\[([^\]]*)\], "
	r"P_max\.subsigs=(\d+)")
RE_V5 = re.compile(
	r"v5\[\S+\]: (\d+) rungs, occupancy hist=\[([^\]]*)\], "
	r"costs=\[([^\]]*)\]")
RE_RATCHET = re.compile(
	r"v5\[(\S+)\]: qm_real_rows (\d+) -> (\d+), re-walking")
RE_SHORT = re.compile(r"qm_real_rows still short after 3 re-walks")
# whole-part stage wall, LEGACY arm only (zkp_driver.rs).
RE_WF = re.compile(r"PERF WORKFLOW Step (\d+) time (\d+) ms")
# whole-part foldpot stage wall, BOTH arms.  NOTE the prefix is .*? and
# not [^0-9]*? -- "set up driver 1" carries a digit, and a no-digit
# class cannot reach past it to the timer.  Lazy .*? anchored on \s*$
# still captures the FINAL number in full, because no earlier digit run
# is followed by a unit at end of line.
RE_FP = re.compile(
	r"PERF 1005: FoldPot:? Step (\d+):.*?(\d+) (ms|us|ns)\s*$")
RE_ALLJOBS = re.compile(r"PERF 1005: === ALL JOBS === (\d+) ms")
# ---- neo pre-fold milestones.  The neo path logs these as plain LOG1
# text with no wall timer, so they are reached/not-reached only.
RE_M_DB = re.compile(r"loadClamDB from: (\S+)")
RE_M_FIN = re.compile(r"fast_finalize: (\d+) files")
RE_M_FOLD = re.compile(r"===== fold_pot starts with (\d+) jobs =====")
# ---- PERF 1007 per-job step wall.  The phase MATTERS: "Phase 1" is the
# main fold, "Phase 2" is the decider's own 8-14 step cyclepair fold.
# Mixing them would blend a 101-hour span with a 13-second one.
RE_STEP = re.compile(
	r"PERF 1007[.:] Phase (\d+) step (\d+):.*?(\d+) (ms|us|ns)\s*$")
RE_WORDS = re.compile(r"for words: (\d+), total_word_len: (\d+)")
RE_NSTEPS = re.compile(r"n_steps: (\d+)\. total_word_len")
RE_SPEED = re.compile(r"mb_speed ([0-9.]+) MB/hr")
RE_RAM = re.compile(r"(?:Total )?RAM: (\d+) GB")
RE_MEMGB = re.compile(r"MEM: (\d+) GB")
RE_START = re.compile(r"_(\d{8})_(\d{6})")
# ---- live progress markers ----
# PHASE 1, one line per WORD (driver.rs:2072, log_level+1 = LOG3).  The
# probe-free phase-1 meter: carries its own denominator and a gap timer
# that tiles phase 1 to 99.8%.
RE_P1_WORD = re.compile(
	r"Pass 1\. END generate advice word (\d+) of (\d+):.*?"
	r"(\d+) (ms|us|ns)\s*$")
# PHASE 1, one line per CHUNK, aggressive only (driver.rs:1957, LOG3).
# pci is the FINAL rung after bumps and is 0-based.
RE_SEL = re.compile(
	r"per-chunk circ sel\..*word_id: (\d+), subseg_id: (\d+), "
	r"fname: .*?, pci: (\d+)")
# PHASE 3, one line per word (driver.rs:2419, LOG1).
RE_P3_PROG = re.compile(r"PROGRESS fold \[[^\]]*\] word (\d+) of (\d+)")
# PHASE 3 sub-spans, all LOG3.  Each trailing value is a GAP timer: it
# measures the span that just ended.
RE_P3_ADV = re.compile(
	r"Pass 3\. gen advice for word_id: (\d+), seg_id: (\d+) "
	r"(\d+) (ms|us|ns)\s*$")
RE_P3_STMT = re.compile(r"Pass 3\. gen stmt (\d+) (ms|us|ns)\s*$")
RE_P3_LK = re.compile(
	r"Pass 3\. update lkup: share size: \d+ (\d+) (ms|us|ns)\s*$")
# the INNER prove_step, mod_super.rs:2027 at log_level-1 = LOG3.  Its
# circ_id is field_to_usize(pc_i1) -- 0-BASED and equal to pci (the "1"
# means pc_{i+1}, not 1-based), so phase 3 buckets by rung with no join.
RE_P3_INNER = re.compile(
	r"-- prove_step cost: i: (\d+), circ_id: (\d+), stmt_len: (\d+), "
	r"wtns size: (\d+) (\d+) (ms|us|ns)\s*$")
# the OUTER prove_step, driver.rs:2524 at log_level+1 = LOG3.  This is
# the span LEG_PROVE_MS was measured from.
RE_P3_OUTER = re.compile(
	r"Pass 3\. prove_step cost for word_id: (\d+), seg_id: (\d+), "
	r"stmt_len: (\d+) (\d+) (ms|us|ns)\s*$")
# ---- PHASE 4, the decider.  Only part2's proving job emits these.
RE_P4_STEP = re.compile(
	r"PERF 1006: Job Step (\d+): .*?(\d+) (ms|us|ns)\s*$")
RE_P4_FOLDDONE = re.compile(
	r"PERF 1006\. Job Step 1: main circuits IVC PROVE STEPS "
	r"\(Folding\) DONE.*?(\d+) (ms|us|ns)\s*$")
RE_P4_MAIN_CS = re.compile(
	r"\*\*\* MainDeciderCirtuit TOTAL constraints: (\d+) \*\*\*")
RE_P4_CP_CS = re.compile(
	r"\*\*\* CyclePairCirc TOTAL constraints: (\d+) \*\*\*")
RE_P4_VERIFY = re.compile(r"FOLDPOT Step 13\. Verify Individual Proof")
RE_P4_BATCH = re.compile(r"==== BatchProof ====")
RE_FOLDONLY = re.compile(r"b_folding_only set, no snark generated")
RE_VERIFY_FAIL = re.compile(r"PROOF VERIFICATION FAILED")

# cheap substring gate: a line holding none of these can never match
# any regex above, and skipping it early is what keeps a full rescan of
# a 1 GB log inside a few seconds.
HOT = ("PERF 1", "PERF W", "PROGRESS fold", "prove_step cost",
	"determine_config_aggr", "v5[", "preprocess()", "KEYS info",
	"ZKP driver", "qm_real_rows", "loadClamDB", "fast_finalize",
	"fold_pot starts", "MainDeciderCirtuit", "CyclePairCirc",
	"FOLDPOT Step 13", "BatchProof", "b_folding_only set",
	"VERIFICATION FAILED")


def dur_ms(val, unit):
	"""A log_perf gap-timer value in ms.  log_perf only ever emits ns,
	us or ms (logger.rs:203)."""
	n = float(val)
	return n / 1e6 if unit == "ns" else (n / 1e3 if unit == "us" else n)


def hm(sec):
	"""Seconds as 'Hh MMm'."""
	sec = int(max(sec, 0))
	return "%dh %02dm" % (sec // 3600, (sec % 3600) // 60)


def clocks(epoch):
	"""An epoch as 'Day HH:MM srv / Day HH:MM you', both clocks."""
	srv = time.strftime("%a %H:%M", time.localtime(epoch))
	mine = time.strftime("%a %H:%M",
		time.localtime(epoch + MY_OFFSET_H * 3600.0))
	return "%s srv / %s you" % (srv, mine)


def com(n):
	"""Integer with thousands separators, or '-' for None."""
	return "-" if n is None else "{:,}".format(int(n))


def med(v):
	"""Median of a list, 0.0 when empty."""
	if not v:
		return 0.0
	v = sorted(v)
	k = len(v) // 2
	return v[k] if len(v) % 2 else (v[k - 1] + v[k]) / 2.0


def mem_gb():
	"""(total, available) RAM in GB from /proc/meminfo, or (0, 0)."""
	vals = {}
	try:
		with open("/proc/meminfo") as fh:
			for ln in fh:
				bits = ln.split()
				if len(bits) >= 2:
					vals[bits[0].rstrip(":")] = int(bits[1])
	except (IOError, OSError, ValueError):
		return 0, 0
	return (vals.get("MemTotal", 0) // 1048576,
		vals.get("MemAvailable", 0) // 1048576)


# ------------------------------------------------------- shape helpers

def curve_sec(curve, f):
	"""Seconds a legacy job had spent to reach work fraction f of a
	stage, linearly interpolated between the 5% samples."""
	f = min(max(f, 0.0), 1.0)
	if f <= 0:
		return 0.0
	x = f * len(curve)
	i = int(x) - 1
	if i >= len(curve) - 1:
		return float(curve[-1])
	lo = float(curve[i]) if i >= 0 else 0.0
	hi = float(curve[i + 1])
	return lo + (hi - lo) * (x - int(x))


def curve_frac(curve, sec):
	"""Inverse of curve_sec: the work fraction a legacy job had reached
	after `sec` seconds in the stage."""
	if sec <= 0:
		return 0.0
	if sec >= curve[-1]:
		return 1.0
	prev_t, prev_f = 0.0, 0.0
	for i, t in enumerate(curve):
		f = (i + 1) / float(len(curve))
		if sec <= t:
			span = t - prev_t
			if span <= 0:
				return f
			return prev_f + (f - prev_f) * (sec - prev_t) / span
		prev_t, prev_f = float(t), f
	return 1.0


def leg_time_at(idx, frac):
	"""Absolute legacy seconds (from process start, mean job) at which
	legacy stood `frac` of the way through stage `idx`.  This is the
	'legacy-equivalent time' every comparison below rests on."""
	_label, t0, t1, curve = LEG_TL[idx]
	frac = min(max(frac, 0.0), 1.0)
	if curve:
		return t0 + curve_sec(curve, frac)
	return t0 + (t1 - t0) * frac


def leg_at_time(t):
	"""(stage index, work fraction in it) legacy had reached at absolute
	second t."""
	for i, (_label, t0, t1, curve) in enumerate(LEG_TL):
		if t < t1 or i == len(LEG_TL) - 1:
			if t <= t0:
				return i, 0.0
			if curve:
				return i, curve_frac(curve, t - t0)
			span = t1 - t0
			return i, min((t - t0) / span, 1.0) if span > 0 else 1.0
	return len(LEG_TL) - 1, 1.0


def short_stage(label):
	"""A stage label trimmed to fit the hourly table."""
	return (label.replace("PHASE ", "P").replace("phase ", "p")
		.replace("setup: ", "").replace("ladder: ", "")[:23])


class Samples(object):
	"""Bounded, decimating sample set: exact count and sum for every
	value, plus a capped list good enough for a median.  Keeps memory
	flat across the ~926,900 fold steps a full run emits."""

	CAP = 4000

	def __init__(self, st=None):
		# n: values seen.  s: their sum.  keep: take every keep-th.
		# v: retained values.  seen: values offered since the last
		# retained one, so decimation survives a resumed scan.
		self.n = st["n"] if st else 0
		self.s = st["s"] if st else 0.0
		self.keep = st["keep"] if st else 1
		self.v = list(st["v"]) if st else []
		self.seen = st["seen"] if st else 0

	def add(self, x):
		self.n += 1
		self.s += x
		self.seen += 1
		if self.seen >= self.keep:
			self.seen = 0
			self.v.append(x)
			if len(self.v) > self.CAP:
				self.v = self.v[1::2]
				self.keep *= 2

	def mean(self):
		return self.s / self.n if self.n else 0.0

	def dump(self):
		return {"n": self.n, "s": self.s, "keep": self.keep,
			"v": self.v, "seen": self.seen}


class Acc(object):
	"""Everything one log contributes, accumulated so a resumed scan
	never re-reads bytes it has already consumed."""

	def __init__(self, st=None):
		st = st or {}
		# bytes of this log already folded in, and the inode they were
		# read at -- a shrink or inode change forces a full rescan.
		self.off = st.get("off", 0)
		self.ino = st.get("ino", 0)
		self.lines = st.get("lines", 0)
		# routing counts over COMPLETED words only, 0-based rung.
		self.sel = list(st.get("sel", [0, 0, 0, 0]))
		# per job, the word still being emitted: [word_id, [c0..c3]].
		# Held back so an in-flight word cannot skew the shares, and
		# folded into self.sel as soon as a higher word_id appears.
		self.sel_cur = {int(k): v
			for k, v in st.get("sel_cur", {}).items()}
		# PHASE 1: END-of-word lines seen, their gap-timer spread, the
		# highest word each job reached, and the "of N" denominator.
		self.p1_n = st.get("p1_n", 0)
		self.p1_ms = Samples(st.get("p1_ms"))
		self.p1_hi = {int(k): v for k, v in st.get("p1_hi", {}).items()}
		self.p1_total = st.get("p1_total", 0)
		# PHASE 3: per-word progress, highest word and denominator.
		self.p3_hi = {int(k): v for k, v in st.get("p3_hi", {}).items()}
		self.p3_total = st.get("p3_total", 0)
		# PHASE 3 spans bucketed by the 0-based circ_id the inner
		# prove_step line carries.  pend holds the advice/stmt/lkup of
		# the step in flight per job until that circ_id arrives; pend_r
		# holds the circ_id until the outer span arrives.
		self.inner = {r: Samples(st.get("inner", {}).get(str(r)))
			for r in range(4)}
		self.outer = {r: Samples(st.get("outer", {}).get(str(r)))
			for r in range(4)}
		self.adv = {r: Samples(st.get("adv", {}).get(str(r)))
			for r in range(4)}
		self.stmt = Samples(st.get("stmt"))
		self.lkup = Samples(st.get("lkup"))
		self.pend = {int(k): v for k, v in st.get("pend", {}).items()}
		self.pend_r = {int(k): v
			for k, v in st.get("pend_r", {}).items()}
		# per-job PERF 1007 step wall in ms, keyed "<phase> <step>".
		self.step = {k: {int(j): x for j, x in v.items()}
			for k, v in st.get("step", {}).items()}
		# whole-part PERF WORKFLOW wall in ms (legacy arm only).
		self.wf = {int(k): v for k, v in st.get("wf", {}).items()}
		# whole-part PERF 1005 FoldPot wall in ms, and === ALL JOBS ===.
		self.fp = {int(k): v for k, v in st.get("fp", {}).items()}
		self.alljobs = st.get("alljobs")
		# neo pre-fold milestones: the plan dir the DB loaded from, the
		# file count the tuner bound, the job count the fold opened
		# with.  None until the run reaches each one.
		self.m_db = st.get("m_db")
		self.m_fin = st.get("m_fin")
		self.m_fold = st.get("m_fold")
		# per-job corpus shape from step 1 / step 7.
		self.words = {int(k): v for k, v in st.get("words", {}).items()}
		self.fields = {int(k): v
			for k, v in st.get("fields", {}).items()}
		self.nsteps = {int(k): v
			for k, v in st.get("nsteps", {}).items()}
		# preprocess blocks: [n_circs, {idx: [cols, rows]}, after_driver]
		self.blocks = st.get("blocks", [])
		self.pending = {int(k): v
			for k, v in st.get("pending", {}).items()}
		self.after = st.get("after", False)
		self.keys = st.get("keys")
		self.gate = st.get("gate")
		self.v5 = st.get("v5")
		self.ratchet = st.get("ratchet", [])
		self.short = st.get("short", False)
		self.ram = st.get("ram", 0)
		self.speed = st.get("speed")
		self.jobs = set(st.get("jobs", []))
		# PHASE 4: per-step wall in ms keyed by PERF 1006 Job Step
		# index, the peak MEM those steps reported, the two decider
		# circuit sizes, the per-job fold-done wall, and the terminal
		# markers PAPER_DATA.py itself scores the run on.
		self.p4 = {int(k): v for k, v in st.get("p4", {}).items()}
		self.p4_mem = st.get("p4_mem", 0)
		self.main_cs = st.get("main_cs")
		self.cp_cs = st.get("cp_cs")
		self.folddone = {int(k): v
			for k, v in st.get("folddone", {}).items()}
		self.verified = st.get("verified", 0)
		self.batchproof = st.get("batchproof", 0)
		self.foldonly = st.get("foldonly", 0)
		self.vfail = st.get("vfail", 0)

	def dump(self):
		return {
			"off": self.off, "ino": self.ino, "lines": self.lines,
			"sel": self.sel,
			"sel_cur": {str(k): v for k, v in self.sel_cur.items()},
			"p1_n": self.p1_n, "p1_ms": self.p1_ms.dump(),
			"p1_hi": {str(k): v for k, v in self.p1_hi.items()},
			"p1_total": self.p1_total,
			"p3_hi": {str(k): v for k, v in self.p3_hi.items()},
			"p3_total": self.p3_total,
			"inner": {str(r): s.dump() for r, s in self.inner.items()},
			"outer": {str(r): s.dump() for r, s in self.outer.items()},
			"adv": {str(r): s.dump() for r, s in self.adv.items()},
			"stmt": self.stmt.dump(), "lkup": self.lkup.dump(),
			"pend": {str(k): v for k, v in self.pend.items()},
			"pend_r": {str(k): v for k, v in self.pend_r.items()},
			"step": self.step,
			"wf": {str(k): v for k, v in self.wf.items()},
			"fp": {str(k): v for k, v in self.fp.items()},
			"alljobs": self.alljobs, "m_db": self.m_db,
			"m_fin": self.m_fin, "m_fold": self.m_fold,
			"words": {str(k): v for k, v in self.words.items()},
			"fields": {str(k): v for k, v in self.fields.items()},
			"nsteps": {str(k): v for k, v in self.nsteps.items()},
			"blocks": self.blocks,
			"pending": {str(k): v for k, v in self.pending.items()},
			"after": self.after, "keys": self.keys, "gate": self.gate,
			"v5": self.v5, "ratchet": self.ratchet,
			"short": self.short, "ram": self.ram, "speed": self.speed,
			"jobs": sorted(self.jobs),
			"p4": {str(k): v for k, v in self.p4.items()},
			"p4_mem": self.p4_mem, "main_cs": self.main_cs,
			"cp_cs": self.cp_cs,
			"folddone": {str(k): v for k, v in self.folddone.items()},
			"verified": self.verified,
			"batchproof": self.batchproof, "foldonly": self.foldonly,
			"vfail": self.vfail,
		}

	# ------------------------------------------------------ consuming

	def close_word(self, job):
		"""Fold a job's finished word into the routing totals."""
		cur = self.sel_cur.pop(job, None)
		if cur:
			for i in range(4):
				self.sel[i] += cur[1][i]

	def feed(self, ln):
		self.lines += 1
		if not any(h in ln for h in HOT):
			return
		m = RE_JOB.match(ln)
		job = int(m.group(1)) if m else -1
		if job >= 0:
			self.jobs.add(job)
		if "per-chunk circ sel" in ln:
			m = RE_SEL.search(ln)
			if m:
				w, p = int(m.group(1)), int(m.group(3))
				cur = self.sel_cur.get(job)
				if cur is None or cur[0] != w:
					if cur is not None and w > cur[0]:
						self.close_word(job)
					self.sel_cur[job] = [w, [0, 0, 0, 0]]
					cur = self.sel_cur[job]
				if p < 4:
					cur[1][p] += 1
			return
		if "prove_step cost" in ln:
			m = RE_P3_INNER.search(ln)
			if m:
				r = int(m.group(2))
				if r < 4:
					self.inner[r].add(dur_ms(m.group(5), m.group(6)))
					# the three spans banked since this job's last step
					# belong to THIS step, whose rung is only knowable
					# here -- the inner line is the first to name it.
					pd = self.pend.pop(job, None)
					if pd:
						self.adv[r].add(pd[0])
						self.stmt.add(pd[1])
						self.lkup.add(pd[2])
					self.pend_r[job] = r
				return
			m = RE_P3_OUTER.search(ln)
			if m:
				r = self.pend_r.pop(job, None)
				if r is not None:
					self.outer[r].add(dur_ms(m.group(4), m.group(5)))
			return
		if "Pass 3." in ln:
			m = RE_P3_ADV.search(ln)
			if m:
				self.pend[job] = [dur_ms(m.group(3), m.group(4)),
					0.0, 0.0]
				return
			m = RE_P3_STMT.search(ln)
			if m and job in self.pend:
				self.pend[job][1] = dur_ms(m.group(1), m.group(2))
				return
			m = RE_P3_LK.search(ln)
			if m and job in self.pend:
				self.pend[job][2] = dur_ms(m.group(1), m.group(2))
			return
		if "Pass 1. END" in ln:
			m = RE_P1_WORD.search(ln)
			if m:
				self.p1_n += 1
				self.p1_ms.add(dur_ms(m.group(3), m.group(4)))
				self.p1_hi[job] = max(self.p1_hi.get(job, 0),
					int(m.group(1)))
				self.p1_total = int(m.group(2))
			return
		if "PROGRESS fold" in ln:
			m = RE_P3_PROG.search(ln)
			if m:
				self.p3_hi[job] = max(self.p3_hi.get(job, 0),
					int(m.group(1)))
				self.p3_total = int(m.group(2))
			return
		self.feed_slow(ln, job)

	def feed_slow(self, ln, job):
		"""The one-shot markers: ladder, keys, gate, stage walls, the
		decider chain.  Each fires a handful of times per run, so cost
		does not matter."""
		if "PERF 1006" in ln:
			m = RE_P4_FOLDDONE.search(ln)
			if m:
				self.folddone[job] = dur_ms(m.group(1), m.group(2))
				return
			m = RE_P4_STEP.search(ln)
			if m:
				self.p4[int(m.group(1))] = dur_ms(
					m.group(2), m.group(3))
				m2 = RE_MEMGB.search(ln)
				if m2:
					self.p4_mem = max(self.p4_mem, int(m2.group(1)))
			return
		m = RE_P4_MAIN_CS.search(ln)
		if m:
			self.main_cs = int(m.group(1))
			return
		m = RE_P4_CP_CS.search(ln)
		if m:
			self.cp_cs = int(m.group(1))
			return
		if RE_P4_VERIFY.search(ln):
			self.verified += 1
			return
		if RE_P4_BATCH.search(ln):
			self.batchproof += 1
			return
		if RE_FOLDONLY.search(ln):
			self.foldonly += 1
			return
		if RE_VERIFY_FAIL.search(ln):
			self.vfail += 1
			return
		if RE_DRIVER.search(ln):
			self.after = True
			return
		m = RE_CIRC.search(ln)
		if m:
			self.pending[int(m.group(1))] = [int(m.group(2)),
				int(m.group(3))]
			return
		m = RE_BLOCK.search(ln)
		if m:
			self.blocks.append([int(m.group(1)), self.pending,
				self.after])
			self.pending = {}
			return
		m = RE_KEYS.search(ln)
		if m:
			if int(m.group(1)) > 1:
				self.keys = [int(m.group(i)) for i in range(1, 6)]
			return
		m = RE_STEP.search(ln)
		if m:
			key = "%s %s" % (m.group(1), m.group(2))
			self.step.setdefault(key, {})[job] = dur_ms(
				m.group(3), m.group(4))
			# corpus shape and RAM come only from the MAIN fold; the
			# decider's Phase 2 steps carry a 14-word toy corpus that
			# would otherwise overwrite the real denominators.
			if m.group(1) == "1":
				m2 = RE_WORDS.search(ln)
				if m2:
					self.words[job] = int(m2.group(1))
					self.fields[job] = int(m2.group(2))
				m2 = RE_NSTEPS.search(ln)
				if m2:
					self.nsteps[job] = int(m2.group(1))
				m2 = RE_RAM.search(ln)
				if m2:
					self.ram = max(self.ram, int(m2.group(1)))
				m2 = RE_SPEED.search(ln)
				if m2:
					self.speed = float(m2.group(1))
			return
		m = RE_WF.search(ln)
		if m:
			self.wf[int(m.group(1))] = float(m.group(2))
			return
		m = RE_ALLJOBS.search(ln)
		if m:
			self.alljobs = float(m.group(1))
			return
		m = RE_FP.search(ln)
		if m:
			self.fp[int(m.group(1))] = dur_ms(m.group(2), m.group(3))
			return
		m = RE_M_DB.search(ln)
		if m:
			self.m_db = m.group(1)
			return
		m = RE_M_FIN.search(ln)
		if m:
			self.m_fin = int(m.group(1))
			return
		m = RE_M_FOLD.search(ln)
		if m:
			self.m_fold = int(m.group(1))
			return
		m = RE_GATE.search(ln)
		if m:
			self.gate = [int(m.group(1)), m.group(2), int(m.group(3))]
			return
		m = RE_V5.search(ln)
		if m:
			self.v5 = [int(m.group(1)), m.group(2), m.group(3)]
			return
		m = RE_RATCHET.search(ln)
		if m:
			self.ratchet.append([int(m.group(2)), int(m.group(3))])
			return
		if RE_SHORT.search(ln):
			self.short = True


def scan(path, acc, rescan):
	"""Fold the bytes of path not yet consumed into acc; returns the
	number of new bytes read.  A partial trailing line is left for the
	next invocation rather than parsed half-formed."""
	try:
		stt = os.stat(path)
	except OSError:
		return 0
	if rescan or stt.st_ino != acc.ino or stt.st_size < acc.off:
		acc.__dict__.update(Acc().__dict__)
	start = acc.off
	with open(path, "rb") as fh:
		fh.seek(start)
		off = start
		for raw in fh:
			if not raw.endswith(b"\n"):
				break
			off += len(raw)
			acc.feed(raw.decode("utf-8", "replace"))
	acc.off = off
	acc.ino = stt.st_ino
	return off - start


# ------------------------------------------------------------- merging

class Run(object):
	"""The whole run: one Acc per part, merged for reporting."""

	def __init__(self, accs, njobs):
		self.accs = accs
		self.njobs = njobs

	def routing(self):
		out = [0, 0, 0, 0]
		for a in self.accs:
			for i, c in enumerate(a.sel):
				out[i] += c
		return out

	def ladder(self):
		"""(n_circs, {idx: (cols, rows)}, tag) for the production fold:
		the last block holding more than one circuit.  A circs: 1 block
		is the side fold, not the prod one."""
		for a in self.accs:
			multi = [b for b in a.blocks if b[0] > 1]
			if multi:
				b = multi[-1]
				return (b[0], {int(k): tuple(v)
					for k, v in b[1].items()},
					"prod fold" if b[2] else "PRE-DRIVER (tuner)")
			if a.pending:
				return (len(a.pending), {int(k): tuple(v)
					for k, v in a.pending.items()}, "IN FLIGHT")
		return None

	def v5_hist(self):
		"""v5 walk occupancy as 4 per-rung WORD counts, or None."""
		v5 = next((a.v5 for a in self.accs if a.v5), None)
		if not v5:
			return None
		try:
			h = [int(x) for x in v5[1].split(",") if x.strip()]
		except ValueError:
			return None
		return h if len(h) == 4 else None

	def ladder_dict(self):
		"""Just the {idx: (cols, rows)} map, or {}."""
		lad = self.ladder()
		return lad[1] if lad else {}

	def step_wall(self, step, phase="1"):
		"""(mean per-job wall in seconds, jobs reporting) for a PERF
		1007 step of the given PHASE.  Phase 1 is the main fold; phase 2
		is the decider's own tiny cyclepair fold, and blending them
		would mix a 101-hour span with a 13-second one."""
		vals = []
		for a in self.accs:
			vals.extend(a.step.get("%s %d" % (phase, step), {}).values())
		if not vals:
			return None, 0
		return sum(vals) / len(vals) / 1000.0, len(vals)

	def steps_per_job(self):
		"""Fold steps ONE job will prove.  Averaged over the jobs that
		have reported, never summed and divided by an assumed job count
		-- early on only some jobs have logged, and dividing their sum
		by 8 would halve every projection."""
		v = [x for a in self.accs for x in a.nsteps.values()]
		if v:
			return sum(v) / float(len(v))
		v = [x for a in self.accs for x in a.fields.values()]
		if v:
			return sum(v) / float(len(v)) / SEG_WORD_LEN
		return LEG_STEPS

	def total_steps(self):
		"""Fold steps the whole run will prove, over every job."""
		return int(self.steps_per_job() * self.njobs)

	def words_per_job(self):
		"""Words ONE job owns, from PERF 1008's own 'of N' term."""
		return max([a.p1_total for a in self.accs] + [0]) or LEG_WORDS

	def p1_done(self):
		return sum(a.p1_n for a in self.accs)

	def p3_done(self):
		return sum(a.outer[r].n for a in self.accs for r in range(4))

	def p1_span_s(self):
		"""(seconds of phase 1 accounted over all jobs, words counted).
		The PERF 1008 gap timers are per-job serial spans that tile
		phase 1, so their sum over a job IS that job's phase-1 wall --
		on the legacy run they recover 19,997 s of the 20,034 s step-2
		wall, 99.8%.  A wall estimate is therefore available from ONE
		reading, with no rate and no second look."""
		return (sum(a.p1_ms.s for a in self.accs) / 1000.0,
			sum(a.p1_ms.n for a in self.accs))

	def p3_span_s(self):
		"""(seconds of phase 3 accounted over all jobs, steps counted).
		Same trick: the four per-step spans tile step 7 to 0.12%."""
		ms = 0.0
		n = 0
		for a in self.accs:
			for r in range(4):
				ms += a.outer[r].s + a.adv[r].s
				n += a.outer[r].n
			ms += a.stmt.s + a.lkup.s
		return ms / 1000.0, n

	def merged(self, attr):
		"""Per-rung Samples merged across parts into (n, mean, med)."""
		out = {}
		for r in range(4):
			n = sum(getattr(a, attr)[r].n for a in self.accs)
			s = sum(getattr(a, attr)[r].s for a in self.accs)
			v = []
			for a in self.accs:
				v.extend(getattr(a, attr)[r].v)
			out[r] = (n, s / n if n else 0.0, med(v))
		return out

	def flat(self, attr):
		"""A plain Samples merged across parts into (n, mean, med)."""
		n = sum(getattr(a, attr).n for a in self.accs)
		s = sum(getattr(a, attr).s for a in self.accs)
		v = []
		for a in self.accs:
			v.extend(getattr(a, attr).v)
		return n, (s / n if n else 0.0), med(v)

	def p4(self):
		"""PERF 1006 decider steps merged: {step index: seconds}."""
		out = {}
		for a in self.accs:
			for k, v in a.p4.items():
				out[k] = max(out.get(k, 0.0), v / 1000.0)
		return out

	def gate(self):
		return next((a.gate for a in self.accs if a.gate), None)

	def keys(self):
		return next((a.keys for a in self.accs if a.keys), None)

	def sum_attr(self, attr):
		return sum(getattr(a, attr) for a in self.accs)

	# -------------------------------------------------- where we stand

	def position(self):
		"""(stage index into LEG_TL, work fraction in that stage) -- the
		single fact every comparison and forecast rests on.  Tested
		latest-stage-first so a finished stage always outranks an
		earlier one."""
		p4 = self.p4()
		if p4 or any(a.main_cs for a in self.accs):
			done = sum(x[2] for x in LEG_DEC if x[0] in p4)
			return DEC_IDX, min(done / LEG_DEC_TOTAL, 1.0)
		if any(a.folddone for a in self.accs):
			return DEC_IDX, 0.0
		if self.step_wall(8)[0] is not None:
			return 9, 1.0
		n3 = self.p3_done()
		if n3:
			return 8, min(n3 / float(max(self.total_steps(), 1)), 1.0)
		if self.step_wall(6)[0] is not None:
			return 8, 0.0
		if self.step_wall(4)[0] is not None:
			return 7, 0.5
		if self.step_wall(3)[0] is not None:
			return 7, 0.0
		if self.step_wall(2)[0] is not None:
			return 6, 0.0          # phase 2, and it is silent at LOG3
		n1 = self.p1_done()
		if n1:
			tot = self.words_per_job() * self.njobs
			return 5, min(n1 / float(max(tot, 1)), 1.0)
		if self.step_wall(1)[0] is not None:
			return 5, 0.0
		if any(a.fp for a in self.accs):
			return 3, 0.5
		if self.gate():
			return 3, 0.0
		if any(a.m_fin for a in self.accs):
			return 2, 0.5
		if any(a.m_db for a in self.accs):
			return 1, 0.5
		return 0, 0.5


# ------------------------------------------------------------- models

def fit_affine(ladder, mix, rung_ms):
	"""(slope ms/col, fixed ms, residuals) of a chunk-share-weighted
	least-squares fit of prove_step against circuit cols.  prove_step is
	NOT proportional to cols -- the fit carries a large intercept, so a
	linear rescale over-credits a smaller ladder.  On the legacy numbers
	this reproduces all four rungs within 5.4%."""
	pts = [(ladder[i + 1][0], rung_ms[i], mix[i] / 100.0)
		for i in range(4) if (i + 1) in ladder]
	sw = sum(p[2] for p in pts)
	if sw <= 0 or len(pts) < 2:
		return None
	mx = sum(p[0] * p[2] for p in pts) / sw
	my = sum(p[1] * p[2] for p in pts) / sw
	sxx = sum(p[2] * (p[0] - mx) ** 2 for p in pts)
	sxy = sum(p[2] * (p[0] - mx) * (p[1] - my) for p in pts)
	if sxx <= 0:
		return None
	slope = sxy / sxx
	fixed = my - slope * mx
	return slope, fixed, [(slope * p[0] + fixed) / p[1] - 1.0
		for p in pts]


LEG_FIT = fit_affine(LEG_LADDER, LEG_MIX,
	[LEG_PROVE_RUNG[i][1] for i in range(4)])


def weighted(ladder, mix, col=0):
	"""Occupancy-weighted circuit size.  Per-rung ratios mislead: one
	rung carries most chunks, so the weighting is what says whether
	total fold cost is comparable."""
	tot = sum(mix)
	if tot <= 0:
		return None
	return sum(ladder[i + 1][col] * mix[i] / tot
		for i in range(4) if (i + 1) in ladder)


def pick_inputs(got, mix, v5=None):
	"""(ladder, ladder source, mix, mix source) for every projection.
	Best available first: this run's own numbers, then the 08-16
	full-scale neo reference this run is expected to reproduce, then
	legacy.  One place decides so every section agrees."""
	if sum(mix):
		m, ms = mix, "measured"
	elif v5 and sum(v5):
		m, ms = v5, "v5 occupancy"
	else:
		# nothing neo-derived exists yet.  Both halves stay on the
		# LEGACY arm: neo's ladder priced with legacy's routing pays
		# neo's oversized rung 2 at legacy's rate of using it, which
		# describes no run (1.495x vs 1.000x legacy, 0.835x neo).
		return LEG_LADDER, "legacy placeholder", LEG_MIX, \
			"legacy placeholder"
	# a partial ladder still prices the run when it covers every rung
	# that carries work; falling back would drop that rung's hours.
	if got and not [r for r in range(1, 5)
			if m[r - 1] > 0 and r not in got]:
		return got, "measured", m, ms
	return NEO_REF_LADDER, "08-16 neo ref", m, ms


def project_step_ms(lad, m):
	"""(ms per fold step, prove_step ms) for a ladder and routing mix,
	from the legacy affine fit."""
	if not LEG_FIT or not lad or len(lad) < 4:
		return None
	slope, fixed, _res = LEG_FIT
	tot = float(sum(m))
	if tot <= 0:
		return None
	pv = sum((slope * lad[i + 1][0] + fixed) * m[i] / tot
		for i in range(4))
	# advice re-weighted from the legacy per-rung table; stmt, lkup and
	# the unaccounted remainder are held flat -- together they are 2% of
	# a step, so their error cannot move the verdict.
	pa = sum(LEG_ADV_RUNG[i][0] * m[i] / tot for i in range(4))
	return (pv + pa + LEG_STMT_MS + LEG_LKUP_MS + LEG_UNACCOUNTED_MS,
		pv)


def p1_projection(run):
	"""(projected phase-1 wall per job in seconds, ratio vs legacy at
	the SAME fraction, fraction done, legacy seconds at that fraction)
	or None.

	The shape is everything here.  Legacy spends 26.3% of phase 1 on the
	first 5% of words, so extrapolating an early neo rate linearly would
	inflate the estimate ~5x.  Instead: take the seconds neo has spent
	to reach fraction f, divide by the seconds LEGACY spent to reach
	that same f, and scale legacy's total by that ratio."""
	span_s, span_n = run.p1_span_s()
	if not span_n:
		return None
	tot = run.words_per_job() * run.njobs
	f = min(span_n / float(max(tot, 1)), 1.0)
	leg = curve_sec(LEG_P1_CURVE, f)
	if f <= 0 or leg <= 0:
		return None
	# span_s is summed over jobs; per-job seconds is the comparable term
	ratio = (span_s / run.njobs) / leg
	return LEG_STEP[2][0] * ratio, ratio, f, leg


def p3_projection(run, mix, got):
	"""(projected phase-3 wall per job in seconds, source, fraction,
	model value, shape value).

	Two estimators.  The MODEL rescales legacy prove_step onto this
	run's ladder and routing and is steady from the first step.  The
	SHAPE estimator divides neo's own seconds-so-far by legacy's seconds
	at the same fraction; it is exact late but reads high early, because
	steps are dispatched largest-circuit-first.  Measured: at 3.9% of
	the legacy fold the model was within 0.2% while the raw spans read
	15% high, so the model leads until a quarter of the fold is done."""
	steps = run.steps_per_job()
	span_s, span_n = run.p3_span_s()
	lad, ls, m, ms = pick_inputs(got, mix, run.v5_hist())
	pr = project_step_ms(lad, m)
	model = pr[0] * steps / 1000.0 if pr else None
	msrc = ("legacy-fitted cost model"
		if ls == ms == "legacy placeholder"
		else "legacy fit on %s + %s" % (ls, ms))
	shape = None
	f = 0.0
	if span_n:
		f = min(span_n / float(max(run.total_steps(), 1)), 1.0)
		leg = curve_sec(LEG_P3_CURVE, f)
		if leg > 0:
			shape = LEG_STEP[7][0] * (span_s / run.njobs) / leg
	if shape is not None and f >= 0.25:
		return shape, "own spans at the same point", f, model, shape
	if model is not None:
		return model, msrc, f, model, shape
	return shape, "own spans at the same point", f, model, shape


def forecast(run, mix, got):
	"""[(seconds, source)] for the whole per-job timeline, index-matched
	to LEG_TL: measured where the run has finished a stage, projected
	where it has not, legacy where neo does not time it at all."""
	out = []
	p1p = p1_projection(run)
	p3p = p3_projection(run, mix, got)
	keys = run.keys()
	p4 = run.p4()
	dec_idx = [x[0] for x in LEG_DEC]
	for i, (_label, t0, t1, _c) in enumerate(LEG_TL):
		leg = t1 - t0
		val, src = leg, LEG_SRC
		if i == P1_IDX:                         # PHASE 1
			m = run.step_wall(2)[0]
			if m is not None:
				val, src = m, "measured"
			elif p1p:
				val, src = p1p[0], "shape projection"
		elif i == 6:                            # PHASE 2 cmF
			m = run.step_wall(3)[0]
			if m is not None:
				val, src = m, "measured"
			elif keys:
				# cmF commits to the witness, so total_w is the term
				# that moves.
				val = leg * keys[1] / float(LEG_TOTAL_W)
				src = "scaled by total_w"
		elif i == 8:                            # PHASE 3 fold
			m = run.step_wall(7)[0]
			if m is not None:
				val, src = m, "measured"
			elif p3p[0]:
				val, src = p3p[0], p3p[1]
		elif i == DEC_IDX:                      # PHASE 4 decider
			if p4:
				done = sum(v for k, v in p4.items() if k in dec_idx)
				todo = sum(x[2] for x in LEG_DEC if x[0] not in p4)
				val, src = done + todo, "measured so far + legacy rest"
		elif i == 3:                            # fold setup
			merged = {}
			for a in run.accs:
				for k, v in a.fp.items():
					merged[k] = max(merged.get(k, 0), v)
			have = sum(merged.get(k, 0) for k in (0, 1, 2)) / 1000.0
			if have > 0:
				val, src = have, "measured"
		elif i in TL_SMALL_STEPS:               # small per-job steps
			acc, ok = 0.0, True
			for st in TL_SMALL_STEPS[i]:
				m = run.step_wall(st)[0]
				if m is None:
					ok = False
					break
				acc += m
			if ok:
				val, src = acc, "measured"
		out.append((val, src))
	return out


# ------------------------------------------------------------ sections

def show_header(paths, accs, new_bytes, dt):
	"""Log identity, elapsed wall, liveness, scan cost."""
	print("=" * 72)
	print("full_dlp NEO meter -- vs the MEASURED legacy full_dlp run")
	print("=" * 72)
	el, src = None, ""
	for p, a in zip(paths, accs):
		age = time.time() - os.path.getmtime(p)
		tag = "part2" if "part2" in p else "part1"
		role = " (PROVES)" if tag == "part2" else " (fold only)"
		print("log %s%s: %s" % (tag, role, p))
		print("             %s lines, %.1f MB, last write %.0f s ago"
			" -- %s" % (com(a.lines), os.path.getsize(p) / 1e6, age,
				"ALIVE" if age < 180 else "QUIET"))
		if el is None:
			m = RE_START.search(os.path.dirname(os.path.realpath(p)))
			if m:
				try:
					t = time.mktime(time.strptime(
						m.group(1) + m.group(2), "%Y%m%d%H%M%S"))
					el, src = time.time() - t, "log dir stamp"
				except ValueError:
					pass
			if el is None:
				el = time.time() - os.path.getctime(p)
				src = "file ctime"
	print("elapsed    : %s  (from %s), now %s"
		% (hm(el), src, clocks(time.time())))
	print("scan       : %.1f MB new in %.1f s  (incremental; --rescan "
		"re-reads all)" % (new_bytes / 1e6, dt))
	return el, min(time.time() - os.path.getmtime(p) for p in paths), src


# a pace outside this band means the elapsed clock is wrong, not that
# the run is 100x faster -- almost always a log whose directory carries
# no _YYYYmmdd_HHMMSS stamp, so elapsed fell back to file ctime.
PACE_SANE = (0.1, 5.0)
# and the same guard on the remaining-time scaler.
DRIFT_SANE = (0.5, 2.0)


def show_position(run, el, src):
	"""Where the run stands, and the one number that matters: how long
	legacy took to reach this same point."""
	print("-" * 72)
	idx, frac = run.position()
	equiv = leg_time_at(idx, frac)
	print("WHERE IT IS: %s -- %.2f%% through it"
		% (LEG_TL[idx][0], 100.0 * frac))
	print("             legacy reached this same point at hour %.2f"
		% (equiv / 3600.0))
	print("             neo is here at hour %.2f  (elapsed from %s)"
		% (el / 3600.0, src))
	if el > 0:
		r = equiv / el
		print("             PACE %.3fx -- %s" % (r,
			"AHEAD of legacy" if r > 1.02 else
			("BEHIND legacy" if r < 0.98 else "at legacy pace")))
		if idx < P1_IDX:
			print("             SETUP ONLY -- neo rebuilds the DB "
				"cache every run, legacy read")
			print("             it from cache. This says nothing "
				"about the fold.")
		if not PACE_SANE[0] <= r <= PACE_SANE[1]:
			print("             WARN: that pace is not physical -- the "
				"ELAPSED clock is wrong,")
			print("             not the run. Source was %s; a real run "
				"gets it from the log" % src)
			print("             dir stamp. Everything else below is "
				"unaffected." )
	return idx, frac, equiv


def show_hourly(bank, el, idx, frac, equiv):
	"""The hour-by-hour comparison up to now.  Legacy's column comes
	from its measured timeline; neo's from the samples this script
	banked on earlier invocations, so a gap means nobody was looking."""
	print("-" * 72)
	print("HOURLY COMPARISON  (legacy = measured timeline; neo = what "
		"this script banked)")
	print("  %-5s %-26s %-26s %s"
		% ("hour", "legacy was", "neo was", "pace"))
	rows = dict(bank.hourly())
	cur = int(el // 3600)
	rows[cur] = (idx, frac, equiv)
	# A 5-day run is 120 rows.  Keep every hour this script actually
	# observed, plus the current one, plus a stride through the rest, so
	# the table stays readable without ever dropping a real reading.
	stride = max(1, (cur + 36) // 36)
	show = set(rows) | set(range(0, cur + 1, stride)) | {cur}
	for h in sorted(show):
		# score each hour at its END, which is when a reading taken
		# during it is closest to being true.
		t = (h + 1) * 3600.0
		li, lf = leg_at_time(t)
		leg_txt = "%s %.0f%%" % (short_stage(LEG_TL[li][0]),
			100.0 * lf)
		neo = rows.get(h)
		if neo is None:
			print("  %-5d %-26s %-26s %s"
				% (h, leg_txt, "(not polled)", "-"))
			continue
		ni, nf, neq = neo
		print("  %-5d %-26s %-26s %.3fx"
			% (h, leg_txt, "%s %.0f%%" % (short_stage(LEG_TL[ni][0]),
				100.0 * nf), neq / t))
	print("             pace = legacy-equivalent hours done / hours "
		"elapsed; >1 = neo ahead")


def show_gate(run):
	"""Tuner verdict, v5 walk, qm ratchet."""
	print("-" * 72)
	short = any(a.short for a in run.accs)
	fires = [f for a in run.accs for f in a.ratchet]
	if short:
		print("ratchet    : DEAD -- still short after 3 re-walks. The "
			"walk did not converge.")
	elif fires:
		print("ratchet    : FIRED %dx, qm_real_rows %s"
			% (len(fires), " -> ".join([str(fires[0][0])]
				+ [str(f[1]) for f in fires])))
	else:
		print("ratchet    : not fired")
	v5 = next((a.v5 for a in run.accs if a.v5), None)
	if v5:
		h = run.v5_hist()
		n = float(sum(h)) if h else 0.0
		print("v5 walk    : %s rungs over %s WORDS (occupancy, not "
			"chunks)" % (v5[0], com(int(n)) if n else "?"))
		if n:
			print("             %s   mean rung %.3f vs %.3f legacy"
				% (" / ".join("%.2f%%" % (100.0 * c / n) for c in h),
					sum((i + 1) * h[i] for i in range(4)) / n,
					sum((i + 1) * LEG_MIX[i] for i in range(4)) / 100.0))
		print("             costs=[%s] -- cost-MODEL units, not ms"
			% v5[2])
		if h:
			print("             %s the 08-16 full-scale reference walk"
				% ("MATCHES" if h == NEO_REF_HIST
					else "DIVERGES from"))
	gate = run.gate()
	if not gate:
		print("gate       : PENDING -- tuner has not reported yet")
		return None, short
	ok = gate[0] >= EXPECT_RUNGS and gate[2] == PROD_SUBSIGS
	print("gate       : %s -- %d rungs (need %d), hist=[%s]"
		% ("PASS" if ok else "FAIL", gate[0], EXPECT_RUNGS, gate[1]))
	print("             P_max.subsigs=%d (both arms settle on %d)%s"
		% (gate[2], PROD_SUBSIGS,
			"" if gate[2] == PROD_SUBSIGS else "  <-- MISMATCH"))
	return ok, short


def show_circuits(run, mix):
	"""Ladder, key sizing and decider circuit sizes vs legacy."""
	print("-" * 72)
	lad = run.ladder()
	if not lad:
		# not just "wait": the 08-16 run fixed what this ladder must
		# be, so print the target now and the operator can check it
		# the moment PERF 1002 lands.
		print("CIRCUITS   : ladder PENDING -- no preprocess block yet."
			"  EXPECTED, from 08-16:")
		print("  %-5s %-13s %-13s %-7s %s"
			% ("circ", "expected", "legacy cols", "x", "expected rows"))
		for i in sorted(NEO_REF_LADDER):
			c, r = NEO_REF_LADDER[i]
			lc = LEG_LADDER[i][0]
			print("  %-5d %-13s %-13s %-7.3f %s"
				% (i, com(c), com(lc), c / float(lc), com(r)))
		print("  %-5s %-13s %-13s %-7.3f"
			% ("cs1e", com(NEO_REF_KEYS[2]), com(LEG_CS1E),
				NEO_REF_KEYS[2] / float(LEG_CS1E)))
		print("  %-5s %-13s %-13s %-7.3f   <-- decider size, peak RAM"
			% ("maxpp", com(NEO_REF_KEYS[3]), com(LEG_MAX_PP),
				NEO_REF_KEYS[3] / float(LEG_MAX_PP)))
		return {}
	n_circs, got, tag = lad
	print("CIRCUITS   : ladder circs: %d  [%s]" % (n_circs, tag))
	print("  %-5s %-13s %-13s %-7s %-13s %-13s"
		% ("circ", "cols", "legacy cols", "x", "rows", "legacy rows"))
	for i in sorted(set(list(got) + list(LEG_LADDER))):
		c, r = got.get(i, (None, None))
		lc, lr = LEG_LADDER.get(i, (None, None))
		print("  %-5d %-13s %-13s %-7s %-13s %-13s"
			% (i, com(c), com(lc),
				"%.3f" % (c / lc) if c and lc else "-", com(r),
				com(lr)))
	# the 08-16 run pinned every one of these; a mismatch is a TREE
	# change, since spec, DB and corpus are identical.
	off = [i for i in NEO_REF_LADDER
		if i in got and got[i][0] != NEO_REF_LADDER[i][0]]
	if len(got) >= EXPECT_RUNGS:
		print("  vs 08-16 ref: %s"
			% ("MATCH on all %d rungs" % EXPECT_RUNGS if not off
				else "DIVERGED at rung %s -- %s"
				% (",".join(str(i) for i in off),
					" ".join("%s vs %s" % (com(got[i][0]),
						com(NEO_REF_LADDER[i][0])) for i in off))))
	keys = run.keys()
	if keys:
		for name, v, lv, note in (
				("cs1e", keys[3], LEG_CS1E,
					"  <-- sets decider size, keygen, RAM"),
				("total_w", keys[1], LEG_TOTAL_W, ""),
				("total_e", keys[2], LEG_TOTAL_E, ""),
				("max_pp", keys[4], LEG_MAX_PP, "")):
			print("  %-10s %-13s %-13s %.3fx%s"
				% (name, com(v), com(lv), v / float(lv), note))
	mcs = next((a.main_cs for a in run.accs if a.main_cs), None)
	ccs = next((a.cp_cs for a in run.accs if a.cp_cs), None)
	print("  %-10s %-13s %-13s %s"
		% ("MainDecid", com(mcs), com(LEG_MAIN_DECIDER_CS),
			"%.3fx" % (mcs / float(LEG_MAIN_DECIDER_CS)) if mcs
			else "(phase 4 not reached)"))
	print("  %-10s %-13s %-13s %s"
		% ("CyclePair", com(ccs), com(LEG_CYCLEPAIR_CS),
			"%.3fx" % (ccs / float(LEG_CYCLEPAIR_CS)) if ccs
			else "(phase 4 not reached)"))
	if len(got) >= 4 and sum(mix):
		w = weighted(got, mix)
		wl = weighted(LEG_LADDER, LEG_MIX)
		x = w / wl
		print("  %-10s %-13s %-13s %.3fx   [measured routing]"
			% ("weighted", com(w), com(wl), x))
		print("             an average chunk's circuit is %s"
			% ("the same size as legacy's" if abs(x - 1) < 0.005
				else "%.0f%% %s than legacy's"
				% (abs(100.0 * (x - 1)),
					"BIGGER" if x > 1 else "SMALLER")))
	return got


def show_routing(run, mix):
	"""Measured rung mix against legacy.  The neo thesis is that it
	routes the bulk of chunks one rung LOWER."""
	print("-" * 72)
	tot = sum(mix)
	if tot == 0:
		print("routing    : no completed words yet (needs the LOG3 "
			"'per-chunk circ sel' lines)")
		return
	pct = [100.0 * c / tot for c in mix]
	# the completeness term matters: a mix over 200 chunks prints
	# exactly like the final one over 926,900, and only the second is
	# safe to price the fold with.
	all_c = run.total_steps()
	print("routing    : %s chunks routed over completed words "
		"(%.1f%% of ~%s)"
		% (com(tot), min(100.0, 100.0 * tot / max(all_c, 1)),
			com(all_c)))
	print("  %-6s %-11s %-11s %s" % ("rung", "measured", "legacy", "n"))
	for i in range(4):
		print("  %-6d %-11s %-11s %s"
			% (i + 1, "%.2f%%" % pct[i], "%.2f%%" % LEG_MIX[i],
				com(mix[i])))
	mean = sum((i + 1) * pct[i] for i in range(4)) / 100.0
	lmean = sum((i + 1) * LEG_MIX[i] for i in range(4)) / 100.0
	print("             mean rung %.3f vs %.3f legacy -- %s"
		% (mean, lmean, "LOWER-SKEWED (the neo win)" if mean < lmean
			else "NOT lower-skewed; check before trusting the fold"))


def rung_step_ms(lad, r, outer, adv):
	"""(ms one fold step costs on 1-based rung r, True if MEASURED).
	Measured spans win once a rung has MEAS_MIN of them; before that
	the legacy affine fit prices the rung from its column count."""
	n, mnp, _md = outer.get(r - 1, (0, 0.0, 0.0))
	if n >= MEAS_MIN:
		na, mna, _mda = adv.get(r - 1, (0, 0.0, 0.0))
		return (mnp + (mna if na else LEG_ADV_RUNG[r - 1][0])
			+ FLAT_MS, True)
	if not LEG_FIT or r not in lad:
		return None
	slope, fixed, _res = LEG_FIT
	return (slope * lad[r][0] + fixed + LEG_ADV_RUNG[r - 1][0]
		+ FLAT_MS, False)


def show_breakdown(run, mix, got):
	"""Where the fold's hours actually GO: chunk share vs COST share
	per rung.  Both inputs go final when phase 1 ends -- ~8 h before
	phase 3 prints anything, since cmF is LOG4-silent -- so this is the
	earliest honest read on the fold."""
	print("-" * 72)
	got, ls, m, ms = pick_inputs(got, mix, run.v5_hist())
	tot = float(sum(m))
	if tot <= 0 or ms == "legacy placeholder":
		print("BREAKDOWN  : PENDING -- needs routing or the v5 walk "
			"(neither has reported)")
		return
	mix = m
	outer = run.merged("outer")
	adv = run.merged("adv")
	done = run.step_wall(2)[0] is not None
	all_c = run.total_steps()
	if ls == "measured" and ms == "measured":
		state = "FINAL (phase 1 done)" if done else "PARTIAL"
		note = ("" if done else ", %.1f%% of ~%s"
			% (min(100.0, 100.0 * tot / max(all_c, 1)), com(all_c)))
		print("BREAKDOWN  : %s -- %s chunks routed%s"
			% (state, com(int(tot)), note))
		tag = "" if done else "   [PARTIAL]"
	else:
		print("BREAKDOWN  : PROJECTED -- ladder %s, routing %s"
			% (ls, ms))
		tag = "   [PROJECTED]"
	# ms[r] is what ONE step on rung r costs; cost[r] weights it by the
	# chunks that route there, which is the only thing hours care about.
	ms, meas, cost = {}, {}, {}
	for r in range(1, 5):
		v = rung_step_ms(got, r, outer, adv)
		if v:
			ms[r], meas[r] = v
			cost[r] = v[0] * mix[r - 1]
	csum = sum(cost.values())
	lms = [LEG_PROVE_RUNG[i][1] + LEG_ADV_RUNG[i][0] + FLAT_MS
		for i in range(4)]
	lcost = [lms[i] * LEG_MIX[i] for i in range(4)]
	lsum = sum(lcost)
	print("  %-5s %-8s %-11s %-6s %-9s %-7s %-7s %s"
		% ("rung", "chunks", "cols", "x", "ms/step", "cost%",
			"legacy%", "x"))
	for r in range(1, 5):
		c = got.get(r, (None, None))[0]
		lc = LEG_LADDER[r][0]
		sh = 100.0 * cost[r] / csum if r in cost and csum else None
		lsh = 100.0 * lcost[r - 1] / lsum
		print("  %-5d %-8s %-11s %-6s %-9s %-7s %-7s %s"
			% (r, "%.2f%%" % (100.0 * mix[r - 1] / tot), com(c),
				"%.3f" % (c / float(lc)) if c else "-",
				"%.0f%s" % (ms[r], "*" if meas[r] else "")
					if r in ms else "-",
				"%.1f" % sh if sh is not None else "-",
				"%.1f" % lsh,
				"%.2f" % (sh / lsh) if sh and lsh else "-"))
	if any(meas.values()):
		print("             * = MEASURED prove+advice; the rest priced "
			"by the legacy fit")
	# a rung carrying chunks but missing from the ladder would silently
	# drop its hours out of the mean, so refuse to print one.
	if [r for r in range(1, 5) if mix[r - 1] > 0 and r not in ms]:
		print("             mean step UNPRICED -- a routed rung has no "
			"ladder entry")
		return
	tail_c = 100.0 * (mix[2] + mix[3]) / tot
	tail_k = 100.0 * (cost.get(3, 0.0) + cost.get(4, 0.0)) / csum
	print("  tail 3+4   %.2f%% of chunks -> %.1f%% of cost  (legacy "
		"%.2f%% -> %.1f%%)"
		% (tail_c, tail_k, LEG_MIX[2] + LEG_MIX[3],
			100.0 * (lcost[2] + lcost[3]) / lsum))
	mean = csum / tot
	print("  mean step  %.1f ms vs legacy %.1f = %.3fx"
		% (mean, LEG_STEP_WALL_MS, mean / LEG_STEP_WALL_MS))
	p3 = mean * run.steps_per_job() / 1000.0
	print("  => PHASE 3 ~= %s per job vs legacy %s = %.3fx%s"
		% (hm(p3), hm(LEG_STEP[7][0]), p3 / LEG_STEP[7][0], tag))


def show_phase1(run, bank):
	"""PHASE 1, circuit selection: the stage the neo arm had to make
	faster.  Rate comes from PERF 1008's per-WORD line, which carries
	its own denominator -- no probe involved."""
	print("-" * 72)
	done = run.p1_done()
	wall, nrep = run.step_wall(2)
	if not done and wall is None:
		print("PHASE 1    : not started (no 'Pass 1. END generate "
			"advice word' line yet)")
		return
	if wall is not None:
		print("PHASE 1    : DONE -- %s per job vs legacy %s = %.3fx"
			"   [%d job(s)]"
			% (hm(wall), hm(LEG_STEP[2][0]), wall / LEG_STEP[2][0],
				nrep))
	else:
		print("PHASE 1    : RUNNING")
	if not done:
		return
	vs = []
	nv, sv = 0, 0.0
	for a in run.accs:
		nv += a.p1_ms.n
		sv += a.p1_ms.s
		vs.extend(a.p1_ms.v)
	tot = run.words_per_job() * run.njobs
	print("  progress   %s / %s words (%.2f%%), %s per job x %d jobs"
		% (com(done), com(tot), 100.0 * done / max(tot, 1),
			com(run.words_per_job()), run.njobs))
	print("  per-word   %.1f ms mean, %.1f median  (legacy OVERALL "
		"%.1f / %.1f)" % (sv / nv if nv else 0.0, med(vs),
			LEG_P1_WORD_MEAN, LEG_P1_WORD_MED))
	pj = p1_projection(run)
	if pj:
		proj, ratio, f, leg_here = pj
		print("  SAME-POINT %s spent vs legacy's %s at the same %.2f%%"
			" = %.3fx" % (hm(run.p1_span_s()[0] / run.njobs),
				hm(leg_here), 100.0 * f, ratio))
		print("  => PHASE 1 ~= %s per job vs legacy %s = %.3fx"
			% (hm(proj), hm(LEG_STEP[2][0]), proj / LEG_STEP[2][0]))
		print("             legacy spends 26.3% of phase 1 on its "
			"first 5% of words, so a")
		print("             linear extrapolation of an early rate "
			"would inflate this ~5x")
	rate = bank.rate("p1", done)
	if rate and rate > 0:
		pjh = rate * 3600.0 / run.njobs
		print("  wall rate  %.0f words/hr per job vs legacy %.0f = "
			"%.2fx  [cross-check]"
			% (pjh, LEG_P1_WORDS_HR, pjh / LEG_P1_WORDS_HR))
		if done < tot:
			left = (tot - done) / rate
			print("             ETA %s left; phase 1 ends %s"
				% (hm(left), clocks(time.time() + left)))


def show_phase2(run):
	"""PHASE 2, cmF.  SILENT at LOG3 by construction: every marker in
	the loop (driver.rs 2146-2300) is log_level+2 = LOG4 while
	log_level there is LOG2, so a ~7.8 h gap with no output is normal,
	not a stall."""
	print("-" * 72)
	wall, nrep = run.step_wall(3)
	p1 = run.step_wall(2)[0]
	if wall is not None:
		print("PHASE 2    : DONE -- %s per job vs legacy %s = %.3fx"
			"   [%d job(s)]"
			% (hm(wall), hm(LEG_STEP[3][0]), wall / LEG_STEP[3][0],
				nrep))
	elif p1 is not None:
		print("PHASE 2    : RUNNING and SILENT -- every cmF marker is "
			"LOG4, the run is LOG3.")
		print("             Legacy took %s per job. The next line you "
			"will see is step 3." % hm(LEG_STEP[3][0]))
	else:
		print("PHASE 2    : not started (phase 1 has not finished)")


def show_phase3(run, mix, got, bank):
	"""PHASE 3, the fold.  Bucketed by the 0-based circ_id the inner
	prove_step line carries, so no join with the routing lines."""
	print("-" * 72)
	outer = run.merged("outer")
	adv = run.merged("adv")
	n_out = run.p3_done()
	total = run.total_steps()
	wall, nrep = run.step_wall(7)
	if not n_out:
		print("PHASE 3    : not started (step 7 has not begun)")
		print("             when it does: %s steps expected, legacy "
			"ran %.1f ms/step" % (com(total), LEG_STEP_WALL_MS))
		return
	if wall is not None:
		print("PHASE 3    : DONE -- %s per job vs legacy %s = %.3fx"
			"   [%d job(s)]"
			% (hm(wall), hm(LEG_STEP[7][0]), wall / LEG_STEP[7][0],
				nrep))
	else:
		print("PHASE 3    : RUNNING -- %s of ~%s steps (%.2f%%)"
			% (com(n_out), com(total), 100.0 * n_out / max(total, 1)))
	mstmt = run.flat("stmt")[1]
	mlk = run.flat("lkup")[1]
	tadv = sum(adv[r][1] * adv[r][0] for r in adv)
	nadv = sum(adv[r][0] for r in adv)
	tout = sum(outer[r][1] * outer[r][0] for r in outer)
	print("  %-14s %-11s %-11s %s"
		% ("span", "neo mean", "legacy", "x"))
	for name, mv, leg in (
			("prove_step", tout / n_out, LEG_PROVE_MS),
			("gen advice", tadv / nadv if nadv else 0.0, LEG_ADV_MS),
			("gen stmt", mstmt, LEG_STMT_MS),
			("update lkup", mlk, LEG_LKUP_MS)):
		print("  %-14s %-11.1f %-11.1f %.3f"
			% (name, mv, leg, mv / leg if leg else 0))
	tt = tout / n_out + (tadv / nadv if nadv else 0.0) + mstmt + mlk
	print("  %-14s %-11.1f %-11.1f %.3f"
		% ("SPAN TOTAL", tt, LEG_STEP_WALL_MS - LEG_UNACCOUNTED_MS,
			tt / (LEG_STEP_WALL_MS - LEG_UNACCOUNTED_MS)))
	print("  per-rung prove_step / gen advice, neo vs legacy:")
	print("    %-5s %-9s %-9s %-9s %-6s %-8s %-8s %s"
		% ("rung", "n", "prove", "leg", "x", "advice", "leg", "x"))
	for r in range(4):
		n, mnp, _md = outer[r]
		if not n:
			continue
		mna = adv[r][1]
		print("    %-5d %-9s %-9.1f %-9.1f %-6.3f %-8.1f %-8.1f %.3f"
			% (r + 1, com(n), mnp, LEG_PROVE_RUNG[r][1],
				mnp / LEG_PROVE_RUNG[r][1], mna, LEG_ADV_RUNG[r][0],
				mna / LEG_ADV_RUNG[r][0]))
	proj, psrc, f, model, shape = p3_projection(run, mix, got)
	if model:
		print("    model      %s per job = %.3fx legacy%s"
			% (hm(model), model / LEG_STEP[7][0],
				"   <-- used" if psrc.startswith("legacy") else ""))
	if shape:
		span_s = run.p3_span_s()[0]
		print("    same-point %s per job = %.3fx legacy%s  (%s vs "
			"legacy's %s at %.2f%%)"
			% (hm(shape), shape / LEG_STEP[7][0],
				"   <-- used" if psrc.startswith("own") else "",
				hm(span_s / run.njobs),
				hm(curve_sec(LEG_P3_CURVE, f)), 100.0 * f))
	if proj:
		print("  => PHASE 3 ~= %s per job vs legacy %s = %.3fx  [%s]"
			% (hm(proj), hm(LEG_STEP[7][0]), proj / LEG_STEP[7][0],
				psrc))
	rate = bank.rate("p3", n_out)
	if rate and total:
		print("  wall rate  %.1f steps/min -> %s left by step count"
			% (rate * 60.0, hm(max(total - n_out, 0) / rate)))


def show_phase4(run):
	"""PHASE 4, the decider.  Only part2's proving job reaches it, and
	the legacy production fold never ran it at all -- the reference is
	the 2026-07-17 makeup snark, which built the identical ladder."""
	print("-" * 72)
	p4 = run.p4()
	if not p4:
		if any(a.folddone for a in run.accs):
			print("PHASE 4    : fold DONE, decider not started yet")
		else:
			print("PHASE 4    : not reached (part2 proves after its "
				"fold finishes)")
		print("             legacy reference %s, peak 369 GB; "
			"MainDecider %s R1CS," % (hm(LEG_DEC_TOTAL),
				com(LEG_MAIN_DECIDER_CS)))
		print("             CyclePair %s R1CS.  NOTE: the 5.05 d "
			"production fold was" % com(LEG_CYCLEPAIR_CS))
		print("             b_folding_only, so this reference comes "
			"from the makeup snark.")
		return
	print("PHASE 4    : in flight or done -- %d of %d steps timed"
		% (len(p4), len(LEG_DEC)))
	print("  %-32s %10s %10s %7s"
		% ("step", "this run", "legacy", "x"))
	for idx, label, leg, _mem in LEG_DEC:
		v = p4.get(idx)
		print("  1006/%d %-25s %10s %10s %7s"
			% (idx, label, "-" if v is None else hm(v), hm(leg),
				"-" if v is None else "%.3f" % (v / leg)))
	have = sum(v for k, v in p4.items()
		if k in [x[0] for x in LEG_DEC])
	print("  %-32s %10s %10s %7.3f"
		% ("TOTAL so far", hm(have), hm(LEG_DEC_TOTAL),
			have / LEG_DEC_TOTAL))
	mem = max([a.p4_mem for a in run.accs] + [0])
	if mem:
		print("  peak MEM   %d GB reported (legacy 369 GB at steps "
			"6/7)" % mem)


def show_markers(run):
	"""The success markers PAPER_DATA.py itself scores the run on, so a
	mismatch is visible here before the leaf reports rc 6."""
	print("-" * 72)
	ver = run.sum_attr("verified")
	bp = run.sum_attr("batchproof")
	fo = run.sum_attr("foldonly")
	vf = run.sum_attr("vfail")
	fd = sum(len(a.folddone) for a in run.accs)
	print("MARKERS    : the same ones dlp_missing_success() checks")
	print("  fold-done per job      %d / %d" % (fd, run.njobs))
	print("  Verify Individual Prf  %d  (needs exactly 1)" % ver)
	print("  BatchProof             %d" % bp)
	print("  b_folding_only         %d  (part1's jobs + part2's "
		"non-proving ones)" % fo)
	if vf:
		print("  PROOF VERIFICATION FAILED x%d  <-- the run is BAD; "
			"the process still exits 0" % vf)


def show_stages(run, fc):
	"""Every stage: what this run has, what legacy measured."""
	print("-" * 72)
	print("STAGE TABLE  (per job; the decider row is part2 only)")
	print("  %-29s %10s %10s %7s  %s"
		% ("stage", "this run", "legacy", "x", "source"))
	for i, (label, t0, t1, _c) in enumerate(LEG_TL):
		val, src = fc[i]
		leg = t1 - t0
		print("  %-29s %10s %10s %7s  %s"
			% (label, hm(val), hm(leg),
				"%.3f" % (val / leg) if leg > 0 else "-",
				"" if src == "measured" else src))
	tot = sum(v for v, _ in fc)
	tot_fold = sum(v for v, _ in fc[:DEC_IDX])
	print("  %-29s %10s %10s %7.3f"
		% ("TOTAL through phase 3", hm(tot_fold), hm(LEG_WALL_FOLD),
			tot_fold / LEG_WALL_FOLD))
	print("  %-29s %10s %10s %7.3f"
		% ("TOTAL incl. phase 4", hm(tot), hm(LEG_WALL_ALL),
			tot / LEG_WALL_ALL))
	print("             legacy part wall MEASURED 436,316 s = 5.05 d "
		"(part1), 414,194 s")
	print("             (part2) -- above the mean-job timeline because "
		"a part ends with")
	print("             its SLOWEST job, %.1f%% over the mean."
		% (100.0 * (LEG_JOB_FOLD[2] / LEG_JOB_FOLD[0] - 1.0)))
	return tot, tot_fold


def show_forecast(run, fc, el, tot, tot_fold, idx, frac, equiv):
	"""When does this finish, and how does that compare with legacy."""
	print("-" * 72)
	# what the forecast says should already be spent at this position
	spent = sum(v for v, _ in fc[:idx]) + fc[idx][0] * frac
	# ... and how the run is actually tracking that.  The ratio absorbs
	# everything neo does NOT time (its own DB load and tuner), which is
	# exactly the part no marker can measure.
	raw = (el / spent) if spent > 0 else 1.0
	# GATED: until the run times a stage of its own, every entry in fc
	# is a legacy placeholder and `spent` is a guess -- position() hands
	# back a hardcoded 0.5 for load DB.  Multiplying a 101-hour fold by
	# a ratio measured inside a DB build neo REBUILDS and legacy read
	# from cache is not a forecast.  The overrun is real but one-time,
	# so it is carried additively instead: the remainder runs at legacy
	# pace and the hours already lost stay lost.
	anchored = any(s != LEG_SRC for _v, s in fc[:idx + 1])
	# Clamped: a wrong elapsed clock (no _YYYYmmdd_HHMMSS in the log dir
	# name, so ctime was used) would otherwise scale the whole remainder
	# by a factor of 100.  A real run sits within a few percent of 1.
	drift = (min(max(raw, DRIFT_SANE[0]), DRIFT_SANE[1])
		if anchored else 1.0)
	left_fold = max(tot_fold - spent, 0.0) * drift
	left_all = max(tot - spent, 0.0) * drift
	print("FORECAST")
	print("  %-32s %10s %10s %7s"
		% ("", "this run", "legacy", "x"))
	print("  %-32s %10s %10s %7.3f"
		% ("through phase 3 (part1 ends)", hm(tot_fold),
			hm(LEG_WALL_FOLD), tot_fold / LEG_WALL_FOLD))
	print("  %-32s %10s %10s %7.3f"
		% ("incl. phase 4 (part2 ends)", hm(tot), hm(LEG_WALL_ALL),
			tot / LEG_WALL_ALL))
	print("  drift      forecast expects %s spent by this point, "
		"actual %s = %.3fx"
		% (hm(spent), hm(el), raw))
	print("             (that ratio absorbs neo's UNTIMED DB load and "
		"tuner)")
	if not anchored:
		print("             NOT PROPAGATED -- no neo-timed stage yet, "
			"so the remainder runs")
		print("             at legacy pace and the %s already lost is "
			"carried additively" % hm(max(el - spent, 0.0)))
	elif abs(raw - drift) > 1e-9:
		print("             CLAMPED to %.2fx for the remainder below "
			"-- see the elapsed" % drift)
		print("             warning above; the per-stage table is the "
			"number to trust")
	print("  remaining  part1 %s -> ends %s"
		% (hm(left_fold), clocks(time.time() + left_fold)))
	print("             part2 %s -> ends %s"
		% (hm(left_all), clocks(time.time() + left_all)))
	if el > 0:
		print("  vs legacy  legacy needed %s to get where neo is now; "
			"neo took %s" % (hm(equiv), hm(el)))
		if anchored:
			print("             pace %.3fx -> whole run lands near "
				"%.3fx legacy"
				% (equiv / el, (el + left_all) / LEG_WALL_ALL))
		else:
			print("             pace %.3fx is SETUP ONLY; at legacy "
				"pace from here the run" % (equiv / el))
			print("             lands near %.3fx legacy -- no fold "
				"evidence yet either way"
				% ((el + left_all) / LEG_WALL_ALL))
	print("             legacy MEASURED 5.05 d part wall + 2h 52m "
		"decider = 5.17 d")


def show_mem(run, bank):
	"""RAM headroom, with the phase-3 OOM floor once the fold starts."""
	print("-" * 72)
	total, avail = mem_gb()
	if total:
		line = "memory     : %d / %d GB available" % (avail, total)
		if avail < MEM_FLOOR_GB:
			line += "  <-- UNDER THE %d GB FLOOR" % MEM_FLOOR_GB
		print(line)
		vel = bank.velocity("mem", avail)
		if vel is not None and vel < -1.0:
			print("             FALLING %.0f GB/hr -- hits the %d GB "
				"floor in %s" % (-vel, MEM_FLOOR_GB,
					hm(max(avail - MEM_FLOOR_GB, 0) / (-vel) * 3600)))
			print("             if it does not plateau this is the "
				"phase-3 OOM; fix is numa_num=2")
		elif vel is not None:
			print("             stable/rising (%+.0f GB/hr)" % vel)
	ram = max([a.ram for a in run.accs] + [0])
	if ram:
		print("log RAM    : %d GB reported (legacy %d-%d, mean %.0f); "
			"true peak runs higher" % (ram, LEG_RAM_GB[0],
				LEG_RAM_GB[1], LEG_RAM_GB[2]))
		print("             -- quote PAPER_DATA_PEAK_RSS_GIB, not "
			"this")
	spd = [a.speed for a in run.accs if a.speed]
	if spd:
		print("throughput : mb_speed %.4f MB/hr (legacy %.3f-%.3f, "
			"mean %.4f) = %.2fx" % (max(spd), LEG_MB_HR[0],
				LEG_MB_HR[1], LEG_MB_HR[2], max(spd) / LEG_MB_HR[2]))


def show_next(run, gate, age, short, idx):
	"""When to look again, and the one-line call."""
	print("-" * 72)
	ver = run.sum_attr("verified")
	vf = run.sum_attr("vfail")
	if ver:
		sec, why = 0, "run is done -- score the tables above"
	elif idx >= DEC_IDX:
		sec, why = 45 * 60, "decider running; watch RAM (369 GB legacy)"
	elif idx == 8:
		sec, why = 120 * 60, "phase 3 is the long haul; watch RAM+pace"
	elif idx == 6:
		sec, why = 90 * 60, "phase 2 is silent at LOG3; next is step 3"
	elif idx == 5:
		sec, why = 45 * 60, "phase 1 running; the pace is the watch item"
	elif gate:
		sec, why = 20 * 60, "gate passed; waiting on the circuit build"
	else:
		sec, why = 30 * 60, "still tuning; the gate is the next signal"
	if sec:
		print("next check : in %s, at %s"
			% (hm(sec), clocks(time.time() + sec)))
		print("             (%s)" % why)
	else:
		print("next check : none -- %s" % why)
	if vf:
		print("VERDICT    : BAD PROOF -- 'PROOF VERIFICATION FAILED' "
			"is in the log.")
	elif short:
		print("VERDICT    : DEAD -- the qm ratchet exhausted its "
			"re-walks.")
	elif gate is False:
		print("VERDICT    : VOID -- the ladder gate failed; this is "
			"not the production fold.")
	elif ver:
		print("VERDICT    : COMPLETE -- proof verified.")
	elif age > STALL_S:
		print("VERDICT    : SUSPECT -- no write for %s. Check the "
			"process and free -g." % hm(age))
	elif gate:
		print("VERDICT    : HEALTHY -- gate passed, run in flight.")
	else:
		print("VERDICT    : EARLY -- still tuning, no gate yet.")


# --------------------------------------------------------------- state

class Bank(object):
	"""Timestamped readings, so rates and the hourly table come from
	this script's own invocations rather than from elapsed wall (which
	spans the untimed pre-fold and so reads pessimistic)."""

	# rate baseline window: at least 2 min old so the interval is
	# meaningful, at most 6 h so a rate that changed hours ago is not
	# averaged back in.  A value that went BACKWARDS means the run
	# restarted, so those rows are dropped.
	MIN_AGE_S = 120
	MAX_AGE_S = 6 * 3600

	def __init__(self, rows):
		# each row: [epoch, {key: value}], kept in append order.
		self.rows = rows
		self.now = {}

	def note(self, key, val):
		self.now[key] = val

	def rate(self, key, val):
		"""Units per second for a monotone counter, or None."""
		self.note(key, val)
		now = time.time()
		ok = [r for r in self.rows
			if key in r[1] and r[1][key] <= val
			and now - r[0] >= self.MIN_AGE_S]
		win = [r for r in ok if now - r[0] <= self.MAX_AGE_S]
		b = (win or ok or [None])[0]
		if not b or val <= b[1][key]:
			return None
		return (val - b[1][key]) / (now - b[0])

	def velocity(self, key, val):
		"""Units per hour for a value that may fall, or None."""
		self.note(key, val)
		now = time.time()
		old = [r for r in self.rows
			if key in r[1] and now - r[0] >= 300]
		if not old:
			return None
		return (val - old[0][1][key]) / ((now - old[0][0]) / 3600.0)

	def stamp(self, idx, frac, equiv, el):
		"""Record this invocation's position against its elapsed hour,
		so later runs can print the hourly table."""
		self.now["h"] = int(el // 3600)
		self.now["pos"] = [idx, frac, equiv]

	def hourly(self):
		"""[(hour, (idx, frac, equiv))] -- the LAST sample banked in
		each elapsed hour this script was actually run in."""
		byh = {}
		for r in self.rows:
			p, h = r[1].get("pos"), r[1].get("h")
			if p is not None and h is not None:
				byh[int(h)] = (p[0], p[1], p[2])
		return sorted(byh.items())

	def dump(self):
		return (self.rows + [[time.time(), self.now]])[-600:]


def load_state(path):
	try:
		with open(path) as fh:
			return json.load(fh)
	except (IOError, OSError, ValueError):
		return {}


def save_state(path, st):
	try:
		tmp = path + ".tmp"
		with open(tmp, "w") as fh:
			json.dump(st, fh)
		os.replace(tmp, path)
	except (IOError, OSError):
		print("             (could not write %s)" % path)


def print_legacy():
	"""Dump the hardcoded legacy reference, with its provenance."""
	print("LEGACY full_dlp REFERENCE")
	print("A. fold: jet1tb 2026-07-11, 8 jobs, two-half 4+4, 64 cpu /")
	print("   961 GiB.  part1 436,316 s = 5.05 d (the wall referee),")
	print("   part2 414,194 s.  ALL 8 jobs b_folding_only: NO decider.")
	print("   data/paper_data/run_data/data/raw_data/jet1tb/extracted/")
	print("       full_dlp.combined.log   (741 MB, 6,680,998 lines)")
	print("B. decider: the 2026-07-17 makeup snark, wall 16,873.8 s,")
	print("   pct=1 corpus but the IDENTICAL production ladder, so its")
	print("   phase-4 timings are the reference.")
	print("   ~/tmp/bora/numa_dlp_run/makeup_snark/")
	print("       paper_data_dlp_BUNDLE_20260717_000520.tgz")
	print("")
	print("corpus/job : %s words, %s packed fields, %.1f fold steps"
		% (com(LEG_WORDS), com(LEG_FIELDS), LEG_STEPS))
	print("")
	print("TIMELINE, mean job, absolute seconds from process start:")
	print("  %-30s %10s %10s %10s" % ("stage", "start", "end", "dur"))
	for label, t0, t1, curve in LEG_TL:
		print("  %-30s %10.1f %10.1f %10.1f%s"
			% (label, t0, t1, t1 - t0, "  [shaped]" if curve else ""))
	print("  through phase 3 %.1f s = %.2f hr;  incl. phase 4 %.1f s "
		"= %.2f hr" % (LEG_WALL_FOLD, LEG_WALL_FOLD / 3600.0,
			LEG_WALL_ALL, LEG_WALL_ALL / 3600.0))
	print("  per-job fold wall: mean %.0f, min %.0f, max %.0f s "
		"(max/mean %.3f)"
		% (LEG_JOB_FOLD[0], LEG_JOB_FOLD[1], LEG_JOB_FOLD[2],
			LEG_JOB_FOLD[2] / LEG_JOB_FOLD[0]))
	print("")
	print("per-job PERF 1007 Phase 1 step wall, s (mean, min, max):")
	for st in sorted(LEG_STEP):
		mn, lo, hi = LEG_STEP[st]
		print("  %d %-26s %10.1f %10.1f %10.1f"
			% (st, LEG_STEP_NAME[st], mn, lo, hi))
	print("  TOTAL steps 2-8 %12.1f s = %.2f hr"
		% (LEG_JOB_TOTAL, LEG_JOB_TOTAL / 3600.0))
	print("")
	print("per-PART PERF 1005 FoldPot wall, s (part1, part2):")
	for st in sorted(LEG_FP):
		print("  %d %-26s %10.1f %10.1f"
			% (st, LEG_FP_NAME[st], LEG_FP[st][0], LEG_FP[st][1]))
	print("  === ALL JOBS ===            %10.1f %10.1f"
		% LEG_ALL_JOBS)
	print("")
	print("PHASE 4 decider, the proving job (source B):")
	for idx, label, sec, mem in LEG_DEC:
		print("  1006/%d %-28s %10.1f s   MEM %d GB"
			% (idx, label, sec, mem))
	print("  TOTAL %36.1f s = %.2f hr"
		% (LEG_DEC_TOTAL, LEG_DEC_TOTAL / 3600.0))
	print("  MainDeciderCirtuit %s R1CS,  CyclePairCirc %s R1CS"
		% (com(LEG_MAIN_DECIDER_CS), com(LEG_CYCLEPAIR_CS)))
	print("")
	print("CIRCUITS: ladder (PERF 1002 A-matrix dims)")
	for i in sorted(LEG_LADDER):
		print("  circ %d  cols %-13s rows %s"
			% (i, com(LEG_LADDER[i][0]), com(LEG_LADDER[i][1])))
	print("  cs1e %s  total_w %s  total_e %s  max_pp %s"
		% (com(LEG_CS1E), com(LEG_TOTAL_W), com(LEG_TOTAL_E),
			com(LEG_MAX_PP)))
	print("  side fold (n_circs 1): cols %s rows %s cs1e %s"
		% (com(LEG_SIDE[0]), com(LEG_SIDE[1]), com(LEG_SIDE[2])))
	print("  RAM at step 7: %d-%d GB per job, mean %.1f"
		% LEG_RAM_GB)
	print("  mb_speed: %.3f-%.3f MB/hr, mean %.4f" % LEG_MB_HR)
	print("")
	print("ROUTING over all 926,900 chunks:  %s"
		% "  ".join("rung %d %.4f%%" % (i + 1, LEG_MIX[i])
			for i in range(4)))
	print("  mean rung %.4f, P_max.subsigs %d"
		% (sum((i + 1) * LEG_MIX[i] for i in range(4)) / 100.0,
			PROD_SUBSIGS))
	print("")
	print("PHASE 1: %.1f ms/word mean, %.1f median, %.0f words/hr/job, "
		"%.1f ms/chunk" % (LEG_P1_WORD_MEAN, LEG_P1_WORD_MED,
			LEG_P1_WORDS_HR, LEG_P1_MS_CHUNK))
	print("  SHAPE, cumulative s to reach fraction f of the words --")
	print("  SEVERELY front-loaded, the first 5% costs 26.3%:")
	for i in range(0, 20, 2):
		f = (i + 1) / 20.0
		print("    f=%.2f  %8d s   (linear %8.0f, %.2fx)"
			% (f, LEG_P1_CURVE[i], f * LEG_STEP[2][0],
				LEG_P1_CURVE[i] / (f * LEG_STEP[2][0])))
	print("")
	print("PHASE 3 per step: prove %.1f + advice %.1f + stmt %.1f + "
		"lkup %.3f" % (LEG_PROVE_MS, LEG_ADV_MS, LEG_STMT_MS,
			LEG_LKUP_MS))
	print("  = %.1f measured vs %.1f step-7 wall/step (%.1f "
		"unaccounted, 0.12%%)"
		% (LEG_PROVE_MS + LEG_ADV_MS + LEG_STMT_MS + LEG_LKUP_MS,
			LEG_STEP_WALL_MS, LEG_UNACCOUNTED_MS))
	print("  prove_step by rung (n, mean, median, p90):")
	for i in range(4):
		print("    rung %d  %9s %10.1f %10.1f %10.1f"
			% ((i + 1, com(LEG_PROVE_RUNG[i][0]))
				+ LEG_PROVE_RUNG[i][1:]))
	print("  gen advice by rung (mean, median, p90):")
	for i in range(4):
		print("    rung %d  %10.1f %10.1f %10.1f"
			% ((i + 1,) + LEG_ADV_RUNG[i]))
	print("  inner prove_step by circ_id (mean, med, stmt_len, wtns):")
	for i in range(4):
		mn, md, sl, wt = LEG_INNER_CIRC[i]
		print("    circ %d  %10.1f %10.1f %12s %12s"
			% (i, mn, md, com(sl), com(wt)))
	print("  SHAPE, cumulative s to reach f of the steps -- nearly")
	print("  linear, worst 1.13x at f=0.10:")
	for i in range(0, 20, 2):
		f = (i + 1) / 20.0
		print("    f=%.2f  %8d s   (linear %8.0f, %.2fx)"
			% (f, LEG_P3_CURVE[i], f * LEG_STEP[7][0],
				LEG_P3_CURVE[i] / (f * LEG_STEP[7][0])))
	if LEG_FIT:
		print("")
		print("prove_step affine model fitted to the 4 legacy rungs:")
		print("  %.6f ms/col + %.0f ms fixed;  residuals %s"
			% (LEG_FIT[0], LEG_FIT[1],
				" ".join("%+.1f%%" % (100 * r) for r in LEG_FIT[2])))


USAGE = """dlp_progress.py [LOG ...] [--jobs N] [--rescan] [--legacy]

Scores a neo full_dlp run against the MEASURED legacy full_dlp run --
stage by stage, hour by hour -- and forecasts the finish.  Read-only and
probe-free: it parses only PERF/PROGRESS markers a production LOG3 run
already emits.  Run it from time to time; each invocation banks a sample
and re-prints the hourly comparison up to that moment.

  LOG ...   logs to read.  Default: /tmp/bora/CURRENT_JOB.log plus
            CURRENT_JOB_part2.log -- both halves of the two-half
            topology PAPER_DATA.py picks on a multi-socket box.
  --jobs N  override the job count (default %d, which is what
            `--run full_run --items dlp` always launches).
  --rescan  re-read from byte 0, discarding the scan checkpoint.
  --legacy  print the whole legacy reference and exit.

Scans are incremental: a first read of a 1 GB log costs ~13 s, later
reads only the bytes appended since.

env  MY_OFFSET_H         hours to add to this box's clock for yours (-4)
     DLP_PROGRESS_STATE  relocate the scan checkpoint""" % DEFAULT_JOBS


def main():
	"""Parse the run's logs and print every checkpoint."""
	argv = list(sys.argv[1:])
	if "--help" in argv or "-h" in argv:
		print(USAGE)
		return
	if "--legacy" in argv:
		print_legacy()
		return
	rescan = "--rescan" in argv
	njobs = DEFAULT_JOBS
	if "--jobs" in argv:
		i = argv.index("--jobs")
		njobs = int(argv[i + 1])
		del argv[i:i + 2]
	argv = [a for a in argv if not a.startswith("--")]
	paths = [p for p in (argv or DEFAULT_LOGS) if os.path.exists(p)]
	if not paths:
		print("NO LOG: none of %s exists" % ", ".join(DEFAULT_LOGS))
		sys.exit(2)
	paths = [os.path.realpath(p) for p in paths]
	# beside the log by default, so archiving the run dir takes the
	# checkpoint with it; DLP_PROGRESS_STATE relocates it when the log
	# lives somewhere that must not be written to.
	spath = os.environ.get("DLP_PROGRESS_STATE") or os.path.join(
		os.path.dirname(paths[0]), STATE_NAME)
	st = load_state(spath)
	accs = []
	t0 = time.time()
	new = 0
	for p in paths:
		a = Acc(st.get("logs", {}).get(p))
		new += scan(p, a, rescan)
		accs.append(a)
	dt = time.time() - t0
	# a log showing MORE jobs than expected is telling the truth; one
	# showing fewer has simply not logged them all yet.
	seen = sum(len(a.jobs) for a in accs)
	run = Run(accs, max(njobs, seen))
	bank = Bank(st.get("bank", []))
	mix = run.routing()

	el, age, esrc = show_header(paths, accs, new, dt)
	idx, frac, equiv = show_position(run, el, esrc)
	bank.stamp(idx, frac, equiv, el)
	show_hourly(bank, el, idx, frac, equiv)
	gate, short = show_gate(run)
	got = show_circuits(run, mix)
	show_routing(run, mix)
	show_breakdown(run, mix, got)
	show_phase1(run, bank)
	show_phase2(run)
	show_phase3(run, mix, got, bank)
	show_phase4(run)
	show_markers(run)
	fc = forecast(run, mix, got)
	tot, tot_fold = show_stages(run, fc)
	show_forecast(run, fc, el, tot, tot_fold, idx, frac, equiv)
	show_mem(run, bank)
	show_next(run, gate, age, short, idx)

	st["logs"] = dict(zip(paths, [a.dump() for a in accs]))
	st["bank"] = bank.dump()
	save_state(spath, st)
	print("-" * 72)
	print("state      : %s" % spath)
	print("reference  : --legacy dumps the full legacy table; --help "
		"for flags")


if __name__ == "__main__":
	main()
