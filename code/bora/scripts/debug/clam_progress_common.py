#!/usr/bin/env python3
"""Shared engine for the full_clam neo run meters.  Read-only,
probe-free: parses only PERF/PROGRESS markers a production LOG3 run
already emits.  The two front-ends (512gb / 1tb) supply a Topology and
call run().  Incremental byte-offset scan + JSON state, so repeated
invocations against a live log are cheap."""

import json
import os
import re
import time

# ---------------------------------------------------------------- io

# PAPER_DATA.py repoints these at the leaf now running.  part2 exists
# ONLY on a two-process (>=2 socket) box: point_current_job() unlinks
# it when n_parts == 1, which is how topology is detected.
CURRENT_1 = "/tmp/bora/CURRENT_JOB.log"
CURRENT_2 = "/tmp/bora/CURRENT_JOB_part2.log"
# hours to ADD to this box's clock to get the owner's laptop clock.
MY_OFFSET_H = float(os.environ.get("MY_OFFSET_H", "-4"))
# a log untouched this long, with no terminal marker, is suspect.
STALL_S = 45 * 60

# =====================================================================
# LEGACY REFERENCE.  Every number below was DERIVED 2026-08-18 by
# parsing, not modelled:
#   data/paper_data/run_data/data/raw_data/jet1tb/extracted/
#       full_clam.combined.log      (3.5 MB, 38,360 lines)
#   host zkregplus-large, 64 logical cpus, 961.1 GiB, EPYC-Milan.
#   8 jobs, two-half 4+4, b_one_proof (ONE job proves).
#
# TRAP, verified: the `label=part1` / `label=part2` headers are
# INVERTED relative to the job tags.  The region labelled part1 holds
# jobs 4-7; the region labelled part2 holds jobs 0-3 AND the decider.
# Job tags in clam are GLOBAL 0-7 and disjoint per region (unlike DLP,
# where dlp_progress.py documents them as part-local).  So: read the
# job tags, never the label, and locate the decider by its
# `generating SNARK proof` marker.
# =====================================================================

# Phase 1 per-job wall in SECONDS, mean over all 8 jobs.  Index = the
# `step N` in `PERF 1007: Phase 1 step N`.  step 5 is sub-ms.
LEG_STEP = {
	1: 257.6,      # generate batch/ind claims
	2: 5403.6,     # dispatch w into steps      == Pass 1
	3: 9041.3,     # generate cmF               == Pass 2
	4: 203.4,      # generate batch prf
	5: 0.0,        # prep for proving steps
	6: 141.1,      # build nova (cs1e-driven)
	7: 43766.1,    # PROVE STEPS                == Pass 3
	8: 0.9,        # verify
}
LEG_STEP_NAME = {
	1: "claims", 2: "pass1", 3: "cmF", 4: "batchprf",
	5: "prep", 6: "nova", 7: "fold", 8: "verify",
}
# per-job total, steps 1-8 = 16.34 hr.
LEG_JOB_TOTAL = sum(LEG_STEP.values())
# The decider, job 3 only (b_one_proof).  PERF 1006 Job Steps 2-7 plus
# the two circuit builds that bracket them.  ~3.11 hr.
LEG_DEC = [
	("build MAIN decider circ", 2127.9),
	("setup Groth16", 945.2),
	("prove MainCirc", 1909.6),
	("cyclepair IVC", 12.4),
	("build CyclePair circ", 0.4),
	("setup Groth16 CpCircuit", 2642.3),
	("prove CyclePair", 3550.5),
]
LEG_DEC_TOTAL = sum(x[1] for x in LEG_DEC)
# PERF 1005 `=== ALL JOBS ===` per region.  The decider region is the
# 19.36 hr referee; the fold-only region is 17.02 hr.
LEG_WALL_DEC = 69683.5
LEG_WALL_FOLD = 61282.6

# ---- SIZE, the scorecard's legacy column.  All at perc_db=100,
# perc_samples=100, 8 jobs, lkup share 143 (a HAND PIN -- the neo
# tuner DERIVES ~120 for the same corpus, see LEG_SHARE below).
LEG_LADDER = {1: (22148882, 14431369), 2: (34841302, 22516864)}
LEG_CS1E = 93938412
LEG_MAINDEC = 218188741        # *** MainDeciderCirtuit TOTAL ***
LEG_CYCLEPAIR = 204052787      # *** CyclePairCirc TOTAL ***
# the side (cyclefold) circuit.  INVARIANT to perc_db/perc_samples/
# jobs/arm -- it reads the same at 0.5% DB and at 100% DB -- so it is
# a BUILD-DRIFT gauge, NOT a comparability control.  Measured drift
# 2026-07-10 -> 2026-08-18 is +2.9%.
LEG_SIDE = (183776, 368893)
# COST-block composition (R1CS constraints, cost model not R1CS cols).
LEG_COST = {
	"CpMapper#1": 850380, "CpMapper#2": 850380,
	"SedMapper": 4694684, "DfaMapper": 1040578,
	"framework": 14995638,
}
LEG_COST_TOTAL = 22431660
LEG_LOGUP = 12583643           # PERF 1012, a SUBSET of framework
# lkup table size and the per-step share.  share size scales as
# lkup/chunks_of_smallest_job, so it is set by the JOB SPLIT, not by
# the circuit -- a subsampled run derives a wildly larger share.
LEG_LKUP = 246225855
LEG_SHARE = 143                # hand-pinned in legacy
LEG_SHARE_SIZE = 363151
NEO_SHARE_PRED = 120           # derived for the same corpus, 8 jobs
# corpus shape, per job.
LEG_WORDS_PER_JOB = 152
LEG_CHUNKS = [820, 816, 818, 819, 820, 823, 819]   # 7 real jobs seen
LEG_CHUNKS_MIN = 816
# TUNER reference, v1 arm, parsed from the 2026-08-16 neo_run log at
# this corpus: 19 rounds, TOTAL 2,199,665 ms, per-round wall climbing
# 0.4 s -> 283 s as the caps grow.  13 of those rounds bumped
# `cp::subsigs` by exactly +1 (the CP under-seed crawl).  The tuner
# runs BEFORE Phase 1 step 1 and is charged to NO stage column, so it
# is pure added wall that appears nowhere else in this report.
LEG_TUNE_V1_ROUNDS = 19
LEG_TUNE_V1_S = 2199.665
LEG_TUNE_V1_CRAWL_S = 1944.0    # rounds 5-17, all cp::subsigs +1
# tuner rows printed before the middle is elided.  A pathological tune
# is ~20 rounds; showing head and tail keeps the seed climb AND the
# expensive tail visible without burying the rest of the report.
TUNE_ROWS = 14
# RAM, GiB.  The log's `MEM:`/`Total RAM:` UNDERSTATE true peak RSS by
# ~3% (cross-checked against PAPER_DATA_PEAK_RSS_GIB on small_full_
# snark: 433.151 GiB measured for a 204.06M-constraint decider).
LEG_RAM_DEC_HALF = 527.0       # printed max, the decider region
LEG_RAM_FOLD_HALF = 369.0      # printed max, the fold-only region
LEG_RAM_1PROC_8JOB = 657.0     # 8 jobs in ONE process, +decider (10%)
LEG_RAM_1PROC_FOLD = 410.0     # same, decider backed out (657-247)
# GiB of peak RSS per MILLION decider R1CS constraints.  TOPOLOGY-
# DEPENDENT, and not mildly: a process that ONLY decides is far
# lighter than one that folds and then decides in the same address
# space, because the fold's residency is still held when the decider
# allocates.  A single global anchor printed GREEN (341 GiB) for a run
# the OOM guard killed at 469.6 GiB.
#   2.12 = small_full_snark, decider-only process: 433.151 GiB
#          MEASURED peak RSS / 204.06M cs.  The floor.
#   2.42 = legacy's own two-half decider region: 527 GiB / 218.19M cs.
#          Matched anchor for the 1 TB box.
#   2.92 = V101 dec_big 2026-08-18 on the 512 box, ONE process folding
#          AND proving: 469.6 GiB / 160.95M cs.  A LOWER BOUND -- the
#          guard killed it during decider synthesis, before the
#          Groth16 prove that carries the true peak.
RAM_PER_MCS_DECIDER_ONLY = 2.12
RAM_PER_MCS_TWO_HALF = 2.42
RAM_PER_MCS_ONE_PROC = 2.92

# ---------------------------------------------------------- regexes

# per-circuit measured R1CS dims.  Emitted twice per run: once for the
# main ladder (n_circs=2) and once for the side circuit (n_circs=1).
RE_CIRC = re.compile(
	r"PERF 1002 circ (\d+), r1cs cols: (\d+), rows: (\d+)")
# the key block that closes a preprocess pass; carries cs1e.
RE_KEYS = re.compile(
	r"KEYS info: n_circs: (\d+), total_w: (\d+), total_e: (\d+), "
	r"cs1e: (\d+), max_pp: (\d+)")
# per-job phase step wall.  The PHASE matters: Phase 1 is the corpus
# fold, Phase 2 is the decider's own cyclepair fold (8 tiny steps).
RE_STEP = re.compile(
	r"\[job (\d+)\].*PERF 1007[.:] Phase (\d+) step (\d+)[:.]"
	r".*?(\d+(?:\.\d+)?)\s*(ms|us|s)\s*$")
# corpus size for this job, off step 1.
RE_WORDS = re.compile(r"for words: (\d+), total_word_len: (\d+)")
# fold progress inside a phase.
RE_PROG = re.compile(r"PROGRESS fold \[Phase (\d+)\] word (\d+) of (\d+)")
# per-step prove spans (Pass 3).  These TILE the pass, which is what
# lets one reading project the whole thing.
RE_PROVE = re.compile(
	r"PERF 1009: -- Pass 3\. prove_step cost for word_id: \d+, "
	r"seg_id: \d+, stmt_len: (\d+)\s+(\d+(?:\.\d+)?)\s*(ms|us|s)")
# RAM LEVEL, GiB.  Every spelling UNDERSTATES true peak RSS by ~3%.
# The BARE `RAM:` form carries most readings (14 of 20 in V101
# dec_big, 32 of 62 in the legacy combined log) and `Total RAM` also
# appears upper-cased, so a `Total RAM|MEM|mem` alternation misses the
# peak outright: it read 231 where the log's own maximum was 407.
# The lookbehind is LOAD-BEARING, not defensive -- `INCREASED RAM: 18
# GB` is a DELTA that shares its line with the level it belongs to
# (`KEYS info: ... INCREASED RAM: 18 GB, TOTAL RAM: 164 GB`), so a
# plain `RAM:` alternative would report an increment as an absolute.
RE_RAM = re.compile(
	r"(?<![Cc][Rr][Ee][Aa][Ss][Ee][Dd] )(?:RAM|MEM|mem): (\d+) GB")
# the decider.  b_one_proof => exactly ONE job emits this.  This is
# how the proving job is identified -- NEVER from the part label.
RE_SNARK = re.compile(r"Job (\d+) generating SNARK proof")
RE_DECCS = re.compile(
	r"\*\*\* (MainDeciderCirtuit|CyclePairCirc) TOTAL constraints: "
	r"(\d+) \*\*\*")
RE_DECSTEP = re.compile(
	r"PERF 1006: Job Step (\d+): ([^.]*)\. MEM: (\d+) GB\.\s+"
	r"(\d+) ms")
# tuner.  v2 announces itself by its OWN plan dir, which is a more
# robust arm detector than the converge line.
RE_PLAN = re.compile(r"loadClamDB from: (\S+)")
RE_V2CONV = re.compile(r"V2 CONVERGED @iter (\d+): qm_real (\d+)")
RE_V1CONV = re.compile(
	r"determine_config_non_aggr CONVERGED @iter (\d+)")
# tuner ROUNDS, both arms.  Every round prints its own `round N ms`
# and the CONVERGED line adds `TOTAL T ms`, so tune time is MEASURED.
# It is deliberately NOT summed from the rounds: that sum omits the
# seed block and v1's post-converge fwd-queue tightening.
RE_V2SEED = re.compile(
	r"V2 SEED BLOCK: subsigs (\d+) igc (\d+) cp (\d+) dfa (\d+) "
	r"perc_comp (\d+)")
RE_V2ITER = re.compile(r"v2 iter (\d+): (.+)")
RE_V1ITER = re.compile(r"determine_config_non_aggr iter (\d+): (.+)")
RE_ROUNDMS = re.compile(r"round (\d+) ms")
RE_TOTALMS = re.compile(r"TOTAL (\d+) ms")
# one bumped cap.  The name may itself contain a comma
# (`dis_adv::neo_qm_real, b_igc: false`), so the quoted span -- not a
# comma split -- is what delimits it.
RE_BUMP = re.compile(r'\("([^"]+)",\s*(\d+)\)')
# run start: the header line PAPER_DATA writes as the log's first
# line.  Exact, and the only wall-clock anchor in the file.
RE_START = re.compile(r"^# (\d{4}-\d{2}-\d{2} \d{2}:\d{2}:\d{2})")
# the subcommand, off the argv header PAPER_DATA writes as line 2.
# This is the AUTHORITATIVE arm: it mirrors Rust's `arm_of`
# (bora_data_driver.rs), it is exact, and it is known before the run
# does any work -- unlike the plan dir, which the bare token leaves
# canonical, and unlike the tuner markers, which arrive minutes in.
RE_CMD = re.compile(r"^# cmd=.*bora_cli -- (\S+)")
# lkup / share.  The share is derived from the SMALLEST job's chunk
# count; a wrong share is the single biggest circuit-size distorter.
RE_SHARE = re.compile(r"perc_lkup_share\s*:\s*(\d+)")
RE_SHARESZ = re.compile(r"share size: (\d+)")
RE_LKUP = re.compile(r"preprocess\(\) START: lkup size: (\d+)")
# COST composition block.
RE_COSTTOT = re.compile(
	r"==== COST (\S+) \(R1CS constraints\) ====\s+total = (\d+)")
RE_COSTSUB = re.compile(r"^\s{2}(\S+)\s+subtotal = (\d+)")
RE_COSTFW = re.compile(r"framework \(poseidon/logup/io\)\s+(\d+)")
RE_LOGUP = re.compile(r"PERF 1012: logup query cost \(measured\) = (\d+)")
# whole-run milestones and the terminal marker.
RE_FOLDPOT = re.compile(r"fold_pot starts with (\d+) jobs")
RE_ALLJOBS = re.compile(r"PERF 1005: === ALL JOBS === (\d+) ms")

# ---------------------------------------------------------- helpers


def hm(sec):
	"""Seconds -> `NhNNm`, the one duration spelling used everywhere."""
	sec = max(int(sec or 0), 0)
	return "%dh%02dm" % (sec // 3600, (sec % 3600) // 60)


def arm_of(sub):
	"""Subcommand token -> arm, mirroring Rust's `arm_of`.  A BARE
	token takes the default arm, which has been v2 for clam and dna
	since 2026-08-18; only an explicit _v1/_v2 suffix overrides."""
	if sub.endswith("_v1"):
		return "v1"
	if sub.endswith("_v2"):
		return "v2"
	return "v2"


def secs(s):
	"""Seconds -> the tightest exact spelling.  Tune rounds span 0.4 s
	to 283 s within ONE run and the total reaches 37 min, so a single
	fixed unit misreads one end or the other."""
	if s is None:
		return "-"
	if s < 60:
		return "%.1fs" % s
	if s < 3600:
		return "%.1f min" % (s / 60.0)
	return "%.2f hr" % (s / 3600.0)


def com(n):
	"""Thousands separators, and `-` for a value never measured."""
	return "-" if n is None else "{:,}".format(n)


def ratio(neo, leg):
	"""neo/legacy as `N.NNx`, or `-` when either side is missing."""
	if not neo or not leg:
		return "-"
	return "%.2fx" % (float(neo) / float(leg))


def dur_s(val, unit):
	"""One timed marker -> seconds.  The Rust logger prints ms, us or
	s on the SAME marker depending on magnitude, so the unit must be
	read, never assumed."""
	v = float(val)
	return v / 1e3 if unit == "ms" else (v / 1e6 if unit == "us" else v)


def clocks(epoch):
	"""(box clock, owner clock) as HH:MM, so every ETA is quotable."""
	return (time.strftime("%H:%M", time.localtime(epoch)),
		time.strftime("%H:%M",
			time.localtime(epoch + MY_OFFSET_H * 3600)))


def mem_avail_gib():
	"""MemAvailable in GiB, or None off-Linux.  This is the number the
	RAM verdict is scored against -- not MemTotal, which the box never
	makes fully available."""
	try:
		for ln in open("/proc/meminfo"):
			if ln.startswith("MemAvailable:"):
				return int(ln.split()[1]) / 1048576.0
	except OSError:
		pass
	return None


def proc_rss_gib():
	"""Summed RSS of every live bora_cli process tree, in GiB, or None.
	The log's own RAM lines understate the peak, and PAPER_DATA writes
	PAPER_DATA_PEAK_RSS_GIB only at exit, so a live meter must sample
	/proc itself and bank a running max."""
	tot = 0
	found = False
	try:
		for pid in os.listdir("/proc"):
			if not pid.isdigit():
				continue
			try:
				cmd = open("/proc/%s/cmdline" % pid).read()
			except OSError:
				continue
			if "bora_cli" not in cmd:
				continue
			try:
				for ln in open("/proc/%s/status" % pid):
					if ln.startswith("VmRSS:"):
						tot += int(ln.split()[1])
						found = True
						break
			except OSError:
				continue
	except OSError:
		return None
	return tot / 1048576.0 if found else None


class Topology(object):
	"""One box shape.  The per-JOB model is topology-invariant (all
	three runs -- legacy, 512, 1TB -- carry 8 jobs at the same
	cpus-per-job), so ONLY these fields differ between front-ends."""

	def __init__(self, key, label, n_procs, n_jobs, ram_gib,
			b_wall_ref, note, ram_per_mcs):
		# short name used in the state filename and the header.
		self.key = key
		# human label printed in the header line.
		self.label = label
		# processes the leaf spawns: 1 on a 1-socket box, 2 two-half.
		self.n_procs = n_procs
		# TOTAL jobs across all processes.  8 in every real full_clam.
		self.n_jobs = n_jobs
		# RED line for projected peak RSS, GiB.  Owner set 490 GB
		# decimal = 456 GiB on the 512 box (leaves ~27 GiB slack).
		self.ram_gib = ram_gib
		# True when a legacy wall reference transfers (matched
		# topology).  False on the 512 box: legacy never ran 8 jobs in
		# one process at 100%, so only the PER-JOB budget compares.
		self.b_wall_ref = b_wall_ref
		# one-line caveat printed under the header.
		self.note = note
		# GiB of peak RSS per MILLION decider R1CS constraints, for
		# THIS box shape.  One of the RAM_PER_MCS_* anchors above;
		# never the module default, because there is none.
		self.ram_per_mcs = ram_per_mcs

	def logs(self):
		"""Log paths for this topology, existing ones only."""
		out = [CURRENT_1]
		if self.n_procs > 1:
			out.append(CURRENT_2)
		return [p for p in out if os.path.exists(p)]


class Acc(object):
	"""Everything scanned out of ONE log.  Every field is a raw
	measurement; nothing here is modelled."""

	def __init__(self, path):
		# the log this accumulator owns.
		self.path = path
		# bytes already consumed, so a re-run is ~free.
		self.off = 0
		# job id -> {step_key: seconds}, Phase 1 only.  Phase 2 is the
		# decider's own 8-step cyclepair fold and is kept apart.
		self.steps = {}
		# job id -> (words, packed fields) off step 1.
		self.corpus = {}
		# job id -> (done, total) from the newest PROGRESS line.
		self.prog = {}
		# ladder: circ index -> (cols, rows).  Only the n_circs=2
		# block; the n_circs=1 block is the side circuit.
		self.ladder = {}
		# PERF 1002 lines seen since the last KEYS line.  A run emits
		# the ladder block then the side block, and ONLY the trailing
		# `KEYS info: n_circs: N` says which is which -- sizing the
		# split by column count misfiles a dry ladder, whose circuits
		# are smaller than production's side circuit.
		self.pend = []
		# side circuit (cols, cs1e), the build-drift gauge.
		self.side = [None, None]
		# cs1e of the MAIN ladder -- the size headline.
		self.cs1e = None
		self.total_w = None
		self.total_e = None
		self.max_pp = None
		# COST composition: name -> constraints, plus the total.
		self.cost = {}
		self.cost_total = None
		self.logup = None
		# decider: name -> constraints; step list; the proving job.
		self.dec_cs = {}
		self.dec_steps = []
		self.snark_job = None
		# lkup / share -- the single biggest circuit-size distorter.
		self.share = None
		self.share_size = None
		self.lkup = None
		# tuner arm and its converge line.
		self.arm = None
		self.tune_iter = None
		self.qm_real = None
		# seed caps as a 5-list [subsigs, igc, cp, dfa, perc_comp].
		# v2 only -- v1 has no seed marker.
		self.tune_seed = None
		# one entry per round: [iter, seconds, "cap -> val, ..."].
		self.tune_rounds = []
		# `TOTAL T ms` off the CONVERGED line, in seconds.  None means
		# the tuner has NOT converged -- while a run is tuning that is
		# the live signal, not missing data.
		self.tune_total_s = None
		# epoch of the log header line = the exact run start.
		self.t_start = None
		# the bora_cli subcommand this leaf was launched with, e.g.
		# `full_clam` / `full_clam_v1`.  Printed so the arm is
		# attributable to argv rather than inferred.
		self.sub = None
		# highest RAM the log itself printed, GiB (UNDERSTATES peak).
		self.ram_log = 0.0
		# Pass 3 prove spans: (count, summed seconds).
		self.prove_n = 0
		self.prove_s = 0.0
		# jobs the fold announced, and the terminal marker.
		self.n_jobs_log = None
		self.all_jobs_s = None
		# mtime at last scan, for stall detection.
		self.mtime = 0.0

	def to_json(self):
		return {k: v for k, v in self.__dict__.items()}

	def from_json(self, d):
		for k, v in d.items():
			if k in self.__dict__:
				# json turns int keys into strings; restore them.
				if k in ("steps", "corpus", "prog", "ladder"):
					v = {int(a): b for a, b in v.items()}
				setattr(self, k, v)

	def scan(self):
		"""Consume new bytes only.  Returns bytes read."""
		try:
			sz = os.path.getsize(self.path)
			self.mtime = os.path.getmtime(self.path)
		except OSError:
			return 0
		if sz < self.off:            # rotated/replaced
			self.__init__(self.path)
			sz = os.path.getsize(self.path)
		if sz == self.off:
			return 0
		with open(self.path, "r", errors="replace") as f:
			f.seek(self.off)
			data = f.read()
			self.off = f.tell()
		for ln in data.splitlines():
			self._line(ln)
		return len(data)

	def _line(self, ln):
		m = RE_STEP.search(ln)
		if m:
			job, ph, st, val, unit = m.groups()
			if ph == "1":
				self.steps.setdefault(int(job), {})[int(st)] = \
					dur_s(val, unit)
			w = RE_WORDS.search(ln)
			if w and ph == "1" and st == "1":
				self.corpus[int(job)] = (int(w.group(1)),
					int(w.group(2)))
			return
		m = RE_CIRC.search(ln)
		if m:
			self.pend.append([int(m.group(1)), int(m.group(2)),
				int(m.group(3))])
			return
		m = RE_KEYS.search(ln)
		if m:
			n, tw, te, cs, mp = [int(x) for x in m.groups()]
			blk = self.pend[-n:] if n <= len(self.pend) else self.pend
			self.pend = []
			if n == 1:
				if blk:
					self.side[0] = blk[0][1]
				self.side[1] = cs
			else:
				for i, c, r in blk:
					self.ladder[i] = (c, r)
				self.cs1e, self.total_w = cs, tw
				self.total_e, self.max_pp = te, mp
			return
		for rx, attr in ((RE_SHARE, "share"),
				(RE_SHARESZ, "share_size"), (RE_LKUP, "lkup")):
			m = rx.search(ln)
			if m:
				v = int(m.group(1))
				if attr != "lkup" or v > 0:
					setattr(self, attr, v)
				return
		m = RE_COSTTOT.search(ln)
		if m:
			self.cost_total = int(m.group(2))
			return
		m = RE_COSTSUB.match(ln.split("LOG")[-1] if "LOG" in ln else ln)
		if m:
			self.cost[m.group(1)] = int(m.group(2))
			return
		m = RE_COSTFW.search(ln)
		if m:
			self.cost["framework"] = int(m.group(1))
			return
		m = RE_LOGUP.search(ln)
		if m:
			self.logup = int(m.group(1))
			return
		m = RE_DECCS.search(ln)
		if m:
			self.dec_cs[m.group(1)] = int(m.group(2))
			return
		m = RE_DECSTEP.search(ln)
		if m:
			self.dec_steps.append((int(m.group(1)),
				m.group(2).strip(), int(m.group(3)),
				int(m.group(4)) / 1e3))
			return
		m = RE_SNARK.search(ln)
		if m:
			self.snark_job = int(m.group(1))
			return
		m = RE_PROVE.search(ln)
		if m:
			self.prove_n += 1
			self.prove_s += dur_s(m.group(2), m.group(3))
			return
		m = RE_PROG.search(ln)
		if m and m.group(1) == "1":
			jm = re.search(r"\[job (\d+)\]", ln)
			if jm:
				self.prog[int(jm.group(1))] = (int(m.group(2)),
					int(m.group(3)))
			return
		m = RE_V2ITER.search(ln) or RE_V1ITER.search(ln)
		if m:
			self.arm = "v2" if "v2 iter" in ln else "v1"
			self._round(m.group(1), m.group(2))
			return
		m = RE_V2SEED.search(ln)
		if m:
			self.arm = "v2"
			self.tune_seed = [int(g) for g in m.groups()]
			return
		m = RE_CMD.search(ln)
		if m:
			self.sub = m.group(1)
			if self.arm is None:
				self.arm = arm_of(self.sub)
			return
		m = RE_START.search(ln)
		if m and self.t_start is None:
			try:
				self.t_start = time.mktime(time.strptime(
					m.group(1), "%Y-%m-%d %H:%M:%S"))
			except ValueError:
				pass
			return
		m = RE_PLAN.search(ln)
		if m:
			# The plan dir is a valid arm signal ONLY for an explicit
			# A/B token.  Since 2026-08-18 the bare `full_clam` /
			# `full_dna` run v2 under the CANONICAL dir (arm_plan_dir
			# renames on Some(..) only), so "no clam_v2 in the path"
			# no longer means v1 -- reading it that way reported every
			# production run as the legacy tuner.  A canonical dir now
			# says nothing, and the arm comes from the tuner markers.
			d = m.group(1)
			if "clam_v2" in d or "dna_v2" in d:
				self.arm = "v2"
			elif "clam_v1" in d or "dna_v1" in d:
				self.arm = "v1"
			return
		m = RE_V2CONV.search(ln)
		if m:
			self.arm = "v2"
			self.tune_iter = int(m.group(1))
			self.qm_real = int(m.group(2))
			self._converged(ln)
			return
		m = RE_V1CONV.search(ln)
		if m:
			if self.arm is None:
				self.arm = "v1"
			self.tune_iter = int(m.group(1))
			self._converged(ln)
			return
		m = RE_RAM.search(ln)
		if m:
			self.ram_log = max(self.ram_log, float(m.group(1)))
			return
		m = RE_FOLDPOT.search(ln)
		if m:
			self.n_jobs_log = int(m.group(1))
			return
		m = RE_ALLJOBS.search(ln)
		if m:
			self.all_jobs_s = int(m.group(1)) / 1e3

	def _round(self, it, rest):
		"""Record one tuner round.  `rest` is everything after the
		iter number, which differs per arm and per outcome."""
		ms = RE_ROUNDMS.search(rest)
		bumps = RE_BUMP.findall(rest)
		if bumps:
			what = ", ".join("%s -> %s" % (n, v) for n, v in bumps)
		elif "subset clean" in rest:
			# not a bump: the subset passed, so the round re-runs on
			# the FULL corpus.  Costed, and it is NOT a crawl step.
			what = "(subset clean, promote to full corpus)"
		else:
			what = "(no bump parsed)"
		self.tune_rounds.append([int(it),
			float(ms.group(1)) / 1e3 if ms else 0.0, what])

	def _converged(self, ln):
		"""Fold the CONVERGED line's own round into the table and
		take its TOTAL, which is the authoritative tune time."""
		ms = RE_ROUNDMS.search(ln)
		it = self.tune_iter
		if ms and it is not None:
			self.tune_rounds.append([it,
				float(ms.group(1)) / 1e3, "(CONVERGED)"])
		t = RE_TOTALMS.search(ln)
		if t:
			self.tune_total_s = float(t.group(1)) / 1e3


class Run(object):
	"""The merged view over every process's Acc.  The per-JOB model is
	topology-invariant; only RSS and wall AGGREGATE differently, and
	those two are the only places `topo` is consulted."""

	def __init__(self, topo, accs):
		self.topo = topo
		self.accs = accs

	def _first(self, attr):
		for a in self.accs:
			v = getattr(a, attr)
			if v:
				return v
		return None

	# ---- size (topology-invariant: one ladder, built per process) --
	def ladder(self):
		for a in self.accs:
			if a.ladder:
				return a.ladder
		return {}

	def cs1e(self):
		return self._first("cs1e")

	def share(self):
		return self._first("share")

	def lkup(self):
		return self._first("lkup")

	def arm(self):
		return self._first("arm")

	def dec_cs(self):
		out = {}
		for a in self.accs:
			out.update(a.dec_cs)
		return out

	def cost(self):
		for a in self.accs:
			if a.cost:
				return a.cost
		return {}

	# ---- per-job (topology-invariant) ------------------------------
	def jobs(self):
		"""job id -> {step: seconds}, merged.  Tags are GLOBAL in clam
		and disjoint per process, so a plain merge is correct here --
		this is exactly what does NOT hold for DLP."""
		out = {}
		for a in self.accs:
			out.update(a.steps)
		return out

	def corpus(self):
		out = {}
		for a in self.accs:
			out.update(a.corpus)
		return out

	def progress(self):
		out = {}
		for a in self.accs:
			out.update(a.prog)
		return out

	def prove(self):
		"""(count, mean seconds) over every Pass-3 span seen."""
		n = sum(a.prove_n for a in self.accs)
		s = sum(a.prove_s for a in self.accs)
		return n, (s / n if n else None)

	def snark_job(self):
		return self._first("snark_job")

	def tune_iter(self):
		return self._first("tune_iter")

	def tune(self):
		"""(seed, rounds, total_s) from whichever process tuned.  On a
		two-half box both processes tune independently and agree, so
		the first that has anything wins."""
		for a in self.accs:
			if a.tune_rounds or a.tune_total_s or a.tune_seed:
				return a.tune_seed, a.tune_rounds, a.tune_total_s
		return None, [], None

	def sub(self):
		return self._first("sub")

	def t_start(self):
		"""Earliest run start across processes, epoch seconds."""
		v = [a.t_start for a in self.accs if a.t_start]
		return min(v) if v else None

	# ---- RAM (TOPOLOGY-SPECIFIC) -----------------------------------
	def ram_log_gib(self):
		"""What the logs printed.  For a 2-process box the BOX figure
		is the SUM -- both processes are resident at once (legacy:
		527 + 369 = 896 on a 961 GiB box) -- while the per-process max
		is what compares against legacy's per-half numbers."""
		vals = [a.ram_log for a in self.accs if a.ram_log]
		if not vals:
			return None, None
		return sum(vals), max(vals)

	def stalled(self):
		"""True when every log is older than STALL_S and no terminal
		marker was seen."""
		if any(a.all_jobs_s for a in self.accs):
			return False
		now = time.time()
		return all(a.mtime and now - a.mtime > STALL_S
			for a in self.accs)


# ------------------------------------------------------------ sections


def show_header(run, bank, new_bytes, dt):
	L = []
	t = run.topo
	box, own = clocks(time.time())
	L.append("=" * 66)
	L.append("full_clam NEO METER  %s  (owner %s)" % (box, own))
	L.append("topology %s: %d process(es) x %d jobs   %s"
		% (t.label, t.n_procs, t.n_jobs // max(t.n_procs, 1), t.note))
	arm = run.arm()
	sh, lk = run.share(), run.lkup()
	L.append("arm %s%s%s   share %s (legacy pin %d, neo pred %d)   "
		"lkup %s" % (
			arm or "not seen",
			"" if not run.sub() else " (%s)" % run.sub(),
			"" if arm != "v1" else "  <- WARN: legacy tuner",
			sh if sh else "-", LEG_SHARE, NEO_SHARE_PRED,
			com(lk)))
	L.append("logs %d, %d new bytes in %s" % (
		len(run.accs), new_bytes, hm(dt)))
	return L


def show_ram(run, bank):
	"""HEADLINE.  Answers 'can this finish in this box's memory' from
	the ladder, long before the fold ends.  Every projection states
	what it was derived from; nothing is asserted unsourced."""
	t = run.topo
	L = ["", "RAM VERDICT  (budget %.0f GiB)" % t.ram_gib]
	avail = mem_avail_gib()
	live = proc_rss_gib()
	peak = bank.get("rss_peak") or 0.0
	if live:
		peak = max(peak, live)
		bank["rss_peak"] = peak
	box_log, proc_log = run.ram_log_gib()
	L.append("  MemAvailable   %s GiB" % (
		"%.1f" % avail if avail else "-"))
	L.append("  live RSS       %s GiB   banked peak %s GiB" % (
		"%.1f" % live if live else "-",
		"%.1f" % peak if peak else "-"))
	if box_log:
		L.append("  log RAM        %.0f GiB box / %.0f GiB per proc  "
			"(UNDERSTATES peak by ~3%%)" % (box_log, proc_log))
	# projection: decider first (exact), then cs1e (early estimate).
	dec = run.dec_cs()
	cs1e = run.cs1e()
	proj, src = None, None
	if dec:
		mx = max(dec.values())
		proj = mx / 1e6 * t.ram_per_mcs
		src = "measured %s %s cs" % (
			max(dec, key=dec.get), com(mx))
	elif cs1e:
		# legacy MainDecider is 2.32x cs1e; neo's ratio is NOT yet
		# established (dec_big died mid-build), so the legacy ratio is
		# used and flagged.  This is an UPPER bound if neo's ratio is
		# lower, which partial evidence suggests.
		proj = cs1e * 2.32 / 1e6 * t.ram_per_mcs
		src = "cs1e %s x2.32 (LEGACY ratio, neo's unmeasured)" % \
			com(cs1e)
	if proj is None:
		L.append("  projection     not yet -- no ladder seen")
		L.append("  VERDICT        PENDING")
		return L
	L.append("  projected peak %.0f GiB   from %s" % (proj, src))
	L.append("                 @ %.2f GiB per M decider R1CS "
		"(%s anchor)" % (t.ram_per_mcs, t.key))
	head = t.ram_gib - proj
	if proj > t.ram_gib:
		L.append("  VERDICT        *** RED *** over budget by %.0f GiB"
			% -head)
		L.append("                 RECOMMEND KILL -- the decider runs "
			"LAST, after the fold")
		L.append("                 nothing guards this run: "
			"max_rss_gb is set only on V101 dec_big")
	elif head < t.ram_gib * 0.10:
		L.append("  VERDICT        AMBER  headroom %.0f GiB (<10%%)"
			% head)
	else:
		L.append("  VERDICT        GREEN  headroom %.0f GiB" % head)
	return L


def show_size(run):
	"""The tuner-win scorecard: neo vs the legacy hand-tuned caps."""
	lad = run.ladder()
	cs1e = run.cs1e()
	dec = run.dec_cs()
	L = ["", "SIZE vs LEGACY  (legacy = hand-declared caps, "
		"perc 100/100, 8 jobs)"]
	L.append("  %-22s %14s %14s %8s" % ("metric", "legacy", "neo", "x"))
	rows = [
		("ladder circ1 cols", LEG_LADDER[1][0],
			lad.get(1, (None,))[0]),
		("ladder circ2 cols", LEG_LADDER[2][0],
			lad.get(2, (None,))[0]),
		("cs1e", LEG_CS1E, cs1e),
		("MainDecider R1CS", LEG_MAINDEC,
			dec.get("MainDeciderCirtuit")),
		("CyclePair R1CS", LEG_CYCLEPAIR, dec.get("CyclePairCirc")),
	]
	for name, leg, neo in rows:
		L.append("  %-22s %14s %14s %8s" % (
			name, com(leg), com(neo), ratio(neo, leg)))
	side = run.accs[0].side if run.accs else [None, None]
	L.append("  %-22s %14s %14s %8s   <- build-drift gauge, NOT a"
		" comparability control" % (
			"side circ cols", com(LEG_SIDE[0]), com(side[0]),
			ratio(side[0], LEG_SIDE[0])))
	cost = run.cost()
	if cost:
		L.append("  COST composition (R1CS constraints)")
		for k in ("CpMapper#1", "CpMapper#2", "SedMapper",
				"DfaMapper", "framework"):
			L.append("    %-20s %14s %14s %8s" % (
				k, com(LEG_COST.get(k)), com(cost.get(k)),
				ratio(cost.get(k), LEG_COST.get(k))))
	sh = run.share()
	if sh and sh > NEO_SHARE_PRED * 2:
		L.append("  !! share %d is %.1fx the predicted production %d "
			"-- the circuit is INFLATED by the job split, not by the"
			" tuner" % (sh, float(sh) / NEO_SHARE_PRED,
				NEO_SHARE_PRED))
	return L


def show_stages(run):
	"""Per-job stage budget vs legacy.  Topology-invariant: all three
	runs carry 8 jobs at the same cpus-per-job, so this compares 1:1
	even on the 512 box where the WALL does not."""
	jobs = run.jobs()
	L = ["", "STAGES  per job, seconds, vs legacy mean over 8 jobs"]
	if not jobs:
		L.append("  no Phase 1 step has completed yet")
		return L
	# A stage budget is per-job SECONDS, so it only transfers when the
	# job carries the same corpus.  Comparing a subsampled run against
	# legacy reads as a fake win (a 2% log scores 0.10x on Pass 1).
	# Guard it: below ~half legacy's words/job the table is timings
	# only, and the per-STEP Pass 3 span at the bottom is the figure
	# that does transfer.
	corp = run.corpus()
	wpj = (sum(v[0] for v in corp.values()) / float(len(corp))
		if corp else None)
	b_cmp = wpj is None or wpj >= LEG_WORDS_PER_JOB * 0.5
	if not b_cmp:
		L.append("  !! %.0f words/job vs legacy %d -- this run is "
			"SUBSAMPLED, so the" % (wpj, LEG_WORDS_PER_JOB))
		L.append("     x column below is NOT a comparison.  Only the "
			"Pass 3 per-STEP")
		L.append("     span at the foot of this table transfers.")
	L.append("  %-10s %10s %12s %8s %6s" % (
		"step", "legacy", "neo mean", "x", "n"))
	tot_leg = tot_neo = 0.0
	for st in sorted(LEG_STEP):
		vals = [j[st] for j in jobs.values() if st in j]
		leg = LEG_STEP[st]
		tot_leg += leg
		if not vals:
			L.append("  %-10s %10.1f %12s %8s %6d" % (
				LEG_STEP_NAME[st], leg, "-", "-", 0))
			continue
		mean = sum(vals) / len(vals)
		tot_neo += mean
		L.append("  %-10s %10.1f %12.1f %8s %6d" % (
			LEG_STEP_NAME[st], leg, mean,
			ratio(mean, leg) if b_cmp else "n/a", len(vals)))
	if tot_neo:
		L.append("  %-10s %10.1f %12.1f %8s" % (
			"TOTAL", tot_leg, tot_neo,
			ratio(tot_neo, tot_leg) if b_cmp else "n/a"))
		L.append("  legacy per job %s; decider adds %s (one job only,"
			" b_one_proof)" % (hm(LEG_JOB_TOTAL), hm(LEG_DEC_TOTAL)))
	n, mean = run.prove()
	if n:
		leg_ps = LEG_STEP[7] / float(LEG_CHUNKS_MIN)
		L.append("  Pass 3 span    %10.3f %12.3f %8s %6d   "
			"(s/step; spans TILE the pass)" % (
				leg_ps, mean, ratio(mean, leg_ps), n))
	return L


def show_progress(run, bank):
	"""Where the run is and when it lands.  Cost-weighted, because the
	fold is front-loaded by circuit size -- a step-count ETA reads
	optimistic early and pessimistic late."""
	t = run.topo
	L = ["", "PROGRESS"]
	corp = run.corpus()
	prog = run.progress()
	if corp:
		w = sum(v[0] for v in corp.values())
		f = sum(v[1] for v in corp.values())
		L.append("  corpus         %d jobs, %d words, %s packed "
			"fields (legacy %d words/job)" % (
				len(corp), w, com(f), LEG_WORDS_PER_JOB))
	if not prog:
		L.append("  fold has not started (Pass 1/2 are SILENT at "
			"LOG3 -- a long gap here is NORMAL)")
		return L
	done = sum(v[0] for v in prog.values())
	tot = sum(v[1] for v in prog.values())
	pct = 100.0 * done / tot if tot else 0.0
	L.append("  fold           %d of %d words  %.1f%%  (%d jobs "
		"reporting)" % (done, tot, pct, len(prog)))
	n, mean = run.prove()
	if n and mean and done:
		# project on the LEGACY per-job step count, not on what this
		# run has emitted so far: a job that has not logged yet must
		# not shrink the denominator.
		left = max(tot - done, 0)
		per_job = max(len(prog), 1)
		eta_s = left * mean / per_job
		box, own = clocks(time.time() + eta_s)
		L.append("  fold ETA       %s left -> %s box / %s owner" % (
			hm(eta_s), box, own))
		if t.b_wall_ref:
			L.append("  legacy wall    %s (decider half) / %s "
				"(fold-only half)" % (
					hm(LEG_WALL_DEC), hm(LEG_WALL_FOLD)))
		else:
			L.append("  legacy wall    NOT comparable: legacy never "
				"ran %d jobs in one process at perc 100" % t.n_jobs)
	sj = run.snark_job()
	if sj is not None:
		L.append("  DECIDER        job %d is proving -- this is the "
			"RAM peak, and it runs LAST" % sj)
	return L


def full_corpus(run):
	"""True/False that this run's jobs carry legacy's corpus, or None
	when no job has reported yet.  Every cross-run RATIO in this file
	is gated on it: a per-job second measures corpus as much as speed,
	so a 2% log scores a fake 5x win.  None is common and NOT an
	error -- the tuner runs before step 1 reports."""
	corp = run.corpus()
	if not corp:
		return None
	wpj = sum(v[0] for v in corp.values()) / float(len(corp))
	return wpj >= LEG_WORDS_PER_JOB * 0.5


def crawl_span(rounds):
	"""Longest run of consecutive rounds that bump exactly ONE cap,
	the same cap each time.  Returns (name, count, seconds).

	This is the CP under-seed pathology measured 2026-08-16: the seed
	is below the true demand, so the tuner walks the cap up by +1 and
	pays a FULL probe round per step, each costlier than the last.  It
	is the difference between a 4-minute tune and a 37-minute one, and
	no other section of this report can show it."""
	best = (None, 0, 0.0)
	i = 0
	while i < len(rounds):
		w = rounds[i][2]
		# a single bump renders as exactly one `name -> val`.
		if " -> " not in w or "," in w.split(" -> ")[0]:
			i += 1
			continue
		name = w.split(" -> ")[0]
		if w.count(" -> ") != 1:
			i += 1
			continue
		j, tot = i, 0.0
		while j < len(rounds) and rounds[j][2].count(" -> ") == 1 \
				and rounds[j][2].split(" -> ")[0] == name:
			tot += rounds[j][1]
			j += 1
		if j - i > best[1]:
			best = (name, j - i, tot)
		i = max(j, i + 1)
	return best


def show_tuner(run):
	"""Tune rounds and tune time.  The tuner runs FIRST, before Phase
	1 step 1, and its cost lands in NO stage column -- so without this
	section a 37-minute tune is invisible everywhere in the report."""
	seed, rounds, total = run.tune()
	arm = run.arm()
	L = ["", "TUNER  arm %s" % (arm or "not seen")]
	if seed:
		L.append("  seed   subsigs %d  igc %d  cp %d  dfa %d  "
			"perc_comp %d" % tuple(seed))
	if not rounds:
		L.append("  no round yet.  The tuner is the FIRST thing that "
			"runs, so a run that")
		L.append("  has printed nothing else is most likely HERE "
			"(v1 reference: %s)." % secs(LEG_TUNE_V1_S))
		return L
	L.append("  %5s %10s   %s" % ("iter", "wall", "bumped"))
	if len(rounds) <= TUNE_ROWS:
		show = rounds
	else:
		# head AND tail: the head carries the seed climb, the tail
		# carries the expensive rounds.  Dropping either misleads.
		h = TUNE_ROWS // 2
		show = rounds[:h] + [None] + rounds[-h:]
	for r in show:
		if r is None:
			L.append("  %5s %10s   ... %d rounds elided ..." % (
				"", "", len(rounds) - TUNE_ROWS))
			continue
		L.append("  %5d %10s   %s" % (r[0], secs(r[1]), r[2]))
	if total is not None:
		L.append("  CONVERGED @iter %s   TOTAL %s over %d rounds" % (
			run.tune_iter(), secs(total), len(rounds)))
		if arm == "v2":
			# the ratio is printed ONLY at a comparable corpus: the
			# v1 reference is a 100% tune, so dividing a 0.5% smoke
			# tune into it reads 0.00x and means nothing.
			ok = full_corpus(run)
			L.append("  v1 reference, 100%% corpus 08-16: %s over %d "
				"rounds%s" % (secs(LEG_TUNE_V1_S),
					LEG_TUNE_V1_ROUNDS,
					"   -> %s" % ratio(total, LEG_TUNE_V1_S)
					if ok else ""))
			if not ok:
				L.append("  (no ratio: %s)" % (
					"this run is SUBSAMPLED" if ok is False
					else "corpus not reported yet"))
	else:
		el = sum(r[1] for r in rounds)
		L.append("  TUNING -- %d rounds, %s so far, last round %s"
			% (len(rounds), secs(el), secs(rounds[-1][1])))
		# rounds grow as the caps grow, so a rising trend is normal;
		# it is quoted so a FLAT trend (a stuck probe) is visible too.
		if len(rounds) >= 4:
			prev = sum(r[1] for r in rounds[-4:-1]) / 3.0
			if prev > 0:
				L.append("             last vs prior 3 mean: %s "
					"(rounds grow with the caps)"
					% ratio(rounds[-1][1], prev))
		L.append("             v1 reference %s over %d rounds; the "
			"tuner is NOT hung" % (secs(LEG_TUNE_V1_S),
				LEG_TUNE_V1_ROUNDS))
	name, n, sp = crawl_span(rounds)
	if n >= 3:
		L.append("  !! CRAWL: %d consecutive rounds bumping %s by +1 "
			"= %s" % (n, name, secs(sp)))
		L.append("     that cap is UNDER-SEEDED; the seed, not the "
			"probe, is the cost")
	return L


def show_position(run):
	"""WHERE IT IS plus a pace verdict, scored in per-JOB seconds
	against the legacy stage budget -- the one axis that transfers
	across all three box shapes."""
	L = ["", "POSITION"]
	t0 = run.t_start()
	# "as of" is NOW while the run is live, but the log's last write
	# once it is not: a finished or dead run must report its runtime,
	# not the age of its log.  Live runs are unaffected -- the log is
	# being written, so mtime is now.
	mt = max([a.mtime for a in run.accs if a.mtime] or [0])
	asof = mt if (run.stalled() and mt) else time.time()
	wall = (asof - t0) if t0 else None
	seed, rounds, tune_total = run.tune()
	jobs = run.jobs()
	if wall is not None:
		L.append("  wall since start  %s%s" % (hm(wall),
			"   (tuner %s of it, see TUNER)" % secs(tune_total)
			if tune_total else ""))
	if not jobs:
		where = ("TUNING" if rounds and tune_total is None
			else "pre-step-1 (tuner done, Phase 1 not yet reporting)"
			if tune_total else "before the tuner's first round")
		L.append("  WHERE IT IS: %s" % where)
		L.append("  no Phase 1 step has completed, so there is "
			"nothing to pace yet.")
		return L
	# the LEADING job sets the position: jobs run concurrently and the
	# run ends when the last finishes, but the furthest job is what
	# says which stage the run has reached.
	lead = max(jobs, key=lambda j: sum(jobs[j].values()))
	done = jobs[lead]
	cur = max(done) + 1 if done else 1
	neo_cum = sum(done.values())
	leg_cum = sum(LEG_STEP[k] for k in done if k in LEG_STEP)
	if cur > 8:
		L.append("  WHERE IT IS: Phase 1 COMPLETE on job %d "
			"(all 8 steps)" % lead)
	else:
		frac = None
		if cur == 7:
			p = run.progress().get(lead)
			if p and p[1]:
				frac = float(p[0]) / p[1]
		L.append("  WHERE IT IS: step %d %s%s  (job %d leads of %d "
			"reporting)" % (cur, LEG_STEP_NAME.get(cur, "?"),
				" -- %.1f%% through it" % (100.0 * frac)
				if frac is not None else "",
				lead, len(jobs)))
		if frac is None:
			L.append("               (no in-step progress marker; "
				"only step 7 emits one)")
		L.append("               legacy budget for this step: %s"
			% secs(LEG_STEP.get(cur, 0.0)))
	if not leg_cum:
		L.append("  nothing comparable has completed yet.")
		return L
	# A per-job second only compares when the job carries the same
	# corpus, so this takes show_stages' guard verbatim: below half
	# legacy's words/job a subsampled run scores a FAKE win (a 2% log
	# reads ~5x AHEAD purely because its steps are shorter).
	corp = run.corpus()
	if full_corpus(run) is False:
		wpj = sum(v[0] for v in corp.values()) / float(len(corp))
		L.append("  completed steps   legacy %9.1f s   neo %9.1f s"
			% (leg_cum, neo_cum))
		L.append("                    NO PACE: %.0f words/job vs "
			"legacy %d -- this run is" % (wpj, LEG_WORDS_PER_JOB))
		L.append("                    SUBSAMPLED, so a ratio here "
			"measures corpus, not speed")
		return L
	L.append("  completed steps   legacy %9.1f s   neo %9.1f s   "
		"PACE %s" % (leg_cum, neo_cum, ratio(leg_cum, neo_cum)))
	r = leg_cum / neo_cum if neo_cum else 0.0
	L.append("                    %s" % (
		"AHEAD of legacy" if r > 1.02 else
		("BEHIND legacy" if r < 0.98 else "at legacy pace")))
	# the pace above is a STEP-BOUNDARY comparison: it excludes the
	# step in flight and the tuner, both of which are reported above.
	# Said plainly so it is not read as an end-to-end ratio.
	L.append("                    step-boundary only -- excludes the "
		"step in flight")
	L.append("                    and the tuner; neither is in the "
		"legacy stage budget")
	return L


def show_next(run):
	L = ["", "NEXT"]
	if run.stalled():
		L.append("  !! every log is older than %s with no terminal "
			"marker -- check the box" % hm(STALL_S))
	sj = run.snark_job()
	if sj is None:
		L.append("  fold in progress.  The decider begins at "
			"`Job N generating SNARK proof`;")
		L.append("  to take the fold WITHOUT the decider peak, stop "
			"the run at that line.")
	else:
		L.append("  decider running: peak RSS is being paid now.")
	L.append("  re-run this meter any time; the scan is incremental.")
	L.append("=" * 66)
	return L


# --------------------------------------------------------------- state


def state_path(topo):
	return "/tmp/bora/clam_progress_%s.state.json" % topo.key


def run(topo, argv):
	"""Entry point both front-ends call.  Returns the report text."""
	if "--legacy" in argv:
		return "\n".join(dump_legacy())
	logs = topo.logs()
	if "--log" in argv:
		logs = [argv[argv.index("--log") + 1]]
	if not logs:
		return ("no log found.  Expected %s%s, or pass --log PATH."
			% (CURRENT_1,
				" and %s" % CURRENT_2 if topo.n_procs > 1 else ""))
	sp = state_path(topo)
	st = {}
	if "--fresh" not in argv:
		try:
			st = json.load(open(sp))
		except (OSError, ValueError):
			st = {}
	bank = st.get("bank", {})
	accs = []
	t0 = time.time()
	new = 0
	for p in logs:
		a = Acc(p)
		saved = (st.get("accs") or {}).get(p)
		if saved:
			a.from_json(saved)
		new += a.scan()
		accs.append(a)
	r = Run(topo, accs)
	out = []
	out += show_header(r, bank, new, time.time() - t0)
	out += show_ram(r, bank)
	out += show_tuner(r)
	out += show_position(r)
	out += show_size(r)
	out += show_stages(r)
	out += show_progress(r, bank)
	out += show_next(r)
	try:
		json.dump({"accs": {a.path: a.to_json() for a in accs},
			"bank": bank}, open(sp, "w"))
	except OSError:
		pass
	return "\n".join(out)


def dump_legacy():
	"""`--legacy`: the whole reference, so it can be checked without
	re-parsing 3.5 MB of combined log."""
	L = ["=" * 66, "LEGACY full_clam REFERENCE (derived 2026-08-18)",
		"source data/paper_data/run_data/data/raw_data/jet1tb/"
		"extracted/full_clam.combined.log",
		"host zkregplus-large, 64 cpu, 961.1 GiB; 8 jobs two-half "
		"4+4; b_one_proof.",
		"",
		"TRAP: the label=part1/part2 headers are INVERTED vs the job "
		"tags.  Job tags",
		"are GLOBAL 0-7 and disjoint per region.  Read tags, never "
		"labels; find the",
		"decider by `generating SNARK proof`.",
		"", "PER-JOB STAGE BUDGET, seconds (mean over 8 jobs)"]
	for st in sorted(LEG_STEP):
		L.append("  step %d %-9s %10.1f  %5.2f%%" % (
			st, LEG_STEP_NAME[st], LEG_STEP[st],
			100.0 * LEG_STEP[st] / LEG_JOB_TOTAL))
	L.append("  TOTAL %s = %s" % (com(int(LEG_JOB_TOTAL)),
		hm(LEG_JOB_TOTAL)))
	L.append("")
	L.append("DECIDER (one job only), seconds")
	for n, s in LEG_DEC:
		L.append("  %-26s %9.1f" % (n, s))
	L.append("  TOTAL %s = %s" % (com(int(LEG_DEC_TOTAL)),
		hm(LEG_DEC_TOTAL)))
	L.append("")
	L.append("WALL   decider region %s   fold-only region %s" % (
		hm(LEG_WALL_DEC), hm(LEG_WALL_FOLD)))
	L.append("SIZE   circ1 %s cols, circ2 %s cols, cs1e %s" % (
		com(LEG_LADDER[1][0]), com(LEG_LADDER[2][0]), com(LEG_CS1E)))
	L.append("       MainDecider %s, CyclePair %s" % (
		com(LEG_MAINDEC), com(LEG_CYCLEPAIR)))
	L.append("       side circ %s cols / cs1e %s (build-drift gauge "
		"only)" % (com(LEG_SIDE[0]), com(LEG_SIDE[1])))
	L.append("LKUP   table %s, share %d (HAND PIN), share size %s" % (
		com(LEG_LKUP), LEG_SHARE, com(LEG_SHARE_SIZE)))
	L.append("       neo DERIVES ~%d for the same corpus at 8 jobs; a"
		" subsampled run" % NEO_SHARE_PRED)
	L.append("       derives far higher and inflates every circuit.")
	L.append("RAM    %.0f GiB decider half, %.0f GiB fold half, "
		"%.0f GiB 8-job 1-proc" % (
			LEG_RAM_DEC_HALF, LEG_RAM_FOLD_HALF, LEG_RAM_1PROC_8JOB))
	L.append("       log RAM UNDERSTATES peak RSS by ~3%.")
	L.append("=" * 66)
	return L
