#!/usr/bin/env python3
"""small_full_dlp run meter: qm ratchet, ladder gate, circ sizes vs the
measured neo full_dlp reference, Pass 1 rate, fold progress. Read-only;
safe to run against a live log."""

import os
import re
import sys
import time

# default live log written by PAPER_DATA.py's launcher (a SYMLINK into
# /tmp/bora/logs/small_dlp_full_<stamp>/run.log).
DEFAULT_LOG = "/tmp/bora/CURRENT_JOB.log"

# ---------------------------------------------------------------- refs

# MEASURED neo full_dlp production ladder, from the circs: 4 preprocess
# block of ~/tmp/bora/neo_run/speed/neo_pass1_0816.log.  circ index is
# 1-based; (cols, rows) are R1CS A-matrix dims as PERF 1002 reports
# them.  NOT the "==== COST circN ====" totals in that log -- those are
# cost-model predictions and over-count ~6x.  Override with --ref LOG.
REF_LADDER = {
	1: (295516, 245348),
	2: (1942772, 1620648),
	3: (7920188, 6738718),
	4: (20453765, 17296201),
}
# P_max.subsigs the full_dlp tuner settles on; the small run must match
# it or the sampled corpus lost the top-rung words.
PROD_SUBSIGS = 18751
# rung count the ladder must reach; 3 means circ4 (the tier that sets
# cs1e, decider size and peak RAM) never appears and the run is void.
EXPECT_RUNGS = 4
# Pass 1 ms/chunk reference points (full_dlp, 8 jobs): legacy arm, neo
# before the S5 advice-reuse fix, neo after it.  See memory M101.
MS_LEGACY = 175.6
MS_NEO_PRE_S5 = 588.7
MS_NEO_POST_S5 = 323.2
# packed fields per chunk on the DLP/enron corpus (seg_word_len).  Used
# only to turn step 1's total_word_len into a chunk denominator.
SEG_WORD_LEN = 64
# a log untouched this long, with no terminal marker, is suspect.
STALL_S = 45 * 60

# ------------------------------------------------------------- regexes

# per-circuit measured R1CS dims, emitted before the block's circs: N.
RE_CIRC = re.compile(
	r"PERF 1002 circ (\d+), r1cs cols: (\d+), rows: (\d+)")
# closes a preprocess block and states how many circuits it held.
RE_BLOCK = re.compile(
	r"preprocess\(\) Step 2: setup circ params\. circs: (\d+)")
# the fold proper begins; PERF 1002 lines before it are tuner-internal.
RE_DRIVER = re.compile(r"=== ZKP driver \(aggr\) starts ====")
# my b_fold_only ratchet raising the qm_real_rows ceiling (old -> new).
RE_RATCHET = re.compile(
	r"v5\[(\S+)\]: qm_real_rows (\d+) -> (\d+), re-walking")
# the ratchet giving up after 3 re-walks: the run is dead, save the log.
RE_SHORT = re.compile(r"qm_real_rows still short after 3 re-walks")
# tuner verdict: rung count, occupancy histogram, the P_max top.
RE_GATE = re.compile(
	r"determine_config_aggr: (\d+) rungs, hist=\[([^\]]*)\], "
	r"P_max\.subsigs=(\d+)")
# v5 walk verdict: same rung count plus its per-rung cost estimates.
RE_V5 = re.compile(
	r"v5\[\S+\]: (\d+) rungs, occupancy hist=\[([^\]]*)\], "
	r"costs=\[([^\]]*)\]")
# Pass 1 partA roll-up: per-segment rung router (halo + try outcomes).
RE_PA = re.compile(
	r"69120\.7: partA chunks=(\d+) tries=(\d+) halo_us=(\d+) "
	r"ok_us=(\d+) fail_us=(\d+)")
# Pass 1 partB roll-up: the statement loop, advice now reused (S5).
RE_PB = re.compile(
	r"69120\.8: partB n=(\d+) halo_us=(\d+) adv_us=(\d+) "
	r"stmt_us=(\d+) lkup_us=(\d+)")
# fold step boundary; "." after 1007 on step 1, ":" on the rest.
RE_STEP = re.compile(r"PERF 1007[.:] (Phase \d+) step (\d+): ([^.]*)")
# step 1 states the corpus size actually loaded for this part.
RE_WORDS = re.compile(r"for words: (\d+), total_word_len: (\d+)")
# proving throughput, only printed once step 7 completes.
RE_SPEED = re.compile(r"mb_speed (\d+) MB/hr")
# highest RAM figure the fold reports, for headroom on a 512 GB box.
RE_RAM = re.compile(r"(?:Total )?RAM: (\d+) GB")
# run start stamp, from the resolved log's directory name.
RE_START = re.compile(r"_(\d{8})_(\d{6})")

# the fold steps in order, with the short label each one prints.
STEP_NAMES = [
	(1, "generate batch/ind claims"),
	(2, "dispatch w into steps"),
	(3, "generate cmF"),
	(4, "generate batch prf"),
	(5, "prep for proving steps"),
	(6, "build nova"),
	(7, "PROVE STEPS"),
	(8, "verify (skipped: b_fold_only)"),
]


def hm(sec):
	"""Seconds as 'Hh MMm'."""
	sec = int(max(sec, 0))
	return "%dh %02dm" % (sec // 3600, (sec % 3600) // 60)


def com(n):
	"""Integer with thousands separators, or '-' for None."""
	return "-" if n is None else "{:,}".format(n)


def elapsed_of(target):
	"""Run elapsed seconds from the log dir name, else file ctime."""
	m = RE_START.search(os.path.dirname(target))
	if m:
		try:
			t = time.mktime(time.strptime(m.group(1) + m.group(2),
				"%Y%m%d%H%M%S"))
			return time.time() - t, "dir name"
		except ValueError:
			pass
	return time.time() - os.path.getctime(target), "file ctime"


def ladder_blocks(lines):
	"""All preprocess blocks as (n_circs, {idx: (cols, rows)},
	after_driver), plus PERF 1002 lines not yet closed by a block."""
	blocks = []
	pending = {}
	after = False
	for ln in lines:
		if RE_DRIVER.search(ln):
			after = True
			continue
		m = RE_CIRC.search(ln)
		if m:
			pending[int(m.group(1))] = (int(m.group(2)),
				int(m.group(3)))
			continue
		m = RE_BLOCK.search(ln)
		if m:
			blocks.append((int(m.group(1)), pending, after))
			pending = {}
	return blocks, pending


def prod_ladder(blocks):
	"""The production fold's ladder: the last block holding more than
	one circuit.  A circs: 1 block is a side fold, not the prod one."""
	multi = [b for b in blocks if b[0] > 1]
	return multi[-1] if multi else None


def load_ref(path):
	"""Re-derive REF_LADDER from another run's log, or None."""
	with open(path, errors="replace") as fh:
		blocks, _ = ladder_blocks(fh.read().splitlines())
	blk = prod_ladder(blocks)
	return blk[1] if blk else None


def show_header(target, lines):
	"""Log identity, age, elapsed wall."""
	age = time.time() - os.path.getmtime(target)
	el, src = elapsed_of(target)
	print("log        : %s" % target)
	print("lines      : %d" % len(lines))
	print("started    : %s ago  (from %s)" % (hm(el), src))
	print("last write : %.0f s ago  -- %s"
		% (age, "ALIVE" if age < 180 else "QUIET"))
	return el, age


def show_ratchet(lines):
	"""qm_real_rows ratchet: did it fire, did it converge."""
	fires = [RE_RATCHET.search(l) for l in lines]
	fires = [m for m in fires if m]
	short = any(RE_SHORT.search(l) for l in lines)
	if short:
		print("ratchet    : DEAD -- still short after 3 re-walks. "
			"The fix did not converge; save this log.")
	elif fires:
		hops = " -> ".join([fires[0].group(2)]
			+ [m.group(3) for m in fires])
		print("ratchet    : FIRED %dx, qm_real_rows %s  [converged]"
			% (len(fires), hops))
	else:
		print("ratchet    : not fired (walk held the T305 seed of 2)")
	return short


def show_gate(lines):
	"""Ladder gate: rung count and P_max.subsigs vs production."""
	gate = None
	v5 = None
	for ln in lines:
		m = RE_GATE.search(ln)
		if m:
			gate = m
		m = RE_V5.search(ln)
		if m:
			v5 = m
	if v5:
		print("v5 walk    : %s rungs, hist=[%s], costs=[%s]"
			% (v5.group(1), v5.group(2), v5.group(3)))
	if not gate:
		print("gate       : PENDING -- tuner has not reported yet")
		return None
	rungs = int(gate.group(1))
	subsigs = int(gate.group(3))
	ok = rungs >= EXPECT_RUNGS and subsigs == PROD_SUBSIGS
	print("gate       : %s -- %d rungs (need %d), hist=[%s]"
		% ("PASS" if ok else "FAIL", rungs, EXPECT_RUNGS,
			gate.group(2)))
	print("             P_max.subsigs=%d (prod %d)%s"
		% (subsigs, PROD_SUBSIGS,
			"" if subsigs == PROD_SUBSIGS else "  <-- MISMATCH"))
	return ok


def show_ladder(lines, ref):
	"""Measured circ sizes against the neo full_dlp reference."""
	blocks, pending = ladder_blocks(lines)
	blk = prod_ladder(blocks)
	got = blk[1] if blk else {}
	n_want = blk[0] if blk else max(list(ref) + [EXPECT_RUNGS])
	if not blk and pending:
		print("ladder     : IN FLIGHT -- %d circ line(s) not yet "
			"closed by a 'circs: N' line" % len(pending))
		got = pending
	elif not blk:
		print("ladder     : PENDING -- no preprocess block yet")
	else:
		tag = "prod fold" if blk[2] else "PRE-DRIVER (tuner-internal)"
		print("ladder     : circs: %d  [%s]" % (blk[0], tag))
	if pending and blk:
		print("             (+%d circ line(s) in a newer, open block)"
			% len(pending))
	if not got and not ref:
		return
	print("  %-5s %-12s %-12s %-6s %-12s %-12s %-6s"
		% ("circ", "cols", "ref cols", "x", "rows", "ref rows", "x"))
	for i in sorted(set(list(got) + list(ref))):
		cols, rows = got.get(i, (None, None))
		rc, rr = ref.get(i, (None, None))
		xc = "%.2f" % (cols / rc) if cols and rc else "-"
		xr = "%.2f" % (rows / rr) if rows and rr else "-"
		print("  %-5d %-12s %-12s %-6s %-12s %-12s %-6s"
			% (i, com(cols), com(rc), xc, com(rows), com(rr), xr))
	miss = [i for i in range(1, n_want + 1) if i not in got]
	if miss:
		print("             waiting on circ %s"
			% ",".join(str(i) for i in miss))


def show_pass1(lines, el):
	"""Pass 1 rate in ms/chunk against the legacy and neo references."""
	pa = None
	pb = None
	# summed over every step 1 line: the probe counters are process
	# statics spanning all parts, so the denominator must be too.
	n_words = 0
	n_fields = 0
	for ln in lines:
		m = RE_PA.search(ln)
		if m:
			pa = [int(g) for g in m.groups()]
		m = RE_PB.search(ln)
		if m:
			pb = [int(g) for g in m.groups()]
		m = RE_WORDS.search(ln)
		if m:
			n_words += int(m.group(1))
			n_fields += int(m.group(2))
	if not pa and not pb:
		print("Pass 1     : not started (no 69120.7/.8 probe yet)")
		return
	total_ms = 0.0
	if pa:
		n, tries, halo, ok, fail = pa
		total_ms += (halo + ok + fail) / 1000.0 / max(n, 1)
		print("  partA n=%s tries=%s | halo %.1f  ok %.1f  fail %.1f "
			"ms/chunk" % (com(n), com(tries), halo / 1000.0 / n,
				ok / 1000.0 / n, fail / 1000.0 / n))
	if pb:
		n, halo, adv, stmt, lk = pb
		total_ms += (halo + adv + stmt + lk) / 1000.0 / max(n, 1)
		print("  partB n=%s | halo %.1f  adv %.4f  stmt %.1f  "
			"lkup %.1f ms/chunk" % (com(n), halo / 1000.0 / n,
				adv / 1000.0 / n, stmt / 1000.0 / n,
				lk / 1000.0 / n))
		if adv / 1000.0 / n > 1.0:
			print("             WARN: adv is not ~0 -- S5 advice "
				"reuse is NOT active on this arm")
	print("  TOTAL %.1f ms/chunk  = %.2fx legacy(%.1f), %.2fx "
		"neo-pre-S5(%.1f), %.2fx neo-post-S5(%.1f)"
		% (total_ms, total_ms / MS_LEGACY, MS_LEGACY,
			total_ms / MS_NEO_PRE_S5, MS_NEO_PRE_S5,
			total_ms / MS_NEO_POST_S5, MS_NEO_POST_S5))
	print("             (ms/chunk is CPU time summed over workers, "
		"NOT wall -- the same basis as the 3 references)")
	done = (pb or pa)[0]
	if not n_fields:
		print("  progress %s chunks (no step 1 line yet for a "
			"denominator)" % com(done))
		return
	est = n_fields // SEG_WORD_LEN
	pct = 100.0 * done / max(est, 1)
	line = "  progress %s / ~%s chunks (%.1f%%)" % (com(done),
		com(est), pct)
	if done and pct < 100.0:
		# elapsed spans the tuner too, so this rate is pessimistic.
		line += "  ETA <= %s" % hm(el / done * (est - done))
	print(line)
	print("             (denominator = summed total_word_len %s / %d "
		"over %s words)" % (com(n_fields), SEG_WORD_LEN, com(n_words)))
	if pct > 105.0:
		print("             WARN: over 100% -- a part is missing its "
			"step 1 line, so the denominator is short")


def show_steps(lines):
	"""Which fold steps have been entered, plus speed and peak RAM."""
	seen = {}
	for ln in lines:
		m = RE_STEP.search(ln)
		if m:
			seen.setdefault(int(m.group(2)), m.group(1))
	rams = [int(m.group(1)) for m in
		(RE_RAM.search(l) for l in lines) if m]
	speed = [m.group(1) for m in
		(RE_SPEED.search(l) for l in lines) if m]
	print("fold steps :")
	for idx, name in STEP_NAMES:
		mark = "DONE/ENTERED" if idx in seen else "-"
		print("  step %d %-32s %s" % (idx, name, mark))
	if rams:
		print("peak RAM   : %d GB (log-reported; true peak runs "
			"higher -- quote PAPER_DATA_PEAK_RSS_GIB)" % max(rams))
	if speed:
		print("throughput : mb_speed %s MB/hr" % speed[-1])
	return seen


def verdict(short, gate, steps, age):
	"""One-line call on whether to keep waiting."""
	print("-" * 68)
	if short:
		print("VERDICT    : DEAD -- ratchet exhausted. Send me the "
			"log; the ceiling needs more than 3 re-walks.")
	elif gate is False:
		print("VERDICT    : VOID -- the sample lost the top rung. "
			"Widen EXTRA_HARD in gen_small_full_dlp_list.py.")
	elif 7 in steps:
		print("VERDICT    : FOLD DONE -- score the ladder table and "
			"the Pass 1 rate above.")
	elif age > STALL_S:
		print("VERDICT    : SUSPECT -- no write for %s. Check the "
			"process and free -g." % hm(age))
	elif gate:
		print("VERDICT    : HEALTHY -- gate passed, run in flight. "
			"Let it run.")
	else:
		print("VERDICT    : EARLY -- still tuning, no gate yet.")


def main():
	"""Parse a small_full_dlp log and print every checkpoint."""
	argv = [a for a in sys.argv[1:]]
	ref = dict(REF_LADDER)
	if "--ref" in argv:
		i = argv.index("--ref")
		got = load_ref(argv[i + 1])
		if got:
			ref = got
			print("ref ladder : re-derived from %s" % argv[i + 1])
		del argv[i:i + 2]
	path = argv[0] if argv else DEFAULT_LOG
	if not os.path.exists(path):
		print("NO LOG: %s" % path)
		sys.exit(2)
	target = os.path.realpath(path)
	with open(target, errors="replace") as fh:
		lines = fh.read().splitlines()

	el, age = show_header(target, lines)
	print("-" * 68)
	short = show_ratchet(lines)
	gate = show_gate(lines)
	print("-" * 68)
	show_ladder(lines, ref)
	print("-" * 68)
	show_pass1(lines, el)
	print("-" * 68)
	steps = show_steps(lines)
	verdict(short, gate, steps, age)


if __name__ == "__main__":
	main()
