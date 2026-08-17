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
# below this many chunks the cumulative ms/chunk average is still
# climbing steeply (461 at n=10.7k -> 589 at n=66.9k on full_dlp), so
# comparing it to the references above is meaningless.
MS_TRUST_N = 10000
# banked (epoch, chunk count) samples, written beside the log so a
# second invocation can report a true Pass 1 wall rate.
STATE_NAME = "small_dlp_progress.state"
# hours to ADD to this box's clock to get the owner's laptop clock, so
# every "check again at" is quotable without mental arithmetic.  The
# server runs UTC; the laptop measured UTC-4 on 2026-08-17.  Override
# with MY_OFFSET_H=<hours> when travelling or on a different box.
MY_OFFSET_H = float(os.environ.get("MY_OFFSET_H", "-4"))
# free memory below this many GB while the fold runs means the
# single-process 8-job topology is heading for the Pass 3 OOM that
# M101 warns about; the fix is numa_num=2, not a capacity bump.
MEM_FLOOR_GB = 50
# legacy full_dlp rung mix in percent, low rung first (M101 doc v7.6).
# neo's thesis is that it routes the bulk of chunks one rung LOWER, so
# this is the number the measured mix has to beat.
LEG_MIX = [24.65, 70.44, 4.66, 0.24]
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
# one line per routed chunk (aggressive only, needs LOG3).  pci is the
# FINAL rung after bumps and is 0-based, unlike PERF 1002's circ index.
RE_SEL = re.compile(
	r"\[job (\d+)\].*per-chunk circ sel\..*word_id: (\d+), "
	r"subseg_id: (\d+), fname: .*?, pci: (\d+)")
# which job emitted a line, for counting how many are actually running.
RE_JOB = re.compile(r"\[job (\d+)\]")

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


def clocks(epoch):
	"""An epoch as 'HH:MM srv / HH:MM you', both clocks side by side."""
	srv = time.strftime("%H:%M", time.localtime(epoch))
	mine = time.strftime("%a %H:%M",
		time.localtime(epoch + MY_OFFSET_H * 3600.0))
	return "%s srv / %s you" % (srv, mine)


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


def show_mem(steps):
	"""RAM headroom, with the Pass 3 OOM floor once the fold starts."""
	total, avail = mem_gb()
	if not total:
		return
	line = "memory     : %d / %d GB available" % (avail, total)
	if 6 in steps and avail < MEM_FLOOR_GB:
		line += ("  <-- UNDER %d GB FLOOR. This is the single-process "
			"8-job topology M101 says OOMs in Pass 3; rerun with "
			"numa_num=2." % MEM_FLOOR_GB)
	print(line)


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
		return None, []
	rungs = int(gate.group(1))
	subsigs = int(gate.group(3))
	ok = rungs >= EXPECT_RUNGS and subsigs == PROD_SUBSIGS
	print("gate       : %s -- %d rungs (need %d), hist=[%s]"
		% ("PASS" if ok else "FAIL", rungs, EXPECT_RUNGS,
			gate.group(2)))
	print("             P_max.subsigs=%d (prod %d)%s"
		% (subsigs, PROD_SUBSIGS,
			"" if subsigs == PROD_SUBSIGS else "  <-- MISMATCH"))
	hist = [int(x) for x in gate.group(2).replace(" ", "").split(",")
		if x]
	return ok, hist


def show_ladder(lines, ref, hist, cnt):
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
		return
	show_fidelity(got, ref, hist, cnt)


def show_fidelity(got, ref, hist, cnt):
	"""Occupancy-weighted cols, this run vs the reference ladder.  Per-
	rung ratios mislead: one rung carries most chunks, so the weighting
	is what says whether total fold cost is comparable.  Weights come
	from the MEASURED routing when the log has it -- the tuner's
	prediction is a different distribution and gives a different
	answer (1.13x predicted vs 1.35x measured on the 08-17 run)."""
	idx = sorted(set(got) & set(ref))
	src = "measured routing"
	hist = list(hist)
	if sum(cnt) > 0:
		hist = list(cnt)
	else:
		src = "tuner prediction"
	if not idx or len(hist) < len(idx):
		return
	w = [hist[i - 1] for i in idx]
	tot = float(sum(w))
	if tot <= 0:
		return
	a = sum(got[i][0] * n / tot for i, n in zip(idx, w))
	b = sum(ref[i][0] * n / tot for i, n in zip(idx, w))
	if b <= 0:
		return
	print("  weighted   %s vs %s cols  = %.3fx  [%s: %s]"
		% (com(int(a)), com(int(b)), a / b, src,
			",".join("%.3f" % (n / tot) for n in w)))
	print("             %s: an average chunk's circuit is %.0f%% %s "
		"than production's"
		% ("PESSIMISTIC" if a > b else "OPTIMISTIC",
			abs(100.0 * (a / b - 1.0)),
			"bigger" if a > b else "smaller"))


def routed_mix(lines):
	"""(counts per pci, n_jobs) over COMPLETED words only.  A word still
	being emitted would skew the shares, so each job's highest word_id
	is excluded; (job, word, subseg) is deduped so an appended re-run
	cannot double-count."""
	seen = set()
	hi = {}
	rows = []
	jobs = set()
	for ln in lines:
		m = RE_JOB.search(ln)
		if m:
			jobs.add(int(m.group(1)))
		m = RE_SEL.search(ln)
		if not m:
			continue
		j, w, b, p = (int(m.group(i)) for i in (1, 2, 3, 4))
		if (j, w, b) in seen:
			continue
		seen.add((j, w, b))
		hi[j] = max(hi.get(j, 0), w)
		rows.append((j, w, p))
	cnt = [0, 0, 0, 0]
	for j, w, p in rows:
		if w < hi[j] and p < 4:
			cnt[p] += 1
	return cnt, len(jobs)


def show_routing(hist, cnt):
	"""Measured rung mix vs the tuner's prediction and vs legacy.  This
	is the neo thesis: route the bulk of chunks one rung LOWER."""
	tot = sum(cnt)
	if tot == 0:
		print("routing    : no completed words yet (needs LOG3 "
			"'per-chunk circ sel' lines)")
		return
	mix = [100.0 * c / tot for c in cnt]
	print("routing    : %s chunks routed over completed words" % com(tot))
	print("  %-9s %-9s %-9s %-9s %s"
		% ("rung", "measured", "tuner", "legacy", "n"))
	for i in range(4):
		pred = (100.0 * hist[i] / sum(hist)
			if len(hist) == 4 and sum(hist) else None)
		print("  %-9d %-9s %-9s %-9s %s"
			% (i + 1, "%.2f%%" % mix[i],
				"-" if pred is None else "%.2f%%" % pred,
				"%.2f%%" % LEG_MIX[i], com(cnt[i])))
	# Mean rung, not the rungs-1+2 share: both arms put ~95% in 1+2, so
	# only the mean separates "mostly rung 1" from "mostly rung 2".
	mean = sum((i + 1) * mix[i] for i in range(4)) / 100.0
	lmean = sum((i + 1) * LEG_MIX[i] for i in range(4)) / 100.0
	print("             mean rung %.2f here vs %.2f legacy -- %s"
		% (mean, lmean,
			"LOWER-SKEWED (the neo win)" if mean < lmean
			else "NOT lower-skewed; check before trusting the fold"))
	print("             for the ms-cost GREEN/RED call run: "
		"bash scripts/debug/circ_sel_ratio.sh")


def next_check(gate, got, pa, done, steps, el):
	"""(seconds until the next useful look, why).  Keyed to the phase,
	so a quiet stretch is not checked every ten minutes."""
	if 7 in steps:
		return 0, "run is done -- score it"
	if 6 in steps:
		return 90 * 60, "fold running; watch RAM and wait for step 7"
	if pa:
		if done < MS_TRUST_N:
			return 30 * 60, ("Pass 1 early; ms/chunk not comparable "
				"until n>%s" % com(MS_TRUST_N))
		return 45 * 60, "Pass 1 steady; next milestone is step 6"
	if got:
		return 20 * 60, "ladder built; Pass 1 should start shortly"
	if gate:
		return 20 * 60, "gate passed; waiting on the circuit build"
	return 30 * 60, "still tuning; the gate is the next signal"


def show_next(gate, got, pa, done, steps, el):
	"""When to look again, in both clocks."""
	sec, why = next_check(gate, got, pa, done, steps, el)
	if sec <= 0:
		print("next check : none -- %s" % why)
		return
	print("next check : in %s, at %s"
		% (hm(sec), clocks(time.time() + sec)))
	print("             (%s)" % why)


def show_rate(target, done, est):
	"""True wall rate from a chunk count banked by an earlier run of
	this script.  Pass 1 starts hours into the run, so the elapsed-based
	ETA above overstates; this one uses only Pass 1's own interval."""
	path = os.path.join(os.path.dirname(target), STATE_NAME)
	now = time.time()
	old = []
	try:
		with open(path) as fh:
			for ln in fh:
				bits = ln.split()
				if len(bits) == 2:
					old.append((float(bits[0]), int(bits[1])))
	except (IOError, OSError, ValueError):
		pass
	# a count that went backwards means the run restarted; drop those.
	old = [s for s in old if s[1] <= done and now - s[0] < 30 * 86400]
	try:
		with open(path, "a") as fh:
			fh.write("%d %d\n" % (now, done))
	except (IOError, OSError):
		print("             (could not bank a sample in %s)" % path)
	base = old[0] if old else None
	if not base or done <= base[1] or now - base[0] < 60:
		print("             rate: need a 2nd reading -- banked this "
			"one, run again in ~10 min for a true ETA")
		return
	dt = now - base[0]
	dn = done - base[1]
	cpm = dn * 60.0 / dt
	print("             rate: %.1f chunks/min over the last %s "
		"(%s chunks)" % (cpm, hm(dt), com(dn)))
	if done < est:
		print("             ETA : %s for this part, at that rate"
			% hm((est - done) / max(cpm, 1e-9) * 60.0))


def show_pass1(lines, el, target, n_jobs):
	"""Pass 1 rate in ms/chunk against the legacy and neo references."""
	pa = None
	pb = None
	# The probe counters are process statics spanning ALL jobs, so the
	# denominator must cover all jobs too.  One step 1 line per job, but
	# jobs stagger, so scale by how many have reported vs how many the
	# log shows -- otherwise progress reads ~8x too high early on.
	per_job = {}
	for ln in lines:
		m = RE_PA.search(ln)
		if m:
			pa = [int(g) for g in m.groups()]
		m = RE_PB.search(ln)
		if m:
			pb = [int(g) for g in m.groups()]
		m = RE_WORDS.search(ln)
		if m:
			j = RE_JOB.search(ln)
			per_job[j.group(1) if j else len(per_job)] = (
				int(m.group(1)), int(m.group(2)))
	n_words = sum(v[0] for v in per_job.values())
	n_fields = sum(v[1] for v in per_job.values())
	scale = 1.0
	if per_job and n_jobs > len(per_job):
		scale = float(n_jobs) / len(per_job)
	if not pa and not pb:
		print("Pass 1     : not started (no 69120.7/.8 probe yet)")
		return None, 0
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
	if done < MS_TRUST_N:
		print("             WARN: n=%s is too small to compare. The "
			"cumulative average DRIFTS UP with n" % com(done))
		print("             (full_dlp measured 461 ms/chunk at n=10.7k "
			"-> 589 at n=66.9k). Re-read past n=%s."
			% com(MS_TRUST_N))
	if not n_fields:
		print("  progress %s chunks (no step 1 line yet for a "
			"denominator)" % com(done))
		return pa, done
	est = int(n_fields * scale) // SEG_WORD_LEN
	pct = 100.0 * done / max(est, 1)
	line = "  progress %s / ~%s chunks (%.1f%%)" % (com(done),
		com(est), pct)
	if done and pct < 100.0:
		# elapsed spans the tuner too, so this rate is pessimistic.
		line += "  ETA <= %s" % hm(el / done * (est - done))
	print(line)
	show_rate(target, done, est)
	print("             (denominator = total_word_len %s / %d, from %d "
		"of %d jobs%s)" % (com(n_fields), SEG_WORD_LEN, len(per_job),
			n_jobs, "" if scale == 1.0 else " x%.2f extrapolated"
			% scale))
	if pct > 105.0:
		print("             WARN: over 100% -- a part is missing its "
			"step 1 line, so the denominator is short")
	return pa, done


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
	gate, hist = show_gate(lines)
	print("-" * 68)
	cnt, n_jobs = routed_mix(lines)
	show_ladder(lines, ref, hist, cnt)
	print("-" * 68)
	show_routing(hist, cnt)
	print("-" * 68)
	pa, done = show_pass1(lines, el, target, n_jobs)
	print("-" * 68)
	steps = show_steps(lines)
	show_mem(steps)
	blocks, pending = ladder_blocks(lines)
	blk = prod_ladder(blocks)
	show_next(gate, blk[1] if blk else pending, pa, done, steps, el)
	verdict(short, gate, steps, age)


if __name__ == "__main__":
	main()
