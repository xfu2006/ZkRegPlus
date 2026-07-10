#!/usr/bin/env python3
"""Run collect_scale_data_dlp (§7.5 Q4 regex-set scalability, DLP twin) in
RELEASE mode and pack the per-round logs as a single tgz for gen_scale_dlp.py.

DLP twin of run_collect_scale_data.py. collect_scale_data_dlp(counts) keeps the
corpus FIXED (one short difficult email -- donohoe-t/sent/6 by default; override
with ZKR_SCALE_WORD) and sweeps the rule set: each round folds the first `count`
rules of a FIXED pseudo-random permutation of the 9,860 sweepable MS-DLP rules
(strict nested supersets; the Win.Alphabet.SAMPLE-1 alphabet sig is always
pinned). The sweep counts are owned by the Rust test_collect_scale_dlp -- NOT set
here. It REBUILDS the DB from each subset into the isolated scale_data_dlp cache,
runs the AGGRESSIVE tuner, and folds with config-gated catchable-CapErr bump
retries. Each round is bracketed on stdout with
    ==== SCALE ROUND BEGIN count=<N> ... ====  ...  ==== SCALE ROUND END count=<N> ====

UNLIKE the ClamAV runner there is NO 0-word pad concat: the DLP corpus is the
email written straight into the scan list. collect_scale_data_dlp adds/handles
the foldpot 0-word internally (the bump-retry loop sizes the 0-word advice), and
it generates the per-subset main_fanout.dat itself. So the ONLY thing we set up
here is /tmp/bora/scale_dlp/binexec_3.dat -> the absolute email path.

Output bundle (ALWAYS written, even on crash/panic/non-zero exit):
    /tmp/bora/scale_data_dlp_<word>.tgz
      -> log_<count>.txt.tgz  (one per completed round, gzip level 9)
           -> log_<count>.txt
gen_scale_dlp.py points its BUNDLE at this tgz.

Env:  ZKR_SCALE_WORD       override corpus email (default donohoe-t/sent/6).
      ZKR_VM_MAX_MAP_COUNT  target vm.max_map_count (default 1G; 0 skips).
"""
import os, sys, re, subprocess, time, datetime, tarfile, platform

# ----------------------------------------------------------------------------
VMA_TARGET = int(os.environ.get("ZKR_VM_MAX_MAP_COUNT", "1073741824"))  # 0=skip

HERE = os.path.dirname(os.path.abspath(__file__))          # zkregplus/src
REPO = os.path.abspath(os.path.join(HERE, "..", ".."))     # bora
SCRATCH = "/tmp/bora/scale_dlp"                             # MUST match the Rust
# Corpus: one short difficult NON-MATCHING email that saturates the SDE forward
# queue (~91% at 10%). Default = donohoe-t/sent/6 (805 B, accept+pass, in
# full_dlp's folded corpus). Override with ZKR_SCALE_WORD=/abs/path/to/email.
WORD_SRC = os.environ.get(
    "ZKR_SCALE_WORD",
    os.path.join(REPO, "data/samples/email/src/maildir/donohoe-t/sent/6."))
WORD_LABEL = os.path.basename(WORD_SRC.rstrip(".")) or "email"
BUNDLE = "/tmp/bora/scale_data_dlp_%s.tgz" % WORD_LABEL
SCAN_LIST = os.path.join(SCRATCH, "binexec_3.dat")         # the Rust reads this

BEGIN_RE = re.compile(r"==== SCALE ROUND BEGIN count=(\d+)\b")
END_RE = re.compile(r"==== SCALE ROUND END count=(\d+)")
# Per-round outputs we surface for progress (the actual figure parse is in
# gen_scale_dlp.py). The fold can emit MULTIPLE COST blocks per round on
# bump-retries -- the LAST one is the converged circuit, so we take last.
COST_RE = re.compile(r"==== COST circ0 \(R1CS constraints\) ====\s+total = (\d+)")
SAT_RE = re.compile(
    r"FWD-QUEUE SATURATION cs=([\d.]+)% \((\d+)/(\d+)\) "
    r"igc=([\d.]+)% \((\d+)/(\d+)\)")
LADDER_RE = re.compile(r"count=\d+: ladder \d+ rungs hist=\[([\d,\s]*)\]")

# ----------------------------------------------------------------------------
def build_corpus_list():
    """Write our own scan list -> the absolute email path. No pad concat: the
    Rust handles the foldpot 0-word internally. Fully isolated in
    /tmp/bora/scale_dlp; no existing sample/config touched, full_dlp unaffected."""
    if not os.path.exists(WORD_SRC):
        print("[run_scale_dlp] FATAL: corpus email not found: %s" % WORD_SRC)
        sys.exit(2)
    os.makedirs(SCRATCH, exist_ok=True)
    with open(SCAN_LIST, "w") as f:
        f.write(WORD_SRC + "\n")
    sz = os.path.getsize(WORD_SRC)
    print("[run_scale_dlp] corpus: '%s' %d B -> %s" % (WORD_LABEL, sz, SCAN_LIST))


def ensure_vma(target):
    """Best-effort raise vm.max_map_count (the VMA ceiling) via sudo sysctl.
    The dense-SDE fold makes many small mimalloc mappings; the default 1048576
    can be exhausted and SIGABRT on a tiny alloc while RAM is free. Non-fatal."""
    if target <= 0:
        return
    path = "/proc/sys/vm/max_map_count"
    try:
        cur = int(open(path).read().strip())
    except Exception as e:
        print("[run_scale_dlp] vm.max_map_count: cannot read (%s); skip" % e)
        return
    if cur >= target:
        print("[run_scale_dlp] vm.max_map_count=%d already >= %d" % (cur, target))
        return
    print("[run_scale_dlp] vm.max_map_count=%d < %d; raising via sudo sysctl"
          % (cur, target))
    rc = subprocess.run(["sudo", "sysctl", "-w",
                         "vm.max_map_count=%d" % target]).returncode
    if rc != 0:
        print("[run_scale_dlp] WARN: could not raise vm.max_map_count (sudo?). "
              "Run manually: sudo sysctl -w vm.max_map_count=%d" % target)


def split_and_pack(log_path):
    """Split the captured stdout on the SCALE ROUND markers and pack each
    completed round into /tmp/bora/scale_dlp/log_<count>.txt(.tgz), then bundle
    all inner tgzs into BUNDLE. Best-ratio gzip (level 9). Tolerant: a round
    with a BEGIN but no END (crash mid-round) is still written."""
    os.makedirs(SCRATCH, exist_ok=True)
    rounds, cur_cnt, buf = [], None, []
    for line in open(log_path, errors="replace"):
        mb = BEGIN_RE.search(line)
        if mb:
            if cur_cnt is not None:
                rounds.append((cur_cnt, buf))
            cur_cnt, buf = int(mb.group(1)), [line]
            continue
        if cur_cnt is None:
            continue
        buf.append(line)
        if END_RE.search(line):
            rounds.append((cur_cnt, buf))
            cur_cnt, buf = None, []
    if cur_cnt is not None:                    # trailing (un-ENDed) round
        rounds.append((cur_cnt, buf))

    inner = []
    for cnt, lines in rounds:
        txt = os.path.join(SCRATCH, "log_%d.txt" % cnt)
        with open(txt, "w") as f:
            f.writelines(lines)
        tgz = os.path.join(SCRATCH, "log_%d.txt.tgz" % cnt)
        with tarfile.open(tgz, "w:gz", compresslevel=9) as t:
            t.add(txt, arcname=os.path.basename(txt))
        inner.append(tgz)
        # Progress verdict: converged circuit COST (LAST block; retries emit
        # several), final SDE forward-queue saturation, and the ladder.
        cost = None
        for ln in lines:
            m = COST_RE.search(ln)
            if m: cost = int(m.group(1))       # last wins = converged
        sat = None
        for ln in lines:
            m = SAT_RE.search(ln)
            if m: sat = m                       # last wins
        ladder = None
        for ln in lines:
            m = LADDER_RE.search(ln)
            if m: ladder = m.group(1).strip()
        ended = any(END_RE.search(ln) for ln in lines)
        msg = "[run_scale_dlp] round count=%d: %d lines%s" % (
            cnt, len(lines), "" if ended else " (NO END -- partial)")
        if cost is not None:
            msg += " | COST=%d" % cost
        if sat:
            msg += " | SDE sat cs=%s%% (%s/%s) igc=%s%% (%s/%s)" % sat.groups()
        if ladder is not None:
            msg += " | hist=[%s]" % ladder
        print(msg)

    os.makedirs(os.path.dirname(BUNDLE), exist_ok=True)
    with tarfile.open(BUNDLE, "w:gz", compresslevel=9) as t:
        for tgz in inner:
            t.add(tgz, arcname=os.path.basename(tgz))
    print("[run_scale_dlp] packed %d round(s) -> %s" % (len(inner), BUNDLE))


def main():
    os.makedirs(SCRATCH, exist_ok=True)
    ts = datetime.datetime.now().strftime("%Y%m%d_%H%M%S")
    log = os.path.join(SCRATCH, "run_%s.log" % ts)

    env = dict(os.environ)
    env.setdefault("RUSTFLAGS", "-C link-args=-fuse-ld=lld -Awarnings")
    env.setdefault("ZKR_DC_THREADS", "8")   # determine_config probe threads
    env["ZKR_SCALE_CORPUS"] = WORD_LABEL    # corpus identity for the markers

    time_prefix = ["/usr/bin/time", "-v"] if os.path.exists("/usr/bin/time") \
        else []
    cmd = time_prefix + ["cargo", "test", "-p", "zkregplus", "--release", "--",
        "zkp_driver::tests_zkp_driver::test_collect_scale_dlp",
        "--exact", "--nocapture"]

    print("[run_scale_dlp] REPO   =", REPO)
    print("[run_scale_dlp] sweep  = counts owned by Rust test_collect_scale_dlp "
          "(1, 10%..100% of 9,860; nested supersets); rounds parsed from "
          "count= markers in the log")
    print("[run_scale_dlp] LOG    =", log)
    print("[run_scale_dlp] cmd    =", " ".join(cmd))
    print("[run_scale_dlp] bundle =", BUNDLE, "(packed even on crash)")

    build_corpus_list()
    ensure_vma(VMA_TARGET)
    t0 = time.time()
    code = -1
    try:
        with open(log, "w") as lf:
            lf.write("# %s host=%s cpu=%s\n# cmd=%s\n\n" % (
                datetime.datetime.now(), platform.node(), os.cpu_count(),
                " ".join(cmd)))
            lf.flush()
            p = subprocess.Popen(cmd, cwd=REPO, env=env,
                                 stdout=subprocess.PIPE,
                                 stderr=subprocess.STDOUT, text=True)
            for line in p.stdout:
                sys.stdout.write(line); lf.write(line); lf.flush()
            p.wait()
            code = p.returncode
    finally:
        wall = time.time() - t0
        try:
            split_and_pack(log)
        except Exception as e:
            print("[run_scale_dlp] WARN: pack failed: %s" % e)
        print("[run_scale_dlp] done (exit=%s, wall=%.0fs)" % (code, wall))
    sys.exit(0 if code == 0 else code)


if __name__ == "__main__":
    main()
