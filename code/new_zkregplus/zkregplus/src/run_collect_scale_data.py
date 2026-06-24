#!/usr/bin/env python3
"""Run collect_scale_data (§7.5 Q4 regex-set scalability) in RELEASE mode and
pack the per-round logs as a single best-ratio tgz for gen_scale.py.

collect_scale_data(base_share_pct, num_rounds) keeps the corpus FIXED (the
difficult gdb file) and sweeps the rule set: round r uses pct = r*BASE_SHARE_PCT
percent of the rules (modulo-100 stratified, strict nested supersets). It
REBUILDS the DB from each subset into the isolated data/cache/scale_data cache
and runs folding-only. Each round is bracketed on stdout with
    ==== SCALE ROUND BEGIN pct=<P> ... ====   ...   ==== SCALE ROUND END pct=<P> ====
We capture the whole stdout, then SPLIT it on those markers into per-round
/tmp/bora/scale/log_<pct>.txt files (COST GRAND TOTAL is stdout-only, so the
per-job log files are not enough).

Output bundle (ALWAYS written, even on crash/panic/non-zero exit, so a partial
run is still analyzable):
    /tmp/bora/scale_data.tgz
      -> log_<pct>.txt.tgz  (one per completed round, gzip level 9)
           -> log_<pct>.txt
This is exactly the structure gen_scale.py expects (just point its BUNDLE at
/tmp/bora/scale_data.tgz).

Env:  ZKR_VM_MAX_MAP_COUNT  target vm.max_map_count (default 1G; 0 skips).
"""
import os, sys, re, subprocess, time, datetime, tarfile, io, platform

# ----------------------------------------------------------------------------
# One knob: the sweep percentages -- ASCENDING, DISTINCT, each in [1,100].
# Each round folds the first pct% of a FIXED pseudo-random permutation of the
# rule set, so rounds are nested supersets. 100 takes ALL rules.
# ----------------------------------------------------------------------------
VEC_PERC = [5, 10]

VMA_TARGET = int(os.environ.get("ZKR_VM_MAX_MAP_COUNT", "1073741824"))  # 0=skip

HERE = os.path.dirname(os.path.abspath(__file__))          # zkregplus/src
REPO = os.path.abspath(os.path.join(HERE, "..", ".."))     # new_zkregplus
SCRATCH = "/tmp/bora/scale"                                 # per-round logs
BUNDLE = "/tmp/bora/scale_data.tgz"                         # final artifact

BEGIN_RE = re.compile(r"==== SCALE ROUND BEGIN pct=(\d+)\b")
END_RE = re.compile(r"==== SCALE ROUND END pct=(\d+)")
# Per-round forward-queue audit. TEMP: the Rust b_show_queue_saturated print is
# UNGATED, so it emits StepFwdPrf usage for EVERY fold step -- we report the max
# and flag <85% as over-provisioned. FOLD_MARK brackets the fold (logged right
# before folding) so we only consider fold-time usage.
SAT_RE = re.compile(r"StepFwdPrf usage:\s*([\d.]+) b_igc: false")   # CP fwd queue
SDE_RE = re.compile(r"SDE basis_acc_states usage:\s*([\d.]+) b_igc: false")  # SDE acc-states
FOLD_MARK = "folding with converged caps"

# ----------------------------------------------------------------------------
# Concat-corpus: prepend the foldpot 0-word (deterministic seed-0 pad, exactly
# one max_word segment) to the real gdb corpus so the FOLD actually exercises
# the circuit it is sized for -- the validity certificate for the scalability
# figure. Fully isolated in /tmp/bora/scale: we write BOTH the concat word and
# our OWN corpus list file there; collect_scale_data reads scan_files =
# "/tmp/bora/scale/binexec_3.dat", so NO existing sample/config is touched and
# full_clam()/full_data3() are unaffected. The gdb sample is read-only. The pad
# stream mirrors utils/src/data.rs gen_pad_nibbles (splitmix64,
# PAD_SEED=0xCAFEF00DDEADBEEF) -- VERIFIED bit-identical to the Rust dump; and
# read_nibbles (byte->hi,lo) is its exact inverse, so the file reads back as the
# bitwise 0-word.
# ----------------------------------------------------------------------------
MAX_WORD  = 512 * 8            # == zkp_driver.rs collect_scale_data: max_word = 512*8
REAL_GDB  = os.path.join(REPO, "data/samples/binexec_merged128k/gdb")  # read-only
CONCAT    = os.path.join(SCRATCH, "gdb_with_zeroword.bin")   # /tmp/bora/scale/...
SCAN_LIST = os.path.join(SCRATCH, "binexec_3.dat")           # our own corpus list

_MASK = (1 << 64) - 1
def _block_r(block):
    s = ((0xCAFEF00DDEADBEEF ^ block) + 0x9E3779B97F4A7C15) & _MASK
    s = ((s ^ (s >> 30)) * 0xBF58476D1CE4E5B9) & _MASK
    s = ((s ^ (s >> 27)) * 0x94D049BB133111EB) & _MASK
    return (s ^ (s >> 31)) & _MASK
def _gen_pad_nibbles(start, length):
    out, idx = [], start
    while len(out) < length:
        b, inner = idx // 16, idx % 16
        r = _block_r(b)
        for k in range(inner, 16):
            if len(out) >= length: break
            out.append((r >> (k * 4)) & 0xf)
        idx = (b + 1) * 16
    return out
def gen_pad_bytes(length):     # byte = (nib[2i]<<4)|nib[2i+1] == read_nibbles inverse
    nb = _gen_pad_nibbles(0, length * 2)
    return bytes(((nb[2*i] << 4) | nb[2*i+1]) for i in range(length))

def build_concat_corpus():
    """0-word (seed-0 pad, one segment) ++ real gdb, plus our own corpus list
    file -- both written to /tmp/bora/scale. No existing sample/config touched."""
    os.makedirs(SCRATCH, exist_ok=True)
    pad = gen_pad_bytes(MAX_WORD * 31)            # 126976 B == one max_word segment
    with open(REAL_GDB, "rb") as f: gdb = f.read()
    with open(CONCAT, "wb") as f: f.write(pad + gdb)
    with open(SCAN_LIST, "w") as f: f.write(CONCAT + "\n")   # absolute -> Rust guard handles it
    print("[run_scale] concat corpus: 0-word %d B + gdb %d B -> %s (list %s)"
          % (len(pad), len(gdb), CONCAT, SCAN_LIST))


def ensure_vma(target):
    """Best-effort raise vm.max_map_count (the VMA ceiling) via sudo sysctl.
    The fold makes many small mimalloc mappings; the default 1048576 can be
    exhausted and SIGABRT on a tiny alloc while RAM is free. Non-fatal."""
    if target <= 0:
        return
    path = "/proc/sys/vm/max_map_count"
    try:
        cur = int(open(path).read().strip())
    except Exception as e:
        print("[run_scale] vm.max_map_count: cannot read (%s); skip" % e)
        return
    if cur >= target:
        print("[run_scale] vm.max_map_count=%d already >= %d" % (cur, target))
        return
    print("[run_scale] vm.max_map_count=%d < %d; raising via sudo sysctl"
          % (cur, target))
    rc = subprocess.run(["sudo", "sysctl", "-w",
                         "vm.max_map_count=%d" % target]).returncode
    if rc != 0:
        print("[run_scale] WARN: could not raise vm.max_map_count (sudo?). "
              "Run manually: sudo sysctl -w vm.max_map_count=%d" % target)


def split_and_pack(log_path):
    """Split the captured stdout on the SCALE ROUND markers and pack each
    completed round into /tmp/bora/scale/log_<pct>.txt(.tgz), then bundle all
    inner tgzs into /tmp/bora/scale_data.tgz. Best-ratio gzip (level 9).
    Tolerant: a round with a BEGIN but no END (crash mid-round) is still
    written, capturing up to the next BEGIN / EOF."""
    os.makedirs(SCRATCH, exist_ok=True)
    rounds, cur_pct, buf = [], None, []
    for line in open(log_path, errors="replace"):
        mb = BEGIN_RE.search(line)
        if mb:
            if cur_pct is not None:
                rounds.append((cur_pct, buf))
            cur_pct, buf = int(mb.group(1)), [line]
            continue
        if cur_pct is None:
            continue
        buf.append(line)
        if END_RE.search(line):
            rounds.append((cur_pct, buf))
            cur_pct, buf = None, []
    if cur_pct is not None:                    # trailing (un-ENDed) round
        rounds.append((cur_pct, buf))

    inner = []
    for pct, lines in rounds:
        txt = os.path.join(SCRATCH, "log_%d.txt" % pct)
        with open(txt, "w") as f:
            f.writelines(lines)
        tgz = os.path.join(SCRATCH, "log_%d.txt.tgz" % pct)
        with tarfile.open(tgz, "w:gz", compresslevel=9) as t:
            t.add(txt, arcname=os.path.basename(txt))
        inner.append(tgz)
        print("[run_scale] round pct=%d: %d lines -> %s"
              % (pct, len(lines), os.path.basename(tgz)))
        # Saturation verdicts (FOLD phase only): CP (fwd queue) + SDE (acc states).
        in_fold, sat, sde = False, [], []
        for ln in lines:
            if FOLD_MARK in ln:
                in_fold = True
            elif in_fold:
                m = SAT_RE.search(ln)
                if m: sat.append(float(m.group(1)))
                m = SDE_RE.search(ln)
                if m: sde.append(float(m.group(1)))
        for label, vals in (("CP  fwd-queue ", sat), ("SDE acc-states", sde)):
            if vals:
                mx, mn = max(vals), min(vals)
                tag = "tight OK" if mx >= 0.85 else "OVER-PROVISIONED (<85%)"
                print("[run_scale] round pct=%d: %s usage over %d fold steps "
                      "-- max %.4f min %.4f -- %s"
                      % (pct, label, len(vals), mx, mn, tag))
            else:
                print("[run_scale] round pct=%d: %s -- no usage lines "
                      "(b_show_queue_saturated off?)" % (pct, label))

    os.makedirs(os.path.dirname(BUNDLE), exist_ok=True)
    with tarfile.open(BUNDLE, "w:gz", compresslevel=9) as t:
        for tgz in inner:
            t.add(tgz, arcname=os.path.basename(tgz))
    print("[run_scale] packed %d round(s) -> %s" % (len(inner), BUNDLE))


def main():
    os.makedirs(SCRATCH, exist_ok=True)
    ts = datetime.datetime.now().strftime("%Y%m%d_%H%M%S")
    log = os.path.join(SCRATCH, "run_%s.log" % ts)

    env = dict(os.environ)
    env.setdefault("RUSTFLAGS", "-C link-args=-fuse-ld=lld -Awarnings")
    env.setdefault("ZKR_DC_THREADS", "8")   # determine_config probe threads
    env["ZKR_SCALE_PERCS"] = ",".join(str(p) for p in VEC_PERC)

    time_prefix = ["/usr/bin/time", "-v"] if os.path.exists("/usr/bin/time") \
        else []
    cmd = time_prefix + ["cargo", "test", "-p", "zkregplus", "--release", "--",
        "zkp_driver::tests_zkp_driver::test_collect_scale_data",
        "--exact", "--nocapture"]

    print("[run_scale] REPO   =", REPO)
    print("[run_scale] sweep  = percs %s%% of ruleset (nested supersets)"
          % VEC_PERC)
    print("[run_scale] LOG    =", log)
    print("[run_scale] cmd    =", " ".join(cmd))
    print("[run_scale] bundle =", BUNDLE, "(packed even on crash)")

    build_concat_corpus()
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
        # Always pack whatever rounds completed.
        try:
            split_and_pack(log)
        except Exception as e:
            print("[run_scale] WARN: pack failed: %s" % e)
        print("[run_scale] done (exit=%s, wall=%.0fs)" % (code, wall))
    sys.exit(0 if code == 0 else code)


if __name__ == "__main__":
    main()
