# -------------------------------------------
# Creator: BORA Author. Implemented with Claude Code; reviewed by BORA author.
# Date: 06/06/2026
# Purpose: build the real Zombie regex non-membership circuit for every policy in
#          regex_zombie/ and measure its cost (R1CS size, prove time, verify time,
#          proof size). Sequential. Sweeps a set of document lengths (STR_LENGTH).
#
#   Pipeline per (policy, str_len):
#     1. parse the baked policy regex (PAT.{0,N}KWS)|(KWS.{0,N}PAT) back into its
#        three parts -- PAT, KWS, proximity -- with extract_parts().
#     2. feed Zombie NATIVELY: stdin = "PAT & KWS", proximity pair "0 1"
#        (TestRegex F). The window is enforced by Zombie's procCheck/spread, not
#        by a baked .{0,N}; PROXY_DIST is the SIT's proximity.
#     3. rewrite STR_LENGTH / PROXY_DIST in the emitted .zok, drop it at
#        circ/zkmb/policy<str_len>.zok, and run circ_executable (Spartan NIZK):
#          circ_executable policy_<str_len> true prover_verifier
#        which prints constraints / prove ms / proof bytes / verify ms.
#
#   The witness is Zombie's all-zero default (RegexProverWitness::<N>::default()):
#   cost is fixed by the DFA x STR_LENGTH and is content-invariant, so an all-zero
#   (trivially non-matching) document yields the same numbers as any real one.
#
#   ENABLEMENT: the circ benchmark dispatcher (zk_test() in circ/src/zkmb.rs, which
#   main() already calls) only ships arms for a couple of sizes. circ also cannot be
#   built where it sits -- it is inside the BORA cargo workspace. So ensure_zombie_
#   built() follows download_zombie.py's verified recipe: it makes a persistent COPY
#   of circ OUTSIDE the workspace (BUILD_ROOT, in /tmp), adds the "policy_<N>" arms
#   to that copy's zkmb.rs, and builds circ_executable there with the committed
#   Cargo.lock (--locked) and system GMP/MPFR/MPC (CARGO_FEATURE_USE_SYSTEM_LIBS=1).
#   The arm patch is IDEMPOTENT (pristine zkmb.rs.orig + regenerate each run), so any
#   number of runs never compounds; the in-tree clone is left untouched. It aborts
#   loudly if the upstream source has drifted from the pinned commit.
#
#   The Zombie tree (zombie/) is a pinned, no-license local clone -- not
#   redistributed; all edits/artifacts here stay local.
# -------------------------------------------

import os
import re
import sys
import time
import json
import shutil
import subprocess
import statistics
from concurrent.futures import ThreadPoolExecutor, as_completed

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from common import gen_report_header, gen_machine_config, get_ms_dlp_dir  # noqa: E402

# --- configuration ---------------------------------------------------------
# RULESETS: each baked policy folder is measured as its OWN pass (no document
# axis -- circuits are built from regex, not corpora). main() reassigns FULL_DIR
# / LOG_FILE / PARTIAL per ruleset, writing run_zombie_<ruleset>.log. Edit the
# array to add rule sets.
RULESETS   = ["regex_zombie_international"]  # international-only re-measure (1k/2k/4k)
# RULESETS = ["regex_zombie", "regex_zombie_international"]  # full both-pass run
FULL_DIR   = "regex_zombie"                 # input : baked policy regexes (per-pass)
DOCS_DIR   = "docs"
LOG_FILE   = os.path.join(DOCS_DIR, "run_zombie.log")            # per-pass below
# resume/crash cache. The PRIMARY copy is a transient build artifact in /tmp, but a
# reboot wipes /tmp and would lose all progress, so we ALSO keep a DURABLE mirror
# under docs/. _append_partial() writes BOTH; _load_partial() reads /tmp first and
# falls back to the docs mirror when /tmp is gone/empty (e.g. after a reboot).
# Delete BOTH to force a clean re-measure of all sizes.
PARTIAL_DIR  = "/tmp/bora_zombie_run"
PARTIAL      = os.path.join(PARTIAL_DIR, "run_zombie.partial.jsonl")  # per-pass below
PARTIAL_DOCS = os.path.join(DOCS_DIR, "run_zombie.partial.jsonl")     # durable mirror

ZOMBIE     = "zombie"
REGEX_DIR  = os.path.join(ZOMBIE, "regex")         # TestRegex source (built via make)
TESTREGEX  = os.path.join(REGEX_DIR, "bin", "TestRegex")
CLONE_CIRC = os.path.join(ZOMBIE, "circ")          # pristine clone (copy source)

# circ cannot be built where it sits -- it is inside the BORA cargo workspace, and
# adding a local [workspace] re-resolves the lockfile to MSRV-incompatible crates
# (see download_zombie.py's note). Per that verified recipe we build a COPY of circ
# OUTSIDE the workspace, with the committed Cargo.lock (--locked) and system
# GMP/MPFR/MPC (CARGO_FEATURE_USE_SYSTEM_LIBS=1). The copy is persistent so the slow
# first build is reused; delete BUILD_ROOT to force a fresh copy + rebuild.
BUILD_ROOT = "/tmp/bora_zombie_circ"
CIRC_BUILD = os.path.join(BUILD_ROOT, "circ")
BUILD_RS      = os.path.join(CIRC_BUILD, "src", "zkmb.rs")
BUILD_RS_ORIG = BUILD_RS + ".orig"
ZKMB_DIR   = os.path.join(CIRC_BUILD, "zkmb")      # circ reads ./zkmb/<circuit>.zok
KEYS_DIR   = os.path.join(CIRC_BUILD, "keys")      # circ writes ./keys/<circuit>_*
CIRC_BIN   = os.path.join(CIRC_BUILD, "target", "release", "circ_executable")
SYSTEM_LIBS_ENV = {"CARGO_FEATURE_USE_SYSTEM_LIBS": "1"}

VEC_SIZE   = [1000, 2000, 4000]             # STR_LENGTH sweep (each > 2*PROXY_DIST)
CODEGEN_TIMEOUT = 300                        # s, TestRegex F (DFA build)
PROVE_TIMEOUT   = 7200                       # s, key-gen + prove + verify per run

# Parallel-build pipeline: keygen (the ~60s/circuit cost) is RAM-heavy, so we
# build several circuits CONCURRENTLY -- each in its OWN work dir (own ./zkmb +
# ./keys, shared abs-path binary) so the per-circuit 'policy2000' key files do
# not collide -- then TIME each built circuit one-by-one (clean timing, no build
# running). After a circuit is timed its work dir is deleted.
#
# Concurrency is NOT a fixed per-STR_LENGTH count anymore: run_pipeline forms each
# build batch from a RAM budget + a >=MIN_CPUS_PER_CIRC cap + a disk budget (see
# the scheduling section below), so big circuits self-limit and small ones pack
# the cores -- no JOBS_BY_STR_LEN table to tune.
PAR_ROOT = "/tmp/bora_zombie_par"          # per-circuit isolated work dirs (default)

# --- per-process RAM cap ---------------------------------------------------
# circ_executable key-gen is RAM-heavy and several run concurrently, so a single
# >240 GB keygen can choke the box. Each parallel job's address space is capped
# via prlimit(1) (RLIMIT_AS) at a per-circuit value (see _as_cap); the SERIAL
# timing phase and the serial fallback get the FULL headroom (_mem_cap_bytes(1)).
# When a job exceeds its cap, malloc fails -> keygen aborts by signal ->
# 'oom_or_killed' -> requeued at lower parallelism.
MEM_HEADROOM_FRAC = 0.9
_PRLIMIT = shutil.which("prlimit")


def _total_ram_bytes():
    try:
        with open("/proc/meminfo") as f:
            for ln in f:
                if ln.startswith("MemTotal:"):
                    return int(ln.split()[1]) * 1024
    except OSError:
        pass
    return None


def _mem_cap_bytes(jobs):
    """Address-space cap per process when `jobs` run concurrently, or None when the
    total RAM cannot be determined (-> no cap)."""
    total = _total_ram_bytes()
    if not total or jobs < 1:
        return None
    return int(total * MEM_HEADROOM_FRAC / jobs)


def _limited(cmd, mem_bytes):
    """Prefix a command with `prlimit --as=<bytes>` so the child cannot exceed
    mem_bytes of virtual memory. No-op if mem_bytes is None or prlimit is absent."""
    if mem_bytes and _PRLIMIT:
        return [_PRLIMIT, "--as=%d" % int(mem_bytes), "--"] + cmd
    return cmd

# --- memory / cpu / disk-aware scheduling ----------------------------------
# A fixed per-STR_LENGTH job count is wrong both ways: too high OOMs on the few
# giant circuits (canada-drivers-license at 4000 ~ 2^21 constraints, ~hundreds of
# GB keygen RAM each), too low starves the thousands of small ones (CPU idle). So
# instead each BUILD batch is filled greedily under a RAM budget: per-circuit RAM
# is predicted (measured peak RSS from a prior run > slope*r1cs_cons > default),
# big circuits clump into tiny batches, small ones pack CPU-wide. The batch is
# also capped so every concurrent job keeps >= MIN_CPUS_PER_CIRC cores, and by a
# DISK budget so the batch's keys fit the scratch drive. Estimates need not be
# accurate: each job's prlimit AS cap = margin*est, so a low estimate trips the
# cap -> SIGABRT -> 'oom_or_killed', and a disk under-estimate -> ENOSPC ->
# 'disk_full'; both are then requeued at lower parallelism (see run_pipeline) and
# the measured RSS feeds the slope calibration.
RAM_BUDGET_FRAC          = 0.85        # batch summed est RAM stays under this
MIN_CPUS_PER_CIRC        = 4           # cap jobs so each has >= this many cores
EST_SLOPE_BYTES_PER_CONS = 200_000     # cold RAM est: bytes per r1cs constraint
EST_DEFAULT_FRAC         = 0.10        # unknown circuit reserves this frac of RAM
EST_AS_MARGIN            = 1.5         # per-job prlimit AS cap = margin * est RAM
DISK_BUDGET_FRAC         = 0.80        # batch summed est keys stay under free*this
DISK_SLOPE_BYTES_PER_CONS = 40_000     # cold disk est: key bytes per constraint
DISK_DEFAULT_FRAC        = 0.10        # unknown circuit reserves this frac of free
# Adaptive retry: a circuit whose failure is a RESOURCE class (too much
# concurrency) is NOT emitted -- it is requeued with its RAM reservation ratcheted
# up RETRY_BACKOFF x, which makes the scheduler run it at lower parallelism next
# round (down to serial at full headroom). Only ok / deterministic outcomes are
# emitted, so each regex ends with exactly one record. Deterministic failures
# (regex/circuit errors) cannot be fixed by backing off, so they are emitted at
# once. MAX_ATTEMPTS bounds the loop.
RESOURCE_FAIL = ("oom_or_killed", "disk_full", "build_timeout", "prove_timeout")
RETRY_BACKOFF = 2.0                    # x RAM reservation per requeue
MAX_ATTEMPTS  = 5                      # per-circuit attempt cap (last is serial)
_GNU_TIME = "/usr/bin/time" if os.path.isfile("/usr/bin/time") else None


def _mem_available_bytes():
    try:
        with open("/proc/meminfo") as f:
            for ln in f:
                if ln.startswith("MemAvailable:"):
                    return int(ln.split()[1]) * 1024
    except OSError:
        pass
    return None


def _ram_budget_bytes():
    t = _total_ram_bytes()
    return int(t * RAM_BUDGET_FRAC) if t else None


def _cpu_max_jobs():
    """Concurrency ceiling so each running circuit keeps >= MIN_CPUS_PER_CIRC."""
    return max(1, (os.cpu_count() or MIN_CPUS_PER_CIRC) // MIN_CPUS_PER_CIRC)


def _calib_slope(done, vkey, default):
    """Median bytes-per-constraint over done records carrying vkey and r1cs_cons;
    `default` when none are measured yet."""
    pts = [r[vkey] / r["r1cs_cons"] for r in done.values()
           if r.get(vkey) and r.get("r1cs_cons")]
    return statistics.median(pts) if pts else default


def _estimate(name, str_len, done, slope, vkey, floor):
    """Predict vkey (bytes) for (name, str_len): measured at this size > measured
    at a smaller size scaled by str_len > slope*r1cs_cons (also size-scaled) >
    floor. r1cs_cons grows ~linearly in STR_LENGTH, so the scaling is a proxy."""
    r = done.get("%s|%d" % (name, str_len))
    if r and r.get(vkey):
        return r[vkey]
    smaller = [(done["%s|%d" % (name, s)], s) for s in sorted(VEC_SIZE)
               if s < str_len and ("%s|%d" % (name, s)) in done]
    for rr, s in reversed(smaller):              # nearest smaller size first
        if rr.get(vkey):
            return int(rr[vkey] * (str_len / s))
    for rr, s in reversed(smaller):
        if rr.get("r1cs_cons"):
            return int(rr["r1cs_cons"] * (str_len / s) * slope)
    if r and r.get("r1cs_cons"):
        return int(r["r1cs_cons"] * slope)
    return floor


def _as_cap(est_rss, full_mem):
    """Per-job prlimit AS cap from its RAM estimate, clamped to [8 GiB, full]."""
    if not full_mem:
        return None
    floor = min(full_mem, 8 * 2**30)
    return int(min(full_mem, max(est_rss * EST_AS_MARGIN, floor)))


def _dir_bytes(d):
    tot = 0
    for root, _, files in os.walk(d):
        for fn in files:
            try:
                tot += os.path.getsize(os.path.join(root, fn))
            except OSError:
                pass
    return tot

# --- scratch drive auto-selection ------------------------------------------
# Per-circuit keygen writes ./keys/policy<N>_inst, which is multi-GB; the largest
# circuits (e.g. canada-drivers-license at STR_LENGTH=4000, ~2^21 constraints)
# emit tens of GB each, and several of them build CONCURRENTLY. On a box whose
# /tmp sits on a small root fs this exhausts the disk -> circ exits
# non-zero (status 'build_fail', NOT an OOM kill). So at startup we pick the
# writable LOCAL (non-tmpfs, non-network) mount with the most free space, put the
# per-job work dirs there, and delete that folder when the run ends. BUILD_ROOT
# (the reused compiled binary) stays in /tmp -- it is small and persistent, and
# moving it would force a slow rebuild every run.
SCRATCH_MIN_FREE_GB = 60               # require this much free to pick a drive
# Skip pseudo, RAM-backed and network filesystems: keygen writes large files and
# reads them back, so we want a real local block device, not tmpfs/ceph/nfs/etc.
_NON_SCRATCH_FSTYPES = {
    "tmpfs", "devtmpfs", "ramfs", "proc", "sysfs", "cgroup", "cgroup2",
    "devpts", "overlay", "squashfs", "efivarfs", "autofs", "mqueue",
    "debugfs", "tracefs", "securityfs", "pstore", "bpf", "configfs",
    "fusectl", "binfmt_misc", "hugetlbfs", "nsfs",
    "ceph", "nfs", "nfs4", "cifs", "smbfs", "fuse.sshfs", "9p",
}


def _candidate_mounts():
    """Real local mount points from /proc/mounts (pseudo/tmpfs/network skipped)."""
    seen, out = set(), []
    try:
        with open("/proc/mounts") as f:
            for ln in f:
                parts = ln.split()
                if len(parts) < 3:
                    continue
                mp, fstype = parts[1], parts[2]
                if fstype in _NON_SCRATCH_FSTYPES or mp in seen:
                    continue
                seen.add(mp)
                out.append(mp)
    except OSError:
        pass
    return out


def _writable_free_gb(mp):
    """Free GiB on mp if we can actually create a file there, else None."""
    probe = os.path.join(mp, ".bora_zombie_wtest")
    try:
        with open(probe, "w") as f:
            f.write("x")
        os.remove(probe)
        return shutil.disk_usage(mp).free / 2**30
    except OSError:
        return None


def _pick_scratch_base():
    """Return <mount>/bora_zombie_scratch on the writable local drive with the
    most free space (>= SCRATCH_MIN_FREE_GB); fall back to the /tmp PAR_ROOT when
    no drive qualifies. The caller creates and (at run end) removes it."""
    best, best_free = None, -1.0
    for mp in _candidate_mounts():
        free = _writable_free_gb(mp)
        if free is not None and free > best_free:
            best, best_free = mp, free
    if best is None or best_free < SCRATCH_MIN_FREE_GB:
        print("[scratch] no local drive with >= %d GiB free; using %s"
              % (SCRATCH_MIN_FREE_GB, PAR_ROOT))
        return PAR_ROOT
    base = os.path.join(best, "bora_zombie_scratch")
    print("[scratch] using %s (%.0f GiB free) for per-job key work dirs"
          % (base, best_free))
    return base

# patch sentinel (delimits OUR auto-generated match arms inside zk_test()).
SENT_BEGIN = "        // >>> run_zombie auto-generated arms (do not edit)"
SENT_END   = "        // <<< run_zombie auto-generated arms"
ARM_ANCHOR = "        _ => ()\n"            # the catch-all arm we insert before


# --- tiny io helpers -------------------------------------------------------
def _read(p):
    with open(p) as f:
        return f.read()


def _atomic_write(p, text):
    tmp = p + ".tmp"
    with open(tmp, "w") as f:
        f.write(text)
    os.replace(tmp, p)


# ===========================================================================
# part 1: parse the baked policy regex into its three parts (round-trippable)
# ===========================================================================
# The generator (gen_zombie_regex.sit_to_regex) emits exactly
#     (PAT.{0,N}KWS)|(KWS.{0,N}PAT)
# where KWS = (kw1|kw2|...) is a single parenthesized group and N = proximity.
# In our dialect bare '(' ')' are always structural (literal parens are \x28/\x29),
# so plain paren-depth counting is safe.

def _match_group_fwd(s, i):
    """s[i] must be '('; return index just past its matching ')'."""
    if s[i] != "(":
        raise ValueError("expected '(' at %d" % i)
    depth = 0
    for j in range(i, len(s)):
        if s[j] == "(":
            depth += 1
        elif s[j] == ")":
            depth -= 1
            if depth == 0:
                return j + 1
    raise ValueError("unbalanced parentheses")


def _split_fwd_branch(a):
    """a = PAT.{0,N}KWS -> (pat, kws, prox). KWS is the trailing balanced group."""
    if not a.endswith(")"):
        raise ValueError("forward branch does not end in KWS group")
    depth = 0
    for j in range(len(a) - 1, -1, -1):
        if a[j] == ")":
            depth += 1
        elif a[j] == "(":
            depth -= 1
            if depth == 0:
                kws, prefix = a[j:], a[:j]    # KWS = "(...)", prefix = PAT + ".{0,N}"
                break
    else:
        raise ValueError("could not locate KWS group")
    m = re.match(r"^(.*)\.\{0,(\d+)\}$", prefix, re.S)  # greedy -> last .{0,N} = connector
    if not m:
        raise ValueError("no .{0,N} proximity connector before KWS")
    return m.group(1), kws, int(m.group(2))


def extract_parts(full):
    """Parse a baked policy regex into (pat, kws, prox). Cross-checks the backward
    branch against the forward one; raises ValueError on any malformed input."""
    full = full.strip()
    end_a = _match_group_fwd(full, 0)        # first balanced group = "(A)"
    a = full[1:end_a - 1]
    rest = full[end_a:]
    if not (rest.startswith("|(") and rest.endswith(")")):
        raise ValueError("expected '|(...)' backward branch")
    b = rest[2:-1]
    pat, kws, prox = _split_fwd_branch(a)
    if b != "{k}.{{0,{n}}}{p}".format(k=kws, n=prox, p=pat):
        raise ValueError("backward branch inconsistent with forward branch")
    return pat, kws, prox


def assemble_parts(pat, kws, prox):
    """Inverse of extract_parts; identical to gen_zombie_regex.sit_to_regex's body."""
    return "({p}.{{0,{n}}}{k})|({k}.{{0,{n}}}{p})".format(p=pat, n=prox, k=kws)


def list_policy_names(full_dir=FULL_DIR):
    """Every policy UNIT under full_dir as a name resolvable to <full_dir>/<name>.regex.
    gen_zombie_regex writes per COMBO: a single-combo SIT is the flat '<slug>.regex'
    (name '<slug>'); an expanded SIT is '<slug>/comb<MM>.regex' (name
    '<slug>/comb<MM>'). Each unit is its OWN Zombie circuit, so total cost sums over
    these names."""
    names = []
    if not os.path.isdir(full_dir):
        return names
    for entry in sorted(os.listdir(full_dir)):
        path = os.path.join(full_dir, entry)
        if os.path.isdir(path):
            for fn in sorted(os.listdir(path)):
                if fn.endswith(".regex"):
                    names.append("%s/%s" % (entry, fn[:-6]))
        elif entry.endswith(".regex"):
            names.append(entry[:-6])
    return names


def list_sit_reps(full_dir=FULL_DIR):
    """One representative policy name per SIT (combo 0 for expanded SITs). All
    combos of a SIT share the same KWS, so vocabulary parsing must use ONE per SIT
    (else a C-combo SIT's keywords are counted C times)."""
    reps, seen = [], set()
    for name in list_policy_names(full_dir):
        slug = name.split("/", 1)[0]
        if slug not in seen:
            seen.add(slug)
            reps.append(name)
    return reps


def selftest():
    """Round-trip extract/assemble over every regex_zombie/ file plus hand cases."""
    cases = [
        ("[0-9]{3}", "(visa|card)", 300),
        ("(a|b)[A-Za-z0-9]{2}", "(ssn)", 50),
        ("X.{0,50}[0-9]", "(kw1|kw2)", 300),     # PAT itself ends in .{0,k}
        ("\\x41\\x42", "(\\x70\\x77)", 17),
    ]
    n_ok = 0
    for pat, kws, prox in cases:
        full = assemble_parts(pat, kws, prox)
        assert extract_parts(full) == (pat, kws, prox), full
        n_ok += 1
    for name in list_policy_names(FULL_DIR):
        full = _read(os.path.join(FULL_DIR, name + ".regex")).strip()
        parts = extract_parts(full)
        assert assemble_parts(*parts) == full, name
        n_ok += 1
    print("[selftest] round-trip OK on %d cases" % n_ok)
    return n_ok


# ===========================================================================
# part 2: idempotent Rust enablement + build
# ===========================================================================
def _arm(n):
    return ('        "policy_%d" => benchmark_one_circuit("policy%d", '
            'vec![RegexProverWitness::<%d>::default()], '
            'vec![RegexVerifierWitness::<%d>::default()], '
            'should_generate, benchmark_method),' % (n, n, n, n))


def _render_zkmb(orig, sizes):
    """Deterministically produce the patched zkmb.rs from the pristine baseline:
    drop any existing policy_<N> arm for our sizes (avoid duplicate/unreachable
    arms), then insert our sentinel block before the catch-all arm."""
    text = orig
    for n in sizes:
        text = re.sub(r'^[ \t]*"policy_%d" => .*\n' % n, "", text, flags=re.M)
    block = SENT_BEGIN + "\n" + "\n".join(_arm(n) for n in sizes) + "\n" + SENT_END + "\n"
    if text.count(ARM_ANCHOR) != 1:
        raise SystemExit("zkmb.rs: expected exactly one catch-all arm anchor "
                         "(%r); upstream may have drifted." % ARM_ANCHOR.strip())
    return text.replace(ARM_ANCHOR, block + ARM_ANCHOR)


def _copy_circ_out_of_workspace():
    """Make the persistent out-of-workspace copy of circ once (excluding the
    top-level target/ and .git only -- an unanchored 'target' would also drop the
    source module circ/src/target/ and break the build). The pristine clone (with
    download_zombie.py's patches) is the source; the copy lives in /tmp, outside
    the BORA workspace, so cargo never walks up to it."""
    if os.path.isdir(CIRC_BUILD):
        return
    if not os.path.isfile(os.path.join(CLONE_CIRC, "src", "zkmb.rs")):
        raise SystemExit("missing %s -- run download_zombie.py first." % CLONE_CIRC)
    print("[zombie] copying circ -> %s (out of the BORA workspace)..." % CIRC_BUILD)
    os.makedirs(BUILD_ROOT, exist_ok=True)

    def _root_ignore(dirpath, names):
        if os.path.abspath(dirpath) == os.path.abspath(CLONE_CIRC):
            return {n for n in names if n in ("target", ".git")}
        return set()

    shutil.copytree(CLONE_CIRC, CIRC_BUILD, symlinks=True, ignore=_root_ignore)


def ensure_testregex():
    """Ensure <ms_dlp>/zombie/regex/bin/TestRegex (the regex->DFA codegen tool) is
    present. It is a `make` artifact -- the source copy ships zombie/regex/src but
    not the compiled bin/ -- so build it in place on first use. Paths are relative
    to cwd (set to get_ms_dlp_dir() in main), so this is machine-independent. Fail
    early with an actionable message instead of crashing deep in a worker thread
    with FileNotFoundError."""
    if os.path.isfile(TESTREGEX):
        return
    if not os.path.isdir(REGEX_DIR):
        raise SystemExit(
            "TestRegex missing and %s/ not found. Run scripts/download_zombie.py to "
            "fetch + build the Zombie tree." % REGEX_DIR)
    print("[zombie] TestRegex missing; building (make in %s)..." % REGEX_DIR)
    r = subprocess.run(["make"], cwd=REGEX_DIR)
    if r.returncode != 0 or not os.path.isfile(TESTREGEX):
        raise SystemExit(
            "`make` in %s did not produce bin/TestRegex (needs g++ + libgmp-dev). "
            "See output above, or run scripts/download_zombie.py." % REGEX_DIR)


def ensure_zombie_built(sizes):
    """Build circ_executable (with our policy_<N> arms) from the out-of-workspace
    copy and return the binary path. Also provisions TestRegex if absent.

    The copy's zkmb.rs is patched IDEMPOTENTLY: a pristine zkmb.rs.orig is captured
    once and zkmb.rs is regenerated from it every call, so the result is a pure
    function of the baseline -- N runs equal 1 run. Rebuilds only when the source
    changed or the binary is missing. Uses the committed Cargo.lock (--locked) and
    system GMP/MPFR/MPC (download_zombie.py's verified recipe)."""
    ensure_testregex()                 # regex->DFA codegen tool (make artifact)
    _copy_circ_out_of_workspace()

    # capture the copy's pristine baseline once (the clone never patches zkmb.rs).
    if not os.path.isfile(BUILD_RS_ORIG):
        cur = _read(BUILD_RS)
        if SENT_BEGIN in cur:
            raise SystemExit("copy zkmb.rs already patched but no .orig backup; "
                             "delete %s and re-run." % BUILD_ROOT)
        if "fn main() {\n    zk_test()\n}" not in cur:
            raise SystemExit("zkmb.rs: unexpected main(); upstream may have "
                             "drifted from the pinned commit.")
        _atomic_write(BUILD_RS_ORIG, cur)

    orig = _read(BUILD_RS_ORIG)
    desired = _render_zkmb(orig, sizes)
    changed = _read(BUILD_RS) != desired
    if changed:
        _atomic_write(BUILD_RS, desired)

    if changed or not os.path.isfile(CIRC_BIN):
        print("[zombie] building circ_executable (first build is slow)...")
        env = dict(os.environ)
        env.update(SYSTEM_LIBS_ENV)
        r = subprocess.run(["cargo", "build", "--release", "--bin",
                            "circ_executable", "--locked"], cwd=CIRC_BUILD, env=env)
        if r.returncode != 0 or not os.path.isfile(CIRC_BIN):
            raise SystemExit("cargo build failed; see output above.")
    os.makedirs(KEYS_DIR, exist_ok=True)
    return CIRC_BIN


# ===========================================================================
# part 3: run one circuit, measure
# ===========================================================================
def _rec(slug, str_len, pat=None, kws=None, prox=None, status="", err="", **m):
    d = {"regex_name": slug, "str_len": str_len,
         "pat_len": len(pat) if pat is not None else None,
         "kws_len": len(kws) if kws is not None else None,
         "prox": prox, "r1cs_cons": None, "prove_ms": None,
         "verify_ms": None, "proof_bytes": None, "peak_rss": None,
         "key_bytes": None, "status": status, "err": err}
    d.update(m)
    return d


def _slice_zok(stdout):
    """The .zok begins at the 'const u32 STR_LENGTH' line (after 'Parse
    Successful!' / '[Zokrates Code]')."""
    i = stdout.find("const u32 STR_LENGTH")
    return stdout[i:] if i >= 0 else None


def _parse_metrics(stdout):
    def g(p):
        m = re.search(p, stdout)
        return int(m.group(1)) if m else None
    cons = g(r"circuit constraints cons (\d+)")
    prove = g(r"prove takes (\d+)")
    proof = g(r"proof size is (\d+) bytes")
    verify = g(r"verify takes (\d+)")
    if None in (cons, prove, proof, verify):
        return None
    return {"r1cs_cons": cons, "prove_ms": prove,
            "verify_ms": verify, "proof_bytes": proof}


def run_zombie(binp, regex_name, str_len, mem_bytes=None):
    """Build the real Zombie circuit for one policy at one document length and
    measure it. Returns a result dict; tolerant of every failure mode (parse,
    proximity-too-large, codegen/prove timeout, OOM, prove failure)."""
    full = _read(os.path.join(FULL_DIR, regex_name + ".regex")).strip()
    try:
        pat, kws, prox = extract_parts(full)
    except Exception as e:
        return _rec(regex_name, str_len, status="parse_fail", err=str(e))

    # spread() loops PROXY_DIST..(STR_LENGTH-PROXY_DIST); a too-short document
    # makes procCheck vacuous, so skip rather than emit a meaningless number.
    if str_len <= 2 * prox:
        return _rec(regex_name, str_len, pat, kws, prox,
                    status="skip_proximity", err="str_len<=2*prox")

    # stage 1: codegen (native proximity: two patterns, pair 0 1).
    stdin = pat + " & " + kws + "\n"
    try:
        z = subprocess.run([TESTREGEX, "F", "0", "1"], input=stdin,
                           capture_output=True, text=True, timeout=CODEGEN_TIMEOUT)
    except subprocess.TimeoutExpired:
        return _rec(regex_name, str_len, pat, kws, prox, status="codegen_timeout")
    if "Parse Successful!" not in z.stdout:
        return _rec(regex_name, str_len, pat, kws, prox,
                    status="parse_fail", err=(z.stderr or z.stdout)[:200])
    zok = _slice_zok(z.stdout)
    if zok is None:
        return _rec(regex_name, str_len, pat, kws, prox,
                    status="codegen_fail", err="no .zok in stdout")
    zok = zok.replace("const u32 STR_LENGTH = 1000",
                      "const u32 STR_LENGTH = %d" % str_len, 1)
    if prox != 300:
        zok = zok.replace("const u32 PROXY_DIST = 300",
                          "const u32 PROXY_DIST = %d" % prox, 1)
    _atomic_write(os.path.join(ZKMB_DIR, "policy%d.zok" % str_len), zok)

    # stage 2: key-gen + prove + verify via Spartan NIZK.
    try:
        p = subprocess.run(_limited([os.path.abspath(binp),
                            "policy_%d" % str_len, "true", "prover_verifier"], mem_bytes),
                           cwd=CIRC_BUILD, capture_output=True, text=True,
                           timeout=PROVE_TIMEOUT)
    except subprocess.TimeoutExpired:
        return _rec(regex_name, str_len, pat, kws, prox, status="prove_timeout")
    if p.returncode != 0:
        st = "oom_or_killed" if p.returncode < 0 else "prove_fail"
        return _rec(regex_name, str_len, pat, kws, prox,
                    status=st, err=(p.stderr or "")[-300:])
    m = _parse_metrics(p.stdout)
    if m is None:
        return _rec(regex_name, str_len, pat, kws, prox,
                    status="prove_fail", err="metrics not found in stdout")
    return _rec(regex_name, str_len, pat, kws, prox, status="ok", **m)


# ===========================================================================
# part 4: sweep one size over all policies (sequential), with resume
# ===========================================================================
def _load_partial():
    """Map "slug|str_len" -> prior result, for crash/resume skip. Reads the /tmp
    partial if present and non-empty; otherwise falls back to the durable docs
    mirror, which survives a reboot that wipes /tmp."""
    src = (PARTIAL if (os.path.isfile(PARTIAL) and os.path.getsize(PARTIAL) > 0)
           else PARTIAL_DOCS)
    done = {}
    if os.path.isfile(src):
        with open(src) as f:
            for ln in f:
                ln = ln.strip()
                if not ln:
                    continue
                r = json.loads(ln)
                done["%s|%d" % (r["regex_name"], r["str_len"])] = r
    return done


def _append_partial(rec):
    # write the primary (/tmp) copy and the durable docs mirror in lockstep.
    line = json.dumps(rec) + "\n"
    for p in (PARTIAL, PARTIAL_DOCS):
        with open(p, "a") as f:
            f.write(line)


def run_zombie_on_all(binp, str_len, done):
    """Measure every regex_zombie/ policy at one document length, sequentially.
    Reuses already-completed (slug,str_len) results from the partial log."""
    slugs = list_policy_names(FULL_DIR)     # one Zombie circuit per combo
    results = []
    for i, slug in enumerate(slugs, 1):
        key = "%s|%d" % (slug, str_len)
        if key in done:
            r = done[key]
            tag = "%s (cached)" % r["status"]
        else:
            r = run_zombie(binp, slug, str_len)
            _append_partial(r)
            done[key] = r
            tag = r["status"]
        results.append(r)
        print("[run] size=%d %d/%d %-52s -> %s"
              % (str_len, i, len(slugs), slug, tag))
    return {"meta": {"str_len": str_len, "n_policies": len(slugs),
                     "machine": gen_machine_config()}, "results": results}


# ===========================================================================
# part 5: log
# ===========================================================================
def _fmt(v):
    return "-" if v is None else str(v)


def write_log(results, sizes):
    by_size = {s: [r for r in results if r["str_len"] == s] for s in sizes}
    with open(LOG_FILE, "w") as f:
        f.write(gen_report_header("Zombie regex non-membership cost measurement"))
        f.write("\n\n")
        f.write("input:   %s/  (baked policy regexes)\n" % FULL_DIR)
        f.write("circuit: native two-pattern proximity (PAT & KWS, pair 0 1), "
                "all-zero witness\n")
        f.write("metrics: r1cs constraints, prove ms, verify ms, proof bytes "
                "(Spartan NIZK)\n")
        f.write("sizes:   %s\n" % ", ".join(str(s) for s in sizes))
        hdr = ("%-52s %7s %7s %6s %10s %9s %9s %10s  %s"
               % ("policy", "pat_len", "kws_len", "prox", "r1cs_cons",
                  "prove_ms", "verify_ms", "proof_B", "status"))
        for s in sizes:
            rows = by_size[s]
            f.write("\n\n== STR_LENGTH = %d ==\n" % s)
            f.write(hdr + "\n")
            f.write("-" * len(hdr) + "\n")
            for r in sorted(rows, key=lambda x: x["regex_name"]):
                f.write("%-52s %7s %7s %6s %10s %9s %9s %10s  %s\n"
                        % (r["regex_name"], _fmt(r["pat_len"]), _fmt(r["kws_len"]),
                           _fmt(r["prox"]), _fmt(r["r1cs_cons"]), _fmt(r["prove_ms"]),
                           _fmt(r["verify_ms"]), _fmt(r["proof_bytes"]), r["status"]))
            ok = [r for r in rows if r["status"] == "ok"]
            bad = [r for r in rows if r["status"] != "ok"]
            f.write("\n  -- summary (STR_LENGTH=%d) --\n" % s)
            f.write("  policies: %d   ok: %d   not-ok: %d\n"
                    % (len(rows), len(ok), len(bad)))
            if ok:
                for label, key in (("r1cs_cons", "r1cs_cons"),
                                   ("prove_ms", "prove_ms"),
                                   ("verify_ms", "verify_ms"),
                                   ("proof_bytes", "proof_bytes")):
                    vals = [r[key] for r in ok]
                    f.write("  %-12s mean/median/min/max: %.1f / %.1f / %d / %d\n"
                            % (label, statistics.mean(vals),
                               statistics.median(vals), min(vals), max(vals)))
            for r in bad:
                f.write("  ! %-52s %s  %s\n"
                        % (r["regex_name"], r["status"], r["err"][:80]))


# ===========================================================================
# part 4b: parallel-build / sequential-time pipeline
# ===========================================================================
def _codegen_zok(regex_name, str_len):
    """Codegen one policy's .zok (TestRegex F, fast). Returns (zok|None, prox, status)."""
    full = _read(os.path.join(FULL_DIR, regex_name + ".regex")).strip()
    try:
        pat, kws, prox = extract_parts(full)
    except Exception as e:
        return None, None, "parse_fail"
    if str_len <= 2 * prox:
        return None, prox, "skip_proximity"
    try:
        z = subprocess.run([TESTREGEX, "F", "0", "1"], input=pat + " & " + kws + "\n",
                           capture_output=True, text=True, timeout=CODEGEN_TIMEOUT)
    except subprocess.TimeoutExpired:
        return None, prox, "codegen_timeout"
    if "Parse Successful!" not in z.stdout:
        return None, prox, "parse_fail"
    zok = _slice_zok(z.stdout)
    if zok is None:
        return None, prox, "codegen_fail"
    zok = zok.replace("const u32 STR_LENGTH = 1000", "const u32 STR_LENGTH = %d" % str_len, 1)
    if prox != 300:
        zok = zok.replace("const u32 PROXY_DIST = 300", "const u32 PROXY_DIST = %d" % prox, 1)
    return zok, prox, "ok"


def _parse_time(stderr):
    """Split GNU time -v's trailing report off `stderr`; return (child_stderr,
    peak_rss_bytes|None, kill_signal|None). time wraps the child, so a signal
    death shows as time's positive exit -- we recover it from the report so the
    caller can still classify it as 'oom_or_killed'."""
    idx = stderr.rfind("\tCommand being timed:")
    block = stderr[idx:] if idx >= 0 else stderr
    child = stderr[:idx] if idx >= 0 else stderr
    mr = re.search(r"Maximum resident set size \(kbytes\): (\d+)", block)
    ms = re.search(r"Command terminated by signal (\d+)", block)
    return (child, int(mr.group(1)) * 1024 if mr else None,
            int(ms.group(1)) if ms else None)


def _run_keygen(cmd, cwd):
    """Run the (already prlimit-wrapped) keygen, measuring peak RSS via GNU time
    -v when present. Returns (returncode, stdout, child_stderr, peak_rss_bytes);
    returncode is negative for a signal death (recovered through time's report)."""
    full = ([_GNU_TIME, "-v"] + cmd) if _GNU_TIME else cmd
    p = subprocess.run(full, cwd=cwd, capture_output=True, text=True,
                       timeout=PROVE_TIMEOUT)
    if not _GNU_TIME:
        return p.returncode, p.stdout, p.stderr, None
    child_err, rss, sig = _parse_time(p.stderr)
    return (-sig if sig else p.returncode), p.stdout, child_err, rss


def _build_one(binp, idx, regex_name, str_len, mem_bytes=None):
    """BUILD phase (concurrent): codegen + keygen into the circuit's OWN work dir.
    should_generate=true writes ./keys/. Returns {name, prox, dir, status, ...};
    on a built circuit also peak_rss + key_bytes (for size-aware scheduling).
    mem_bytes caps the keygen's address space (per-job RAM share)."""
    zok, prox, cg = _codegen_zok(regex_name, str_len)
    if cg != "ok":
        return {"name": regex_name, "prox": prox, "dir": None, "status": cg}
    d = os.path.join(PAR_ROOT, "c%05d" % idx)
    shutil.rmtree(d, ignore_errors=True)
    os.makedirs(os.path.join(d, "zkmb"))
    os.makedirs(os.path.join(d, "keys"))
    _atomic_write(os.path.join(d, "zkmb", "policy%d.zok" % str_len), zok)
    # circ resolves the Z# stdlib by walking up from cwd for ZoKrates/zokrates_stdlib
    # (parser.rs); the isolated dir has no such ancestor, so symlink it in.
    os.symlink(os.path.join(os.path.abspath(CIRC_BUILD), "third_party", "ZoKrates"),
               os.path.join(d, "ZoKrates"))
    try:
        rc, _out, errtxt, rss = _run_keygen(
            _limited([os.path.abspath(binp), "policy_%d" % str_len,
                      "true", "prover"], mem_bytes), d)
    except subprocess.TimeoutExpired:
        return {"name": regex_name, "prox": prox, "dir": d, "status": "build_timeout"}
    if rc != 0:
        if rc < 0:
            st = "oom_or_killed"
        elif "No space left on device" in (errtxt or ""):
            st = "disk_full"                 # drive full; retry once drained
        else:
            st = "build_fail"
        return {"name": regex_name, "prox": prox, "dir": d, "status": st,
                "err": (errtxt or "")[-300:], "peak_rss": rss, "as_cap": mem_bytes}
    return {"name": regex_name, "prox": prox, "dir": d, "status": "built",
            "peak_rss": rss, "as_cap": mem_bytes,
            "key_bytes": _dir_bytes(os.path.join(d, "keys"))}


def _time_one(binp, built, str_len, mem_bytes=None):
    """TIME phase (sequential): prove+verify on the PRE-BUILT keys
    (should_generate=false). Returns a result rec (same shape as run_zombie).
    Runs alone, so mem_bytes is the FULL headroom cap."""
    name, prox, d = built["name"], built["prox"], built["dir"]
    pat, kws, _ = extract_parts(_read(os.path.join(FULL_DIR, name + ".regex")).strip())
    try:
        p = subprocess.run(_limited([os.path.abspath(binp), "policy_%d" % str_len, "false",
                            "prover_verifier"], mem_bytes), cwd=d, capture_output=True,
                           text=True, timeout=PROVE_TIMEOUT)
    except subprocess.TimeoutExpired:
        return _rec(name, str_len, pat, kws, prox, status="prove_timeout")
    if p.returncode != 0:
        st = "oom_or_killed" if p.returncode < 0 else "prove_fail"
        return _rec(name, str_len, pat, kws, prox, status=st, err=(p.stderr or "")[-300:])
    m = _parse_metrics(p.stdout)
    if m is None:
        return _rec(name, str_len, pat, kws, prox, status="prove_fail", err="no metrics")
    return _rec(name, str_len, pat, kws, prox, status="ok", **m)


def run_pipeline(binp, str_len, names, done):
    """Size-aware build/time over `names` at one str_len with an adaptive retry
    loop. Each ROUND forms build batches from a RAM budget + a >=MIN_CPUS_PER_CIRC
    cap + a disk budget (giants self-limit, smalls pack the cores). A circuit whose
    failure is a RESOURCE class is NOT emitted: its RAM reservation is ratcheted up
    and it is requeued to the next round, which the scheduler then runs at lower
    parallelism (down to serial). Only ok / deterministic outcomes are written, so
    each regex ends with exactly one record. Resumes from `done`."""
    key = lambda n: "%s|%d" % (n, str_len)
    results = [done[key(n)] for n in names if key(n) in done]
    pending = [n for n in names if key(n) not in done]
    os.makedirs(PAR_ROOT, exist_ok=True)
    budget = _ram_budget_bytes()             # summed est RAM ceiling for a batch
    max_jobs = _cpu_max_jobs()               # >= MIN_CPUS_PER_CIRC cores per job
    full_mem = _mem_cap_bytes(1)             # serial time / final attempt: full
    ram_default = int((budget or 0) * EST_DEFAULT_FRAC) or 2**34
    total = len(pending)
    floor_rss, attempts, widx, fin = {}, {}, [0], [0]

    def est_ram(n):
        slope = _calib_slope(done, "peak_rss", EST_SLOPE_BYTES_PER_CONS)
        e = _estimate(n, str_len, done, slope, "peak_rss", ram_default)
        return max(e, floor_rss.get(n, 0))   # honour the ratcheted reservation

    def finalize(rec):                       # write the ONE record for this regex
        nm = rec["regex_name"]
        _append_partial(rec); done[key(nm)] = rec
        for j, r in enumerate(results):
            if r["regex_name"] == nm and r["str_len"] == str_len:
                results[j] = rec
                break
        else:
            results.append(rec)
        fin[0] += 1
        rss = rec.get("peak_rss")
        tag = "ok" if rec["status"] == "ok" else "failed (%s)" % rec["status"]
        print("[run] size=%d %d/%d %-52s -> %s%s" % (str_len, fin[0], total, nm,
              tag, "  rss=%.0fGiB" % (rss / 2**30) if rss else ""))

    rnd = 0
    while pending:
        rnd += 1
        pending.sort(key=est_ram, reverse=True)   # giants first -> few-at-a-time
        if budget:
            print("[sched] size=%d round=%d: %d pending, RAM budget %.0f GiB, "
                  "max_jobs %d (>=%d cpu each)" % (str_len, rnd, len(pending),
                  budget / 2**30, max_jobs, MIN_CPUS_PER_CIRC))
        requeue, i = [], 0
        while i < len(pending):
            disk_free = shutil.disk_usage(PAR_ROOT).free
            dslope = _calib_slope(done, "key_bytes", DISK_SLOPE_BYTES_PER_CONS)
            disk_floor = int(disk_free * DISK_DEFAULT_FRAC)
            disk_budget = int(disk_free * DISK_BUDGET_FRAC)
            batch, ram, disk = [], 0, 0       # fill one batch under all three limits
            while i < len(pending) and len(batch) < max_jobs:
                w = est_ram(pending[i])
                dk = _estimate(pending[i], str_len, done, dslope, "key_bytes",
                               disk_floor)
                if batch and ((budget and ram + w > budget)
                              or (disk_budget and disk + dk > disk_budget)):
                    break                     # full (we always take >= 1)
                batch.append((widx[0], pending[i])); ram += w; disk += dk
                widx[0] += 1; i += 1
            caps = {idx: _as_cap(est_ram(n), full_mem) for idx, n in batch}
            with ThreadPoolExecutor(max_workers=len(batch)) as ex:   # build (parallel)
                built = [f.result() for f in as_completed(
                    [ex.submit(_build_one, binp, idx, n, str_len, caps[idx])
                     for idx, n in batch])]
            order = {n: k for k, (idx, n) in enumerate(batch)}
            built.sort(key=lambda b: order[b["name"]])
            serial = len(batch) == 1          # this circuit ran with full headroom
            for b in built:                                          # time (serial)
                nm = b["name"]
                if b["status"] == "built":
                    rec = _time_one(binp, b, str_len, full_mem)
                    rec["peak_rss"] = b.get("peak_rss")
                    rec["key_bytes"] = b.get("key_bytes")
                else:
                    rec = _rec(nm, str_len, prox=b.get("prox"), status=b["status"],
                               err=b.get("err", ""), peak_rss=b.get("peak_rss"))
                if b.get("dir"):
                    shutil.rmtree(b["dir"], ignore_errors=True)
                attempts[nm] = attempts.get(nm, 0) + 1
                # retry only RESOURCE failures, and only while backing off can still
                # help: stop once it has run serially (full headroom) or hit the cap.
                retryable = (rec["status"] in RESOURCE_FAIL
                             and attempts[nm] < MAX_ATTEMPTS and not serial)
                if rec["status"] == "ok" or not retryable:
                    finalize(rec)             # ok, or no point retrying -> emit once
                else:
                    base = b.get("as_cap") or est_ram(nm)
                    floor_rss[nm] = min(full_mem or int(base * RETRY_BACKOFF),
                                        int(base * RETRY_BACKOFF))
                    requeue.append(nm)
                    print("[run] size=%d  -/%d %-52s -> repeat (%d of %d)"
                          % (str_len, total, nm, attempts[nm], MAX_ATTEMPTS))
        pending = requeue
    return results


def validate_pipeline(binp, str_len=2000, n=8):
    """Tiny-batch correctness gate: run the first n circuits BOTH ways and assert the
    DETERMINISTIC stats (r1cs_cons, proof_bytes) match exactly; report timings."""
    names = list_policy_names(FULL_DIR)[:n]
    print("[validate] %d circuits in %s\n[validate] baseline (sequential one-shot)..."
          % (len(names), FULL_DIR))
    t0 = time.time()
    base = {nm: run_zombie(binp, nm, str_len) for nm in names}
    t_base = time.time() - t0
    print("[validate] pipeline (parallel-build / sequential-time)...")
    t1 = time.time()
    par = {r["regex_name"]: r for r in run_pipeline(binp, str_len, names, {})}
    t_par = time.time() - t1
    ok = True
    print("\n[validate] per-circuit comparison (deterministic stats must match):")
    for nm in names:
        b, p = base[nm], par[nm]
        same = (b["status"] == p["status"] and b.get("r1cs_cons") == p.get("r1cs_cons")
                and b.get("proof_bytes") == p.get("proof_bytes"))
        ok = ok and same
        print("  %-46s base cons=%s proof=%s prove=%sms | par cons=%s proof=%s prove=%sms  %s"
              % (nm.split("/")[-1][:46], b.get("r1cs_cons"), b.get("proof_bytes"),
                 b.get("prove_ms"), p.get("r1cs_cons"), p.get("proof_bytes"),
                 p.get("prove_ms"), "MATCH" if same else "*** MISMATCH ***"))
    print("\n[validate] deterministic stats (cons, proof_bytes, status) match: %s"
          % ("YES" if ok else "NO"))
    print("[validate] wall: baseline=%.0fs  pipeline=%.0fs  (speedup %.1fx, "
          "max_jobs=%d)" % (t_base, t_par, t_base / t_par if t_par else 0,
                            _cpu_max_jobs()))
    return ok


# -------------------------------------------
# MAIN
# -------------------------------------------
def run_ruleset(rs_dir, binp):
    """Measure one ruleset folder into run_zombie_<rs>.log via the parallel-build /
    sequential-time pipeline, with its own /tmp partial. Returns (n_results, n_ok)."""
    global FULL_DIR, LOG_FILE, PARTIAL, PARTIAL_DOCS
    FULL_DIR = rs_dir
    LOG_FILE = os.path.join(DOCS_DIR, "run_zombie_%s.log" % rs_dir)
    PARTIAL = os.path.join(PARTIAL_DIR, "run_zombie_%s.partial.jsonl" % rs_dir)
    PARTIAL_DOCS = os.path.join(DOCS_DIR, "run_zombie_%s.partial.jsonl" % rs_dir)
    selftest()                             # round-trip over THIS ruleset's combos
    done = _load_partial()
    results = []
    for s in VEC_SIZE:
        results.extend(run_pipeline(binp, s, list_policy_names(FULL_DIR), done))
    write_log(results, VEC_SIZE)
    n_ok = sum(1 for r in results if r["status"] == "ok")
    print("[run_zombie] %s : %d results, %d ok across sizes %s"
          % (LOG_FILE, len(results), n_ok, VEC_SIZE))
    return len(results), n_ok


def main():
    os.chdir(get_ms_dlp_dir())                     # resolve relative paths here
    os.makedirs(DOCS_DIR, exist_ok=True)
    os.makedirs(PARTIAL_DIR, exist_ok=True)        # transient cache lives in /tmp

    if "--selftest" in sys.argv:           # parse round-trip only; no Rust/build
        for rs in RULESETS:
            if os.path.isdir(rs):
                globals()["FULL_DIR"] = rs
                selftest()
        return

    binp = ensure_zombie_built(VEC_SIZE)   # one circ binary serves all rulesets

    # put the key-heavy per-job work dirs on the roomiest local drive, and remove
    # the folder we made when the run ends (per-job dirs are already cleaned
    # incrementally; this drops the now-empty parent).
    global PAR_ROOT
    PAR_ROOT = _pick_scratch_base()
    os.makedirs(PAR_ROOT, exist_ok=True)
    try:
        if "--validate" in sys.argv:       # tiny-batch baseline-vs-pipeline gate
            globals()["FULL_DIR"] = RULESETS[0]
            ok = validate_pipeline(binp)
            sys.exit(0 if ok else 1)

        for rs in RULESETS:
            if not os.path.isdir(rs):
                print("[run_zombie] ruleset %s/ absent -- skipping" % rs)
                continue
            print("\n=== run_zombie %s (sizes %s) ===" % (rs, VEC_SIZE))
            run_ruleset(rs, binp)
    finally:
        shutil.rmtree(PAR_ROOT, ignore_errors=True)
        print("[scratch] removed %s" % PAR_ROOT)


if __name__ == "__main__":
    main()
