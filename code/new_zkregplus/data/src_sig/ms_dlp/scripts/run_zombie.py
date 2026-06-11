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
# resume/crash cache: a transient build artifact (not a deliverable), so it lives
# in /tmp, never under docs/. Delete it to force a clean re-measure of all sizes.
PARTIAL_DIR = "/tmp/bora_zombie_run"
PARTIAL     = os.path.join(PARTIAL_DIR, "run_zombie.partial.jsonl")  # per-pass below

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
# build N_BUILD_JOBS circuits CONCURRENTLY -- each in its OWN /tmp work dir (own
# ./zkmb + ./keys, shared abs-path binary) so the per-circuit 'policy2000' key
# files do not collide -- then TIME each built circuit one-by-one (clean timing,
# no build running). After a circuit is timed its work dir is deleted (disk stays
# ~N_BUILD_JOBS x ~70MB).
N_BUILD_JOBS = max(1, (os.cpu_count() or 8) // 4)   # 32 cores -> 8
PAR_ROOT     = "/tmp/bora_zombie_par"               # per-circuit isolated work dirs

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
         "verify_ms": None, "proof_bytes": None, "status": status, "err": err}
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


def run_zombie(binp, regex_name, str_len):
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
        p = subprocess.run([os.path.abspath(binp),
                            "policy_%d" % str_len, "true", "prover_verifier"],
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
    """Map "slug|str_len" -> prior result, for crash/resume skip."""
    done = {}
    if os.path.isfile(PARTIAL):
        with open(PARTIAL) as f:
            for ln in f:
                ln = ln.strip()
                if not ln:
                    continue
                r = json.loads(ln)
                done["%s|%d" % (r["regex_name"], r["str_len"])] = r
    return done


def _append_partial(rec):
    with open(PARTIAL, "a") as f:
        f.write(json.dumps(rec) + "\n")


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


def _build_one(binp, idx, regex_name, str_len):
    """BUILD phase (concurrent): codegen + keygen into the circuit's OWN /tmp dir.
    should_generate=true writes ./keys/. Returns {name, prox, dir, status[, err]}."""
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
        p = subprocess.run([os.path.abspath(binp), "policy_%d" % str_len, "true", "prover"],
                           cwd=d, capture_output=True, text=True, timeout=PROVE_TIMEOUT)
    except subprocess.TimeoutExpired:
        return {"name": regex_name, "prox": prox, "dir": d, "status": "build_timeout"}
    if p.returncode != 0:
        st = "oom_or_killed" if p.returncode < 0 else "build_fail"
        return {"name": regex_name, "prox": prox, "dir": d, "status": st,
                "err": (p.stderr or "")[-300:]}
    return {"name": regex_name, "prox": prox, "dir": d, "status": "built"}


def _time_one(binp, built, str_len):
    """TIME phase (sequential): prove+verify on the PRE-BUILT keys
    (should_generate=false). Returns a result rec (same shape as run_zombie)."""
    name, prox, d = built["name"], built["prox"], built["dir"]
    pat, kws, _ = extract_parts(_read(os.path.join(FULL_DIR, name + ".regex")).strip())
    try:
        p = subprocess.run([os.path.abspath(binp), "policy_%d" % str_len, "false",
                            "prover_verifier"], cwd=d, capture_output=True, text=True,
                           timeout=PROVE_TIMEOUT)
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
    """Batched parallel-build / sequential-time over `names` at one str_len; resumes
    from `done`; appends each result to the partial log. Returns all results."""
    key = lambda n: "%s|%d" % (n, str_len)
    results = [done[key(n)] for n in names if key(n) in done]
    todo = [n for n in names if key(n) not in done]
    os.makedirs(PAR_ROOT, exist_ok=True)
    total, ti = len(todo), 0
    for b0 in range(0, total, N_BUILD_JOBS):
        batch = todo[b0:b0 + N_BUILD_JOBS]
        with ThreadPoolExecutor(max_workers=N_BUILD_JOBS) as ex:   # phase 1: build
            built = [f.result() for f in as_completed(
                [ex.submit(_build_one, binp, b0 + j, n, str_len)
                 for j, n in enumerate(batch)])]
        order = {n: k for k, n in enumerate(batch)}
        built.sort(key=lambda b: order[b["name"]])
        for b in built:                                            # phase 2: time, serial
            ti += 1
            if b["status"] != "built":
                rec = _rec(b["name"], str_len, prox=b.get("prox"),
                           status=b["status"], err=b.get("err", ""))
            else:
                rec = _time_one(binp, b, str_len)
            if b.get("dir"):
                shutil.rmtree(b["dir"], ignore_errors=True)
            _append_partial(rec); done[key(b["name"])] = rec; results.append(rec)
            print("[run] size=%d %d/%d %-52s -> %s"
                  % (str_len, ti, total, b["name"], rec["status"]))
    # OOM fallback: at STR_LENGTH=4000 the largest circuits cross 2^20 constraints;
    # keygen for those can exhaust RAM under N_BUILD_JOBS-way concurrency. Rebuild any
    # OOM-killed circuit ONE AT A TIME (full RAM per circuit). A later partial line
    # overwrites the failed one on resume; the in-memory result is replaced in place.
    retry = [r["regex_name"] for r in results if r.get("status") == "oom_or_killed"]
    for ri, nm in enumerate(retry, 1):
        print("[retry] size=%d %d/%d %-52s (serial OOM fallback) ..."
              % (str_len, ri, len(retry), nm))
        b = _build_one(binp, 0, nm, str_len)
        rec = (_time_one(binp, b, str_len) if b["status"] == "built"
               else _rec(nm, str_len, prox=b.get("prox"), status=b["status"],
                         err=b.get("err", "")))
        if b.get("dir"):
            shutil.rmtree(b["dir"], ignore_errors=True)
        _append_partial(rec); done[key(nm)] = rec
        for i, r in enumerate(results):
            if r["regex_name"] == nm and r["str_len"] == str_len:
                results[i] = rec
                break
        print("[retry] size=%d %d/%d %-52s -> %s"
              % (str_len, ri, len(retry), nm, rec["status"]))
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
    print("[validate] wall: baseline=%.0fs  pipeline=%.0fs  (speedup %.1fx, jobs=%d)"
          % (t_base, t_par, t_base / t_par if t_par else 0, N_BUILD_JOBS))
    return ok


# -------------------------------------------
# MAIN
# -------------------------------------------
def run_ruleset(rs_dir, binp):
    """Measure one ruleset folder into run_zombie_<rs>.log via the parallel-build /
    sequential-time pipeline, with its own /tmp partial. Returns (n_results, n_ok)."""
    global FULL_DIR, LOG_FILE, PARTIAL
    FULL_DIR = rs_dir
    LOG_FILE = os.path.join(DOCS_DIR, "run_zombie_%s.log" % rs_dir)
    PARTIAL = os.path.join(PARTIAL_DIR, "run_zombie_%s.partial.jsonl" % rs_dir)
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

    if "--validate" in sys.argv:           # tiny-batch baseline-vs-pipeline gate
        globals()["FULL_DIR"] = RULESETS[0]
        ok = validate_pipeline(binp)
        sys.exit(0 if ok else 1)

    for rs in RULESETS:
        if not os.path.isdir(rs):
            print("[run_zombie] ruleset %s/ absent -- skipping" % rs)
            continue
        print("\n=== run_zombie %s (sizes %s) ===" % (rs, VEC_SIZE))
        run_ruleset(rs, binp)


if __name__ == "__main__":
    main()
