# -------------------------------------------
# Creator: BORA Author. Implemented with Claude Code; reviewed by BORA author.
# Date: 06/07/2026
# Purpose: empirically characterize the limits of Zombie's regex-to-circuit
#          compiler that bound which MS-DLP policies it can prove.
#          Each test is a full baked policy in the canonical
#              (PAT.{0,N}KWS)|(KWS.{0,N}PAT)
#          form, run through the SAME extract_parts -> TestRegex F 0 1 -> circ
#          path that run_zombie.py uses (str_len=1000, prox=300, all-zero
#          witness). Only one literal/repetition varies per case; the rest is
#          trivial filler. We classify each as PASS or one of the failure modes
#          and check it against the predicted behavior, then write the findings
#          and every case to docs/verify_zombie_limit.log.
#
#   TWO real failure modes (plus a codegen catch-all):
#     ceiling  : a packed match-run group holds at most 32 literal bytes -- the
#                33rd term's coefficient overflows the
#                256-bit arkworks BigInteger256.
#				 The can a literal string, one keyword
#                alternative, an EXACT rep X{n}.
#                It surfaces two ways:
#                at exactly 33 B the constant 2^256 is built -> panic
#                "index out of bounds: the len is 4" (ff/biginteger/mod.rs:507);
#                at >=34 B the chunker splits and emits a malformed "... + )"
#                (dangling +) -> "expected unaried_term" parse error first.
#     zerolb   : ANY zero-lower-bound rep {0,N} (literal OR wildcard, every N) is
#                miscompiled to "f[i] =  * start[i]" (empty coefficient) and
#                rejected by the parser. Independent of N and of the 32 B limit.
#     codegen  : TestRegex itself fails to parse the regex.
#   Safe: a variable rep {m,N} with m>=1 compiles via a DFA loop / doubling and
#   builds as long as no tile exceeds 32 B (a{1,33}, a{1,63}); wildcard reps with
#   m>=1 always build (.{1,500}) -- a wildcard has no fixed bytes to pack.
#
# -------------------------------------------

import os
import re
import sys
import subprocess

HERE = os.path.dirname(os.path.abspath(__file__))
MS_DLP = os.path.dirname(HERE)
sys.path.insert(0, HERE)
os.chdir(MS_DLP)                       # run_zombie's relative paths resolve here

import run_zombie as rz                # reuse the real pipeline helpers
from common import gen_report_header   # noqa: E402

STR_LEN = 1000
PROX = 300
LOG_FILE = os.path.join("docs", "verify_zombie_limit.log")

LIMITS_SUMMARY = """\
ZOMBIE REGEX-TO-CIRCUIT COMPILER LIMITS (empirically established)

A circuit is built iff (1) every packed literal run/tile is <=32 bytes AND
(2) the regex uses no zero-lower-bound repetition {0,N}. The longest SINGLE run
is what matters -- never the total pattern length. Two real rejection modes:

  1. ceiling  (the 32-byte packed-run limit)
     Each match-run is packed base-256 into a field element:
         isZero((t[i-k]-c) + (t[i-k+1]-c)*256 + ... )
     A group holds at most 32 literal bytes; the 33rd term's coefficient is
     256^32 = 2^256, which overflows the 256-bit arkworks BigInteger256 (a BN254
     field element is 4 x u64 = 256 bits). Same root cause, two manifestations:
       - run == 33 B : the constant 2^256 is built -> panic
                       "index out of bounds: the len is 4" (ff/biginteger:507)
       - run >= 34 B : chunker splits, emits malformed "... + )" (dangling +)
                       -> "expected unaried_term" parse error (fires first)
     Sources of a >=33 B run -- ALL fail, regardless of total length:
       - a literal string >=33 B            aaaa...(33)            FAIL
       - one keyword alternative >=33 B      (aaaa...(33)|b)        FAIL
       - an EXACT rep X{n} tiled to >=33 B   x{33}, (ab){17}       FAIL
     (A variable rep {m,N} can also overflow once its doubling tile exceeds
      32 B -- see SAFE below.)
     It is the longest SINGLE run, not the total:
       (a*20|b*20|c*20)  -> 60 literal chars but max run 20        PASS

  2. zerolb  (zero-lower-bound repetition unsupported)
     ANY {0,N} -- literal OR wildcard, for EVERY N -- is miscompiled to
     "f[i] =  * start[i]" (empty coefficient) and rejected by the parser.
     Independent of N and of the 32 B limit:
       a{0,5}, a{0,32}, a{0,33}, .{0,33}                           FAIL
     (This is why the pipeline strips .{0,300} and does proximity natively.)

  (codegen: TestRegex itself failing to parse the regex -- not seen here.)

SAFE: a variable rep {m,N} with m>=1 compiles via a DFA loop / doubling and
builds as long as no doubling tile exceeds 32 B; a wildcard has nothing to pack.
The construction caps tiles at 32 B up to N~96, then jumps to 63/64 B tiles that
overflow -- so the flip is in (96,127] (not at 2^k as one might guess):
       a{1,33}, a{1,96}           PASS   (max tile 32 B)
       a{1,127}, a{1,200}         FAIL   (tile 63/64 B -> ceiling)
       .{1,500}                   PASS   (wildcard: nothing to pack)

ONE-LINE RULE: a single literal run/tile >32 B overflows the 256-bit packing
field element; any {0,N} is unsupported; everything else builds.
"""


def grp(s):                            # parenthesized keyword group
    return "(" + s + ")"


# (id, group, pat, kws, longest-fixed-run-bytes, predict_status, predict_mode)
CASES = [
    # G1 -- fixed literal run inside a single KEYWORD (pat fixed = "a")
    ("k31", "G1 literal in keyword", "a", grp("K" * 31), 31, "PASS", "-"),
    ("k32", "G1 literal in keyword", "a", grp("K" * 32), 32, "PASS", "-"),
    ("k33", "G1 literal in keyword", "a", grp("K" * 33), 33, "FAIL", "ceiling"),
    ("k34", "G1 literal in keyword", "a", grp("K" * 34), 34, "FAIL", "ceiling"),
    # G2 -- combined keywords (total>32) vs one long keyword
    ("c1",  "G2 combined keywords",  "a", grp("a"*20 + "|" + "b"*20 + "|" + "c"*20), 20, "PASS", "-"),
    ("c2",  "G2 combined keywords",  "a", grp("a"*33 + "|" + "b"), 33, "FAIL", "ceiling"),
    # G3 -- fixed literal run inside PAT (kws fixed = "(z)")
    ("p32", "G3 literal in pat", "p" * 32, grp("z"), 32, "PASS", "-"),
    ("p33", "G3 literal in pat", "p" * 33, grp("z"), 33, "FAIL", "ceiling"),
    # G4 -- EXACT repetition tiled into one run (kws fixed = "(z)")
    ("e32", "G4 exact rep tiling", "x{32}",    grp("z"), 32, "PASS", "-"),
    ("e33", "G4 exact rep tiling", "x{33}",    grp("z"), 33, "FAIL", "ceiling"),
    ("e16", "G4 exact rep tiling", "(ab){16}", grp("z"), 32, "PASS", "-"),
    ("e17", "G4 exact rep tiling", "(ab){17}", grp("z"), 34, "FAIL", "ceiling"),
    # G5 -- zero-lower-bound rep {0,N} (N-independent; literal & wildcard)
    ("z05", "G5 zero-lower-bound", "a{0,5}",  grp("z"),  5, "FAIL", "zerolb"),
    ("z32", "G5 zero-lower-bound", "a{0,32}", grp("z"), 32, "FAIL", "zerolb"),
    ("z33", "G5 zero-lower-bound", "a{0,33}", grp("z"), 33, "FAIL", "zerolb"),
    ("zw",  "G5 zero-lower-bound", ".{0,33}", grp("z"),  0, "FAIL", "zerolb"),
    # G6 -- variable rep, lower bound >=1: safe until a doubling tile exceeds 32 B
    ("l33", "G6 lower-bound>=1",   "a{1,33}",  grp("z"),  33, "PASS", "-"),
    ("l96", "G6 lower-bound>=1",   "a{1,96}",  grp("z"),  96, "PASS", "-"),
    ("l127","G6 lower-bound>=1",   "a{1,127}", grp("z"), 127, "FAIL", "ceiling"),
    ("l200","G6 lower-bound>=1",   "a{1,200}", grp("z"), 200, "FAIL", "ceiling"),
    ("lw",  "G6 lower-bound>=1",   ".{1,500}", grp("z"),   0, "PASS", "-"),
]


def _offending_line(err):
    """Return the source line circ flagged (the 'NN | <code>' under '--> NN:C')."""
    m = re.search(r"-->\s*(\d+):", err)
    if m:
        cm = re.search(r"^\s*%s\s*\|\s?(.*)$" % m.group(1), err, re.M)
        if cm:
            return cm.group(1)
    return ""


def classify(returncode, stdout, stderr):
    """Map a circ run to (status, mode, detail). Two failure modes:
    ceiling (>32 B packed run -- biginteger overflow OR over-long-expr parse) and
    zerolb ({0,N} empty-coefficient parse)."""
    if returncode == 0:
        m = rz._parse_metrics(stdout)
        if m:
            return "PASS", "-", "cons=%d prove=%dms" % (m["r1cs_cons"], m["prove_ms"])
        return "FAIL", "other", "exit0 but no metrics"
    err = stderr or stdout or ""
    if "index out of bounds: the len is 4" in err:
        return "FAIL", "ceiling", "BigInteger256 overflow (run==33 B)"
    if "expected unaried_term" in err or re.search(r"-->\s*\d+:\d+", err):
        code = _offending_line(err)
        if re.search(r"=\s+\*", code):                 # "f[i] =  * start[i]"
            return "FAIL", "zerolb", "empty coefficient ({0,N} miscompiled)"
        if "isZero" in code or "+ )" in code or re.search(r"\d{30,}", code):
            return "FAIL", "ceiling", "over-long packed run (>=34 B, dangling +)"
        return "FAIL", "parse", "Z# parse: " + code[:70]
    return "FAIL", "other", err.strip().splitlines()[-1][:90] if err.strip() else "rc=%d" % returncode


def run_case(binp, pat, kws):
    """Codegen + circ for one full-format regex; return (status, mode, detail)."""
    full = rz.assemble_parts(pat, kws, PROX)
    try:
        p, k, n = rz.extract_parts(full)          # sanity: must round-trip
    except Exception as e:
        return "FAIL", "codegen", "extract_parts: %s" % e
    z = subprocess.run([rz.TESTREGEX, "F", "0", "1"], input=p + " & " + k + "\n",
                       capture_output=True, text=True, timeout=rz.CODEGEN_TIMEOUT)
    if "Parse Successful!" not in z.stdout:
        return "FAIL", "codegen", (z.stderr or z.stdout)[:90]
    zok = rz._slice_zok(z.stdout)
    if zok is None:
        return "FAIL", "codegen", "no .zok emitted"
    zok = zok.replace("const u32 STR_LENGTH = 1000",
                      "const u32 STR_LENGTH = %d" % STR_LEN, 1)
    rz._atomic_write(os.path.join(rz.ZKMB_DIR, "policy%d.zok" % STR_LEN), zok)
    r = subprocess.run([os.path.abspath(binp), "policy_%d" % STR_LEN,
                        "true", "prover_verifier"], cwd=rz.CIRC_BUILD,
                       capture_output=True, text=True, timeout=rz.PROVE_TIMEOUT)
    return classify(r.returncode, r.stdout, r.stderr)


def write_log(results):
    """results: list of dicts. Write the limits summary, then every case."""
    n_match = sum(1 for r in results if r["match"])
    with open(LOG_FILE, "w") as f:
        f.write(gen_report_header("Zombie regex-to-circuit compiler limits"))
        f.write("\n\n")
        f.write(LIMITS_SUMMARY)
        f.write("\n")
        f.write("=" * 78 + "\n")
        f.write("VERIFICATION: %d/%d test cases matched the predicted behavior "
                "(str_len=%d, prox=%d).\n" % (n_match, len(results), STR_LEN, PROX))
        f.write("=" * 78 + "\n\n")
        hdr = ("%-4s %-22s %-12s %5s  %-7s %-9s  %-7s %-9s %-4s  %s"
               % ("#", "group", "pat", "runB", "pred", "pred-mode",
                  "actual", "act-mode", "ok?", "detail"))
        f.write(hdr + "\n")
        f.write("-" * len(hdr) + "\n")
        for r in results:
            f.write("%-4s %-22s %-12s %5s  %-7s %-9s  %-7s %-9s %-4s  %s\n"
                    % (r["id"], r["group"], r["pat"][:12], r["runb"],
                       r["pred"], r["pred_mode"], r["actual"], r["act_mode"],
                       "OK" if r["match"] else "XX", r["detail"]))
        mism = [r for r in results if not r["match"]]
        if mism:
            f.write("\nMISMATCHES (predicted != actual):\n")
            for r in mism:
                f.write("  ! %-4s pat=%-14s pred=%s/%s actual=%s/%s  %s\n"
                        % (r["id"], r["pat"][:14], r["pred"], r["pred_mode"],
                           r["actual"], r["act_mode"], r["detail"]))


def main():
    binp = rz.ensure_zombie_built(rz.VEC_SIZE)    # same sizes as on disk: no rebuild
    print("binary: %s\n" % binp)
    results = []
    for cid, group, pat, kws, runb, pred, pred_mode in CASES:
        status, mode, detail = run_case(binp, pat, kws)
        match = (status == pred) and (status == "PASS" or mode == pred_mode)
        results.append({"id": cid, "group": group, "pat": pat, "runb": runb,
                        "pred": pred, "pred_mode": pred_mode, "actual": status,
                        "act_mode": mode, "match": match, "detail": detail})
        print("%-4s %-22s %-12s runB=%-3s  pred=%-4s/%-9s actual=%-4s/%-9s  %s  %s"
              % (cid, group, pat[:12], runb, pred, pred_mode, status, mode,
                 "OK" if match else "XX", detail))
    write_log(results)
    n_match = sum(1 for r in results if r["match"])
    print("\n[verify_zombie_limit] %s : %d/%d matched prediction"
          % (LOG_FILE, n_match, len(results)))


if __name__ == "__main__":
    main()
