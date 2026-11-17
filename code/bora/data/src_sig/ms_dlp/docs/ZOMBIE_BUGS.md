# Two bugs in Zombie's regex-to-ZoKrates generator for the MS DLP rules

Bug 1 fails 1 of 8 randomly selected e-mails on 5 randomly sampled DLP rules.
The 8 e-mails were drawn from the 32 clean 1,000-byte e-mails, which are
raw Enron e-mails that BORA finds clean, and the 5 units from the 194. Here
"fails" means that Zombie's original circuit cannot produce a verifying
proof for a clean e-mail, so a clean e-mail is reported as a violation. All
80 runs behind this number use the real prover. On the full set, the
original circuits reject all 96 of the 96 drawn clean e-mails: each fails
at least 1 of the 194 units. At 1,000 bytes the median
is 2 failing units per e-mail (maximum 12), at 2,000 bytes the median is 4.5
(maximum 31), and at 4,000 bytes the median is 3 (maximum 28), 32 e-mails per
length. The full-set numbers come from the direct evaluator
(`docs/zombie_bugs/emails/fixture/zombie_check.tsv`). At 1,000 bytes every rejection comes from bug 1: the original circuits reject
106 of the 6,208 (e-mail, unit) pairs, every one fails only the `accum`
assertion, and all 32 e-mails are hit. Fix 1 alone and both fixes give 0
rejections (evaluator, `docs/zombie_bugs/scripts/zdoc/full1000.py`, output in
`docs/zombie_bugs/runs/full1000_eval.txt`). The same check at 2,000 and 4,000 bytes,
on the other 64 drawn e-mails and all 194 units, also gives 0 rejections for both
fix 1 alone and both fixes (`docs/zombie_bugs/scripts/evaluator/fixsim2.py`, output in
`docs/zombie_bugs/runs/fixsim2.txt`).


Source of the Zombie code. `src_sig/ms_dlp/zombie/` is a clone of upstream
Zombie (`src_sig/ms_dlp/zombie/UPSTREAM.txt`: PepperSieve/Zombie, commit
ae5ae94828aca2fb0d84e46c323b18a405f3309e), re-cloned by
`src_sig/ms_dlp/scripts/download_zombie.py`. Paths in this document are
relative to `code/bora/data/`. Evidence paths `docs/zombie_bugs/...` are
relative to `src_sig/ms_dlp/`. E-mail ids such as `1000_13` refer to
`docs/zombie_bugs/emails/fixture/emails/padded/<id>.eml` (original bytes in
`.../emails/orig/`, sources in `.../fixture/ids.tsv`), and `nz_near` refers
to `docs/zombie_bugs/emails/violation_tests/nz_near.eml`. The generated
circuits (original, fix 1, fix 1 and fix 2) are in
`docs/zombie_bugs/circuits_zok_orig_fix1_fix12.tgz` (directories `zok/`,
`zok_fix1/`, `zok_fix12/`, 194 files each). Prover logs are in
`docs/zombie_bugs/runs/`.

Since DLP_T999 the BORA artifact applies both fixes automatically:
`src_sig/ms_dlp/scripts/download_zombie.py` applies them (P5 and P6) after
cloning, `scripts/INSTALL.py` runs `download_zombie.py --patch-only` on a
kept tree, and `src_sig/ms_dlp/scripts/run_zombie.py` (`ensure_testregex`)
applies them before every Zombie run. So every Zombie number produced by the
artifact uses the fixed generator. (`scripts/INSTALL.py` is relative to
`code/bora/`.)

How the sample was drawn. Python `random.Random(1)`, then
`rng.sample(sorted 194 units, 5)` and `rng.sample(sorted 32 drawn 1,000-byte
e-mails, 8)` with the same generator (`docs/zombie_bugs/scripts/zdoc/draw.py 1`, output in
`docs/zombie_bugs/runs/draw_seed1.txt`). Seed 1 was
the first seed tried and is the one reported. We also computed seeds 2 and 3
with the evaluator only (no real-prover runs). Both give 0 of 8. The rate
per sample therefore varies. The full-set sentence above is the stable
number.

How rules are counted. We count each Zombie unit as one rule. The 194 units
come from 136 MS DLP rule definitions, because 19 definitions are split into
several units (names ending `/combNN`). The 5 drawn units belong to 5
different definitions. Two of them are each one part of a split definition
(Philippines passport `/comb00`, Australia driver's license `/comb09`).

Real-prover coverage. All 80 (e-mail, unit, circuit) runs of the sample
completed with the real prover. The fixed circuits give 40 of 40 true. The
original circuits give 39 true and 1 false (`1000_13` on the Czech driver's
license unit). The original Czech circuit needed more than 16 GB (peak
resident set about 20.9 GiB) and ran under a 40 GB cap. The 16 GB cap killed
it at key generation.
The direct evaluator agrees with the real prover on all 88 real-prover runs
completed in this work (80 sample runs and 8 evidence runs).

## What a Zombie DLP unit checks

Each of the 194 Zombie units is one (pattern, keyword list) pair taken from
an MS DLP rule. The rule fires when a pattern match lies within 300 bytes of
a keyword match, in either order. The harness (`src_sig/ms_dlp/scripts/run_zombie.py`) runs
`TestRegex F 0 1` on the input `PAT & KWS`, so regex 0 is the pattern, regex
1 is the keyword list, and (0, 1) is the one proximity pair. The generated
circuit asserts two things. First, `procCheck(f_A, f_B)` asserts that no
keyword match ending at byte offsets 300 to 699 has a pattern match ending
within 300 bytes of it (see "Other observations"). Second, `accum` must be
0. `accum` is meant to be the sum of the final tapes of all regexes that are
not in a proximity pair. Bug 1 below shows what it actually sums. Matching
starts after the first CR LF CR LF, and a match must start at least one
byte after it: the first body byte cannot start a match. A proof that verifies means
"this e-mail does not violate the unit".

Source files: `src_sig/ms_dlp/zombie/regex/src/builder/ZokWriter.C`,
`src_sig/ms_dlp/zombie/regex/src/builder/FABuilder.C`, and
`src_sig/ms_dlp/zombie/regex/src/Test.C`.

## Bug 1: finals of proximity regexes are also forced to zero

`src_sig/ms_dlp/zombie/regex/src/builder/ZokWriter.C` builds `proximitySet` from the pair (0, 1), so it holds regex
numbers (lines 5 to 10). Line 23 then tests the DFA state id `i` against
that set:

``
23      stateToLoop(fa, i, fa.finalStates.count(i) > 0, proximitySet.count(i) == 0);
``

State ids are not regex numbers. A final state whose id is not 0 or 1 is
treated as "not in a proximity pair", and line 269 adds its tape to `accum`.

Scope. The effect depends on the state ids of the two finals in each of the
194 original circuits.
- In 71 units neither final has id 0 or 1, so both final tapes go into
  `accum`. These circuits reject any e-mail whose body contains a pattern
  match or a keyword match anywhere (starting at least one byte after the
  first CR LF CR LF). Examples are
  Czech and Italy driver's license, Belgium VAT, and Philippines passport
  `/comb00`.
- In 122 units the pattern final is state 0, which happens to be in
  `proximitySet`, so only the keyword final goes into `accum`. These circuits
  reject any e-mail with a keyword in the body, but not an e-mail with only a
  pattern match. Two of the 5 drawn units are of this kind (Australia
  driver's license `/comb09`, Austria social security number).
- In 1 unit (Japan my number corporate, `procCheck(f_0, f_1)`) both ids are
  0 and 1, so nothing goes into `accum` and bug 1 has no effect.

Fix 1 removes 264 `accum` lines in total.

Example. The Czech driver's license unit has the pattern
`[A-Za-z][A-Za-z]\x20?[0-9]{6}` (regex 0, final state 3) and keywords such as
` driver license ` (regex 1, final state 122). The generated circuit
contains:

``
		f_3[i] = p_2[i] * (s_0[i - 6] + s_1[i - 6])
		accum = accum + f_3[i]
		...
		accum = accum + f_122[i]
	endfor
	assert(procCheck(f_3, f_122))
	assert(accum == 0)
``

Clean e-mail `1000_13` (Enron `symes-k/all_documents/3426.`, 909 bytes,
padded with 0x0A to 1,000 bytes) has its first CR LF CR LF at byte offset
456. Its body contains "disregard 584137" (offsets 597 to 612), and
`rd 584137` (offsets 604 to 612) matches the pattern. The e-mail contains no
keyword. `f_3` is nonzero at offset 612 and `f_122` is zero everywhere, so
`procCheck` passes but `accum` is nonzero. No proof can verify. This unit
has no single-class pattern line, so bug 2 plays no part. (Offsets from the
direct Python evaluator of the generated `.zok`.) The real prover gives
verify false on the original circuit (397,003 constraints) and verify true
with both fixes (193,195 constraints).

Fix 1. Test the regex number of the final being visited. `parseForest`
(`src_sig/ms_dlp/zombie/regex/src/builder/FABuilder.C:50-53`) parses the regexes in order, and states are only appended
(`src_sig/ms_dlp/zombie/regex/src/builder/FABuilder.C:16-17`), so finals are visited in regex order and
`regNumToFinalId.size()` is that regex's number. Line 34 already uses this
mapping for `procCheck`.

``
-      stateToLoop(fa, i, fa.finalStates.count(i) > 0, proximitySet.count(i) == 0);
+      stateToLoop(fa, i, fa.finalStates.count(i) > 0, proximitySet.count(regNumToFinalId.size()) == 0);
``

After fix 1 the Czech circuit drops both `accum` lines, and e-mail `1000_13`
verifies.

How the two bugs interact (Italy). The Italy driver's license unit has the
pattern `[A-Za-z][A-Za-z0-9][\x2D\x20]?[A-Za-z0-9]{7}[\x2D\x20]?[A-Za-z]`
(regex 0, final state 6) and keyword final state 130. Both finals go into
`accum`. Clean e-mail `1000_02` (Enron `giron-d/inbox/472.`, 959 bytes) has
its first CR LF CR LF at offset 613, and its body starts at offset 617 with
"We've updated the Merger Q&A document on our Enron Updates site". It
contains no keyword. The string `ve updated t` (ending at offset 631) fits
the true ID shape. In the original circuit, however, `f_6` does not fire
there. Bug 2 complements the single-class atoms of this pattern (the final
`[A-Za-z]` becomes `p_3[i] = 1 - t_2[i]`), so `f_6` fires at 8 other
positions, the first at offset 713 (the `/` after `updates`). With fix 1
alone, `f_6` fires at the same 8 positions, no keyword is near, and the
e-mail is accepted. With both fixes, `f_6` fires at 19 positions, including
offset 631. (Positions from the evaluator.) The real prover gives verify
true with fix 1 and with both fixes (203,325 constraints each). The original
circuit (415,826 constraints) did not fit the 16 GB cap here. An earlier
real-prover log of it on the same e-mail is reported in
`docs/zombie_bugs/runs/zreal/logs2/sit-defn-italy-drivers-license-number.1000_02.log`
with verify false. The script and memory cap of
that run are not recorded in the artifacts.

## Bug 2: a single-class pattern is complemented

In a multi-atom pattern, a character-class atom becomes the mismatch term
`(1 - t_k[i - n])` inside `isZero(sum)` (`src_sig/ms_dlp/zombie/regex/src/builder/ZokWriter.C:202`). This is correct:
the sum is 0 only when every atom matches (exact for up to 31 literal atoms,
see "Other observations" on field wrap-around). A pattern
that is one class only takes the shortcut at line 188:

``
188     std::cout << "\t\tp_" << patId << "[i] = 1 - t_" << classToId[pattern[0]] << "[i]" << std::endl;
``

This drops the `isZero`, so the tape is the mismatch indicator: it is 1 on
every byte that is not in the class.

Example. The New Zealand inland revenue unit has the pattern
`[0-9]{2,3}[\x2D\x20]?[0-9]{3}[\x2D\x20]?[0-9]{3}`. The separator class
`[\x2D\x20]` and the optional third digit `[0-9]` are single-class patterns:

``
		t_0[i] = isZero((t[i] - 32) * (t[i] - 45))
		p_2[i] = 1 - t_0[i]
		...
		p_1[i] = 1 - t_1[i]
``

So the optional separator matches any byte except `-` and space, and the
pattern no longer matches `713-750-514`. The test e-mail `nz_near` (1,000
bytes) is a real Enron header followed by a body of "ok see you at noon."
repeated, with " ird number 713-750-514 " inserted. It violates the rule:
the keyword ` ird number ` ends at byte offset 511 and the ID ends at offset
522. With fix 1 alone, the keyword final `f_15` is nonzero at offset 511
but the ID final `f_8` is zero everywhere, so `procCheck` passes and the
proof verifies: a missed violation. With fix 1 and fix 2, `f_8` is nonzero
at offset 522, `procCheck` fails, and the proof does not verify. (Offsets
from the evaluator. Verify results from the real prover, see the table.) In
the original circuit the same e-mail is rejected only because of bug 1,
since `f_15` is added to `accum`.

Fix 2. Emit the match indicator itself. This is a 0 or 1 match indicator
for the class-tape forms that occur in the Dlp units (see "Other
observations" for the one form that is not 0 or 1).

``
-    std::cout << "\t\tp_" << patId << "[i] = 1 - t_" << classToId[pattern[0]] << "[i]" << std::endl;
+    std::cout << "\t\tp_" << patId << "[i] = t_" << classToId[pattern[0]] << "[i]" << std::endl;
``

Scope. 57 of the 194 units contain such a line (79 lines in total). Bug 2
can also create false matches, as the Italy example shows.

## Evidence: real-prover runs

All runs use the real Spartan prover in a scratch Zombie copy, with the real
e-mail bytes as witness, at 1,000 bytes, on cpus 12 to 15, except the
earlier original-Italy log, whose script and cpus are not recorded. The
8 original-Czech runs under the 40 GB cap were run by us with
the same command (cpus 12 to 15, key generation on `1000_13`, the other 7
reusing the keys). "Constraints" is
the R1CS count after linearity reduction. "true" means the proof verified,
so the circuit accepts the e-mail.

Evidence runs (each cell is the verify result, with the constraint count in
parentheses where that run did key generation):

| Unit | E-mail | Original | Fix 1 | Fix 1 and fix 2 |
|---|---|---|---|---|
| New Zealand inland revenue | `nz_near` (violates the rule) | false (43,870) | true (33,349) | false (33,349) |
| New Zealand inland revenue | `1000_02` (clean) | true | true | true |
| Italy driver's license | `1000_02` (clean) | not completed, 16 GB cap (415,826). Earlier log reports false | true (203,325) | true (203,325) |

Sample runs (seed 1, 8 e-mails `1000_32`, `1000_25`, `1000_15`, `1000_16`,
`1000_21`, `1000_13`, `1000_26`, `1000_07`):

| Unit | Constraints original | Constraints fixed | Original circuit, 8 e-mails | Fixed circuit, 8 e-mails |
|---|---|---|---|---|
| Belgium VAT number | 52,688 | 40,374 | 8 true | 8 true |
| Philippines passport `/comb00` | 85,274 | 64,283 | 8 true | 8 true |
| Australia driver's license `/comb09` | 201,485 | 93,611 | 8 true | 8 true |
| Czech driver's license | 397,003 | 193,195 | 7 true, `1000_13` false (40 GB cap) | 8 true |
| Austria social security number | 83,722 | 43,860 | 8 true | 8 true |

All 194 fixed units verify true on e-mails `1000_01` to `1000_04` (776 of
776 real-prover runs, `docs/zombie_bugs/runs/zfix_eval/acceptance_fixed_1k.tsv`).

Extra violation tests on 3 more units
(`docs/zombie_bugs/runs/zfix_eval/violations.tsv`, e-mails in
`docs/zombie_bugs/runs/zfix_eval/viol3/`): Malta driver's license,
Australia driver's license `/comb12`, and Austria passport. For each, a
"near" e-mail with an ID within 300 bytes of a keyword is rejected by both
circuits, and a "far" e-mail with the two farther apart is accepted by the
fixed circuit and rejected by the original one (bug 1). The table also
repeats the Italy, Indonesia and New Zealand cases with the fixed circuits.

## What the fixes do not change

Both fixes change only the `.zok` text. The regex parser, the DFA, the class
tapes, the multi-atom pattern tapes, `procCheck`, the 300-byte window, the
start after the first CR LF CR LF, and the 1,000-byte input are unchanged.
Fix 1 only removes `accum` lines for finals in a proximity pair. In these
units both regexes are in the pair, so `accum` becomes the constant 0. Fix 2
changes one linear expression per affected line and adds no constraints.
Measured here: Italy has 203,325 constraints with fix 1 and 203,325 with
both fixes, and New Zealand has 33,349 with fix 1 and 33,349 with both.

## Other observations (not analysed further)

- Proximity window. `spread` and `procCheck` (`src_sig/ms_dlp/zombie/regex/src/builder/ZokWriter.C:48-49`) test only
  keyword end positions 300 to 699 of a 1,000-byte input, with pattern ends
  from 300 bytes before to 299 bytes after. A violation whose keyword ends
  outside 300 to 699 is not caught. Measured on the Austria passport unit
  (`docs/zombie_bugs/runs/zfix_eval/viol3/austria_early.eml` and
  `austria_late.eml`, positions in `python_re_window.json`): the ID and the
  keyword are 60 bytes apart, with the keyword ending at byte 290 or byte
  820. Python `re` finds the rule's match in both, and the fixed circuit
  accepts both. The original circuit rejects both, but only because bug 1
  rejects any keyword anywhere, which hid this gap.
- Field wrap-around. A multi-atom pattern is one weighted sum inside
  `isZero`, with weight 256 per literal byte and 2 per class atom, and a new
  `isZero` group only after 33 atoms (`src_sig/ms_dlp/zombie/regex/src/builder/ZokWriter.C:212-216`, marked "TO DO").
  18 pattern lines in 14 original units use a weight of 256^31 = 2^248, for
  example `p_8` of the Philippines national identification number unit. All
  18 are 32-byte literal strings (for example the keyword
  ` canadian financial institution `), and in each the 2^248 term is the
  trailing space `(t[i - 0] - 32)`. Since 255 x 2^248 exceeds the field size
  (about 2^252), a non-matching string could in principle sum to 0 and
  count as a match. The sum is exact for up to 31 literal atoms.
- Large classes. Classes with 239 to 255 members (for example a negated
  class such as `[^a]`) take a different tape branch (`src_sig/ms_dlp/zombie/regex/src/builder/ZokWriter.C:112-121`),
  which emits a bare product with no `isZero`, so the tape is not 0 or 1.
  The full 256-member set is handled separately. No Dlp unit reaches that
  branch: all 373 class-tape lines in the 194 generated files are `isZero` or
  `inRange` forms.

## Cost impact (measured)

All 194 units, original and fixed (fix 1 and fix 2) circuits, real prover,
cpus 0 to 11. Per-unit data:
`docs/zombie_bugs/runs/zfix_eval/constraints_1k.tsv` (1,000 bytes) and
`docs/zombie_bugs/runs/zfix_eval/constraints_2k.tsv` (2,000 bytes), parsed
by `docs/zombie_bugs/runs/zfix_eval/scripts/parse.py` and `parse2.py`.
"Ratio" is fixed over original.

At 1,000 bytes:

| Quantity | Units with both | Original total | Fixed total | Total ratio | Per-unit ratio median, mean, range |
|---|---|---|---|---|---|
| Constraints after linearity reduction | 192 | 28,467,572 | 15,404,224 | 0.541 | 0.609, 0.628, 0.432 to 1.000 |
| Variables | 184 | 53,933,330 | 27,712,235 | 0.514 | 0.528, 0.560, 0.437 to 1.000 |
| Padded Spartan instance (constraints) | 184 | 33,488,896 | 19,333,120 | 0.577 | 0.500, 0.671, 0.500 to 1.000 |

- The smallest constraint ratio is Canada driver's license `/comb00`
  (395,817 to 171,060). The ratio is 1.000 only for Japan my number
  corporate, the one unit bug 1 does not affect.
- The padded Spartan instance halves for 121 of the 184 units and is
  unchanged for 63. For all 184, the original instance size equals the
  `r1cs_cons` of the jet1tb run of 07/02
  (`docs/zombie_bugs/runs/zfix_eval/jet1tb_1k.tsv`).
- Units lacking original counts. Ireland and Italy driver's license have no
  original constraint count, because their original run under a 29 GB cap
  was stopped (signal 15) before the count was printed. Our earlier run
  gives 415,826 for Italy (Evidence section). 8 more units (Poland,
  Portugal `/comb00` and `/comb01`, Romania, Slovakia, Spain, Sweden and US
  driver's license) have an original constraint count but no variable,
  instance or key-generation data, because their original key generation was
  killed at the 16 GB cap. For all 10, jet1tb gives an original instance of
  524,288. The fixed instance is 262,144 (131,072 for US).
- Key-generation peak memory. Example: Czech driver's license 21,895,308 kB
  original and 9,638,544 kB fixed. The largest fixed value over all 194 units
  is 11,578,568 kB (Germany driver's license, original 26,736,732 kB). The
  total fixed over original over all 194 units is 0.504. For units whose
  original run was killed, the original value is the value at the kill.

Prove and verify time at 1,000 bytes, on a sample of 10 units drawn with
seed 61430 (`docs/zombie_bugs/runs/zfix_eval/prove_verify_1k.tsv`). Keys are
reused, the witness is e-mail `1000_01`, and each value is the median of 3
runs on cpus 0 to 11. All 60 runs verify true.

| Quantity | Original total | Fixed total | Total ratio | Per-unit ratio median, range |
|---|---|---|---|---|
| Prove time | 22,468 ms | 10,767 ms | 0.479 | 0.484, 0.403 to 0.988 |
| Verify time | 9,685 ms | 4,156 ms | 0.429 | 0.453, 0.394 to 1.000 |

At 2,000 bytes, on a sample of 10 units, with the default witness of the
`policy_2000` mode and a 28 GB cap:
- 6 units finished in both versions. Their constraints total 911,684
  original and 772,167 fixed (ratio 0.847, per-unit 0.793 to 0.882). The
  original instance sizes equal jet1tb's. Single-run prove time totals
  21,205 ms original and 15,616 ms fixed (ratio 0.736).
- 4 units were killed at the 28 GB cap in both versions (Denmark personal
  identification number, Indonesia driver's license `/comb01`, Canada
  driver's license `/comb08` and `/comb13`). jet1tb gives original instances
  of 524,288, 524,288, 1,048,576 and 1,048,576.

## Reproduction

The archived scripts in `docs/zombie_bugs/scripts/` were run from a session
scratch directory and still contain its absolute paths. Map them as follows.

| Path in the scripts | Archived copy or source |
|---|---|
| `<scratch>/same_sample/fixture/` | `docs/zombie_bugs/emails/fixture/` |
| `<scratch>/same_sample/scripts/` | `docs/zombie_bugs/scripts/evaluator/` |
| `<scratch>/zdoc/scripts/`, `<scratch>/zdoc/rev_eval.py` | `docs/zombie_bugs/scripts/zdoc/` |
| `<scratch>/zdoc/runs/` | `docs/zombie_bugs/runs/` |
| `<scratch>/zreal/logs2/`, `logs3/`, `viol/`, `viol2/` | `docs/zombie_bugs/runs/zreal/logs2/` and so on |
| `<scratch>/zreal/viol2/*.eml` | `docs/zombie_bugs/emails/violation_tests/` |
| `~/tmp/same_sample_work/zok/`, `zok_fix1/`, `zok_fix12/` | `docs/zombie_bugs/circuits_zok_orig_fix1_fix12.tgz` |
| `~/tmp/same_sample_work/zcopy/zombie/` (scratch Zombie copy) | rebuild, see step 1 |
| `<scratch>/zdoc/gen/g0`, `g1`, `g12` (generator copies) | rebuild, see step 2 |
| `<scratch>/zdoc/rundirs/` (prover keys) | not archived, recreated by `runs.sh` |

1. Scratch Zombie copy with the real-witness test arm. Copy
   `src_sig/ms_dlp/zombie/` to a scratch directory, apply
   `docs/zombie_bugs/patches/zkmb_real_witness_arm_test_only.patch` from the
   copy's root (`patch -p1`, it changes `circ/src/zkmb.rs` only), and build
   `circ_executable` the way `src_sig/ms_dlp/scripts/run_zombie.py` builds
   it. The patch adds the test-only mode `policy_1000_real`. It reads the
   e-mail named by `ZREAL_EMAIL`, pads it with 0x0A to 1,000 bytes, uses it
   as the witness, and prints `DEBUG USE 61427.x` lines (R1CS satisfiability,
   key-generation time, verify result).

2. Generator copies. Copy `src_sig/ms_dlp/zombie/regex/` three times. Leave
   the first unchanged. In the second apply only the first hunk of
   `docs/zombie_bugs/patches/ZokWriter_fix1_fix2.patch` (fix 1,
   `src_sig/ms_dlp/zombie/regex/src/builder/ZokWriter.C:23`). In the third apply the whole patch (fix 1 and fix 2,
   `src_sig/ms_dlp/zombie/regex/src/builder/ZokWriter.C:23` and `:188`). The patch paths start with `regex/`, so apply
   it with `patch -p1` from the parent of `regex/`. Build each copy with
   `make` and regenerate all 194 units:

   ``
   taskset -c 12-15 python3 -I docs/zombie_bugs/scripts/zdoc/gen_patched.py <copy>/bin/TestRegex <out dir>
   ``

   The unchanged build reproduces `zok/` of the archived tarball byte for
   byte, and the patched builds reproduce `zok_fix1/` and `zok_fix12/` byte
   for byte (0 differing files of 194 each).

3. Draw the sample: `python3 docs/zombie_bugs/scripts/zdoc/draw.py 1` (prints
   the 5 units, the 8 e-mails, and the evaluator prediction).

4. Real-prover runs: `docs/zombie_bugs/scripts/zdoc/runs.sh`. For each
   (variant, unit) it copies the `.zok` to
   `<run dir>/<variant>_<unit>/zkmb/policy1000.zok` and runs, from that
   directory,

   ``
   ZSHARP_STDLIB_PATH=<zombie copy>/circ/third_party/ZoKrates/zokrates_stdlib/stdlib \
   ZREAL_EMAIL=<padded e-mail> /usr/bin/time -v systemd-run --user --scope -q -p MemoryMax=16G -p MemorySwapMax=0 \
     taskset -c 12-15 <zombie copy>/circ/target/release/circ_executable \
     policy_1000_real <true for the first e-mail, else false> prover_verifier
   ``

   Logs are in `docs/zombie_bugs/runs/<variant>.<unit>.<e-mail>.log` (a `/`
   in a unit name is written as `__`), one line per run in
   `docs/zombie_bugs/runs/summary.tsv`. The original Czech circuit was tried
   twice under the 16 GB cap (`1000_32`, `1000_25`) and killed both times
   (exit 137). A third attempt was stopped by hand
   (`...1000_15.KILLED_BY_ME.log`). The rest of the sample was finished by
   `docs/zombie_bugs/scripts/zdoc/runs2.sh`.

5. Original Czech circuit under a 40 GB cap. From the run directory of the
   original Czech circuit, with the same `ZSHARP_STDLIB_PATH`, run key
   generation on `1000_13` first, then reuse the keys for the other 7
   e-mails:

   ``
   ZREAL_EMAIL=docs/zombie_bugs/emails/fixture/emails/padded/1000_13.eml \
     systemd-run --user --scope -q -p MemoryMax=40G -p MemorySwapMax=0 \
     taskset -c 12-15 <zombie copy>/circ/target/release/circ_executable \
     policy_1000_real true prover_verifier
   # then the same command with each other e-mail and "false"
   ``

   Logs: `docs/zombie_bugs/runs/old_czech_<e-mail>_40G.log`. Only the
   `1000_13` log records the command (`/usr/bin/time -v`). The other 7 logs
   hold only the program output. We ran them with the same command and
   `false`.

6. Final-tape positions (evaluator):
   `python3 docs/zombie_bugs/scripts/zdoc/finals.py docs/zombie_bugs/scripts/evaluator <unit> <e-mail file>`.
   Evaluator against every real-prover run:
   `python3 docs/zombie_bugs/scripts/zdoc/rev_eval.py <scratch>` (prints
   `agree 88 disagree 0 no real result 3`. The 3 are the original Italy run
   and the two original-Czech runs killed at 16 GB). The scripts expect the
   scratch layout above, so restore it from the mapping first.
