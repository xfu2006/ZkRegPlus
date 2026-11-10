# TODO — deferred defects and cleanup

Repo-root scratch list. **This file never reaches the artifact:** the
exporter runs `git archive HEAD:code/bora` (`prepare.py:65`,
`SOURCE_SUBDIR = "code/bora"`), so anything outside `code/bora/` is
outside the exported subtree by construction — not by a prune rule that
could be edited. Same reason `LOG` and `git_check.sh` never ship.

---

## 1. `big_to_dfa` uses a 64-bit hash as set identity — LATENT CORRECTNESS BUG

**Status 2026-11-09:** scheduled as ALL_T973 (GRP3 batch B3, 11/17). Fix =
key the map on the sorted `Vec<usize>` itself; DFA byte-diff vs HEAD on all
3 datasets. Design: PaperDiscussion align_implementation r21/r22.

**Where:** `code/bora/vendor/rustomaton/src/nfa.rs:96-160`
(`big_to_dfa` -> `big_to_dfa_new`; stock impl kept at `:161` as
`big_to_dfa_old`, `#[allow(dead_code)]`).

**What:** the NFA->DFA subset construction keys its set-to-state map on
`HashMap<u64, usize>`, where the `u64` is a `DefaultHasher` digest of the
sorted state vector (`Self::hash`, `:154`). The stock implementation keyed
on `HashMap<BTreeSet<usize>, usize>` — the actual set. The new code never
compares sets: `map.contains_key(&hash_other)` answers "have I seen this
hash", and the result is used as "have I seen this state subset".

**Consequence:** a 64-bit collision silently merges two distinct state
subsets into one DFA state, producing a wrong automaton with no error.
Incorrect by construction, not merely fragile.

**Why deferred (decided 2026-08-27, artifact deadline 08-28):** collision
probability is ~n^2/2^65 — roughly 3e-8 at 1e6 DFA states, 3e-6 at 1e7.
`DefaultHasher` is fixed-key SipHash, so construction is deterministic:
if it has not bitten, it will not spontaneously start. Inputs are ClamAV
signatures, not attacker-chosen. Changing automaton construction on the
ClamAV path the night before the deadline would require regenerating the
DFAs to prove the output is unchanged — hours of work to validate a ~5
line fix. Documented instead in `vendor/PATCHES.md` §3, which calls the
change out as the one behavioural edit in the vendor tree and states the
collision caveat explicitly.

**Fix when there is time:** keep the `u64` map for speed but store the
sorted `Vec<usize>` alongside the state id, and on a hash hit compare the
vectors; on mismatch, fall back to a second-level probe. Then confirm the
regenerated DFAs are byte-identical to the shipped ones.

**Optional, weaker, no behaviour change:** instrument one offline run to
assert set-equality on every map hit, and record "zero collisions observed
on the paper's automata" as evidence.

---

## 2. BP walk stops early — LATENT PROVER CRASH on matching inputs

**Status 2026-11-09: CLOSED (stale).** At HEAD neither walk has the early
`break` (neo :897, legacy :933 run to completion; r19/r20). Only a stale
comment remains at `discharge_adv.rs:930` (removed in GRP3 B3).

**Where:** `code/bora/crates/zkregplus/src/gadgets/discharge_adv_neo.rs:883`
`if del == 0 { break; }` (the "BP DESC" block), mirrored by
`discharge_adv.rs:984` `if item_to_del.locs.len()==0 {break;}`.

**What:** the backward-pruning walk descends from the deepest step and
stops at the first step that deletes nothing. A dead row at a LOWER step is
then never examined and stays labelled `C`. If such a dead row is a frozen
step's minimum, `apply_sp_pass` keeps it and demotes the LIVE row to
`Q_sp`; the next step's `C` row then has no predecessor in the final `Q_c`
and `fill_nonaggr` panics at `:1682`
`"nonaggr C row: no final-C predecessor"`.

**REPRODUCED 2026-09-03** (scratch copy, crate otherwise unmodified):
SDE `a1 .{1,9} a2 .{1,9} a3 .{1,9} a4`, one chunk 1..80, pat-locs
a1:{6,50}, a2:58, a3:66, a4:74 — a genuine chain 0->50->58->66->74. The
walk breaks at step 4 (66+9 >= 74) and never reaches step 1, where
6+9 = 15 < 58 should have pruned the 6. Post-SP step 1 keeps the dead 6 and
demotes the live 50. Panic.

**Not a soundness issue.** No proof is produced; the prover simply fails.
It cannot make a verifier accept bad advice.

**Why it matters beyond the crash:** the shipped generator therefore does
NOT implement the exact merged rule. Its carry is not chain-closed, which
is the property `:1596-1599` cites ("the min always reaches (min-chain
lemma)") to justify re-picking a `C` predecessor for every carried row.

**Why deferred (decided 2026-09-03, USENIX Sec'27 cycle):** the one-line
fix — delete both `break`s — was applied, tested and REVERTED, because it
regresses the aggressive arm. Measured on `cargo test -p zkregplus
--release gadgets::` (159 tests, fixtures present):
  pre-fix (control)   158 passed / 1 failed
  post-fix            157 passed / 2 failed
The new failure is `tests_neo_t301::test_t301_emits_zone_edges`
(`:11830`): `step2_locs` returns all 11 rows
`[5,8,14,23,37,44,55,61,70,83,max]` instead of the 7 zone edges
`[8,14,23,44,55,61,max]`. The test's own comment says "37, 70, 83 and 5
go"; post-fix they do not. 11 is exactly what `test_t301_control_dense_sat`
asserts under `DenseGuard::on()`, i.e. **the complete walk silently
defeats the zone-edge (windowed-join) row dropping** — the first of the two
optimizations `impl.tex:16-18` discloses. That is a table-size regression
on the AGGRESSIVE arm (the BP walk is shared by both arms), so it could
move measured constraint counts and timings. Not worth taking near a
deadline with the artifact frozen.

A second, smaller consequence: `discharge_adv.rs`'s `test_bwd_prf`
(`:5604 assert!(prf200.len()==0)`, "completely empty proof") encodes the
truncated walk. With the walk complete, measured values are prf200 0->2
(deletions `[0,0]`) and prf205 1->3 (deletions `[0,0,2]`, deleting item
moves to index 2); prf100 and prf206 are unchanged. Both `break`s must move
TOGETHER — `test_m5_oracle_backward`, `test_m5_oracle_random` and
`test_nonaggr_oracle_decision` compare neo against legacy byte for byte,
and fixing neo alone breaks two more `t301` tests (151/8).

**Fix when there is time:** (1) understand why a complete BP walk defeats
the zone-edge emitter on the aggressive arm, and either restore the
dropping or accept and re-measure; (2) delete both `break`s; (3) update
`test_bwd_prf` to assert `locs_to_del` emptiness rather than item counts,
preserving each example's intent; (4) re-run the full suite and confirm
constraint counts.

**Pre-existing, unrelated:** `tests_neo_t301::test_t301_bwd_emits_zone_edges`
(`:11923`) fails identically before and after this change, with the same
left/right values. It is failing in the repo today.

---

## 3. Other deferred items

- **`compactify` skipped above 1000 terms** —
  `code/bora/vendor/dependency/ark-relations/src/r1cs/impl_lc.rs:49`.
  Row values, sat/unsat verdict and `num_constraints` are all unchanged;
  only the matrix *representation* is non-canonical, so a nonzero-entry
  count read off the matrices is an upper bound. Documented in
  `vendor/PATCHES.md` §1. Open question: confirm no reported paper number
  is a constraint *density* rather than a count.
- **Dead instrumentation in the same function** (`impl_lc.rs:50-68`):
  unused `timer`, unused `new_len`, empty `if old_len>1000*20{}`.
  Cosmetic, but it sits beside the disabled stock function a reviewer
  auditing soundness would open first.
- **83 `DEBUG USE` / `TEMP PROBE` sites** across 6 live foldpot files
  (tags 62080, 62081, 69801, 69908) and more in `crates/`. All env-gated
  behind `ZKR_*`, which `scripts/PAPER_DATA.py:454` strips from the child
  env, so they cannot perturb a reviewer's run. Repo-wide decision;
  deferred rather than editing live prover files near a deadline.
- **`vendor/PATCHES.md` §2 omits two author-marked files** —
  `vendor/sonobe_mod/folding-schemes/src/utils/vec.rs` and
  `.../commitment/kzg.rs`.
- **`code/bora/attic/` has no README disclaimer** ("not used for any paper
  result"). Low value: `attic` is in `prepare.py`'s `PRUNE_PATHS`, so no
  reviewer sees it; matters only for the browsable git repo.
- **Stale LOC comment** at `impl.tex:23`: says "99918 across 68 files";
  `count_loc.py` prints 99,754 across 67 today. Rendered prose shows only
  `$99$k`, so the paper is unaffected.
