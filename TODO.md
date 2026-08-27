# TODO — deferred defects and cleanup

Repo-root scratch list. **This file never reaches the artifact:** the
exporter runs `git archive HEAD:code/bora` (`prepare.py:65`,
`SOURCE_SUBDIR = "code/bora"`), so anything outside `code/bora/` is
outside the exported subtree by construction — not by a prune rule that
could be edited. Same reason `LOG` and `git_check.sh` never ship.

---

## 1. `big_to_dfa` uses a 64-bit hash as set identity — LATENT CORRECTNESS BUG

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

## 2. Other deferred items

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
