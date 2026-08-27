# Vendored / patched dependencies

Three vendoring mechanisms cooperate; breaking any one causes link-time
surprises. All are bound to Rust **1.76.0** — do not bump versions without
regenerating the forks.

## 1. arkworks forks (`vendor/dependency/`)

The root `Cargo.toml` `[patch.crates-io]` redirects these crates to local
paths under `vendor/dependency/`:

- `ark-r1cs-std`  → `vendor/dependency/r1cs-std`
- `ark-bn254`     → `vendor/dependency/ark-curves-cherry-picked/bn254`
- `ark-grumpkin`  → `vendor/dependency/ark-curves-cherry-picked/grumpkin`
- `ark-relations` → `vendor/dependency/ark-relations`

**What they change:** `ark-r1cs-std` and the two cherry-picked curve crates
**add pairing support in R1CS** for BN254/Grumpkin (needed by the Groth16
decider and the cyclefold circuits here), on top of arkworks v0.4.0, without
pulling in unrelated post-v0.4.0 changes that would break compatibility.

`ark-relations` is the exception: it is **hand-edited in the constraint-system
core and none of it is about pairings**. Every measurement in the paper is
built on top of these edits, so they are listed in full:

- `src/r1cs/constraint_system.rs:75,85` — `lc_map` and `lc_assignment_cache`
  change from `BTreeMap<LcIndex, _>` to an index-addressed `Vec<Option<_>>`;
  the unused `cache_map` is dropped. `LcIndex` is allocated densely from 0, so
  this is a lookup-cost change only — the stored LCs and the ascending-index
  iteration order match the `BTreeMap`. The inlining loop
  (`transform_lc_map_old_worker`, `:384-500`) is rewritten to walk `0..=max_idx`
  and skip `None` slots; a deleted LC becomes `None` instead of a removed key.
- `src/r1cs/constraint_system.rs:284-291` — the `#[cfg(feature = "std")]`
  `ConstraintTrace::capture()` call in `enforce_constraint` is commented out
  (setting `default-features = false` on `ark-r1cs-std` did not disable it), so
  `constraint_traces` stays empty. Diagnostics only: the reader at `:1111`
  already guards on the vector's length, and `:1114` says so in the message.
- `src/r1cs/constraint_system.rs:469,486` — `transform_lc_map` is narrowed to
  the *inlining* case. New witness variables are no longer accepted:
  `assert!(num_new_witness_variables == 0)`, and the outlining branch is
  commented out. Nothing in this build outlines — `inline_all_lcs` (`:902`)
  passes an empty transformer and `OptimizationGoal` is never set away from its
  default — and the assert makes a violation loud rather than silent.
- `src/r1cs/impl_lc.rs:49-51` — `LinearCombination::compactify` runs its
  sort-and-dedup **only when the LC has at most 1000 terms**; longer LCs are
  returned untouched (the stock body is retained as `compactify_old`). This is
  the one edit that changes what the R1CS *looks like*: a long row may carry
  unsorted and duplicated column entries. Its **value is unchanged** — a row is
  evaluated as a sum, so duplicates add back to the same field element and the
  satisfied/unsatisfied verdict is identical — but the matrices are no longer
  in canonical form, so a nonzero-entry count read off them is an upper bound,
  not the stock arkworks figure. `num_constraints` is unaffected.
- `src/r1cs/mod.rs:32` — `LcIndex` additionally derives `Hash`.
- Not on the measured path: `report_max_lc_len` (`constraint_system.rs:322`, a
  debug probe) and the rayon-parallel inliners `transform_lc_map_new_1` /
  `_new_2` (`:506`, `:647`), both dead — the dispatcher at `:352` hard-codes
  `b_new = false` because the single-threaded version measured faster.

**Net effect on semantics:** the constraint system this fork builds is the one
stock ark-relations v0.4.0 would build, with a single representation-level
exception (rows over 1000 terms left uncompactified, above), which changes a
row's encoding but not its value.

## 2. Sonobe fork — `foldpot` (`vendor/sonobe_mod/`)

A fork of [Sonobe](https://github.com/privacy-scaling-explorations/sonobe)
forked at commit `21ff3cf1ab825dd1c741cf0f028ac5934ef0f19d`. It **adds the
`foldpot` folding scheme** in
`vendor/sonobe_mod/folding-schemes/src/folding/foldpot/` — a modified
SuperNova + CycleFold with lookups (Hab22 / CQ / Mangrove).

`crates/zkregplus` depends on `folding-schemes` by path, with the
`light-test` feature by default. Switching to the full (non-light) build
is the commented dependency line in `crates/zkregplus/Cargo.toml` and
requires ~250 GB RAM.

Note: `folding-schemes` also has a path dependency on the workspace
`utils` crate (`../../../crates/utils`).

**License-compliance removal:** upstream Sonobe ships two circuit
frontends this project does not use — `frontend/circom` (pulls
`circom`, **GPL-3.0**) and `frontend/noname` (pulls `noname`, **no
license**). Both were removed (the `pub mod circom;`/`pub mod noname;`
lines in `folding-schemes/src/frontend/mod.rs`, the `ark-circom`/
`ark-noname`/`noname` dependencies, and the corresponding example
targets) so the artifact is free of strong-copyleft / unlicensed code.
The `FCircuit` trait (the only part used here) is unaffected.

**Test-only dependency fix:** `folding-schemes/Cargo.toml` gained
`num-bigint = { version = "0.4", features = ["rand"] }` under
`[dev-dependencies]`.  The `#[cfg(test)] mod tests` in
`src/folding/circuits/nonnative/uint.rs` imports
`num_bigint::RandBigInt`, which lives behind that feature, so
`cargo check --all-targets` (and `cargo test`) failed to compile the
crate's lib-test target upstream.  Dev-dependencies are absent from
the release build graph, so no shipped code or measurement changes.

## 3. ClamAV-pipeline forks (`vendor/{rustomaton, aho-corasick}`)

`vendor/{rustomaton, aho-corasick}` are local forks used by the ClamAV
signature pipeline. `crates/data_processor` depends on both by path. Every
edit is marked in-source with a `BORA paper author` comment; the full list:

**`aho-corasick` (fork of 1.1.2) — additive / API-only.** No matching or
construction code is touched; these exist only so `data_processor` can read
the automaton out of the crate.

- `src/util/mod.rs:9` — `pub(crate) mod primitives` widened to `pub mod
  primitives`.
- `src/dfa.rs:190` — added `pub fn num_states()`, returning `self.state_len`.
- `src/util/primitives.rs:736` — added `state_id_to_usize`,
  `pattern_id_to_usize`, `state_id_from_usize`, `pattern_id_from_usize`.

Consumers: `crates/data_processor/src/hex_acdfa.rs` (nibble AC-DFA
construction).

`Cargo.lock` deliberately carries two `aho-corasick` entries — `1.1.2` with no
`source` (the path fork, used by `data_processor`) and `1.1.3` from crates.io
(pulled in by `regex-automata 0.4.7` under `regex`) — because
`[patch.crates-io]` covers only the four arkworks crates, so transitive users
keep the registry copy.

**`rustomaton` (fork of 0.2.1) — one behavioural change, the rest additive.**

- `src/nfa.rs:96-101` — **behavioural.** `big_to_dfa` now dispatches to a new
  `big_to_dfa_new`; the stock body is kept as `big_to_dfa_old`
  (`#[allow(dead_code)]`, `:161`). The subset construction keys its
  set-to-state map on a 64-bit `DefaultHasher` digest of the sorted state
  vector instead of on a `BTreeSet<usize>`, which is what makes large NFA
  determinisation tractable here. Two consequences a reviewer should know:
  a 64-bit digest collision would merge two distinct state subsets (never
  observed on our datasets, but it is a hash, not a set comparison); and the
  alphabet is now iterated in sorted order, so state numbering is
  deterministic where the stock `HashSet` iteration was not.
- `src/dfa.rs:21` — added `MyHashSet`, a `HashSet<usize>` newtype with an
  order-independent `Hash`, used as a partition key.
- `src/dfa.rs:43` — `DFA`'s fields made `pub` and a `pub raw_str: String`
  field added, carrying the source regex for debugging and reporting. Set at
  `crates/data_processor/src/clamav.rs:655` and `pcre.rs:1292`.
- `src/dfa.rs:84` — added `get_shortest_accepted()` (shortest accepted word
  via `fast_paths`). No caller.
- `src/dfa.rs:123` — added `intersect2()`, a product construction. No caller.
- `src/dfa.rs:190` — added `build_reverse_trans()`, the reverse-transition
  table used by Hopcroft.
- `src/dfa.rs:227` — added `partition_to_mapping()`, a Hopcroft helper.
- `src/dfa.rs:247` — added `dump()`, a small-DFA debug viewer.
- `src/dfa.rs:257` — added `minimize_hop()`, Hopcroft minimisation. Its only
  call site (`clamav.rs:2286`) is commented out, so it is off the measured
  path; the stock `minimize()` is unchanged and still used.

Except for `big_to_dfa`, nothing above replaces or edits an upstream code
path — the stock functions are all still present and still what gets called.

**Nested fourth fork:** `vendor/rustomaton/dependency/logos-0.10.0` is a local
copy of `logos` + `logos-derive` 0.10.0 (28 files), which `rustomaton` depends
on by path, and it is itself modified: `logos-derive/src/util.rs:97-102`
replaces the `panic!("Only one callback can be defined per variant
definition!")` with a plain `let _ = self.callback.insert(callback)`, so a
second `callback` attribute on a variant now silently overrides the first
instead of aborting the build. `LICENSE-MIT` and `LICENSE-APACHE` ship with
the copy; this note is the Apache-2.0 §4(b) change notice.

## Workspace exclusions

The root `Cargo.toml` excludes `data/src_sig/chr17_variants/reef` from
the workspace: it is a vendored third-party crate (Reef, MIT) that the
dna dataset unpacks inside this repo, and Cargo would otherwise abort
with "current package believes it's in a workspace when it's not".
