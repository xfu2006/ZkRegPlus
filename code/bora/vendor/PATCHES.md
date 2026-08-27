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

**What they change:** cherry-picked forks that **add pairing support in
R1CS** for BN254/Grumpkin (needed by the Groth16 decider and the cyclefold
circuits here), on top of arkworks v0.4.0, without pulling in unrelated
post-v0.4.0 changes that would break compatibility.

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
signature pipeline.

## Workspace exclusions

The root `Cargo.toml` excludes `data/src_sig/chr17_variants/reef` from
the workspace: it is a vendored third-party crate (Reef, MIT) that the
dna dataset unpacks inside this repo, and Cargo would otherwise abort
with "current package believes it's in a workspace when it's not".
