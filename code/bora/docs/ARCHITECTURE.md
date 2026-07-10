# Architecture

## Workspace crates (`crates/`)

- **`data_processor/`** — ClamAV signature parsing, PCRE handling, AC-DFA
  construction over hex nibbles, and the "discharge" prover logic (proving
  a file matches no signature). `clam_db.rs` is the central preprocessed
  DB shared with the circuit layer.
- **`zkregplus/`** — the ZKP framework. Entry point is
  `zkp_driver::zkp_driver{,_adv}`. `src/circs/` holds **gadget mappers**
  (CP, SED, DFA, and a `composable_gadget_mapper` that stitches them);
  `src/gadgets/` holds the actual R1CS gadgets (word extractor, FSM, pack,
  sigs, discharge, etc.). Each mapper has a `*Capacity` struct — circuit
  sizing is driven by these capacities, not the input data.
- **`utils/`** — shared logging (`log(job_id, level, msg)` with levels
  `ERR`..`LOG7`), timers, nibble/field packing, and
  **`consts::GlobalConfig`**, a process-wide `RwLock<GlobalConfig>`
  (access via `get_global_config()` / `read_global_config()`) that
  controls `log_level`, `range2_bit`, `b_light_test`, `b_read_cache`,
  snark cache, and parallelism knobs. Setting fields on this config is how
  the runners tune runs — there is no CLI flag layer.

(A fourth crate, `paper_data_gen`, was retired to `attic/`.)

## End-to-end run

1. `data/src_sig/` ClamAV signatures → `data_processor::clamav` parses
   them → `ClamavDB` preprocesses patterns, AC-DFAs, and critical-pattern
   maps (`dfa_crit`, `dfa_crit_igc`).
2. `data_processor::discharge_prover` non-ZK-"discharges" a target file
   against the DB, producing `WordInfo` traces per file (which subsigs
   match, which do not, and which evidence words prove it). This step is
   what the ZK circuit re-verifies.
3. `zkregplus::zkp_driver` packs the file as nibbles (via
   `utils::data::pack_nibbles`), then builds a list of folded circuits via
   `build_circs_adv`. Each circuit is a `SigmaIR1CS_Inst` wrapping a
   `CompositeGadgetMapper` that composes up to four sub-mappers: **CP**
   (critical-pattern, with an `igc` variant for ignore-case), **SED**
   (subsig-evaluation discharge), and optionally **DFA**.
4. `folding_schemes::folding::foldpot::driver::foldpot_main` folds the
   circuits incrementally; the decider is Groth16 over BN254 with KZG
   commitments on the BN254 side and Pedersen on Grumpkin. Curve types are
   plumbed through as generics `C1=Projective (BN254)`,
   `C2=Projective2 (Grumpkin)`, `GC1=GVar`, `GC2=GVar2` — see
   `crates/zkregplus/examples/main.rs` for the canonical parameterization.

## Capacity structs

`CpCapacity`, `SedCapacity`, `DfaCapacity` are **declared by the caller**
(the runner) and drive circuit size. `SedCapacity::new(...)` takes
empirical coefficients (`basis_unique_states`, `basis_acc_states`,
`basis_pats_in_trace`, `perc_pats_expansion_rate`) tuned per dataset.
`decreased_copy(level)` on each capacity is how `build_circs_adv` produces
a descending ladder of circuits across categories/layers.

## Data directory

- `data/src_sig/` — ClamAV + MS-DLP source signatures.
- `data/samples/` — CentOS binaries and Enron emails used as scan targets.
- `data/debug/` — smaller pre-baked configs the `small_*`/`full_*` runners
  point at.
- `data/cache/` — DFA and key caches (not in git; regenerated on demand;
  `get_global_config().b_read_cache` toggles reading).
