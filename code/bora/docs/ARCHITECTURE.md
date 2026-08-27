# Architecture

## A. Codemap

**Entry points.** Everything the paper reports runs through
`scripts/PAPER_DATA.py`, which spawns the Rust binary
`crates/zkregplus/examples/bora_cli.rs` (full/scale/report leaves) or a
`cargo test` target (the `small*` items). `bora_cli` is a thin argv
dispatcher over `zkregplus::bora_data_driver`; direct invocation is for
debugging only — run the Python driver instead.

### Workspace crates (`crates/`)

- **`data_processor/`** — ClamAV signature parsing (`clamav.rs`,
  `pcre.rs`), AC-DFA construction over hex nibbles (`hex_acdfa.rs`),
  and the non-ZK "discharge" prover (`discharge_prover.rs`): scanning a
  file against the DB and recording, per subsignature, the evidence
  words that prove non-match. `clam_db.rs` is the central preprocessed
  DB shared with the circuit layer.
- **`zkregplus/`** — the ZKP framework. Entry point is
  `zkp_driver::zkp_driver{,_adv}`. `src/circs/` holds the **gadget
  mappers** — CP (`cp_mapper.rs`), SDE (`sed_mapper.rs`; the paper's
  Single-Thread Distance Encoding, code prefix `sed_`), DFA
  (`dfa_mapper.rs`), and `composable_gadget_mapper.rs`, which stitches
  them into one circuit. `src/gadgets/` holds the R1CS gadgets (word
  extractor, FSM, pack, sigs, discharge). `src/bora_data_driver.rs`
  hosts the per-experiment collectors `bora_cli` dispatches to.
- **`utils/`** — logging, timers, nibble/field packing, and
  **`consts::GlobalConfig`**, a process-wide `RwLock` (via
  `get_global_config()` / `read_global_config()`) controlling
  `log_level`, `range2_bit`, `b_light_test`, `b_read_cache`, caches and
  parallelism. Runners tune runs by setting these fields — there is no
  CLI-flag layer in the Rust core.

### FoldPot (`vendor/sonobe_mod/.../folding/foldpot/`)

A Sonobe fork adding the paper's folding framework: `driver.rs`
(`foldpot_main`, the fold loop), `sigma_ir1cs.rs` (the step relation
and the two-column lookup argument), `circuits_super.rs` (SuperNova-
style augmented circuit), `cyclepair.rs` (CycleFold-side gadget),
`qa_nizk.rs` + `batch_proc.rs` (QA-NIZK and batch proof),
`decider_eth_circuit_super.rs` (Groth16 decider circuit),
`capacity_planner.rs` (circuit sizing). Curves: BN254 (KZG) paired
with Grumpkin (Pedersen); `bora_cli.rs` shows the canonical generic
parameterization.
Every FoldPot number in the paper comes from `mod_super.rs`
(`FoldPotSuper`) with `circuits_super.rs`, reached through
`driver::foldpot_main` from `zkp_driver.rs:46`. The older
single-instance `FoldPot` in `mod.rs` is superseded: it is not
compiled into any measured run and produces no reported number.

**Invariants.** (1) Circuit shape is driven by *capacity structs*
(`CpCapacity`, `SedCapacity`, ...), declared by the runner, never by
input data; `decreased_copy(level)` yields the descending circuit
ladder. (2) Run shape is fixed per leaf: rule/corpus percentages,
circuit and job counts are argv baked into `PAPER_DATA.py`, not
user-tunable knobs. (3) The runner strips every inherited `ZKR_*`
env var (two documented resume knobs excepted) and forces `RUSTFLAGS`,
so a stale shell export cannot perturb a run.

### Data directory (`data/`)

`src_sig/` signature sources + baseline scripts; `samples/` scan
targets (installed corpora); `small_data_set/` the in-tree demo;
`debug/` pre-baked full-run configs; `cache/` DFA/key caches (not in
git); `paper_data/` recorded runs + the table generators below.

## B. Paper -> code map

Generators live in `data/paper_data/run_data/scripts/eval/` and are run
by `PAPER_DATA.py --run figs`; each reads the raw run logs and emits
one `figs/*.tex` fragment.

| Paper anchor | Concept | Code | Generator |
|--------------|---------|------|-----------|
| §2 (fig:arch) | pipeline / cascade | `zkregplus/src/zkp_driver.rs` | — |
| §3.1 | Critical Pattern (CP) tier | `circs/cp_mapper.rs` (`CpComponentMapper`) | — |
| §3 (fig:sde) | SDE tier | `circs/sed_mapper.rs` (`SedComponentMapper`) | — |
| §3 | DFA tier | `circs/dfa_mapper.rs` | — |
| §3, §6.1 | tier composition | `circs/composable_gadget_mapper.rs` | — |
| §5 (fig:alg_db) | relational encoding, lookups | `foldpot/sigma_ir1cs.rs` (`LookupTableTwoCol`), `zkregplus/src/gadgets/` | — |
| §4 | FoldPot fold loop | `foldpot/driver.rs` (`foldpot_main`) | — |
| §4.2 | step relation Σ-IR1CS | `foldpot/sigma_ir1cs.rs` (`SigmaIR1CS`) | — |
| §4.3 | folding IVC | `foldpot/circuits_super.rs`, `foldpot/cyclepair.rs` | — |
| §4.4 | batch proof + QA-NIZK | `foldpot/qa_nizk.rs`, `foldpot/batch_proc.rs` | — |
| §4, §6.5 | Groth16 decider | `foldpot/decider_eth_circuit_super.rs` | — |
| Table 1 (tab:datasets) | dataset sizes | `data_processor` parsing + corpus manifests | `datasets.py` |
| §6.3, Tables 2/5/6 | approximation effectiveness | `bora_data_driver::collect_assess_tier_data_adv` | `effectiveness.py` |
| §6.4, Table 7 (tbl:lkup) | lookup composition | `bora_data_driver::collect_lookup_stats_adv` | `gen_lkup_info.py` |
| §6.4, Table 8 (tbl:component-cost) | per-circuit cost | full-run COST dumps | `gen_component_cost.py` |
| §6.5, Table 3 (tbl:overall-perf) | end-to-end prover cost | `bora_data_driver::full_{clam,dna,dlp}_neo` | `gen_overall_perf.py` |
| §6.5, Fig. 8 (fig:scale-regex) | regex-set scaling | `collect_scale_{clamav,dlp}_neo` | `gen_scale_all.py` |
| Tables 9/10/11, 4 | baseline comparison | `data/src_sig/{chr17_variants,ms_dlp}/scripts/` (Reef, Zombie) | `dna_reef_bora.py`, `gen_zombie_table.py`, `gen_compare_all.py` |

**Terminology concordance.** Paper **SDE** (Single-Thread Distance
Encoding) ≡ code prefix `sed_` — there is no "SDE" identifier in the
code. **CP = Critical Pattern** (never commit-and-prove). BORA's ZK
framework crate is `crates/zkregplus/`; the problem it solves is
**zk-BuNR** (bulk regex
zero-knowledge non-match). Paper **discharge** ≡
`data_processor::discharge_prover` (non-ZK) re-verified in-circuit.
