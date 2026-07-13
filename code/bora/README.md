# bora

Reference implementation and research artifact for **BORA** (internally
code-named `zkregplus`) — a *bulk regex zero-knowledge non-membership*
(zk-BuNR) system that proves a committed file does **not** match any regex
in a large published collection (e.g. the ~38k-rule ClamAV rule base),
at near-linear cost in the file length. BORA combines a **tiered
approximation** (CP / SDE / DFA) discharge with a folding-based prover
(`FoldPot`: modified SuperNova + CycleFold with lookups) and a Groth16
decider over the BN254/Grumpkin curve cycle.

> **Paper:** BORA: Bulk Zero-Knowledge Discharging of Regex Collections
> via Tiered Approximation. Under submission.
> **Authors:** Anonymous.
> **Cite as:** Anonymous submission — citation to be added on
> de-anonymization.

---

## 1. What this artifact does

Given a target file and a signature database, the pipeline:

1. **Parses** ClamAV / MS-DLP signatures and builds AC-DFAs over hex
   nibbles (`crates/data_processor`).
2. **Discharges** the file against the DB (non-ZK), producing a per-file
   trace of which sub-signatures match / do not match and the evidence
   words that prove it.
3. **Re-verifies that trace in zero knowledge**: packs the file as
   nibbles, builds a ladder of folded circuits, folds them incrementally,
   and proves the result with Groth16 (`crates/zkregplus`).

See [`docs/ARCHITECTURE.md`](docs/ARCHITECTURE.md) for the full pipeline.

## 2. Repository layout

```
bora/
├── crates/          Rust workspace crates
│   ├── zkregplus/       ZK framework (gadgets, circuit mappers, driver)
│   ├── data_processor/  signature parsing, AC-DFA, discharge prover
│   └── utils/           logging, timers, global config, nibble packing
├── vendor/          patched / vendored dependencies (see vendor/PATCHES.md)
│   ├── dependency/      arkworks forks (pairing-in-R1CS cherry-picks)
│   └── sonobe_mod/      Sonobe fork adding the `foldpot` folding scheme
├── scripts/         PAPER_DATA.py (run menu), INSTALL.py (data install)
├── data/            signatures, samples, per-experiment configs
├── attic/           retired / superseded files (safe to delete)
├── Cargo.toml  Cargo.lock  rust-toolchain
└── docs/
```

## 3. Requirements

**Software**
- Rust **1.76.0** — pinned in `rust-toolchain`; do **not** change it (the
  vendored arkworks/Sonobe forks are bound to it).
- `lld` linker (required for reasonable link times).
- Python 3 (for `scripts/INSTALL.py` and `scripts/PAPER_DATA.py`).
- Python packages: `pip install -r requirements.txt` (core dep: `gdown`;
  the rest are optional, only for regenerating the signature corpora).
- Linux. `numactl` is used by the large NUMA runs (optional otherwise).

**Hardware (per experiment)**

| Run | RAM | Time | Notes |
|-----|-----|------|-------|
| small data (demo) | ~7 GB | ~30–40 s | single process, ships its own config |
| full DNA | large | ~hours | single job |
| full ClamAV | ideally ~1 TB / 8 NUMA nodes | ~5–8 h | rebuilds ~40 GB DB |
| full DLP | large / NUMA | ~5–6 h | 8-job two-process scheme |

The default build uses the `light-test` feature. The **full** (non-light)
build needs **~250 GB RAM** (see the commented dependency in
`crates/zkregplus/Cargo.toml`).

> **Performance note:** proving is compute-bound. On a laptop, set the
> power/thermal profile to *performance* — a *low-power* profile roughly
> halves the clock and doubles wall-clock time.

## 4. Setup

```bash
# from the repo root
python3 scripts/INSTALL.py --data all     # or: email | dna | binexec
python3 scripts/INSTALL.py --toolchain    # install the pinned rust 1.76.0
```

`INSTALL.py` downloads and extracts the datasets into `data/`. Caches live
under `data/cache/` (not in git) and are regenerated on first run.

## 5. Build

```bash
RUSTFLAGS="-C link-args=-fuse-ld=lld -Awarnings" cargo build --release
```

## 6. Running the experiments (claim → experiment map)

All runs go through one menu (self-detaches into the background; follow
with `tail -f` on the log path it prints):

```bash
python3 scripts/PAPER_DATA.py               # interactive menu
python3 scripts/PAPER_DATA.py --run small   # non-interactive
#                              --run {small|dna|clam|dlp}
```

| Menu item | Command | Paper dataset (Table 1) | Reproduces |
|-----------|---------|-------------------------|------------|
| (1) small data | `--run small` | — (not in paper) | demo / sanity check only |
| (2) full DNA | `--run dna` | **DNA** — chr17 (GRCh38), 1×83 MB doc vs NCBI ClinVar, 27,500 rules | DNA discharge (Tables 1–2) |
| (3) full ClamAV | `--run clam` | **MAL** — CentOS 7, 1,209 docs / 765 MB vs ClamAV 0.103.11, 38,875 rules (160,854 leaf subsigs) | malware discharge + prover cost (Tables 1–3; §7.4–7.6) |
| (4) full DLP | `--run dlp` | **DLP** — Enron, 509,610 docs / 1.38 GB vs MS-DLP SIT, 136 rules | e-mail DLP discharge (Tables 1, 2, 4) |

The three full runs (`dna`/`clam`/`dlp`) correspond to the paper's three
evaluation datasets (Table 1: MAL / DNA / DLP). `small` is a self-contained
demo not tied to a paper number.

**Expected scale (from the paper).** Reference results were produced on an
**M1 server with 1.4 TB RAM and 60 cores @ 2.23 GHz** (≈$1.05/hr). For the
MAL (ClamAV/CentOS) set the paper reports ≈**44 h folding + 16 h SNARK**
(8 fold jobs, 2 SNARK jobs in parallel) ≈ **$63**. The DNA and DLP costs
and the exact proof sizes are reported in the paper's evaluation tables.
These are **large-RAM, many-hour** runs — see the requirements table in §3;
a laptop can only run the `small` demo.

## 7. Kicking the tires (fast check)

```bash
RUSTFLAGS="-C link-args=-fuse-ld=lld -Awarnings" \
  cargo test -p zkregplus --release --lib -- \
  zkp_driver::tests_zkp_driver::test_zkreg_main --exact --nocapture
```
Runs the `small_data` end-to-end ZK proof in ~30–40 s (~7 GB RAM) and
writes a report under `data/small_data_set/reports/`.

## 8. Vendored dependencies

`vendor/` contains patched arkworks crates (adding pairing support in
R1CS) and a Sonobe fork (adding the `foldpot` folding scheme). What each
fork changes and why is documented in
[`vendor/PATCHES.md`](vendor/PATCHES.md).

## 9. License

This project's own code (`crates/`, `scripts/`, docs, data configs) is
licensed under the **MIT License** — see [`LICENSE`](LICENSE).

Third-party components keep their own licenses:
- Vendored dependencies under `vendor/` retain their upstream licenses
  (arkworks: MIT/Apache-2.0; Sonobe: MIT) — see the `LICENSE*` files in
  each and [`vendor/PATCHES.md`](vendor/PATCHES.md).
- One transitive dependency, `priority-queue` (via `rustomaton` →
  `fast_paths`), is available under `LGPL-3.0 OR MPL-2.0`; it is used
  unmodified under the **MPL-2.0** terms, which permit combining it into
  an MIT-licensed larger work.

The GPL-3.0 `circom` and unlicensed `noname` circuit frontends that Sonobe
ships were **removed** (they were unused here) so the artifact is free of
strong-copyleft / unlicensed code; the removed sources are retained under
`attic/removed_gpl_unlicensed_frontends/`.
