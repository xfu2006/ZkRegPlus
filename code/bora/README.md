# bora

Reference implementation of **BORA** — a *bulk regex zero-knowledge
non-membership* (zk-BuNR) system. BORA proves that a collection of committed documents
match **no** regex in a large published collection (e.g. 38,875 ClamAV
logical signatures) at near-linear cost in the document length. It is
strictly a **non-match** prover: it never proves that a document *does*
match. A tiered approximation (CP / SDE / DFA) discharge feeds a
folding-based prover (`FoldPot`: modified SuperNova + CycleFold with
lookups) and a Groth16 decider on the BN254/Grumpkin cycle.

> **Paper:** BORA: Bulk Zero-Knowledge Discharging of Regex Collections
> via Tiered Approximation. Under submission (anonymous).

## 1. Verifying this artifact, in four steps

Ordered by cost; each step is checkable on its own, and step 1 needs
neither a Rust build nor a full run. Requirements: section 3. **Run the
artifact inside an isolated VM or container** — see section 4 first.

### Step 0 — install

```bash
python3 scripts/INSTALL.py --data all
```

The command installs the pinned Rust 1.76.0 and the
apt build deps if they are missing, then fetches all five data packs
(~5.8 GB). It is possible to install individual data packs
separately using INSTALL.py using its interactive mode. See below:

| `--data` | Contents | Size | Needed by |
|----------|----------|------|-----------|
| `paper_data` | recorded run logs | 0.05 GB | step 1 (`figs`) |
| `dna` | chr17 corpus + Reef baseline | 0.43 GB | `dna`, `reef` |
| `binexec` | CentOS binaries | 1.5 GB | `clam`, `scale_clam` |
| `email` | Enron corpus | 3.8 GB | `dlp`, `scale_dlp` |
| `zombie` | Zombie (NSDI'24) baseline | 0.04 GB | `zombie` |


### Step 1 — regenerate the paper's tables (~1 min, no full runs)

```bash
python3 scripts/PAPER_DATA.py --run figs
```
Re-runs every table generator against the recorded run logs and
compiles `data/paper_data/pdf/list_figures.pdf` (4 pages). Needs
`pdflatex`. These data tables/figures correspond to those contained
in the BORA paper.

### Step 2 — laptop-scale runs of the system itself

```bash
python3 scripts/PAPER_DATA.py --run small
```

End-to-end ZK proof over the in-tree `small_data_set` (~1.3 min leaf
wall, ~3-4 GB RSS). 

**Dry run — the whole pipeline, thinned.**

```bash
python3 scripts/PAPER_DATA.py --run dry_run --items A
```

Runs all nine leaves against deterministically thinned inputs:
**~91 min wall, ~30 GB peak RSS** (sequential, so the peak is the
largest single leaf, not the sum). Needs all five data packs installed
(step 0). This is a pipeline **smoke test only — its numbers are not
the paper's**; use step 3 for the reported results.

To run one leaf at a time, pick it from the interactive menu
(`python3 scripts/PAPER_DATA.py`, then `dry_run`) or name it with
`--items`:

| `--items` | Leaf | Dry cost | Needs `--data` |
|-----------|------|----------|----------------|
| `dlp` | DLP | 2.4 min / 6.5 GB | `email` |
| `dna` | Dna | 7.0 min / 15.9 GB | `dna` |
| `clam` | Clamav | 8.7 min / 17.1 GB | `binexec` |
| `zombie` | Zombie | 15.5 min / 30.3 GB (cold) | `zombie` |
| `reef` | Reef | 31.9 min / 28.5 GB | `dna` |
| `lkup` | Analyze lkup | 3.5 min / 8.3 GB | `email,dna,binexec` |
| `scale_clam` | Scale-ClamAV | 7.3 min / 5.2 GB | `binexec` |
| `scale_dlp` | Scale-DLP | 8.5 min / 13.0 GB | `email` |
| `effective` | Effectiveness | ~6 min (estimated) | `email,dna,binexec` |

Several at once: `--items dlp,clam`. Every key above is also a `step 3`
leaf, with the same `--data` prerequisite and its full cost in the
section 2 table.
  Note that it regenerates the list of figures PDF (but data
  will be different from paper's).

### Step 3 — full reproduction

```bash
python3 scripts/PAPER_DATA.py --run full_run --items A
```

All nine leaves in sequence: **~6.7 days wall, up to 952 GB peak RSS.**
The run self-detaches and survives logout — follow it with `tail -f
/tmp/bora/SUMMARY.log` (verdicts) and `tail -F
/tmp/bora/CURRENT_JOB.log` (live leaf). One leaf failing does not stop
the rest; see section 6.

Leaves can also be run individually — pick one from the interactive
menu (`python3 scripts/PAPER_DATA.py`, then `full_run`) or name it with
`--items`:

| `--items` | Leaf | Full cost | Needs `--data` |
|-----------|------|-----------|----------------|
| `dlp` | DLP | 70.8 h / ~700 GB | `email` |
| `dna` | Dna | 5.8 h / 529 GB | `dna` |
| `clam` | Clamav | 20.3 h / ~900 GB | `binexec` |
| `zombie` | Zombie | 43.5 h / 952 GB | `zombie` |
| `reef` | Reef | 5.0 h / 29 GB | `dna` |
| `lkup` | Analyze lkup | 1.8 h / 73 GB | `email,dna,binexec` |
| `scale_clam` | Scale-ClamAV | 7.1 h / 148 GB | `binexec` |
| `scale_dlp` | Scale-DLP | 3.7 h / 165 GB | `email` |
| `effective` | Effectiveness | 1.9 h / 73 GB | `email,dna,binexec` |

Several at once: `--items clam,dlp`. `--items dna` alone is the cheapest
full reproduction of a paper column.

## 2. Claim -> experiment map

Costs measured 2026-08 (wall covers the whole leaf: build, DB, folding,
decider, teardown). dlp/clam RSS are derived provisioning floors, not
metered peaks. `R` = `data/paper_data/run_data/data/raw_data`.

| Command | Paper artifact (label) | `--data` | Cost | Result file |
|---------|------------------------|----------|------|-------------|
| `--run figs` | Tables 1-11 + Fig. 8, all labels | `paper_data` | ~1 min | `data/paper_data/pdf/list_figures.pdf` |
| `--run small` | — (demo only) | — (in-tree) | 1.3 min / 3-4 GB | console + `/tmp/bora/SUMMARY.log` |
| `full_run --items dna` | Table 3 Dna col (`tbl:overall-perf`), T8 Dna (`tbl:component-cost`), T9 BORA cells (`tab:dna-reef-bora`), T4 (`tab:compare-all`) | `dna` | 5.8 h / 529 GB | `R/jet1tb/full_dna.tgz` |
| `full_run --items clam` | Table 3 Mal col, T8 Mal, T4 | `binexec` | 20.3 h / ~900 GB | `R/jet1tb/full_clam.part{1,2}.tgz` |
| `full_run --items dlp` | Table 3 Dlp col, T8 Dlp, T11 BORA basis (`tab:compare-zombie-bora`), T4 | `email` | 70.8 h / ~700 GB | `R/jet1tb/full_dlp.part{1,2}.tgz` |
| `full_run --items zombie` | Table 10 (`tab:zombie-data`), T11 + T4 Zombie cells | `zombie` | 43.5 h / 952 GB | `R/jet1tb/run_zombie_regex_zombie_international.log` |
| `full_run --items reef` | Table 9 Reef buckets, T4 Reef row | `dna` | 5.0 h / 29 GB | `R/jet1tb/reef_sample_run.log` |
| `full_run --items lkup` | Table 7 (`tbl:lkup`) | `email,dna,binexec` | 1.8 h / 73 GB | `R/any_server/lookup_stats.dat` |
| `full_run --items effective` | Tables 2, 5, 6 (`tab:eff-pair`, `tab:eff-size`, `tab:eff-size-dlp`) | `email,dna,binexec` | 1.9 h / 73 GB | `R/any_server/eval_effective.txt` |
| `full_run --items scale_clam` | Fig. 8 (`fig:scale-regex`) | `binexec` | 7.1 h / 148 GB | `R/any_server/scale_data_{readelf,gdb}.tgz` |
| `full_run --items scale_dlp` | Fig. 8 (`fig:scale-regex`) | `email` | 3.7 h / 165 GB | `R/any_server/scale_data_dlp_{2,6}.tgz` |

`SUMMARY.log`'s `wall=` covers a whole leaf, so it runs higher than the
paper's per-phase cells — Table 3's Mal folding wall of 15.48 h comes
from the same clam run whose whole-leaf wall is 20.3 h above. A leaf
overwrites its result file, and `--run figs` then rebuilds the affected
tables from your run.

## 3. Requirements

- Rust **1.76.0** — pinned in `rust-toolchain`; do **not** change it
  (the vendored arkworks/Sonobe forks are bound to it).
- `lld` linker (the runners force `RUSTFLAGS="-C link-args=-fuse-ld=lld
  -Awarnings"`).
- Python 3 (for `scripts/INSTALL.py` and `scripts/PAPER_DATA.py`).
- **Step 1 (`figs`) additionally needs `pdflatex`** with geometry,
  booktabs, tikz, pgfplots, hyperref (TeX Live >= 2021; `INSTALL.py
  --toolchain` installs the three Ubuntu texlive packages needed).
- Linux. `numactl` for the NUMA-split full runs (optional: without it a
  run degrades to one unpinned process per leaf).
- `vm.max_map_count`: every `PAPER_DATA.py` run raises this kernel knob
  (target 1,073,741,824) and **aborts** below it — full runs exhaust the
  stock 65,530 ceiling otherwise. Without root, `export
  ZKR_SKIP_MAP_COUNT_CHECK=1` bypasses the gate (safe for `small`/`figs`,
  risky for full runs). See `docs/TROUBLESHOOTING.md`.

**Hardware** (wall / peak RSS, measured 2026-08; per-leaf detail in the
section 2 table):

| Step | Example | Wall | Peak RSS |
|------|---------|------|----------|
| demo (laptop) | `small` | ~1.3 min | ~3-4 GB |
| mid-scale SNARK | `small_full_snark` | ~113 min | ~433 GB |
| cheapest full leaf | `full_run --items dna` | 5.8 h | 529 GB |
| largest full leaf | `full_run --items zombie` | 43.5 h | 952 GB |
| all 9 full leaves | `full_run --items A` | ~160 h (sequential) | 952 GB |

The default build uses the `light-test` feature; the **full** non-light
build needs **~250 GB RAM** (commented dependency in
`crates/zkregplus/Cargo.toml`). Proving is compute-bound: a laptop's
*low-power* profile halves the clock and doubles wall-clock time.

## 4. Ethics and safety

- `INSTALL.py` downloads **real malware-scan targets** (CentOS 7 system
  binaries, scanned against the ClamAV rule base) and the Enron e-mail
  corpus.
- **Enron corpus — obtained, not redistributed.** This artifact ships
  no part of the corpus and hosts no copy of it. `INSTALL.py` downloads
  it directly from the original public-domain release — the FERC
  investigation record — and verifies it against a recorded SHA-256
  tree digest, so what you receive is the public corpus, unmodified,
  from its canonical source. It is used solely as a bulk text workload
  for scanning: BORA makes no attempt to identify any individual, and
  the paper reports only aggregate counts and timings, never message
  content.
- **Handle it as personal data.** The corpus is real correspondence
  that was never scrubbed — published audits report hundreds of Social
  Security numbers and dozens of credit-card numbers still in it. Run
  the artifact inside an isolated VM or container, do not redistribute
  the corpus, and remove it when you are finished. Use is subject to
  your own institution's policies and applicable law.
- **No downloaded binary is ever executed** — the pipeline only reads
  their bytes as scan input. No destructive host side effects.
- Network egress happens only during `INSTALL.py` (the Enron source,
  Zenodo, GitHub, apt/pip) and the **first** `cargo` build (section 7).

## 5. Repository layout

```
bora/
├── crates/          Rust workspace crates
│   ├── zkregplus/       ZK framework (gadgets, circuit mappers, driver)
│   ├── data_processor/  signature parsing, AC-DFA, discharge prover
│   └── utils/           logging, timers, global config, nibble packing
├── vendor/          patched / vendored deps (see vendor/PATCHES.md)
├── scripts/         PAPER_DATA.py (run menu), INSTALL.py (data install)
├── data/            inputs: signatures, samples, per-experiment configs
│   └── paper_data/      the paper's recorded runs + table generators
├── Cargo.toml  Cargo.lock  rust-toolchain
└── docs/            ARCHITECTURE.md, TROUBLESHOOTING.md
```

How the paper's design maps onto these modules, section by section with
the generator behind each table: [`docs/ARCHITECTURE.md`](docs/ARCHITECTURE.md).

## 6. On failure

Every run appends to `/tmp/bora/SUMMARY.log` (verdict lines) and
symlinks the live log at `/tmp/bora/CURRENT_JOB.log` (+`_part2` for
2-part leaves). A failed leaf packs one triage tarball under
`data/paper_data/run_data/data/raw_data/failed_tgz/`. Known errors,
with verbatim strings: [`docs/TROUBLESHOOTING.md`](docs/TROUBLESHOOTING.md).

## 7. Vendored dependencies and license

`vendor/` holds patched arkworks crates (adding pairing support in
R1CS) and a Sonobe fork (adding `foldpot`); what each fork changes and
why: [`vendor/PATCHES.md`](vendor/PATCHES.md). One dep is fetched from
GitHub rather than vendored: Espresso Systems' `subroutines`, pinned in
`Cargo.lock` (`8698369`) — the first build needs network access.

This project's own code is **MIT** (see [`LICENSE`](LICENSE)). Vendored
deps keep their upstream licenses (arkworks MIT/Apache-2.0, Sonobe
MIT); the transitive `priority-queue` crate is used under **MPL-2.0**.
The GPL-3.0 `circom` and unlicensed `noname` frontends that Sonobe
ships were **removed** (unused), so the artifact is free of
strong-copyleft and unlicensed code.
