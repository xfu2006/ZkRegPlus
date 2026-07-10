# attic/debug_scripts

Outdated development / experiment scripts, retired during the artifact
cleanup. **They are superseded by `scripts/PAPER_DATA.py`** (the single
consolidated paper-data runner) plus `scripts/INSTALL.py` (data install).
Kept here for reference/history only; nothing in the build or the current
run flow depends on them. Delete once you are sure they are not needed.

Paths below mirror their original location under `crates/` (the leading
`crates/` prefix is dropped).

## Full-run orchestrators  (replaced by `scripts/PAPER_DATA.py`)
- `zkregplus/src/run_full_clam.py`      -- full ClamAV run driver
- `zkregplus/src/run_full_clam_numa.py` -- ClamAV two-half NUMA run
- `zkregplus/src/run_full_dlp.py`       -- full MS-DLP run driver
- `zkregplus/src/run_full_dlp_numa.py`  -- DLP two-half NUMA run
- `zkregplus/src/run_full_dna.py`       -- full DNA (chr17) run driver

## Scale / cost-collection experiments
- `zkregplus/src/run_collect_scale_data.py` / `.sh` -- scale sweep (clam)
- `zkregplus/src/run_collect_scale_dlp.py`  / `.sh` -- scale sweep (dlp)
- `zkregplus/src/run_exp.py`                        -- one-off experiment driver

## NUMA / diagnostic probes
- `zkregplus/src/numa_probe.py`             -- NUMA attribution harness
- `zkregplus/src/one_time_numa_test_dlp.sh` -- one-shot NUMA test harness
- `zkregplus/src/job3_decider_probe.sh`     -- full_clam job3 decider-block probe
- `zkregplus/src/job3_step_probe.sh`        -- full_clam job3 per-step probe
- `zkregplus/src/doxygen_dfa_probe.sh`      -- DFA doxygen probe
- `zkregplus/src/DEBUG.py`                  -- ad-hoc debug driver

## Build cheatsheets  (dev-only `cargo` command lists)
- `zkregplus/compile.sh`
- `zkregplus/src/compile.sh`
- `zkregplus/src/circs/compile.sh`
- `zkregplus/src/gadgets/compile.sh`
- `data_processor/src/compile.sh`

## Note
The `data/**` provenance scripts (e.g. `gen_regex_bora.py`, `gen_data.py`,
`DOWNLOAD.py`) were intentionally NOT moved here -- they document how the
committed signature/DNA/DLP data was generated and are not replaced by
`PAPER_DATA.py`.
