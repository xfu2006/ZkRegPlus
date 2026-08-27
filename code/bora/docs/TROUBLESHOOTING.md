# Troubleshooting

Entries are keyed on the verbatim, greppable error text.

## `PREFLIGHT ABORT: vm.max_map_count`

Every `PAPER_DATA.py` invocation checks `/proc/sys/vm/max_map_count`
against 1,073,741,824 and quits up front when it is lower and cannot be
raised (a stock kernel ships 65,530). Fix (free, no memory cost):

```bash
sudo sysctl -w vm.max_map_count=1073741824          # now
echo 'vm.max_map_count=1073741824' | sudo tee \
  /etc/sysctl.d/99-zkregplus.conf && sudo sysctl --system   # persist
```

No root? `export ZKR_SKIP_MAP_COUNT_CHECK=1` bypasses the gate —
safe for `small`/`figs`, but a full run will hit the failure below.
`ZKR_VM_MAX_MAP_COUNT=<n>` overrides the target.

## `memory allocation of ... bytes failed` / SIGABRT with RAM free

mimalloc hitting ENOMEM on mmap once the process VMA count reaches the
`vm.max_map_count` ceiling — RAM looks free, allocation still dies.
Same fix as above. Full runs need up to ~475M mappings (full_dlp).

## `FileNotFoundError: ... 'pdflatex'`

`--run figs` compiles `list_figures.tex`. Install TeX Live >= 2021
(Ubuntu: `texlive-latex-base texlive-latex-recommended
texlive-pictures`); `INSTALL.py --toolchain` does this. The generators
still run without TeX — only the final PDF compile fails.

## Link error mentioning `ld.lld` or `-fuse-ld=lld`

The runners force `RUSTFLAGS="-C link-args=-fuse-ld=lld -Awarnings"`.
Install `lld` (part of `INSTALL.py --toolchain`'s apt set).

## Compile-time OOM on the full (non-light) build

The default build uses the `light-test` feature. Swapping to the
commented full dependency line in `crates/zkregplus/Cargo.toml` needs
**~250 GB RAM**. Do not switch it for reproduction — every menu item
uses the shipped configuration.

## `PREFLIGHT: NUMA split disabled; one unpinned process per leaf`

`numactl` is missing or `--preferred-many` is unsupported. Not fatal:
the 8-job leaves (`clam`, `dlp`) lose their 4+4 two-socket split and
run as one unpinned process — slower, same results.

## Run much slower than the quoted cost (laptop)

Proving is compute-bound; a *low-power* thermal profile roughly halves
the clock and doubles wall time. Set the profile to performance.

## `RUNALL done: N generator(s) failed.` with N > 0

The `figs` PDF still builds — each failed generator's `figs/*.tex`
fragment simply keeps its previous (possibly stale) content. Scroll up
to the `[FAIL] <generator>.py` line for the cause (usually a missing
raw-data bundle for a leaf you have not run; `--data paper_data`
restores the recorded ones). Success is exactly
`RUNALL done: 0 generator(s) failed.`

## Where the logs are

- `/tmp/bora/SUMMARY.log` — one verdict line per leaf (`wall=`,
  `peak_rss=`, rc).
- `/tmp/bora/CURRENT_JOB.log` (+ `CURRENT_JOB_part2.log`) — symlink to
  the live leaf's log.
- `/tmp/bora/logs/<leaf>_<mode>_<timestamp>/` — per-run spawn logs and
  report files.
- A failed leaf packs one triage tarball:
  `data/paper_data/run_data/data/raw_data/failed_tgz/*_BUNDLE.tgz`.
