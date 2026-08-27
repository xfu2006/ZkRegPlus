# `data/debug/` -- test fixtures, not throwaway debug output

**The name is historical; the contents are not.** These are
version-controlled fixtures: signature databases, DFA tables, scan configs
and manifests opened by name from the Rust test suite and from the runs
behind the paper's tables. Read `debug/` as `fixtures/`.

Two honest caveats. Some subdirectories additionally contain *generated*
artefacts that were committed alongside their inputs -- several `sed/*`
databases are rewritten by `build_test_db()` before they are read, and a
few captured console logs sit in report directories. And not every tracked
file still has a live reader: an audit on 2026-08-27 found a substantial
number of fixtures reachable from no code path, pending a removal pass. So
treat this folder as "fixtures plus some sediment", and check for a reader
before assuming a given file is load-bearing.

Tracked: **325 fixtures** -- 324 spread over 17 subdirectories plus
`test1.bin` at the top level -- alongside four `.gitignore` files, the
`sed/workdir/.gitkeep` placeholder and this file (so `git ls-files
data/debug` lists 331). See `../README.md` for
how this folder relates to the rest of `data/`.

## Why it is still called `debug/`

The folder began as a scratch area early in development and the paths
hardened into the sources before the artifact was packaged. About **127
path literals** name it, in two forms that a single search will not both
find: the absolute `data/debug/...` (91 sites in `crates/`) and the
`data/`-relative `"debug/..."` (23 sites in `crates/`), plus a further 13
in `.gitignore`, `scripts/INSTALL.py` and the export tool. Renaming it late
in the submission cycle would buy tidiness at the risk of a silent path
break, so the name stayed and this file was written instead.
**Read `debug/` as `fixtures/`.**

To see the call sites:

```bash
grep -rn 'data/debug' crates/ --include='*.rs'   # absolute form
grep -rn '"debug/'    crates/ --include='*.rs'   # data/-relative form
```

Note that `data/src_sig/clamav/debug/` is a *different*, unrelated folder.

## What is in here

| Group | Subdirectories (tracked files) | Role |
|---|---|---|
| Full-scale run inputs | `full_par_set` (57), `full_clamav` (46), `full_dlp_sample` (41), `full_data_set` (22), `full_clam_bisect` (2) | pre-baked signature DBs and scan configs for the paper's full runs; `full_clamav/config/main.dat` is the ClamAV base read by the full-scale Rust test |
| Laptop-scale inputs | `small_data_set2` (29), `small_data_set` (28), `small_email` (16), `small_dna` (9), `small_multi_dnf_set` (7) | what the fast demo and the quick unit tests read |
| Targeted regression cases | `sed` (24), `clam_hard_set` (15), `dlp_hard_set` (12), `neo_hard_set` (8), `dfa` (5), `neo_hard_aggr_set` (2) | deliberately hard inputs pinned to specific gadget behaviour, read by `gadgets/{compute_sig_adv,discharge_adv,discharge_adv_neo,fsm_adv,dfa_adv}.rs` and `zkp_driver.rs` |
| Environment probe | `numa_probe` (1) | the corpus *builder* for the NUMA-pinning check; no corpus ships |

Seven subdirectories carry their own `README` describing the fixture's
design and expected behaviour -- `full_clamav/config/`,
`neo_hard_set/config_dfa/`, `small_data_set/config_dfa/`,
`small_data_set2/config_dfa/`, `small_dna/config/`, `small_email/config/`
and `small_multi_dnf_set/config_dfa/`. Start there.

## What is deliberately NOT tracked

`.gitignore` in this folder untracks seven scratch subdirectories that no
code path reads as an input; the tests that need them recreate them (for
example `t602_probe_scratch_*` is a WRITE target that
`debug_probes/probe_t602.rs` regenerates). A fresh checkout will not have
them and does not need them.

It also carries the opposite kind of rule. `test1.bin`, `sed/simple/*.txt`
and `dfa/simple/*.txt` are re-included with `!` overrides because blanket
rules elsewhere in the repo would otherwise untrack them -- and the tests
read them, so a fresh `git archive` export would fail its own test suite
while the working tree passed. **If a test opens it, it must be tracked.**

## Where the bytes come from

All of it is in git -- none of this folder is downloaded. In the anonymous
snapshot only, 4 oversized fixtures from here ship inside
`data/bigfiles/bigfiles.tar.xz` (4 of that pack's 9 members) because the
mirror refuses files over 8 MB; `scripts/INSTALL.py` restores them
byte-identically and checks each against a recorded SHA-256. A normal git
checkout has them loose and has no `bigfiles/` at all.
