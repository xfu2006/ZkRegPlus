# `data/src_sig/` -- signature and regex sources, and where they came from

This folder holds the *inputs* the three datasets are built from: ClamAV
malware signatures (**Mal**), chr17 genomic variants (**Dna**), and a
Microsoft-Purview-derived e-mail regex set (**Dlp**). It is 87% of the
artifact's file count but only ~12% of its bytes.

| Subtree | Tracked files | Tracked bytes | What it is |
|---|---:|---:|---|
| `clamav/` | 21 | 47.1 MB | ClamAV logical-signature database, verbatim and derived |
| `ms_dlp/regex_bora_international/` | 10,458 | 2.25 MB | BORA-format regexes, one directory per Purview SIT |
| `ms_dlp/regex_zombie_international/` | 194 | 431 KB | the same policies in the Zombie baseline's format |
| `ms_dlp/regex_pat_zombie_international/` | 194 | 6.9 KB | generated intermediate; kept for debugging |
| `ms_dlp/scripts/`, `ms_dlp/docs/` | 22 | 10.1 MB | generators and provenance logs |
| `chr17_variants/` | 6 | 113 KB | scripts only -- 1.8 GB of data arrives via `INSTALL.py` |

## Provenance and terms, per dataset

**Mal -- ClamAV.** `clamav/new_src/main.ldb` is the logical-signature set from
**ClamAV 0.103.11 / daily 27152 / Fri Jan 12 04:41:15 2024** (pinned at
`new_src/README` line 1). `main.ldb.original` is the unmodified upstream copy;
`main.ldb` is ours, differing by exactly **14 removed signatures** (documented
in `new_src/removed.ldb`) plus 29 in-place target rewrites. `categories/*.dat`
are derived groupings. ClamAV's database is distributed by Cisco/Talos under
the terms at <https://www.clamav.net/>; consult those before redistributing
this subtree. `new_src/cvd/extract.sh` expects a `main.cvd` that this artifact
does **not** ship -- fetch it from `database.clamav.net` if you want to
re-derive from the signed container.

**Dlp -- Microsoft Purview.** The regexes under `ms_dlp/regex_*` are *derived*
from Microsoft Purview sensitive-information-type (SIT) definitions published
on `learn.microsoft.com`, retrieved by `ms_dlp/scripts/retrieve_ms_dlp.py`.
The scraped upstream records themselves are **not redistributed** (see
`ms_dlp/.gitignore`); only our transformed regex encodings are. Per-record
provenance (`source_url`, `etag`, `Last-Modified`) is in
`ms_dlp/docs/retrieve_record.log`, which ships. Sample values in the corpus
are synthetic and were chosen not to match real values.

**Dlp baseline -- Zombie.** <https://github.com/PepperSieve/Zombie> carries
**no licence (all rights reserved)** and is therefore **never redistributed
here**. `INSTALL.py` clones it at install time, pinned to commit
`ae5ae94828aca2fb0d84e46c323b18a405f3309e`, which is also recorded in
`ms_dlp/docs/download_zombie.log` together with the patches applied to make
the clone build standalone. (Two absolute toolchain paths in that log were
redacted to `~/...` before it was tracked; nothing else was altered.)

**Dna -- chr17.** Variant calls derived from NCBI ClinVar, retrieved by
`chr17_variants/scripts/retrieve_ncbi_variants.py`. Only the scripts are in
git; the 1.8 GB of data is fetched from the pinned Zenodo deposit by
`INSTALL.py`. `chr17_variants/*` is ignored by `data/src_sig/.gitignore` and
`INSTALL.py` rewrites that file on every dna deploy, so do not add files
there by hand -- and note the retrieval log the script's header cites lives
only in a populated tree.

**E-mail corpus.** The Enron corpus is public
(<https://www.cs.cmu.edu/~enron/>); `INSTALL.py` downloads it. Only path
indexes derived from it appear in git.

## Notes for reviewers

* `ms_dlp/scripts/measure.py` is **superseded** -- use `measure_v2.py`; the
  newer file's header explains what the old one got wrong.
* `clamav/debug/debug.ldb` is a small hand-written probe set, unrelated to
  `data/debug/`.
* Several scripts here are one-shot generators whose output is already
  committed; they are kept for provenance, not because the pipeline reruns
  them.
