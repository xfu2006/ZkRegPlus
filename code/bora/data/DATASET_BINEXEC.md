# CentOS 7.9.2009 binary corpus (`binexec`)

> *This document was prepared by Claude Opus 5 under the guidance of the
> BORA authors. Every count, hash, licence and provenance claim in it is
> generated directly from the archive's own contents rather than written
> by hand, and all of them are independently checkable — see
> [Verifying this archive](#verifying-this-archive).*

This archive contains the 2,702-file binary corpus used as the **Mal**
dataset. It is a flat snapshot of the executables and shared objects
present on a CentOS 7 Google Compute Engine instance, plus a small
number of files produced by earlier experiments on the same machine.

The archive is self-describing: every file is attributed to the package
it came from, every package to its licence and its published source, and
every licence text is included. Nothing needs to be taken on trust —
see [Verifying this archive](#verifying-this-archive).

**Release:** CentOS 7.9.2009 (established by hash-matching, not by
`/etc/centos-release`, which is not present in the corpus — see
[How provenance was established](#how-provenance-was-established)).

---

## Contents

| Path | Contents |
|---|---|
| `samples/` | The 2,702 corpus files, flat, original filenames |
| `licenses/` | Licence texts, plus `licenses/README.md` mapping files to licences |
| `manifest/manifest.json` | Per-file record: hash, size, category, origin package, licence, upstream URLs |
| `manifest/manifest.list` | `sha256  name`, in `sha256sum -c` format |
| `manifest/PACKAGES.tsv` | The 376 source packages: licence, binary RPM URL, source RPM URL |
| `manifest/categories/*.list` | One tab-separated table per category |

---

## File categories

| # | Category | Files | Size | Licensing |
|---|---|---:|---:|---|
| 01 | CentOS 7.9.2009 base (`os`) | 1,345 | 426.8 MB | RPM `License` tag per package |
| 02 | CentOS 7.9.2009 `updates` | 1,095 | 150.8 MB | RPM `License` tag per package |
| 03 | EPEL 7 | 13 | 0.9 MB | RPM `License` tag per package |
| 04 | CentOS-derived | 1 | 6.8 MB | Same as its source package (GPLv2) |
| 05 | Google-distributed | 25 | 175.3 MB | Apache-2.0, Python-2.0, MIT, BSD-3-Clause |
| 06 | Experiment artifacts | 223 | 4.9 MB | None — authors' own output |
| | **Total** | **2,702** | **765.5 MB** | |

Categories 01–04 (**2,454 files**, 585.3 MB) are the CentOS 7.9.2009
installation proper. Categories 05 and 06 are not CentOS files, and are
described individually below so that no reader has to infer what they
are.

### 01–02 · CentOS 7.9.2009 base and updates

2,440 files, byte-identical to members of RPMs published at
`https://vault.centos.org/7.9.2009/{os,updates}/x86_64/Packages/`.

The split matters: the machine had the `el7_9` update stream applied, so
1,095 of these files are **not** in the base release and cannot be found
there. Any attempt to reconstruct this corpus from `os/` alone will fail
on roughly 45% of it.

Listings: `manifest/categories/01-centos-os.list`,
`02-centos-updates.list`.

### 03 · EPEL 7

13 files from the Extra Packages for Enterprise Linux 7 archive
(`htop`, `pdsh`, `lua-*`, `Lmod`). Genuinely installed on the machine,
but distributed by the Fedora project rather than by CentOS, which is
why they are counted separately from the 2,440.

One package needs a note. `Lmod-8.7.7-1.el7` (licence
`MIT AND LGPL-2.0-only`) has been superseded in the EPEL archive: only
8.7.20 remains there, so neither its metadata nor its source RPM is
still published. Its source is cited instead as the upstream release tag
`8.7.7` at `github.com/TACC/Lmod`, which is the exact corresponding
source for the one file involved, `tcl2lua.so.1.0.1`.

### 04 · CentOS-derived

One file: `vmlinuz-0-rescue-b1527a5456aab241a74a8a3dc31395c0`. It is
byte-identical (same SHA-256) to
`vmlinuz-3.10.0-1160.76.1.el7.x86_64` from
`kernel-3.10.0-1160.76.1.el7.x86_64.rpm`. Anaconda writes this copy at
install time under a randomised name, so it is a CentOS file that no
package lists.

### 05 · Google-distributed

25 files, 175.3 MB — the largest category by size despite being 0.9% of
the files, because it includes `anthoscli` (73.9 MB), the biggest single
file in the corpus.

These were installed on the instance by Google, not by CentOS, and come
from three components:

| Component | Files | Size | Licence |
|---|---:|---:|---|
| Google Cloud CLI (`anthoscli`, `gcloud-crc32c`) | 2 | 75.4 MB | Apache-2.0 |
| GCE guest environment (guest-agent, osconfig, oslogin) | 6 | 39.5 MB | Apache-2.0 |
| CPython 3.9 bundled inside the Cloud CLI, and its vendored extensions | 17 | 60.3 MB | Python-2.0, Apache-2.0, MIT, BSD-3-Clause |

Per-file component and licence attribution is in
`licenses/README.md`; the listing is
`manifest/categories/05-google.list`.

Unlike categories 01–04 these files **cannot be re-fetched**. The
`cloud-sdk-el7` repository retains only the most recent 50 releases and
has garbage-collected the versions installed here, and the guest
environment repository carries only current builds. Container images on
`gcr.io` retain the matching tags but ship different builds — the
binaries there have the right names and the wrong bytes. This archive is
therefore the only remaining source for these 25 files, which is the
reason they are bundled rather than downloaded on demand.

### 06 · Experiment artifacts

223 files, 4.9 MB. These are **not** operating-system files and not
executables. They are output written by earlier experiments into the
sample directory, where they were subsequently picked up as part of the
corpus. Three formats, over six source stems:

| Stem | `.encrypted` | `.padded` | `.hash` | Total |
|---|---:|---:|---:|---:|
| `git-merge-base` | 70 | 70 | 69 | 209 |
| `capsh` | 1 | 2 | 1 | 4 |
| `Mcrt1.o` | 1 | 1 | 1 | 3 |
| `crtn.o` | 1 | 1 | 1 | 3 |
| `vdso32-syscall.so` | 1 | 1 | 0 | 2 |
| `vdso32-sysenter.so` | 1 | 1 | 0 | 2 |
| **Total** | **75** | **76** | **72** | **223** |

- **`.padded`** — the source file re-encoded by nibble expansion: each
  input byte becomes two bytes carrying its high and low nibble, padded
  to a fixed chunk length with `0x10` (the first invalid nibble value)
  and terminated with a single `0x0a`. This rule has been recovered and
  verified to reproduce all 76 files byte-exactly from their stems, so
  these files are *derivable* and carry no information not already in
  the corpus.
- **`.encrypted`** — Java-serialised `BigInteger[520]` ciphertext
  (`ac ed 00 05` stream header, 32-byte magnitudes). The generating
  program is not part of any released source tree and the key and
  randomness were not recorded, so these are **not** reproducible.
- **`.hash`** — 255-bit values in the BN254 scalar field, consistent
  with a SNARK-friendly hash whose parameters were likewise not
  recorded. Also **not** reproducible.

They are retained because the published measurements were taken over the
corpus as it stands. Removing them would change the input to the 128 KB
merge step that builds the scanned document set, and therefore change
every derived measurement, without making any claim stronger: the
experiment proves the corpus contains no blacklisted pattern, and
proving that for 223 additional files is not a weaker result than
proving it for 2,479.

Their presence does mean one thing should be stated precisely. Where the
corpus is described as "CentOS executables", the exact description is *a
CentOS 7.9.2009 installation directory as scraped, including accumulated
experiment artifacts* — 8.3% of the files, 0.6% of the bytes, are not
CentOS binaries.

---

## Licensing

See `licenses/README.md` for the full mapping and for the lookup
procedure. In summary:

- **Categories 01–04.** Each file's licence is the `License` tag of the
  RPM that contains it, recorded per file in `manifest/manifest.json`
  and per package in `manifest/PACKAGES.tsv`. Across the archive these
  tags decompose into 46 distinct licence names, 42 of which have a
  canonical text; all 42 are in `licenses/`. (The remaining four —
  `Public Domain`, `Copyright only`, `Copyright Only` and `Verbatim` —
  have no canonical wording and appear only as terms inside compound
  expressions.) The most common are GPLv2-or-later (1,039
  files), LGPLv2-or-later (731), GPLv2 (537), GPLv3-or-later (382), BSD
  (379) and MIT (308).
- **Category 05.** Apache-2.0, Python-2.0, MIT and BSD-3-Clause.
  Upstream `LICENSE` and `NOTICE` files are in `licenses/vendor/`;
  Apache-2.0 §4(d) requires the `NOTICE` contents to accompany the
  binaries, so they are included rather than only referenced.
- **Category 06.** No third-party licence applies; this is the authors'
  own output.

Everything in categories 01–05 is freely redistributable. No component
of CentOS base, updates or EPEL is under restricted redistribution
terms, and the Google-distributed files are under permissive licences.

## Source code availability

Categories 01–04 are unmodified binaries built from published sources.
`manifest/PACKAGES.tsv` gives, for each of the 376 packages, the URL of
the exact source RPM corresponding to the binary shipped here — under
`https://vault.centos.org/7.9.2009/{os,updates}/Source/SPackages/` and
`https://archives.fedoraproject.org/pub/archive/epel/7/SRPMS/Packages/`.

This satisfies the source-code requirement of the GPL family for the
binaries in this archive: GPLv3 §6(d) permits Corresponding Source to be
offered from a third-party server given clear directions to it, and
GPLv2 §3(c) permits noncommercial distribution to pass along the offer
received from upstream. The mapping in `PACKAGES.tsv` is those
directions. No binary here has been modified from the form in which
CentOS or Fedora published it.

For category 05, source for the Apache-2.0 and MIT components is
published by the respective projects; those licences do not impose a
source-distribution obligation on redistributors of binaries.

## Verifying this archive

```sh
cd samples
sha256sum -c ../manifest/manifest.list
```

All 2,702 files should report `OK`.

To check the provenance claim rather than just integrity, take any file
in categories 01–03, read its `url` field from `manifest/manifest.json`,
download that RPM from `vault.centos.org`, extract the member named in
the `member` field, and compare hashes. That is exactly how the
attribution in this archive was produced, one file at a time, for all
2,453 of them.

## Relationship to the zkreg dataset

This is not a different corpus from the one used by zkreg; it is the
same scrape, characterised. Two differences are worth recording:

1. **The release is CentOS 7.9.2009, not 7.1.** zkreg cites CentOS 7.1.
   The bytes disagree: 2,440 files match RPMs from the 7.9.2009 vault
   exactly, the bundled shared objects carry `el7_9` dist tags, and the
   kernel is from the 3.10.0-1160 series that shipped with 7.9. The
   minor version is now settled by hash agreement rather than inferred.

2. **223 files are experiment output, not OS files.** They were written
   into the sample directory by earlier runs and became part of the
   corpus. They are identified individually in category 06 above rather
   than left as an unexplained residue.

Neither difference changes any measurement; both change what can
accurately be said about the corpus.

## How provenance was established

The corpus is a flat directory, so the original install paths are gone,
and a basename alone is not sufficient evidence — 1,974 of the basenames
here occur in more than one el7 package. Attribution was therefore done
by content, not by name:

1. Every file in `samples/` was hashed.
2. Repository metadata (`primary.xml.gz`, `filelists.xml.gz`) was read
   from the CentOS 7.9.2009 vault and the EPEL 7 archive to find, for
   each basename, every package that could contain it.
3. Candidate packages were downloaded and their payloads unpacked, and a
   file was recorded as attributed **only when the extracted member's
   SHA-256 equalled the corpus file's**. Resolution and verification are
   the same step; a name match alone never counted.
4. The result was checked by replaying it into an empty directory:
   fetching every recorded package afresh, extracting the recorded
   member for each attributed file, re-deriving category 04 and the
   `.padded` files from their rules, and taking the remaining files from
   the bundled set. That reproduced 2,702 of 2,702 files
   byte-identically, with no mismatches, no omissions and no extras.

`manifest/manifest.json` records the package, member path and upstream
URL behind every attributed file, so step 3 can be repeated for any file
independently.

## What is not in this archive

- **The merged document set.** The measured workload is produced from
  `samples/` by a merge step that concatenates files under 128 KB into
  documents and splits very large ones. That step is part of the code
  artifact, not this archive; this archive holds its input.
- **`/etc/centos-release` or an installation image.** The corpus
  contains executables and shared objects only, which is why the release
  had to be established by hash-matching.
- **Source RPMs.** These are cited by URL in `manifest/PACKAGES.tsv`
  rather than bundled, which would multiply the size of the archive
  several times over.
