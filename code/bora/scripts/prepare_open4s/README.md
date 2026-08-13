# prepare_open4s

Builds the anonymous artifact snapshot published at
[anonymous.4open.science](https://anonymous.4open.science) for USENIX Security
'27 Cycle 1 (submission tasks **T902** / **T903**).

```
python3 scripts/prepare_open4s/prepare.py            # interactive, all 9 steps
python3 scripts/prepare_open4s/prepare.py --list     # show the steps
python3 scripts/prepare_open4s/prepare.py --from pack
python3 scripts/prepare_open4s/prepare.py --only verify
```

Standard library only. No pip, no apt, no `xz` binary.

---

## What it guarantees

**It never writes to this repository.** Every automated step reads through
`git archive` and writes only into the staging directory (`/tmp/bora_open4s` by
default). Re-running it is free; a bad run is thrown away by deleting one
directory.

**It never copies the working tree.** The snapshot comes from
`git archive HEAD:code/bora`. This is not a stylistic choice — a directory copy
sweeps up 38 untracked/gitignored files that embed `/home/xiang` (`__pycache__`
`.pyc` files, generated logs, `dump.txt`), plus a 170 MB
`new_src/cvd/clamav_main.tar.gz` and a rebuilt `reef/target/` with ~1,350 more
such files.

---

## The twelve steps

| # | Step | What happens |
|---|------|--------------|
| 1 | `preflight` | Python/git/lzma present, **no `.git/index.lock`**, HEAD reported, dirty-tree warning |
| 2 | `export` | `git archive HEAD:code/bora` → staging |
| 3 | `prune` | delete `attic/`, **this tool**, editor swap files, `__pycache__` |
| 4 | `pack` | build `data/bigfiles.tar.xz`, drop the loose originals, extend `data/.gitignore` |
| 5 | `verify` | full inspection of the staging tree — hard-fails the run |
| 6 | `initrepo` | `git init`, branch `artifact-sec27`, **one** squashed commit, reconciliation |
| 7 | `manifest` | record the local manifest (kept **outside** the artifact) |
| 8 | `github` | **manual**: create the private repo, push — one action per prompt |
| 9 | `checkpush` | clone the pushed repo back and inspect it |
| 10 | `fouropen` | **manual**: mint the URL, one field per prompt |
| 11 | `checkmirror` | inspect the downloaded 4open ZIP |
| 12 | `freeze` | **manual**: 08-25 URL final, 08-28 pin the SHA (T913) |

Manual steps print **one action at a time** and wait for Enter, so you are never
reading ahead of what you are doing. Nothing is pushed or published for you.

### The inspection, and why it runs three times

`inspect_tree()` is one function run against three different trees, because each
isolates a different failure:

| Checkpoint | Answers |
|---|---|
| **staging** (step 5) | is what I built clean? |
| **GitHub clone** (step 9) | did the push deliver all of it? |
| **4open ZIP** (step 11) | is what reviewers actually receive still correct? |

It performs: **anonymity** (text *and* binary, context-allowlisted), **file-size
limit**, **PAPER_DATA.py readiness**, pack integrity by SHA-256, stray
VCS/bytecode files, symlink safety, and — where a manifest is available — a
**completeness diff** against the published snapshot.

Verified against deliberately broken inputs: a dropped file, a one-byte change
to the pack, and an injected identity string are each caught with a specific
diagnostic.

### Readiness: where the required-input list comes from

`PAPER_DATA.py` declares `required_files` for only 2 of its 8 `JOB_SPECS`
leaves, and that is deliberate — `PAPER_DATA.py:1144-1146` says the rest "assert
on their own config/corpus paths, which live in DatasetSpec". `DatasetSpec` is
**Rust**, at `crates/zkregplus/src/bora_data_driver.rs:367` (consts `DLP` :441,
`DNA` :501, `CLAM` :579).

So the checker reads both: the 2 Python declarations, plus the Rust consts
parsed statically (`config_dir`, `sig_file`, `master_sources`, `scale_sources`
are plain `&'static str` — no build required). That gives 8/8 coverage with one
source of truth. Currently 21 required inputs: **16 present, 1 restored by the
pack** (`CLAM.sig_file` → `data/debug/full_clamav/config/main.dat`), **4 from
INSTALL.py downloads**, **0 unaccounted**.

Two honest limits, both surfaced in the report rather than hidden:

- "from INSTALL.py download" is **accounted for, not verified**. Only a real
  install proves those corpora arrive intact.
- The Rust parser is brittle by nature. It asserts that all 3 consts parse with
  non-empty fields and **fails loudly** if the Rust ever switches to `concat!()`
  or a helper function, rather than silently reporting less.

---

## Four decisions worth knowing before you edit this

### 1. The artifact is re-rooted at `code/bora`

`INSTALL.py:32` fixes the project root one level above `scripts/`, so the
snapshot is exported from `HEAD:code/bora`, not from the git root. A reviewer
then runs `git clone && python3 scripts/INSTALL.py` with no `cd`.

Re-rooting also drops, without any prune rule:

- `LOG` — 1.1 MB development log, deliberately not shipped
- `.gitmodules` — declares `https://bitbucket.org/xfu2009/sonobe/...`, a
  **username leak**, for a submodule path that no longer exists after the tree
  was reorganised
- `git_check.sh`, `.gitattributes`, the root `.gitignore`

### 2. `PACK_MEMBERS` order is load-bearing — do not sort it

Thirteen tracked files exceed 4open's **8 MB per-file limit**, and five of them
are byte-identical copies of the same 11.11 MB ClamAV signature database.
Measured on the real tree:

| Archive | Size | Fits? |
|---|---|---|
| `tar.gz`, any order | 30.94 MB | no — gzip's window is 32 KB and can never see two copies at once |
| `tar.xz`, alphabetical | 8.67 MB | no — 64 MB window, but the copies are spread over 214 MB of tar |
| **`tar.xz`, `PACK_MEMBERS` order, preset 9\|EXTREME** | **3.50 MB** | **yes, 2.3× margin** |

Replacing the list with a glob or a `sort()` silently pushes the pack back over
8 MB, and the failure surfaces only on the published mirror. Step 4 hard-fails
if the result exceeds the limit, and separately hard-fails if any file outside
the list is oversized (which means the list has gone stale).

The originals are deleted only **after** the archive is written, its member
list is checked against `PACK_MEMBERS`, and per-file SHA-256 digests are
recorded in `data/bigfiles.sha256`.

### 3. Nothing is regenerated or recompressed in place

Every shipped file is byte-identical to what is in git. The pack is a
relocation, not a transformation: `INSTALL.py` restores the 13 files with
`tarfile.open(..., "r:xz")` and they hash exactly as before. This was the
explicit design constraint — no rewriting of `gen_data.py`, no per-file `.xz`,
no install-time regeneration.

### 4. This tool prunes *itself* — and that is not tidiness

`scripts/prepare_open4s/` is in `PRUNE_PATHS`. It must never ship inside the
artifact it builds, because `REDACTION_TERMS` in `prepare.py` is a literal list
of the author's name, GitHub handle, Bitbucket handle and institution, and this
README names the build hostname. Publishing the scrubber inside the thing it
scrubs hands a reviewer exactly what it exists to hide.

This was not foreseen — it was **caught by the tool flagging itself** the first
time these two files were committed and therefore appeared in
`git archive HEAD:code/bora`. The identity scan reported 27 hits, all of them in
`prepare.py` and this README. That is the single best argument for keeping the
scan broad and refusing to allowlist by filename: had those two files been
excused as "obviously fine, they're just tooling", the leak would have shipped.

### 5. `git add -A -f`, and the file that proved why

Step 6 forces the add. In a **fresh** repo `git add -A` honours `.gitignore`; in
ZkregPlus these files survive only because ignore rules never apply to
already-tracked files. Without `-f`, `data/.gitignore:3` (`samples/*`) silently
dropped `data/samples/email/README.md` from the snapshot — 12,143 files on disk,
12,142 committed, no warning. Step 6 now also reconciles the two sets and fails
if anything on disk missed the commit.

### 6. The readiness check must not write into the tree it checks

Importing `PAPER_DATA.py` makes CPython write `scripts/__pycache__/*.pyc` next
to the imported file — inside the tree under inspection. That `.pyc` was then
swept into the commit by `git add -A -f`, **after** the anonymity scan had
already passed. Harmless with a `/tmp` staging dir, but `.pyc` files embed the
absolute path they were compiled from, so `--stage ~/work` would have baked a
home directory into a file nothing ever scanned.

Fixed three ways: the subprocess runs with `-B` and `PYTHONDONTWRITEBYTECODE=1`,
`prune` removes any `__pycache__`, and `inspect_tree` treats one as a failure.
Found by the completeness diff in step 9 — the size mismatch was the only
symptom.

### 7. Redaction terms cannot protect binaries

4open's "Terms to redact" box applies to **text files only**; binaries are
served verbatim, and only owner/org/repo names are scrubbed automatically. That
is why step 3 *deletes* the two tracked vim swap files
(`vendor/sonobe_mod/.rust-toolchain.swp` and
`.../foldpot/.circuits_super.rs.swo`) rather than relying on redaction — each
embeds `xiang`, the hostname `xiang-ThinkPad-P16s-Gen-2`, and a home-directory
path.

---

## The restore side, in INSTALL.py

Implemented: `read_bigfiles_sums()` + `restore_bigfiles()`, called at the top of
`main()` before `install_toolchain()` and the dataset loop. `lzma` and
`tarfile` are stdlib, so `APT_PACKAGES` and `requirements.txt` are unchanged.

**Expected digests are read from `data/bigfiles.sha256`, never hardcoded.** tar
records mtimes, so rebuilding the pack from identical inputs yields a different
sha256; a constant in `INSTALL.py` would drift silently the first time the
snapshot was rebuilt. `prepare.py` writes that file in step 4 — the pack digest
on the first line, then one line per member.

Behaviour:

| Situation | Result |
|---|---|
| pack + sums absent | no-op — an ordinary full checkout has the files loose |
| all 13 present and matching | no-op, after one hashing pass |
| some missing, or one altered | verify pack sha256 → extract → re-verify all 13 |
| pack altered in transit | raises, naming expected vs got |
| pack present, sums missing (or vice versa) | raises — refuses to guess |
| pack holds a member with no recorded digest | raises — refuses to extract unverifiable files |

It raises rather than half-restoring: a silently missing fixture would surface
much later as an unexplained eval failure.

Verified on the real snapshot: all 13 restored files hash **identical to git
HEAD**, and every failure mode above was exercised.

**Ordering is safe.** None of `clean_email` / `clean_dna` / `clean_binexec`
touches the restore targets (they wipe `samples/binexec_merged128k`,
`samples/merge_records`, `EMAIL_MAILDIR`, and `src_sig/chr17_variants`), so
restoring once before the loop is not undone by it. It runs unconditionally
because these fixtures are inputs regardless of which corpus is selected — the
Rust `DatasetSpec` `CLAM.sig_file` is one of them.

`data/.gitignore` in the snapshot already lists the 13 restore targets (step 4
appends them), so a reviewer's clone stays clean after install.

> Rebuilding the snapshot after any `INSTALL.py` change also rebuilds the pack,
> and its sha256 will differ — that is expected, and `data/bigfiles.sha256` is
> regenerated alongside it.

---

## Timeline

| Date | What |
|---|---|
| **2026-08-25** | artifact **URL** is final — it is already cited at `src/apdx_open_sci.tex:16` as `https://anonymous.4open.science/r/bora-sec27`, so the minted ID must match exactly |
| **2026-08-28** | artifact **content** frozen — come back and pin the commit SHA on the 4open form (**T913**), a harder freeze than switching auto-update off |

Between those two dates, leave **Auto update ON** and **Commit blank**: that is
what lets the URL be final on the 25th while content still changes until the
28th.

---

## Gotchas

- **`curl` cannot verify the mirror.** 4open returns HTTP 403 to every
  non-browser agent, so a 403 means both "not minted" and "minted but
  bot-blocked". Step 9 exists because only a browser answers this.
- **Re-minting risks losing the ID.** If content is wrong after publishing, fix
  the source repo and push; auto-update picks it up within the hour.
- **Files > 8 MB are not truncated, they are absent.** There is no warning on
  the mirror — hence the hard fail in step 5.
- **Symlinks:** the tree carries 56, all relative and all resolving inside it.
  4open's handling of them is undocumented; step 9 asks you to eyeball a few.
- **GitHub is not enough for the Available badge** at camera-ready. The 4open
  link serves anonymous review only; a Zenodo/Software-Heritage DOI has to
  replace it afterwards.
