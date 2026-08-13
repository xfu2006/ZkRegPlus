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

## The nine steps

| # | Step | What happens |
|---|------|--------------|
| 1 | `preflight` | Python/git/lzma present, **no `.git/index.lock`**, HEAD reported, dirty-tree warning |
| 2 | `export` | `git archive HEAD:code/bora` → staging |
| 3 | `prune` | delete `attic/` and every editor swap file |
| 4 | `pack` | build `data/bigfiles.tar.xz`, drop the loose originals, extend `data/.gitignore` |
| 5 | `verify` | size / identity / symlink / entry-point checks — hard-fails the run |
| 6 | `initrepo` | `git init`, branch `artifact-sec27`, **one** squashed commit, neutral identity |
| 7 | `github` | **manual**: create the private repo, push |
| 8 | `4open` | **manual**: mint the URL, field by field |
| 9 | `browsercheck` | **manual**: verify the live mirror |

Steps 7–9 print instructions and stop. Nothing is pushed or published for you.

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

### 4. Redaction terms cannot protect binaries

4open's "Terms to redact" box applies to **text files only**; binaries are
served verbatim, and only owner/org/repo names are scrubbed automatically. That
is why step 3 *deletes* the two tracked vim swap files
(`vendor/sonobe_mod/.rust-toolchain.swp` and
`.../foldpot/.circuits_super.rs.swo`) rather than relying on redaction — each
embeds `xiang`, the hostname `xiang-ThinkPad-P16s-Gen-2`, and a home-directory
path.

---

## Wiring the pack into INSTALL.py

**Not done by this script** — it prepares the snapshot; restoring is
`INSTALL.py`'s job. The step to add is roughly:

```python
PACK      = os.path.join(DATA_DIR, "bigfiles.tar.xz")
PACK_SHA  = "<sha256 printed by prepare.py step 4>"

def install_bigfiles():
    """Restore the 13 fixtures that exceed 4open.science's 8 MB file limit."""
    if not os.path.exists(PACK):
        return                      # full checkouts already have them loose
    got = sha256_file(PACK)
    if got != PACK_SHA:
        raise RuntimeError("bigfiles.tar.xz sha256 mismatch: %s" % got)
    with tarfile.open(PACK, "r:xz") as tf:
        tf.extractall(ROOT)
```

Call it early in `main()` — before any dataset step, since
`data/src_sig/clamav/categories/main.dat` is an input to the eval path. `lzma`
and `tarfile` are stdlib, so `APT_PACKAGES` and `requirements.txt` need no
change.

`data/.gitignore` in the snapshot already lists the 13 restore targets (step 4
appends them), so a reviewer's clone stays clean after install.

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
