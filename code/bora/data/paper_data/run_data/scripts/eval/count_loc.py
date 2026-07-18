#!/usr/bin/env python3
# ----------------------------------
# Designed by the paper author; implementation by Claude Code.
# Code reviewed and data checked by the paper author.
# ----------------------------------
"""Count lines of the author's own Rust code in new_zkregplus, by module.

Most modules are scanned recursively for ``*.rs`` so newly added files are
picked up automatically; only the FoldPot folder uses a fixed include list,
since it mixes upstream Sonobe sources with the author's own files.

Vendored / upstream code is excluded entirely: everything in sonobe_mod
outside the FoldPot file list, the ark-* forks under ``dependency/``, and
``data_processor/dependency/``.

Output: an itemized per-file, per-module listing followed by the total
number of lines of author-owned Rust code.
"""

from __future__ import annotations

import argparse
import os
from dataclasses import dataclass
from pathlib import Path

# Absolute root of the code tree. Override with --code-root or $BORA_CODE_ROOT.
# The code dir was renamed new_zkregplus -> bora; prefer new_zkregplus when it
# exists, else fall back to bora (keep the legacy name for the not-found error).
_CODE_BASE = Path(
    "/home/xiang/Desktop/NewResearch/Projects/ZkregPlusAll/ZkregPlus/code"
)


def _default_code_root() -> Path:
    for name in ("new_zkregplus", "bora"):
        cand = _CODE_BASE / name
        if cand.is_dir():
            return cand
    return _CODE_BASE / "new_zkregplus"


CODE_ROOT = _default_code_root()


@dataclass(frozen=True)
class Module:
    """One logical module of the system.

    ``files`` non-empty  -> FIXED include list (basenames under ``base``); no
                            directory scan. Used only for FoldPot.
    ``files`` empty       -> recursively scan ``base`` for ``*.rs``, skipping
                            any path with a segment in ``exclude_dirs`` or a
                            basename in ``exclude_files``.
    """

    name: str
    base: str  # path relative to the code root
    files: tuple[str, ...] = ()
    exclude_dirs: tuple[str, ...] = ()
    exclude_files: tuple[str, ...] = ()


# --------------------------------------------------------------------------
# The one place to edit when modules are added or dropped.
# --------------------------------------------------------------------------
MODULES: list[Module] = [
    Module("Regex parser & preprocessing", "data_processor/src"),
    Module(
        "Main framework (circuits, gadgets, driver)",
        "zkregplus/src",
        exclude_dirs=("data_to_move", "scripts_to_move", ".claude"),
    ),
    Module("Common utils", "utils/src"),
    Module("Paper-data generator", "paper_data_gen/src"),
    Module(
        "FoldPot framework",
        "sonobe_mod/folding-schemes/src/folding/foldpot",
        files=(
            # FIXED list: this folder mixes upstream Sonobe + author code.
            "batch_proc.rs",
            "circuits_super.rs",
            "container_config.rs",
            "cyclepair.rs",
            "decider_eth_circuit_super.rs",
            "driver.rs",
            "from_field.rs",
            "mod_super.rs",
            "qa_nizk.rs",
            "sigma_cyclepair.rs",
            "sigma_ir1cs.rs",
            "test_convert.rs",
            "utils.rs",
            "veccom.rs",
        ),
    ),
]


# Layout prefixes. bora relocated the flat new_zkregplus tree into crates/
# (the workspace: data_processor/utils/zkregplus), vendor/ (sonobe_mod), and
# attic/crates/ (the retired paper_data_gen). Try the flat path first for
# new_zkregplus back-compat, then bora's relocations. First existing wins.
_BASE_PREFIXES = ("", "crates", "vendor", "attic/crates")


def _resolve_base(root: Path, base: str) -> Path:
    """Absolute dir for a module base, tolerant of the new_zkregplus (flat) vs
    bora (crates/ vendor/ attic/) layouts. Falls back to the flat path so a
    genuine miss names the plain base in the error."""
    for pref in _BASE_PREFIXES:
        cand = (root / pref / base if pref else root / base).resolve()
        if cand.is_dir():
            return cand
    return (root / base).resolve()


def resolve_files(mod: Module, root: Path) -> list[Path]:
    """Return the absolute ``*.rs`` paths counted for ``mod``, sorted.

    For a fixed-list module every listed file must exist; a missing one is a
    hard error so a rename/removal fails loudly instead of silently
    undercounting. For a scanned module, paths under any excluded directory
    segment or matching an excluded basename are dropped.
    """
    base = _resolve_base(root, mod.base)
    if not base.is_dir():
        raise FileNotFoundError(f"module base not found: {base}")

    if mod.files:
        paths = [base / name for name in mod.files]
        missing = [p for p in paths if not p.is_file()]
        if missing:
            raise FileNotFoundError(
                f"[{mod.name}] fixed-list files missing: "
                + ", ".join(p.name for p in missing)
            )
        return sorted(paths)

    out = []
    for p in base.rglob("*.rs"):
        rel_parts = p.relative_to(base).parts
        if any(seg in mod.exclude_dirs for seg in rel_parts):
            continue
        if p.name in mod.exclude_files:
            continue
        out.append(p)
    return sorted(out)


def count_lines(path: Path) -> int:
    """Physical line count of a file (newline-terminated or not)."""
    with path.open("rb") as fh:
        data = fh.read()
    if not data:
        return 0
    n = data.count(b"\n")
    return n if data.endswith(b"\n") else n + 1


def report(modules: list[Module], root: Path) -> None:
    """Print the itemized per-file listing and the grand total."""
    grand_lines = 0
    grand_files = 0

    for mod in modules:
        paths = resolve_files(mod, root)
        mod_base = _resolve_base(root, mod.base)
        sub_lines = 0
        print(f"== {mod.name}  ({mod.base})")
        for p in paths:
            n = count_lines(p)
            sub_lines += n
            print(f"  {n:6d}  {p.relative_to(mod_base)}")
        print(
            f"  ------ module subtotal: {sub_lines} lines "
            f"({len(paths)} files)\n"
        )
        grand_lines += sub_lines
        grand_files += len(paths)

    print("=" * 60)
    print(
        f"TOTAL Rust lines (author-owned): {grand_lines}   "
        f"across {grand_files} files in {len(modules)} modules"
    )


def main() -> None:
    default_root = os.environ.get("BORA_CODE_ROOT", str(CODE_ROOT))
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument(
        "--code-root",
        default=default_root,
        help="absolute path of the new_zkregplus code tree "
        "(default: built-in / $BORA_CODE_ROOT)",
    )
    args = ap.parse_args()

    root = Path(args.code_root).resolve()
    if not root.is_dir():
        ap.error(f"code root not found: {root}")
    report(MODULES, root)


if __name__ == "__main__":
    main()
