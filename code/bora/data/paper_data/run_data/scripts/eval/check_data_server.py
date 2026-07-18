#!/usr/bin/env python3
# ----------------------------------
# Designed by the paper author; function implementation by Claude Code 4.8.
# Code reviewed and audited by the author; the reported violations were
# manually spot-checked by the paper author.
# ----------------------------------
"""Provenance check for the per-server raw-data folders.

Each measurement folder under ``data/raw_data`` is named after the machine
the data was collected on:

    gcpm1   GCP M1 (Intel Xeon @ 2.00GHz, 96 cores, ~1411 GiB / 1.4 TB RAM)
    jet1tb  Jetstream2 large (AMD EPYC-Milan, 128 cores, ~961 GiB / 1 TB RAM)

Every run log embeds a *compute config dump* recording the machine it ran on.
This script verifies that the logs actually stored under each folder were
collected on the matching server, and reports any file whose config dump
points at a different machine.

What is checked (per the author's spec):
  - the members of every ``*.tgz`` archive in the folder (an archive may hold
    many log files, each with its own config dump), AND
  - the loose log files (``*.log`` / ``*.dat`` / ``*.txt`` / ...) sitting
    directly in the folder.

Server discrimination key: ``ram_total`` from the config dump is authoritative
(1.4 TB vs 1 TB cleanly separate the two machines); cpu model, logical-core
count and OS kernel tag are parsed for corroboration and disagreements are
surfaced as notes. A file whose config dump cannot be found/parsed is reported
as ``unknown`` (a warning, not a violation).

A second, independent check (archive identity): each ``*.tgz`` member also
reports its task in the log header (cargo ``test_<task>`` / a ``task`` or
``run/job`` config field). When that token disagrees with the archive's name
(e.g. a ``full_dlp.tgz`` whose log says ``full_dna``), it is flagged as a
TASK-NAME MISMATCH warning.

Reads : <paper_root>/data/raw_data/{gcpm1,jet1tb}/*
        (*.tgz members are extracted to
         <paper_root>/data/raw_data/extracted/<server>/<archive>/ and read
         there; that tree is git-ignored and regenerable.)
Writes: nothing but the extracted/ scratch tree; report goes to stdout.

Run from data/scripts/eval:  python3 check_data_server.py
Exit code is 1 if any violation is found, else 0.
"""

from __future__ import annotations

import re
import sys
import tarfile
from pathlib import Path

# common.py lives in the parent scripts/ directory.
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from common import get_paper_root, extract_tgz

# Server folders to audit, in report order.
SERVER_DIRS = ("gcpm1", "jet1tb")

# Canonical machine signatures. ``ram_gib`` is the authoritative key; the rest
# are corroboration. ``cpu`` is the lower-cased vendor/family token expected in
# the cpu model string; ``os_tag`` is a substring expected in the OS/kernel
# line.
SERVER_PROFILES = {
    "gcpm1":  {"ram_gib": 1411.0, "cpu": "intel", "cores": 96,  "os_tag": "gcp"},
    "jet1tb": {"ram_gib": 961.0,  "cpu": "amd",   "cores": 128, "os_tag": "generic"},
}

# A config dump's ram_total must land within this relative band of a profile's
# expected RAM to classify; the two profiles' bands (1411 +/-12% vs 961 +/-12%)
# do not overlap, so the classification is unambiguous.
RAM_REL_TOL = 0.12

# Loose files (not inside a *.tgz) with these suffixes are inspected; anything
# else sitting in the folder (the .tgz themselves, stray binaries) is skipped
# as a loose candidate -- the .tgz are handled via extraction instead.
LOOSE_SUFFIXES = {".log", ".dat", ".txt", ".out", ".dump"}

# ---- config-dump field regexes (matched only WITHIN a detected block, so the
# ---- runtime "RAM: 271 GB" job lines elsewhere in a log never leak in) -------
_RE_RAM = re.compile(r"(?:ram_total|ram)\s*:\s*([\d.]+)\s*GiB", re.IGNORECASE)
_RE_CPU_MODEL = re.compile(r"cpu_model\s*:\s*(.+)", re.IGNORECASE)
_RE_CPU = re.compile(r"cpu\s*:\s*(.+)", re.IGNORECASE)
_RE_CORES = re.compile(
    r"(?:logical_cores|cpu_count_proc|cpus)\s*:\s*(\d+)", re.IGNORECASE)
_RE_OS = re.compile(r"os\s*:\s*(.+)", re.IGNORECASE)


def _classify_by_ram(ram_gib: float | None) -> str | None:
    """Return the server whose expected RAM is closest to ``ram_gib`` within
    RAM_REL_TOL, or None if it matches neither (authoritative key)."""
    if ram_gib is None:
        return None
    best, best_rel = None, float("inf")
    for name, prof in SERVER_PROFILES.items():
        rel = abs(ram_gib - prof["ram_gib"]) / prof["ram_gib"]
        if rel < best_rel:
            best, best_rel = name, rel
    return best if best_rel <= RAM_REL_TOL else None


def _classify_by_cpu_cores(cpu: str | None, cores: int | None) -> str | None:
    """Fallback used only when ram_total is absent: classify by cpu vendor and
    core count when they agree (or when one decisive signal is present)."""
    votes = set()
    if cpu:
        low = cpu.lower()
        for name, prof in SERVER_PROFILES.items():
            if prof["cpu"] in low or ("xeon" in low and prof["cpu"] == "intel") \
                    or ("epyc" in low and prof["cpu"] == "amd"):
                votes.add(name)
    core_vote = None
    if cores is not None:
        for name, prof in SERVER_PROFILES.items():
            if prof["cores"] == cores:
                core_vote = name
    if core_vote:
        votes = {core_vote} if not votes else (votes & {core_vote}) or votes
    return next(iter(votes)) if len(votes) == 1 else None


def parse_config_block(lines) -> dict | None:
    """Scan ``lines`` (any iterable) for the FIRST compute-config dump and
    return its parsed fields, or None if no recognizable block is found.

    Recognizes three dump formats used across the run logs:
      - ``========== computer config ==========`` ... closed by a pure ``=``
        fence (cpus/ram/cpu/os labels),
      - ``== 0. MACHINE CONFIG ==`` ... closed by a blank line, and
      - ``[machine config]``        ... closed by a blank line
        (os/logical_cores/cpu_model/cpu_mhz/cpu_count_proc/ram_total labels).
    Streams line-by-line and stops at the first complete block, so it stays
    cheap on multi-GB logs.
    """
    block: list[str] | None = None
    end_on = None  # "fence" or "blank"
    for line in lines:
        stripped = line.strip()
        if block is None:
            low = stripped.lower()
            if "computer config" in low and stripped.startswith("="):
                block, end_on = [], "fence"
            elif "machine config" in low and (
                    stripped.startswith("==") or stripped.startswith("[")):
                block, end_on = [], "blank"
            continue
        # Inside a block: test the end condition, else accumulate.
        if end_on == "fence" and stripped and set(stripped) == {"="}:
            return _parse_block_fields(block)
        if end_on == "blank" and not stripped:
            return _parse_block_fields(block)
        block.append(line)
    # File ended mid-block (no closing marker) -- parse what we captured.
    if block:
        return _parse_block_fields(block)
    return None


def _parse_block_fields(block_lines: list[str]) -> dict:
    """Extract (ram_gib, cpu, cores, os) from a captured config block."""
    text = "\n".join(block_lines)

    m = _RE_RAM.search(text)
    ram_gib = float(m.group(1)) if m else None

    m = _RE_CPU_MODEL.search(text) or _RE_CPU.search(text)
    cpu = None
    if m:
        # drop the trailing " @ <freq>" so only the model/vendor remains.
        cpu = m.group(1).split(" @ ")[0].strip()

    m = _RE_CORES.search(text)
    cores = int(m.group(1)) if m else None

    m = _RE_OS.search(text)
    os_str = m.group(1).strip() if m else None

    return {"ram_gib": ram_gib, "cpu": cpu, "cores": cores, "os": os_str}


def classify_file(path: Path) -> dict | None:
    """Read ``path`` and classify which server its config dump indicates.

    Returns None if no config dump is found, else a dict with keys:
      server  -- "gcpm1" | "jet1tb" | None (None = parsed but inconclusive)
      basis   -- "ram" | "cpu+cores"  (which key decided)
      ram_gib, cpu, cores, os -- raw parsed fields
      notes   -- list of corroboration-disagreement strings
    """
    try:
        with path.open("r", encoding="utf-8", errors="replace") as fh:
            fields = parse_config_block(fh)
    except OSError as exc:
        return {"server": None, "basis": "error", "ram_gib": None, "cpu": None,
                "cores": None, "os": None, "notes": [f"read error: {exc}"]}
    if fields is None:
        return None

    server = _classify_by_ram(fields["ram_gib"])
    basis = "ram"
    if server is None and fields["ram_gib"] is None:
        server = _classify_by_cpu_cores(fields["cpu"], fields["cores"])
        basis = "cpu+cores"

    # Corroboration: flag any secondary signal that contradicts the verdict.
    notes: list[str] = []
    if server is not None:
        prof = SERVER_PROFILES[server]
        if fields["cpu"] and prof["cpu"] not in fields["cpu"].lower() \
                and not ("xeon" in fields["cpu"].lower() and prof["cpu"] == "intel") \
                and not ("epyc" in fields["cpu"].lower() and prof["cpu"] == "amd"):
            notes.append(f"cpu '{fields['cpu']}' != expected {prof['cpu']}")
        if fields["cores"] is not None and fields["cores"] != prof["cores"]:
            notes.append(f"cores {fields['cores']} != expected {prof['cores']}")
        if fields["os"] and prof["os_tag"] not in fields["os"].lower():
            notes.append(f"os '{fields['os']}' lacks tag '{prof['os_tag']}'")

    return {"server": server, "basis": basis, "notes": notes, **fields}


def extract_archive_members(archive: Path, dest_root: Path) -> list[Path]:
    """Extract every file member of ``archive`` into
    ``dest_root/<archive-stem>/`` and return their paths.

    Single-member archives are delegated to common.extract_tgz (the audited
    helper); multi-member archives are extracted here with the same
    "re-extract only when stale" behavior. Each archive gets its own
    sub-directory so members from different archives never collide and the
    extracted/ tree stays clean.
    """
    archive = Path(archive)
    dest_dir = dest_root / archive_stem(archive.name)

    with tarfile.open(archive, "r:gz") as tf:
        members = [m for m in tf.getmembers() if m.isfile()]
        if not members:
            return []
        if len(members) == 1:
            return [extract_tgz(archive, dest_dir=dest_dir)]

        out_paths = [dest_dir / Path(m.name).as_posix().lstrip("/")
                     for m in members]
        # Re-extract only when the dir is missing or older than the archive.
        fresh = dest_dir.is_dir() and all(p.exists() for p in out_paths) \
            and archive.stat().st_mtime <= dest_dir.stat().st_mtime
        if not fresh:
            dest_dir.mkdir(parents=True, exist_ok=True)
            try:
                tf.extractall(path=dest_dir, members=members, filter="data")
            except TypeError:  # Python < 3.12 has no 'filter' kwarg
                tf.extractall(path=dest_dir, members=members)
    return out_paths


# Dataset/task tokens a run log self-reports near its top, used to check a log
# inside an archive actually belongs to that archive (e.g. a full_dlp.tgz that
# really holds a full_dna run). Two well-anchored sources only -- a bare
# ``test_<x>`` is too loose (cargo's compile output mentions e.g. test_macros):
#   - a ``task`` / ``run/job`` config field, and
#   - the cargo test name ``::test_<task>``, but only on the command line.
_RE_TASK_FIELD = re.compile(r"\b(?:task|run/job)\s*:\s*(\S+)", re.IGNORECASE)
_RE_TASK_CMD = re.compile(r"::test_([A-Za-z0-9_]+)")


def archive_stem(name: str) -> str:
    """``full_clam.tgz`` -> ``full_clam`` (also tolerates *.tar.gz / *.tar)."""
    for suf in (".tar.gz", ".tgz", ".tar"):
        if name.endswith(suf):
            return name[: -len(suf)]
    return name


def _norm_task(name: str) -> str:
    """Canonicalize a task token so known aliases compare equal.

    ``clamav`` and ``clam`` are the same dataset (the log self-reports
    ``full_clamav`` while archives are named ``full_clam``), so fold
    ``clamav`` -> ``clam`` before comparing.
    """
    return name.replace("clamav", "clam")


def tasks_match(found: str, expected: str) -> bool:
    """True if the log's task and the archive name refer to the same task."""
    return _norm_task(found) == _norm_task(expected)


def log_task_name(path: Path, max_lines: int = 400) -> str | None:
    """Return the task/dataset token the log self-reports near its top, or None.

    Scans only the first ``max_lines`` lines (the header / config dump) so it
    stays cheap on multi-GB logs.
    """
    try:
        with path.open("r", encoding="utf-8", errors="replace") as fh:
            for i, line in enumerate(fh):
                if i >= max_lines:
                    break
                m = _RE_TASK_FIELD.search(line)
                if m:
                    return m.group(1)
                if "cmd=" in line or "cargo test" in line:
                    m = _RE_TASK_CMD.search(line)
                    if m:
                        return m.group(1)
    except OSError:
        return None
    return None


def _fmt(res: dict) -> str:
    """Compact one-line dump of the parsed signals for the report."""
    ram = f"{res['ram_gib']:.0f}GiB" if res.get("ram_gib") else "ram?"
    return (f"[{ram}, cpu={res.get('cpu') or '?'}, "
            f"cores={res.get('cores') if res.get('cores') is not None else '?'}]")


def main() -> int:
    raw = get_paper_root() / "data" / "raw_data"
    extracted_root = raw / "extracted"

    violations: list[tuple] = []   # (container_path, member, detected, expected, res)
    unknowns: list[tuple] = []     # (container_path, member, expected)
    task_mismatches: list[tuple] = []  # (archive_path, member, found_task, expected)
    ok_count = 0
    note_lines: list[str] = []     # corroboration warnings on otherwise-OK files

    for server in SERVER_DIRS:
        folder = raw / server
        if not folder.is_dir():
            print(f"!! folder missing, skipped: {folder}")
            continue

        for entry in sorted(folder.iterdir()):
            if entry.is_dir():
                continue

            if entry.name.endswith((".tgz", ".tar.gz")):
                items = [(entry, mp) for mp in
                         extract_archive_members(entry, extracted_root / server)]
            elif entry.suffix.lower() in LOOSE_SUFFIXES:
                items = [(None, entry)]   # loose file: its own container
            else:
                continue

            for container, member_path in items:
                # Archive/log identity check: the log's self-reported task name
                # should match the .tgz name it is shipped in (loose files have
                # no archive to compare against, so they are exempt).
                if container is not None:
                    task = log_task_name(member_path)
                    expected_task = archive_stem(container.name)
                    if task is not None and not tasks_match(
                            task, expected_task):
                        task_mismatches.append(
                            (container, member_path.name, task, expected_task))

                res = classify_file(member_path)
                container_disp = container if container is not None else member_path
                if res is None or res["server"] is None:
                    unknowns.append((container_disp, member_path.name, server))
                    continue
                if res["server"] != server:
                    violations.append((container_disp, member_path.name,
                                       res["server"], server, res))
                else:
                    ok_count += 1
                    if res["notes"]:
                        note_lines.append(
                            f"  {container_disp} :: {member_path.name} "
                            f"-> {server} but {'; '.join(res['notes'])}")

    # -------------------------------- report --------------------------------
    print("=" * 70)
    print(f"Server-provenance check over {raw}")
    print("=" * 70)

    print(f"\n### VIOLATIONS ({len(violations)}) "
          "-- file's config dump points at the wrong server")
    if not violations:
        print("  (none)")
    for container, member, detected, expected, res in violations:
        print(f"  container : {container}")
        print(f"    file    : {member}")
        print(f"    detected: {detected}   expected: {expected}   "
              f"{_fmt(res)} (by {res['basis']})")
        for n in res["notes"]:
            print(f"      note  : {n}")

    print(f"\n### UNKNOWN ({len(unknowns)}) "
          "-- no parseable config dump (warning, not a violation)")
    if not unknowns:
        print("  (none)")
    for container, member, expected in unknowns:
        print(f"  container : {container}")
        print(f"    file    : {member}   (folder claims: {expected})")

    print(f"\n### TASK-NAME MISMATCH ({len(task_mismatches)}) "
          "-- archive name vs the log's self-reported task")
    if not task_mismatches:
        print("  (none)")
    for archive, member, found, expected in task_mismatches:
        print(f"  archive : {archive}")
        print(f"    file    : {member}")
        print(f"    log task: {found}   expected (from archive name): {expected}")

    if note_lines:
        print(f"\n### CORROBORATION NOTES ({len(note_lines)}) "
              "-- RAM matched but a secondary signal disagreed")
        for ln in note_lines:
            print(ln)

    print(f"\n### OK: {ok_count} file(s) matched their folder.")
    print("-" * 70)
    print(f"summary: {ok_count} ok, {len(violations)} violation(s), "
          f"{len(unknowns)} unknown, {len(task_mismatches)} task-mismatch")

    return 1 if violations else 0


if __name__ == "__main__":
    sys.exit(main())
