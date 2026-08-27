# ----------------------------------
# Shared functions like analyze job cost.
# Framework defined by paper author, function body 
# completed by Claude Code 4.7
# Code reviewed, and running results audited by paper author
# ----------------------------------
from __future__ import annotations

import io
import os
import re
import statistics
from pathlib import Path


def get_paper_root() -> Path:
    """Return the absolute path of the paper-data root directory.

    Resolves the current working directory and walks up its ancestry
    until a recognized root segment is found: ``usenix27`` (the real
    paper repo) or ``run_data`` (bora's local paper-data mirror under
    ``data/paper_data/run_data``). The caller is guaranteed to invoke
    python3 from somewhere inside that root, but not necessarily from
    ``data/scripts/``/``scripts/``.
    """
    cwd = Path(os.getcwd()).resolve()
    parts = cwd.parts
    for anchor in ("usenix27", "run_data"):
        if anchor in parts:
            idx = parts.index(anchor)
            return Path(*parts[: idx + 1])
    raise RuntimeError(
        f"get_paper_root: neither 'usenix27' nor 'run_data' found in "
        f"cwd ancestry: {cwd}"
    )


def get_proj_root() -> Path:
    """Return the project root holding the raw corpus data.

    Two paper roots are supported (see get_paper_root):
    - ``run_data``: bora's local mirror, sitting at
      ``bora/data/paper_data/run_data`` -- the project root is just
      ``run_data``'s great-grandparent (``bora/``).
    - ``usenix27``: the real paper repo, sitting one or two directory
      levels above ``ZkregPlus/code/<name>``. The code dir was renamed
      ``new_zkregplus`` -> ``bora``; we try both names (new_zkregplus
      first for back-compat) across the paper root's parent and
      grandparent and return the first existing subtree.
    """
    paper = get_paper_root()
    if paper.name == "run_data":
        return paper.parents[2]
    for name in ("new_zkregplus", "bora"):
        rel = Path("ZkregPlus") / "code" / name
        for up in (paper.parents[0], paper.parents[1]):
            cand = up / rel
            if cand.is_dir():
                return cand
    raise RuntimeError(
        "get_proj_root: neither 'new_zkregplus' nor 'bora' found under "
        f"ZkregPlus/code 1-2 levels above {paper}"
    )


# --------------------------- data-collection server -------------------------
# The table generators read each dataset's run logs from a per-server subtree
# of data/raw_data/ -- the machine the data was collected on. Server-specific
# files (the *.tgz dumps and the Reef/Zombie run logs) live under
# data/raw_data/<server>/; machine-independent inputs live under
# data/raw_data/any_server/. Flip this one constant to re-point every
# generator at the other machine's logs.
SERVER_TO_USE = "jet1tb"         # alternative: "gcpm1"
# NB: the raw_data README/spec calls the 1 TB machine's folder "jet1t", but
# on-disk directory is "jet1tb"; this constant must match the directory name.


def raw_data_root() -> Path:
    """Absolute path of ``data/raw_data/`` under the paper root."""
    return get_paper_root() / "data" / "raw_data"


def server_file(name: str) -> Path:
    """raw_data path of a SERVER-SPECIFIC file (under the SERVER_TO_USE folder).

    Use for files produced by a timed run, which therefore live under
    ``data/raw_data/<server>/`` -- the ``*.tgz`` dumps and the Reef/Zombie
    run logs.
    """
    return raw_data_root() / SERVER_TO_USE / name


def any_server_file(name: str) -> Path:
    """raw_data path of a machine-independent file (under ``any_server/``).

    Use for inputs whose value does not depend on the timing machine: corpus
    listings, lookup-stat dumps, the scalability bundle, eval_effective.
    """
    return raw_data_root() / "any_server" / name


# ----------------------- Mal (CentOS x ClamAV) dataset ----------------------

def _clamav_version(readme: Path) -> tuple[str, str | None]:
    """Parse ``Version: ClamAV <ver>/<db>/ ...`` from the ClamAV README."""
    m = re.search(r"Version:\s*ClamAV\s+(\S+)", readme.read_text(errors="replace"))
    if not m:
        raise RuntimeError(f"_clamav_version: no 'Version: ClamAV' line in {readme}")
    field = m.group(1)                      # e.g. "0.103.11/27152/"
    parts = field.split("/")
    version = parts[0]
    db = parts[1] if len(parts) > 1 and parts[1] else None
    return version, db


# ClamAV .ldb logical-signature header fields -- the three ``;``-separated
# parts BEFORE the leaf subsignatures. A line is:
#   Name ; TargetBlock ; LogicalExpr ; Subsig0 ; Subsig1 ; ... ; SubsigN
# Leaf regexes are the subsigs only; these patterns let us verify the header
# shape so we ignore exactly the first three fields (never a subsig).
_LDB_TARGET = re.compile(
    r"(Engine|Target|Container|IconGroup\d|FileSize|NumberOfSections"
    r"|Intermediates):"
)
_LDB_LOGIC = re.compile(r"^[\d\s&|()<>=,]+$")   # subsig indices + boolean ops


def _count_signatures(main_dat: Path) -> tuple[int, int, int]:
    """Count (rules, hex_subsigs, pcre_subsigs) in a ClamAV ``main.dat``.

    Each non-comment, non-empty line is one ``.ldb`` logical signature:

        Name ; TargetBlock ; LogicalExpr ; Subsig0 ; Subsig1 ; ... ; SubsigN

    The leaf regexes are the subsignatures -- the ``;``-separated fields AFTER
    the three-field header (name, target block, logical expression). We verify
    the header shape on every line (field 1 is a target block, field 2 a pure
    boolean expression over subsig indices) so the leaf count can never be
    silently corrupted by a non-ldb line or a shifted header boundary. A
    subsignature is PCRE when it carries a ``/`` delimiter, else hex-based --
    which covers every hex offset anchor (absolute ``N:``, ``EP+-N:``, section
    ``Sx+N:``, version-info ``VI:``, floating ``*:``) and the ``::`` match
    modifiers (e.g. ``::i``); none of these contain ``/``.
    """
    rules = hexs = pcre = 0
    with main_dat.open(encoding="latin-1") as fh:
        for lineno, line in enumerate(fh, 1):
            line = line.rstrip("\n")
            if not line.strip() or line.lstrip().startswith("#"):
                continue
            fields = line.split(";")
            if len(fields) < 4:
                raise RuntimeError(
                    f"_count_signatures: {main_dat}:{lineno} has no subsignature "
                    f"({len(fields)} ;-fields): {line[:80]!r}")
            if not _LDB_TARGET.search(fields[1]) or not _LDB_LOGIC.match(fields[2]):
                raise RuntimeError(
                    f"_count_signatures: {main_dat}:{lineno} unexpected header "
                    f"shape; cannot locate subsig boundary: {line[:80]!r}")
            rules += 1
            for sub in fields[3:]:          # leaf subsignatures only
                if "/" in sub:
                    pcre += 1
                else:
                    hexs += 1
    if rules == 0:
        raise RuntimeError(f"_count_signatures: no signatures parsed from {main_dat}")
    return rules, hexs, pcre


def _detect_centos(clamav_dir: Path) -> tuple[str, str]:
    """Best-effort CentOS version from binary provenance in the ClamAV data.

    Returns ``(detected_version, evidence)``. The ``el7_<minor>`` RPM dist tag
    on bundled shared objects pins the minor release (the ``_9`` in ``el7_9``
    is the 7.9 update stream); the ``3.10.0-<build>`` kernel corroborates.
    No ``/etc/centos-release`` or ISO is on disk, so this is evidence, not
    proof -- the table itself reports the neutral "CentOS 7".
    """
    blob = ""
    sources = [clamav_dir / "README"]
    sources += sorted((clamav_dir / "config").glob("binexec_p*.dat"))
    for f in sources:
        if f.exists():
            blob += f.read_text(errors="replace")
    evidence = []
    minor = None
    m = re.search(r"el7_(\d+)", blob)
    if m:
        minor = m.group(1)
        evidence.append(f"dist tag el7_{minor}")
    k = re.search(r"3\.10\.0-(\d+)[.\w]*\.el7", blob)
    if k:
        evidence.append(f"kernel 3.10.0-{k.group(1)}")
    detected = f"7.{minor}" if minor else "7"
    return detected, "; ".join(evidence) if evidence else "no on-disk evidence"


def extract_mal_dataset(proj_root: Path | None = None) -> dict:
    """Extract real Mal (CentOS x ClamAV) dataset facts from the project tree.

    Reads, under ``<proj_root>/data``:
      - ``paper_data/clamav/README``      -> ClamAV version + db revision
      - ``paper_data/clamav/config/main.dat`` -> rule + leaf-subsig counts
      - ``samples/binexec_merged128k/``   -> doc count and size statistics
    plus a best-effort CentOS minor-version detection (see ``_detect_centos``).

    Returns a raw dict of measured values (no LaTeX formatting); the table
    generator (``eval/datasets.py``) renders these into the Mal row.
    """
    root = proj_root or get_proj_root()
    clamav_dir = root / "data" / "paper_data" / "clamav"
    main_dat = clamav_dir / "config" / "main.dat"
    corpus = root / "data" / "samples" / "binexec_merged128k"

    version, db = _clamav_version(clamav_dir / "README")
    rules, hexs, pcre = _count_signatures(main_dat)

    sizes = sorted(p.stat().st_size for p in corpus.iterdir() if p.is_file())
    if not sizes:
        raise RuntimeError(f"extract_mal_dataset: no files under {corpus}")
    centos, centos_evidence = _detect_centos(clamav_dir)

    return {
        "clamav_version": version,
        "clamav_db": db,
        "rules": rules,
        "ruleset_bytes": main_dat.stat().st_size,   # on-disk size of main.dat
        "subsigs": hexs + pcre,
        "subsigs_hex": hexs,
        "subsigs_pcre": pcre,
        "docs": len(sizes),
        "total_bytes": sum(sizes),
        "size_median": statistics.median(sizes),
        "size_std": statistics.pstdev(sizes),
        "size_min": sizes[0],
        "size_max": sizes[-1],
        "centos": "7",                 # neutral label reported in the table
        "centos_detected": centos,     # evidence-based minor (e.g. "7.9")
        "centos_evidence": centos_evidence,
    }


# ------------------- Dna (chr17 x NCBI ClinVar) dataset ---------------------

# Each generated regex file holds exactly one ``^.{N}LITERAL.*`` (no trailing
# newline), where N is the 0-based GRCh38 offset and LITERAL is a pure-ACGT
# allele. A file that does not match is a generation error and must surface.
_DNA_REGEX = re.compile(r"^\^\.\{(\d+)\}([ACGT]+)\.\*$")


def _log_field(log: Path, key: str) -> str:
    """Read a ``key:   value`` entry from a ``KEY: VALUE`` provenance log."""
    rx = re.compile(rf"^{re.escape(key)}:\s*(.+?)\s*$", re.MULTILINE)
    m = rx.search(log.read_text(errors="replace"))
    if not m:
        raise RuntimeError(f"_log_field: '{key}' not found in {log}")
    return m.group(1)


def analyze_dna_rule_shape(regex_dir: Path, bp_len: int = 32) -> dict:
    """Scan the generated chr17 regexes and summarize their shape.

    Every file under ``regex_dir`` holds one regex ``^.{N}LITERAL.*`` with no
    trailing newline, so its byte size equals the regex character length. ``N``
    is the 0-based GRCh38 offset of the variant site; ``LITERAL`` is the mutated
    ACGT allele, spanning ``bp_len`` bases by default and extended to cover the
    whole changed allele for structural variants. Returns rule/byte counts and
    length statistics (``avg_len``/``max_len`` reproduce docs/reef_regex.log).
    """
    files = sorted(regex_dir.glob("*.txt"))
    if not files:
        raise RuntimeError(f"analyze_dna_rule_shape: no *.txt under {regex_dir}")
    total_bytes = 0
    lengths: list[int] = []
    lit_lengths: list[int] = []
    offsets: list[int] = []
    n_extended = 0
    min_len, min_vcv = None, ""           # shortest regex (char length)
    max_len, max_vcv = -1, ""             # longest regex (char length)
    for f in files:
        text = f.read_text(errors="replace").strip()
        m = _DNA_REGEX.match(text)
        if not m:
            raise RuntimeError(
                f"analyze_dna_rule_shape: {f.name} not '^.{{N}}LITERAL.*': "
                f"{text[:60]!r}")
        literal = m.group(2)
        rlen = len(text)                  # == byte size (no trailing newline)
        total_bytes += f.stat().st_size
        lengths.append(rlen)
        lit_lengths.append(len(literal))
        offsets.append(int(m.group(1)))
        if len(literal) > bp_len:
            n_extended += 1
        if min_len is None or rlen < min_len:
            min_len, min_vcv = rlen, f.stem
        if rlen > max_len:
            max_len, max_vcv = rlen, f.stem
    return {
        "rules": len(files),
        "ruleset_bytes": total_bytes,        # sum of reef_regex/*.txt sizes
        "avg_len": sum(lengths) / len(lengths),
        "min_len": min_len,
        "min_vcv": min_vcv,
        "max_len": max_len,
        "max_vcv": max_vcv,
        "lit_min": min(lit_lengths),
        "n_extended": n_extended,
        "bp_len": bp_len,
        "n_min": min(offsets),
        "n_max": max(offsets),
    }


def parse_dna_skips(log: Path) -> dict:
    """Parse ``docs/reef_regex.log`` -> Dna variant drop provenance.

    ``gen_reef_regex.py`` emits, for chr17, a ``tally: ok=.. skip=.. fail=..``
    line followed by a ``name<TAB>reason`` list of every skipped variant (those
    whose allele cannot become a deterministic ACGT literal). Returns the
    processed/kept/skipped counts and a per-reason breakdown of the skips --
    the numbers cited in the §7.2 Dna drop footnote. This is the single source
    of truth for "65 dropped"; never hand-type it.
    """
    text = log.read_text(errors="replace")
    m = re.search(r"tally:\s*ok=(\d+)\s+skip=(\d+)\s+fail=(\d+)", text)
    if not m:
        raise RuntimeError(f"parse_dna_skips: 'tally:' line not found in {log}")
    n_kept, n_skipped, n_failed = (int(m.group(i)) for i in (1, 2, 3))
    # Skipped variants are listed one per line as "NAME<TAB>reason"; header
    # fields use "key:   value" (spaces, no tab) so they never match here.
    reasons: dict[str, int] = {}
    for reason in re.findall(r"^\S+\t(.+?)\s*$", text, re.MULTILINE):
        reasons[reason] = reasons.get(reason, 0) + 1
    if sum(reasons.values()) != n_skipped:
        raise RuntimeError(
            f"parse_dna_skips: listed reasons ({sum(reasons.values())}) "
            f"disagree with tally skip={n_skipped} in {log}")
    return {
        "n_processed": n_kept + n_skipped + n_failed,
        "n_kept": n_kept,
        "n_skipped": n_skipped,
        "n_failed": n_failed,
        "skip_reasons": reasons,
    }


def extract_dna_dataset(proj_root: Path | None = None) -> dict:
    """Extract real Dna (chr17 x NCBI ClinVar) dataset facts from the project tree.

    Reads, under ``<proj_root>/data/src_sig/chr17_variants``:
      - ``docs/chr17_sample.log``  -> reference accession + assembly
      - ``docs/retrieve_log.txt``  -> ClinVar snapshot version + chromosome
      - ``chr17_samples/NC_000017.11.reef.txt`` -> document byte size
      - ``reef_regex/*.txt``       -> rule count, ruleset byte size, rule shape
        (via ``analyze_dna_rule_shape``)
      - ``docs/reef_regex.log``    -> drop provenance (processed/kept/skipped +
        per-reason breakdown, via ``parse_dna_skips``)

    Returns a raw dict of measured values (no LaTeX formatting); the table
    generator (``eval/datasets.py``) renders these into the Dna row.
    """
    root = proj_root or get_proj_root()
    base = root / "data" / "src_sig" / "chr17_variants"
    sample_log = base / "docs" / "chr17_sample.log"
    retrieve_log = base / "docs" / "retrieve_log.txt"
    reef_regex_log = base / "docs" / "reef_regex.log"
    doc = base / "chr17_samples" / "NC_000017.11.reef.txt"
    regex_dir = base / "reef_regex"

    accession = _log_field(sample_log, "accession")
    description = _log_field(sample_log, "description")
    am = re.search(r"GRCh\d+(?:\.p\d+)?", description)
    assembly = am.group(0) if am else "GRCh38"
    shape = analyze_dna_rule_shape(regex_dir)
    drops = parse_dna_skips(reef_regex_log)

    return {
        "accession": accession,
        "assembly": assembly,
        "chromosome": _log_field(retrieve_log, "chromosome"),
        "doc_bytes": doc.stat().st_size,
        "clinvar_version": _log_field(retrieve_log, "clinvar_version"),
        "skip_log": str(reef_regex_log.relative_to(root)),
        **shape,
        **drops,
    }


# --------------------- Dlp (Enron x MS-DLP SIT) dataset ---------------------

# Each MS-DLP SIT policy is one line holding a keyword-proximity disjunction
#   (kw_1|...|kw_n).{0,N}re  |  re.{0,N}(kw_1|...|kw_n)
# i.e. a structured PII regex within N bytes of a corroborating keyword, in
# either order -- so a well-formed policy carries exactly two ``.{0,N}`` gaps,
# both with the same bound N. We don't parse the alternations; the gap count
# and the single shared N are what validate the shape and feed the table.
_DLP_GAP = re.compile(r"\.\{0,(\d+)\}")


def analyze_dlp_rule_shape(regex_dir: Path) -> dict:
    """Scan the MS-DLP SIT policy regexes and summarize their shape.

    Each SIT is represented either by a single top-level ``*.regex`` policy or
    by a sub-directory of alternation-extracted ``*.regex`` shards (one SIT per
    sub-directory -- the alternation was split across shards so an individual
    branch stays within the downstream compiler's size limit). The SIT (rule)
    count is therefore the number of top-level policies plus the number of
    sub-directories; the on-disk byte size and the shared proximity bound ``N``
    are measured over *all* ``*.regex`` files, recursively (raising if they
    disagree on ``N``, so a malformed policy can never be silently averaged
    away).
    """
    top_policies = sorted(regex_dir.glob("*.regex"))
    sit_subdirs = sorted(p for p in regex_dir.iterdir() if p.is_dir())
    all_files = sorted(regex_dir.glob("**/*.regex"))
    if not all_files:
        raise RuntimeError(f"analyze_dlp_rule_shape: no *.regex under {regex_dir}")
    total_bytes = 0
    gaps: set[int] = set()
    branch_counts: set[int] = set()
    for f in all_files:
        text = f.read_text(errors="replace")
        widths = [int(w) for w in _DLP_GAP.findall(text)]
        if not widths:
            raise RuntimeError(
                f"analyze_dlp_rule_shape: {f.name} has no '.{{0,N}}' "
                f"proximity gap: {text[:60]!r}")
        gaps.update(widths)
        branch_counts.add(len(widths))
        total_bytes += f.stat().st_size
    if len(gaps) != 1:
        raise RuntimeError(
            f"analyze_dlp_rule_shape: policies disagree on the gap bound N: "
            f"{sorted(gaps)}")
    return {
        # one SIT per top-level policy + one per sub-directory of shards
        "rules": len(top_policies) + len(sit_subdirs),
        "ruleset_bytes": total_bytes,        # sum of all *.regex sizes (recursive)
        "gap": gaps.pop(),                   # the shared N in '.{0,N}'
        "branches": sorted(branch_counts),   # branch count per shard/policy
    }


def extract_dlp_dataset(proj_root: Path | None = None,
                        regex_dir: Path | None = None) -> dict:
    """Extract real Dlp (Enron x MS-DLP SIT) dataset facts from the project tree.

    Reads, under ``<proj_root>/data``:
      - ``samples/email/src/maildir/``      -> doc count and size statistics
        (the RAW Enron corpus, walked recursively; the eval deliberately does
        NOT merge these into 128 KB folding units -- merging raises per-unit
        accept density and can span keyword-proximity windows across emails)
      - the MS-DLP regex set (``regex_dir``)  -> policy count, ruleset byte
        size, and proximity-gap bound (via ``analyze_dlp_rule_shape``)

    ``regex_dir`` defaults to ``src_sig/ms_dlp/regex_zombie``; the caller can
    override it (e.g. the table generator points it at
    ``regex_zombie_international`` for the full international SIT set).

    Returns a raw dict of measured values (no LaTeX formatting); the table
    generator (``eval/datasets.py``) renders these into the Dlp row.
    """
    root = proj_root or get_proj_root()
    maildir = root / "data" / "samples" / "email" / "src" / "maildir"
    if regex_dir is None:
        regex_dir = root / "data" / "src_sig" / "ms_dlp" / "regex_zombie"
    if not maildir.is_dir():
        raise RuntimeError(f"extract_dlp_dataset: corpus not found: {maildir}")

    sizes: list[int] = []
    for dirpath, _dirnames, filenames in os.walk(maildir):
        for name in filenames:
            sizes.append(os.path.getsize(os.path.join(dirpath, name)))
    if not sizes:
        raise RuntimeError(f"extract_dlp_dataset: no files under {maildir}")
    sizes.sort()
    shape = analyze_dlp_rule_shape(regex_dir)

    return {
        "docs": len(sizes),
        "total_bytes": sum(sizes),
        "size_median": statistics.median(sizes),
        "size_std": statistics.pstdev(sizes),
        "size_min": sizes[0],
        "size_max": sizes[-1],
        **shape,
    }


# --------------------------- FoldPot dump parsing ---------------------------

# Matches a trailing duration token like "424075 ms", "763 us", "12 s".
_TIME = r"(\d+)\s*(us|ms|s)\b"
_UNIT = {"us": 1e-6, "ms": 1e-3, "s": 1.0}

# Sections whose costs partition a single job (sum ~ that job's ALL JOBS total).
_PARTITION = ("setup", "phase1_main_folding", "groth16_main",
              "phase2_cyclepair_folding", "decider_proof")
# Partition sections + the diagnostic per-step folding sum.
_SECTION_KEYS = _PARTITION + ("phase1_folding_steps_total",)


def _secs(value: str, unit: str) -> float:
    return int(value) * _UNIT[unit]


def _find(text: str, label: str, *, all: bool = False):
    """Find ``label`` ... ``<n><unit>`` anchored at end-of-line; return seconds."""
    rx = re.compile(label + r"[^\n]*?" + _TIME + r"\s*$", re.MULTILINE)
    if all:
        return [_secs(m.group(1), m.group(2)) for m in rx.finditer(text)]
    m = rx.search(text)
    if not m:
        raise RuntimeError(f"marker not found: {label!r}")
    return _secs(m.group(1), m.group(2))


def _phase_total(text: str, phase: int) -> float:
    """Sum of all PERF 1007 'Phase <phase> step N' durations (seconds)."""
    rx = re.compile(rf"Phase {phase} step \d+:[^\n]*?" + _TIME + r"\s*$",
                    re.MULTILINE)
    times = [_secs(m.group(1), m.group(2)) for m in rx.finditer(text)]
    if not times:
        raise RuntimeError(f"no 'Phase {phase} step' lines found")
    return sum(times)


def _prove_step_costs(text: str) -> list:
    """Per-step folding costs (seconds), in order: Phase 1 steps then Phase 2."""
    rx = re.compile(r"prove_step cost: i: \d+,[^\n]*?" + _TIME + r"\s*$",
                    re.MULTILINE)
    return [_secs(m.group(1), m.group(2)) for m in rx.finditer(text)]


def _phase_num_steps(text: str, phase: int) -> int:
    m = re.search(rf"Phase {phase} step 7:.*?n_steps:\s*(\d+)", text)
    if not m:
        raise RuntimeError(f"'Phase {phase} step 7 ... n_steps' not found")
    return int(m.group(1))


def _opt(fn, *args, **kwargs):
    """Call ``fn``; return None instead of raising RuntimeError (marker absent)."""
    try:
        return fn(*args, **kwargs)
    except RuntimeError:
        return None


def _sum_present(*vals):
    """Sum the non-None values; None if all are absent."""
    present = [v for v in vals if v is not None]
    return sum(present) if present else None


def _split_by_job(text: str) -> list:
    """Group lines by their '[job N]' prefix; return [(job_id, text), ...] sorted.

    Lines without a '[job N]' prefix (multi-line spill, warnings) are dropped;
    every timing marker we parse is single-line and prefixed.
    """
    jobs: dict[int, list] = {}
    for line in text.splitlines():
        m = re.match(r"\[job (\d+)\]", line)
        if m:
            jobs.setdefault(int(m.group(1)), []).append(line)
    if not jobs:
        raise RuntimeError("no '[job N]' lines found in dump")
    return [(jid, "\n".join(jobs[jid])) for jid in sorted(jobs)]


def _aggregate(rows: list, keys) -> dict:
    """{key: {'avg': mean, 'total': sum}} over rows where the key is non-None."""
    agg = {}
    for k in keys:
        vals = [r[k] for r in rows if r.get(k) is not None]
        agg[k] = ({"avg": sum(vals) / len(vals), "total": sum(vals)}
                  if vals else {"avg": None, "total": None})
    return agg


def _job_cost(jtext: str) -> dict:
    """Itemized section timings (seconds) for ONE job's lines; None if absent."""
    s0 = _opt(_find, jtext, r"FoldPot Step 0:")
    s1 = _opt(_find, jtext, r"FoldPot Step 1:")
    d1 = _opt(_find, jtext, r"set up driver 1")
    # driver2 has no inline total; take the 2nd 'Driver New' preprocess+batch block.
    pk = _find(jtext, r"Driver New: Step 3: preprocess keys", all=True)
    bp = _find(jtext, r"Driver New: Step 4: batch param", all=True)
    if None not in (s0, s1, d1) and len(pk) >= 2 and len(bp) >= 2:
        setup = s0 + s1 + d1 + pk[1] + bp[1]
    else:
        setup = None

    n1 = _opt(_phase_num_steps, jtext, 1)
    costs = _prove_step_costs(jtext)
    return {
        "setup": setup,
        "phase1_main_folding": _opt(_phase_total, jtext, 1),
        "groth16_main": _sum_present(_opt(_find, jtext, r"Job Step 2:"),
                                     _opt(_find, jtext, r"Job Step 3:")),
        "phase2_cyclepair_folding": _opt(_phase_total, jtext, 2),
        "decider_proof": _sum_present(_opt(_find, jtext, r"Job Step 5:"),
                                      _opt(_find, jtext, r"Job Step 6:"),
                                      _opt(_find, jtext, r"Job Step 7:")),
        # diagnostic only (excluded from the partition): per-step folding sum.
        "phase1_folding_steps_total": (sum(costs[:n1]) if n1 else None),
    }


def get_cost(dump_file) -> tuple:
    """Per-job itemized section timings (seconds) for a multi-job FoldPot dump.

    Partitions lines by their '[job N]' prefix and parses each job independently.
    Returns ``(per_job, aggregate)``:
      per_job   - list of {'job': id, <section>: seconds | None, ...}, one per job.
      aggregate - {section: {'avg': mean, 'total': sum}} over jobs where present.

    Partition sections: setup, phase1_main_folding, groth16_main,
    phase2_cyclepair_folding, decider_proof. Plus the diagnostic
    phase1_folding_steps_total (cross-checks get_main_folding_stats).
    """
    text = Path(dump_file).read_text()
    per_job = [{"job": jid, **_job_cost(jtext)}
               for jid, jtext in _split_by_job(text)]
    return per_job, _aggregate(per_job, _SECTION_KEYS)


def get_main_folding_stats(dump_file) -> tuple:
    """Per-job main (Phase 1) folding per-step stats (seconds) for a multi-job dump.

    Returns ``(per_job, aggregate)``:
      per_job   - list of {'job': id, num_steps, avg, min, max} (None stats when
                  the job has no main folding).
      aggregate - {stat: {'avg': mean, 'total': sum}} over folding jobs.
    """
    text = Path(dump_file).read_text()
    per_job = []
    for jid, jtext in _split_by_job(text):
        n1 = _opt(_phase_num_steps, jtext, 1)
        main = _prove_step_costs(jtext)[:n1] if n1 else []
        if main:
            per_job.append({"job": jid, "num_steps": n1, "avg": sum(main) / n1,
                            "min": min(main), "max": max(main)})
        else:
            per_job.append({"job": jid, "num_steps": None, "avg": None,
                            "min": None, "max": None})
    return per_job, _aggregate(per_job, ("num_steps", "avg", "min", "max"))


def test_get_cost(dump_file) -> None:
    """Per job: per-phase folding per-step costs sum ~ that phase's PROVE-STEPS
    total (90% tolerance)."""
    text = Path(dump_file).read_text()

    for jid, jtext in _split_by_job(text):
        # Per-phase folding per-step sum vs Phase step-7 total.
        n1 = _opt(_phase_num_steps, jtext, 1)
        n2 = _opt(_phase_num_steps, jtext, 2)
        if n1 and n2:
            costs = _prove_step_costs(jtext)
            assert len(costs) == n1 + n2, \
                f"job {jid} test2: {len(costs)} prove_step lines, expected {n1 + n2}"
            r_p1 = sum(costs[:n1]) / _find(jtext, r"Phase 1 step 7:")
            r_p2 = sum(costs[n1:n1 + n2]) / _find(jtext, r"Phase 2 step 7:")
            print(f"[job {jid}][test2] phase1 {r_p1:.1%} ({n1} steps), "
                  f"phase2 {r_p2:.1%} ({n2} steps)")
            assert r_p1 >= 0.90 and r_p2 >= 0.90, f"job {jid} test2: folding <90%"
        else:
            print(f"[job {jid}][test2] skipped (no folding)")
    print("test_get_cost: OK")


def test_get_main_folding_stats(dump_file) -> None:
    """Per folding job: num_steps*avg cross-checks get_cost's per-step folding
    total. Bar 95%."""
    mf_per_job, _ = get_main_folding_stats(dump_file)
    cost_per_job, _ = get_cost(dump_file)
    cost_by_job = {r["job"]: r for r in cost_per_job}

    for row in mf_per_job:
        jid = row["job"]
        if row["num_steps"] is None:
            print(f"[job {jid}] no main folding, skipped")
            continue
        ref = cost_by_job[jid]["phase1_folding_steps_total"]
        recon = row["num_steps"] * row["avg"]
        r = recon / ref
        print(f"[job {jid}] num_steps={row['num_steps']}, avg={row['avg']:.2f}s, "
              f"min={row['min']:.2f}s, max={row['max']:.2f}s | recon/ref={r:.1%}")
        assert r >= 0.95, f"job {jid}: {r:.1%} (<95%)"
    print("test_get_main_folding_stats: OK")


# ----------------------------------------------------------------------------
# Zombie-vs-BORA comparison helpers (used by eval/gen_zombie_table.py).
# All dataset sizes are sourced from the SAME extractors that feed
# eval/datasets.py, so the comparison agrees with tab:datasets.
# ----------------------------------------------------------------------------

def bora_net_cost(dump_file) -> float:
    """BORA net prover cost (seconds): Phase-1 (main-circuit) folding time,
    summed across every '[job N]' in the dump.

    This is the sum of the eight Phase-1 sub-steps (circuit selection, commit
    to witness, main folding, ...) per job -- identical to the ``net`` used in
    the Reef comparison (tab:dna-reef-bora). Works for both the single-job DNA
    dump (-> 3.16 hr) and the 8-job full-ClamAV dump (-> 117.00 hr, the sum
    over the 8 jobs; Dlp is likewise 8 jobs -> 507.94 hr). Reuses ``get_cost``.
    """
    _, agg = get_cost(dump_file)
    total = agg["phase1_main_folding"]["total"]
    if total is None:
        raise RuntimeError(f"bora_net_cost: no phase1_main_folding in {dump_file}")
    return total


def _ensure_extracted(path) -> Path:
    """Return `path`, extracting it from a sibling `<path>.7z` if missing.

    The full-ClamAV dump (dump_bora_full_clam.dat, ~137 MB) is too large for
    GitHub's 100 MB limit, so it is committed compressed as
    dump_bora_full_clam.dat.7z and decompressed on first use. Smaller dumps
    (e.g. dump_dna.txt) ship uncompressed and hit the early return.
    """
    path = Path(path)
    if path.exists():
        return path
    archive = Path(str(path) + ".7z")
    if not archive.exists():
        raise FileNotFoundError(f"{path} (and no {archive} to extract)")
    import subprocess
    subprocess.run(["7z", "x", "-y", f"-o{archive.parent}", str(archive)],
                   check=True, stdout=subprocess.DEVNULL)
    if not path.exists():
        raise RuntimeError(f"_ensure_extracted: {archive} did not yield {path}")
    return path


def extract_tgz(archive, dest_dir=None) -> Path:
    """Extract a single-file ``.tgz`` log archive into ``dest_dir``.

    Used by the table generators to read run logs that are committed
    compressed (e.g. small_par_full_snark.txt.tgz). The member is flattened
    into ``dest_dir`` (no internal paths) and re-extracted only when missing
    or older than the archive, so repeated generator runs are cheap. Returns
    the path to the extracted file.

    ``dest_dir`` defaults to an ``extracted/`` sub-directory beside the
    archive (i.e. ``data/raw_data/extracted/``) so extraction never litters
    ``raw_data`` itself with derived files. Callers may still pass an explicit
    directory (e.g. a per-bundle work dir).
    """
    import tarfile

    archive = Path(archive)
    if dest_dir is None:
        dest_dir = archive.parent / "extracted"
    dest_dir = Path(dest_dir)
    if not archive.exists():
        raise FileNotFoundError(f"extract_tgz: archive not found: {archive}")
    dest_dir.mkdir(parents=True, exist_ok=True)
    with tarfile.open(archive, "r:gz") as tf:
        files = [m for m in tf.getmembers() if m.isfile()]
        if len(files) != 1:
            raise RuntimeError(
                f"extract_tgz: expected one file in {archive.name}, "
                f"found {len(files)}")
        member = files[0]
        member.name = Path(member.name).name           # flatten any path
        out = dest_dir / member.name
        if not out.exists() or archive.stat().st_mtime > out.stat().st_mtime:
            tf.extract(member, dest_dir)
    return out


# ----------------------------------------------------------------------------
# NUMA two-half dumps: full_<ds>.part1.tgz + full_<ds>.part2.tgz
# ----------------------------------------------------------------------------
# The two-half NUMA runner (run_full_clam_numa.py etc.) splits the 8-job
# manifest across two processes pinned to opposite NUMA halves. Each process
# renumbers its OWN jobs [job 0..3] locally, so the two part logs collide on
# [job 0..3]. The GLOBAL manifest id survives only in the 'PROBE FILE job J
# <path>' lines (J indexes binexec_p<J>.dat, 0..7): a part folds its slice in
# ascending id order and logs it as local [job 0..n-1], so local k == the k-th
# ascending PROBE id. We recover the real id per part, re-tag [job k] ->
# [job <global>], and concatenate both parts into ONE dump so every existing
# analyzer (get_cost / bora_cost_breakdown / get_main_folding_stats /
# parse_log) works unchanged.

_JOB_TAG_RE = re.compile(r"^\[job (\d+)\]")
_PROBE_RE = re.compile(r"^PROBE FILE job (\d+)\b")


def _part_index(fname: str) -> int:
    """Numeric part index from 'full_clam.part<N>.tgz' (for part1<part10)."""
    m = re.search(r"\.part(\d+)\.tgz$", fname)
    return int(m.group(1)) if m else 0


def _part_job_map(text: str) -> dict:
    """Map one part's LOCAL [job k] -> REAL global manifest id.

    Global ids are the distinct 'PROBE FILE job J' values; local ids are the
    distinct leading '[job k]' tags. Aligns the k-th ascending local id to the
    k-th ascending global id. Returns {} when PROBE lines are absent or the two
    id sets differ in size (caller falls back to an offset re-tag).
    """
    globals_ = sorted({int(m.group(1)) for ln in text.splitlines()
                       for m in [_PROBE_RE.match(ln)] if m})
    locals_ = sorted({int(m.group(1)) for ln in text.splitlines()
                      for m in [_JOB_TAG_RE.match(ln)] if m})
    if not globals_ or len(globals_) != len(locals_):
        return {}
    return dict(zip(locals_, globals_))


def _retag_jobs(text: str, jobmap: dict) -> str:
    """Rewrite each line's leading '[job k]' to '[job jobmap[k]]'. Lines with
    no leading job tag (or a k absent from jobmap) pass through unchanged."""
    out = []
    for ln in text.splitlines(keepends=True):
        m = _JOB_TAG_RE.match(ln)
        if m and int(m.group(1)) in jobmap:
            ln = f"[job {jobmap[int(m.group(1))]}]" + ln[m.end():]
        out.append(ln)
    return "".join(out)


def _read_part_log(part_tgz) -> str:
    """Un-nest a part's run log: full_<ds>.part<N>.tgz holds one nested
    '*.log.tgz' (plus per-job logs/ files, ignored); that nested tgz holds
    exactly the run log. Return its text."""
    import tarfile

    with tarfile.open(part_tgz, "r:gz") as tf:
        inner = [m for m in tf.getmembers()
                 if m.isfile() and m.name.endswith(".log.tgz")]
        if len(inner) != 1:
            raise RuntimeError(
                f"_read_part_log: expected one '*.log.tgz' in "
                f"{Path(part_tgz).name}, found {len(inner)}")
        blob = tf.extractfile(inner[0]).read()
    with tarfile.open(fileobj=io.BytesIO(blob), mode="r:gz") as itf:
        logs = [m for m in itf.getmembers() if m.isfile()]
        if len(logs) != 1:
            raise RuntimeError(
                f"_read_part_log: expected one log in {inner[0].name}, "
                f"found {len(logs)}")
        return itf.extractfile(logs[0]).read().decode("utf-8", errors="replace")


def extract_parts_tgz(part_paths, dest_dir=None) -> Path:
    """Combine NUMA two-half dumps into ONE analyzable log; return its path.

    The multi-part analog of extract_tgz. Un-nests each part's run log,
    re-tags its LOCAL [job k] to the REAL global manifest id (PROBE-FILE
    alignment; falls back to a cumulative offset when PROBE lines are absent
    so the parts never collide), and concatenates the parts (in part order)
    into '<base>.combined.log' under dest_dir (default: 'extracted/' beside
    the first part). Re-combined only when missing or older than any input.
    """
    part_paths = sorted((Path(p) for p in part_paths),
                        key=lambda p: _part_index(p.name))
    if not part_paths:
        raise RuntimeError("extract_parts_tgz: no part archives given")
    for p in part_paths:
        if not p.exists():
            raise FileNotFoundError(f"extract_parts_tgz: part not found: {p}")

    first = part_paths[0]
    base = re.sub(r"\.part\d+\.tgz$", "", first.name)
    dest_dir = Path(dest_dir) if dest_dir is not None else first.parent / "extracted"
    dest_dir.mkdir(parents=True, exist_ok=True)
    out = dest_dir / f"{base}.combined.log"

    newest = max(p.stat().st_mtime for p in part_paths)
    if out.exists() and out.stat().st_mtime >= newest:
        return out

    offset, combined = 0, []
    for p in part_paths:
        text = _read_part_log(p)
        jobmap = _part_job_map(text)
        if not jobmap:                      # no PROBE ids: keep parts separable
            locs = sorted({int(m.group(1)) for ln in text.splitlines()
                           for m in [_JOB_TAG_RE.match(ln)] if m})
            jobmap = {loc: offset + i for i, loc in enumerate(locs)}
        offset = max([offset] + list(jobmap.values())) + 1
        text = _retag_jobs(text, jobmap)
        combined.append(text if text.endswith("\n") else text + "\n")

    out.write_text("".join(combined))
    return out


def resolve_server_dump(name, dest_dir=None) -> Path:
    """Resolve a dataset dump to a single extracted log, PREFERRING the NUMA
    two-half parts over the single-process archive.

    Given a base archive name (e.g. 'full_clam.tgz'), if
    'full_clam.part*.tgz' exist under the active server folder they take
    PRIORITY and are combined via extract_parts_tgz; otherwise the single
    'full_clam.tgz' is read via extract_tgz. A non-.tgz name resolves to its
    server_file path unchanged (analyzers _ensure_extracted as needed).
    """
    if not str(name).endswith(".tgz"):
        return server_file(name)
    base = name[:-len(".tgz")]
    server_dir = raw_data_root() / SERVER_TO_USE
    parts = sorted(server_dir.glob(base + ".part*.tgz"),
                   key=lambda p: _part_index(p.name))
    if parts:
        return extract_parts_tgz(parts, dest_dir)
    return extract_tgz(server_file(name), dest_dir)


def bora_cost_breakdown(dump_file) -> dict:
    """BORA Phase-1 main-folding cost broken down across jobs.

    Returns {n_jobs, net, wall} in seconds:
      net  - total compute, summed over all jobs (= bora_net_cost).
      wall - wall-clock time when the jobs run fully in parallel, i.e. the
             slowest single job (max per-job Phase-1 folding).
    For the single-job DNA dump net == wall. For the 8-job full-ClamAV dump
    net is the 8-job sum and wall is the slowest job. Reuses get_cost.
    """
    per_job, agg = get_cost(_ensure_extracted(dump_file))
    net = agg["phase1_main_folding"]["total"]
    jobs = [r["phase1_main_folding"] for r in per_job
            if r["phase1_main_folding"] is not None]
    if net is None or not jobs:
        raise RuntimeError(f"bora_cost_breakdown: no phase1_main_folding in {dump_file}")
    return {"n_jobs": len(jobs), "net": net, "wall": max(jobs)}


# Dlp's regex set is the full international SIT set (matches eval/datasets.py).
_DLP_ZOMBIE_REGEX = ("data", "src_sig", "ms_dlp", "regex_zombie_international")

_dataset_facts_cache: dict = {}


def _dataset_facts(dataset: str) -> dict:
    """Cached extract_*_dataset() result for 'mal'|'dna'|'dlp', using the SAME
    sources as eval/datasets.py (the Enron walk is expensive -- cache it)."""
    d = dataset.lower()
    if d in _dataset_facts_cache:
        return _dataset_facts_cache[d]
    if d == "mal":
        facts = extract_mal_dataset()
    elif d == "dna":
        facts = extract_dna_dataset()
    elif d == "dlp":
        rd = get_proj_root().joinpath(*_DLP_ZOMBIE_REGEX)
        facts = extract_dlp_dataset(regex_dir=rd)
    else:
        raise ValueError(f"_dataset_facts: unknown dataset {dataset!r}")
    _dataset_facts_cache[d] = facts
    return facts


def zombie_regex_bytes(dataset: str) -> int:
    """Total regex-set bytes for `dataset`:
      mal -> on-disk paper_data/clamav/config/main.dat size
      dna -> on-disk sum of reef_regex/*.txt sizes
      dlp -> pattern+keyword bytes (pat_len+kws_len summed over the measured
             Zombie SIT instances) -- the accurate cost-driver measure, NOT
             the on-disk .regex size (~2x larger: it writes both sub-patterns
             twice for the bidirectional proximity form, plus regex syntax).
             See dlp_patkws_bytes.
    Mal/Dna match tab:datasets' on-disk 'Size'; Dlp uses the pattern basis.
    """
    if dataset.lower() == "dlp":
        return dlp_patkws_bytes()
    return _dataset_facts(dataset)["ruleset_bytes"]


_dlp_clean_cache: dict | None = None


def _dlp_clean_corpus() -> dict:
    """Step-1 (RE2-screened) clean Dlp corpus -- the emails actually evaluated.

    tab:datasets reports this basis (eval/datasets.py applies it), so every
    downstream table must use it too. Reading the raw maildir instead made
    tab:compare-zombie-bora and tab:compare-all overstate the Dlp speedup by
    3.26% (843x vs the correct 816x). impl.tex pins the clean corpus at
    "96.85% by size" of the raw maildir: 1,376,362,308 / 1,421,183,736.

    Loaded lazily by path: eval/datasets.py imports this module, so a
    top-level import here would be circular, and `eval` is not a package.
    """
    global _dlp_clean_cache
    if _dlp_clean_cache is None:
        import importlib.util
        import sys as _sys
        # resolve next to this file so it works from both paper roots:
        # usenix27/data/scripts/ and bora/.../run_data/scripts/
        p = Path(__file__).resolve().parent / "eval" / "datasets.py"
        spec = importlib.util.spec_from_file_location("_bora_datasets", p)
        mod = importlib.util.module_from_spec(spec)
        # dataclasses resolves annotations via sys.modules[cls.__module__];
        # register before exec or @dataclass in datasets.py raises.
        _sys.modules["_bora_datasets"] = mod
        spec.loader.exec_module(mod)
        _dlp_clean_cache = mod.dlp_step1_corpus(get_paper_root(), get_proj_root())
    return _dlp_clean_cache


def dataset_corpus_bytes(dataset: str) -> int:
    """Total document-corpus bytes for `dataset`, as tab:datasets reports it:
      mal -> sum of CentOS corpus file sizes   (total_bytes)
      dna -> chr17 file size                    (doc_bytes)
      dlp -> step-1 RE2-clean Enron set        (total_bytes; NOT the raw
             maildir -- see _dlp_clean_corpus)
    """
    d = dataset.lower()
    if d == "dlp":
        return _dlp_clean_corpus()["total_bytes"]
    facts = _dataset_facts(dataset)
    return facts["doc_bytes"] if d == "dna" else facts["total_bytes"]


def dataset_rule_count(dataset: str) -> int:
    """Rule (signature) count for `dataset`, the SAME value tab:datasets' Rules
    cell reports (mal: ClamAV logical signatures; dna: ClinVar variants; dlp:
    MS-DLP SITs). Reuses the cached dataset extractors so it cannot drift from
    Table 1. Used as the Reef per-signature multiplier in tab:compare-all."""
    return _dataset_facts(dataset)["rules"]


# Zombie measurement-log columns:
#   policy pat_len kws_len prox r1cs_cons prove_ms verify_ms proof_B status
_ZOMBIE_ROW = re.compile(
    r"^(\S+)\s+(\d+)\s+(\d+)\s+\d+\s+(\d+)\s+(\d+)\s+(\d+)\s+(\d+)\s+ok\s*$",
    re.MULTILINE,
)

# Zombie measurement log -- server-specific (resolved via SERVER_TO_USE).
_ZOMBIE_LOG = "run_zombie_regex_zombie_international.log"


def zombie_totals(log_file, str_len: int) -> dict:
    """Aggregate the Zombie log block for one STR_LENGTH over all 'ok' policies.

    Returns: n, str_len, total_regex_bytes (sum of pat_len+kws_len),
    total_r1cs, total_prove_s, total_verify_s, total_proof_bytes, and
    unit_cost = total_prove_s / (str_len * total_regex_bytes), i.e. seconds
    per (input-byte x regex-byte).
    """
    text = Path(log_file).read_text()
    start = re.search(rf"== STR_LENGTH = {str_len} ==", text)
    if not start:
        raise RuntimeError(f"zombie_totals: no block for STR_LENGTH={str_len}")
    rest = text[start.end():]
    end = re.search(r"^== STR_LENGTH", rest, re.MULTILINE)
    block = rest[: end.start()] if end else rest

    n = regex = r1cs = prove_ms = ver_ms = proof = 0
    rules = set()
    for m in _ZOMBIE_ROW.finditer(block):
        policy = m.group(1)
        pat, kws, cons, pms, vms, pb = map(int, m.groups()[1:])
        regex += pat + kws
        r1cs += cons
        prove_ms += pms
        ver_ms += vms
        proof += pb
        rules.add(policy.split("/")[0])   # top-level SIT defn (combs collapse)
        n += 1
    if n == 0:
        raise RuntimeError(f"zombie_totals: no 'ok' rows for STR_LENGTH={str_len}")
    prove_s = prove_ms / 1000.0
    return {
        "str_len": str_len,
        "n": n,                 # measured regex instances (comb variants)
        "n_rules": len(rules),  # distinct top-level SIT rules
        "total_regex_bytes": regex,
        "total_r1cs": r1cs,
        "total_prove_s": prove_s,
        "total_verify_s": ver_ms / 1000.0,
        "total_proof_bytes": proof,
        "unit_cost": prove_s / (str_len * regex),
    }


def dlp_patkws_bytes() -> int:
    """DLP regex size on the pattern-byte basis: sum of (pat_len + kws_len)
    over all measured Zombie SIT instances -- the two distinct sub-patterns
    per policy, each counted once (the automaton-size cost driver). Read from
    the Zombie measurement log.

    This is the accurate regex measure for the keyword-proximity SIT rules.
    The on-disk .regex size is ~2x larger because it writes both sub-patterns
    twice (the bidirectional proximity form) plus regex grouping/syntax, so it
    is NOT used for Dlp. (Mal/Dna keep their on-disk file sizes, which carry no
    such bidirectional duplication.)
    """
    return zombie_totals(server_file(_ZOMBIE_LOG), 2000)["total_regex_bytes"]
