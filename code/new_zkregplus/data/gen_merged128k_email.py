# ---------------------------------------------------------------------
# gen_merged128k_email.py
#
# Author: Claude Code
# Note:   All code generated under the instructions of the paper
#         author, inspected block-by-block, and unit-tested.
#
# Merge files under email/src/maildir/ into 128KB blobs in
# email_merged128k/.  Writes canonical, human-readable records under
# merge_records/ (file manifest, merge map).
# ---------------------------------------------------------------------

import argparse
import hashlib
import os
import random
import re
import shutil
import sys
import tempfile
import time
import unittest
from concurrent.futures import ThreadPoolExecutor


# ---- constants ------------------------------------------------------

TARGET_SIZE = 128 * 1024  # 128 KB merge target

SCRIPT_DIR  = os.path.dirname(os.path.abspath(__file__))
SRC_DIR     = os.path.join(SCRIPT_DIR, "email", "src", "maildir")
TARGET_DIR  = os.path.join(SCRIPT_DIR, "email_merged128k")
RECORDS_DIR = os.path.join(SCRIPT_DIR, "merged_records_email")

MANIFEST_PATH    = os.path.join(RECORDS_DIR, "email_filelist.txt")
MAP_PATH         = os.path.join(RECORDS_DIR, "email_merge_map.txt")

UNIT_TEST_TMP = "/tmp/merge128k_tests"


# ---- step framing ---------------------------------------------------

# Mark step start.  Prints banner; returns wall-clock t0 for step_done.
def step_enter(name):
    print(f"entering step: {name}")
    return time.time()


# Mark step completion.  Prints elapsed wall-clock as H:MM:SS.
def step_done(name, t0):
    dt = int(time.time() - t0)
    h, rem = divmod(dt, 3600)
    m, s   = divmod(rem, 60)
    print(f"step {name} completed. total time: "
          f"{h}:{m:02d}:{s:02d}")


# ---- folder checks --------------------------------------------------

# Verify src_dir exists; create target_dir and records_dir if missing.
# Exits on hard errors.
def check_data_folders(src_dir, target_dir, records_dir):
    if not os.path.isdir(src_dir):
        print(f"ERROR: source dir not found: {src_dir}")
        sys.exit(1)
    os.makedirs(target_dir,  exist_ok=True)
    os.makedirs(records_dir, exist_ok=True)


# ---- block 2: canonical file list + manifest ------------------------

# Enumerate src_root recursively in canonical (relpath-sorted) order.
# Returns [{"relpath": str, "size": int}, ...].  os.walk's default
# order is filesystem-dependent, so we sort dirnames/filenames in
# place at every level.  Symlinks and non-regular files are skipped.
def canonical_file_list(src_root):
    out = []
    for dirpath, dirnames, filenames in os.walk(
            src_root, topdown=True, followlinks=False):
        dirnames.sort()
        filenames.sort()
        for fn in filenames:
            full = os.path.join(dirpath, fn)
            if os.path.islink(full) or not os.path.isfile(full):
                continue
            rp = os.path.relpath(full, src_root)
            out.append({"relpath": rp,
                        "size":    os.path.getsize(full)})
    # Defensive final sort; survives any future walker swap.
    out.sort(key=lambda r: (r["relpath"], r["size"]))
    return out


# Body text of the manifest: one "relpath\tsize\n" line per file.
def _filelist_body_text(file_list):
    return "".join(f"{r['relpath']}\t{r['size']}\n"
                   for r in file_list)


# Write the file list as human-readable UTF-8 text:
#   <relpath>\t<size>\n  ...
#   # sha256 = <hex>\n
# Trailer hashes the body so a human can recompute with sha256sum.
def write_file_manifest(file_list, path):
    body = _filelist_body_text(file_list)
    h    = hashlib.sha256(body.encode("utf-8")).hexdigest()
    tmp  = path + ".tmp"
    with open(tmp, "w", encoding="utf-8", newline="\n") as f:
        f.write(body)
        f.write(f"# sha256 = {h}\n")
    os.replace(tmp, path)


# Read the manifest; verify the sha256 trailer matches the body.
def read_file_manifest(path):
    with open(path, "r", encoding="utf-8") as f:
        lines = f.read().splitlines()
    if not lines or not lines[-1].startswith("# sha256 = "):
        raise ValueError("manifest missing sha256 trailer")
    expected = lines[-1].split("= ", 1)[1].strip()
    body     = "".join(l + "\n" for l in lines[:-1])
    actual   = hashlib.sha256(body.encode("utf-8")).hexdigest()
    if expected != actual:
        raise ValueError(
            f"manifest sha256 mismatch: {actual} != {expected}")
    out = []
    for ln in lines[:-1]:
        rp, sz = ln.split("\t")
        out.append({"relpath": rp, "size": int(sz)})
    return out


# ---- block 3: merge plan --------------------------------------------

# Greedy in-order packing into target_size bins.  Walks the canonical
# file list once, growing each bin while the next file fits; if the
# first file in a bin already exceeds target_size, it forms its own
# (solo, oversize) bin.  Target names are merged_NNNNN with width
# sized to len(file_list).  Returns
# [{"target_name": str, "list_src": [{"relpath","size"}, ...]}, ...].
def compute_merge_plan(file_list, target_size):
    plan = []
    if not file_list:
        return plan
    width = max(5, len(str(len(file_list))))
    start = 0
    while start < len(file_list):
        bin_src   = []
        bin_total = 0
        end       = start
        while end < len(file_list) and \
                bin_total + file_list[end]["size"] <= target_size:
            bin_src.append(file_list[end])
            bin_total += file_list[end]["size"]
            end += 1
        if not bin_src:
            # First file alone exceeds target_size: solo bin.
            bin_src.append(file_list[end])
            end += 1
        idx = len(plan)
        plan.append({
            "target_name": f"merged_{idx:0{width}d}",
            "list_src":    bin_src,
        })
        start = end
    assert sum(len(b["list_src"]) for b in plan) == len(file_list)
    for b in plan:
        if len(b["list_src"]) > 1:
            sz = sum(s["size"] for s in b["list_src"])
            assert sz <= target_size
    return plan


# ---- block 4: execute merge plan ------------------------------------

# Copy one bin's sources back-to-back into target_path.  Streams 1MB
# at a time; verifies the output size matches the planned total.
def _write_one_merged_file(src_root, target_path, list_src):
    expected = sum(s["size"] for s in list_src)
    tmp = target_path + ".tmp"
    with open(tmp, "wb") as out:
        for s in list_src:
            sp = os.path.join(src_root, s["relpath"])
            with open(sp, "rb") as f:
                shutil.copyfileobj(f, out, length=1 << 20)
    actual = os.path.getsize(tmp)
    if actual != expected:
        os.remove(tmp)
        raise RuntimeError(
            f"size mismatch on {target_path}: "
            f"{actual} != {expected}")
    os.replace(tmp, target_path)


# Materialize plan into target_dir at max parallelism.  Wipes
# target_dir first; uses ThreadPoolExecutor (I/O-bound, GIL-friendly).
def exec_merge_plan(src_root, target_dir, plan, jobs=None):
    jobs = jobs or os.cpu_count() or 1
    shutil.rmtree(target_dir, ignore_errors=True)
    os.makedirs(target_dir)
    with ThreadPoolExecutor(max_workers=jobs) as ex:
        futures = [
            ex.submit(
                _write_one_merged_file, src_root,
                os.path.join(target_dir, b["target_name"]),
                b["list_src"])
            for b in plan
        ]
        for fut in futures:
            fut.result()


# ---- block 5: merged-name pattern ----------------------------------

_MERGED_RE = re.compile(r"^merged_\d+$")


# ---- block 7: merge map + records glue -----------------------------

# Write the plan as canonical UTF-8 TSV:
#   <target_name>\t<relpath_1>\t<relpath_2>...\n
# One line per bin in plan order.  Rejects relpaths containing
# tab/newline (would corrupt the TSV).
def write_merge_map(plan, path):
    for b in plan:
        for s in b["list_src"]:
            rp = s["relpath"]
            if "\t" in rp or "\n" in rp or "\r" in rp:
                raise ValueError(
                    f"tab/newline in relpath: {rp!r}")
    tmp = path + ".tmp"
    with open(tmp, "w", encoding="utf-8", newline="\n") as f:
        for b in plan:
            row = [b["target_name"]] + [
                s["relpath"] for s in b["list_src"]]
            print("\t".join(row), file=f)
    os.replace(tmp, path)


# Read the merge map.  Target names must match merged_NNNNN and be
# strictly increasing in plan order.  Returns a list of dicts:
# [{"target_name": str, "list_src": [{"relpath": str}, ...]}, ...].
def read_merge_map(path):
    plan = []
    last = -1
    with open(path, "r", encoding="utf-8") as f:
        for ln in f:
            ln = ln.rstrip("\n\r")
            if not ln:
                continue
            parts = ln.split("\t")
            tn    = parts[0]
            if not _MERGED_RE.match(tn):
                raise ValueError(f"bad target_name: {tn!r}")
            idx = int(tn.split("_")[1])
            if idx <= last:
                raise ValueError(
                    f"non-monotonic target index: {tn}")
            last = idx
            plan.append({
                "target_name": tn,
                "list_src": [
                    {"relpath": rp} for rp in parts[1:]],
            })
    return plan


# Records glue.  Writes the file manifest + merge map.
def write_all_records(records_dir, file_list, plan):
    os.makedirs(records_dir, exist_ok=True)
    write_file_manifest(
        file_list,
        os.path.join(records_dir, "email_filelist.txt"))
    write_merge_map(
        plan,
        os.path.join(records_dir, "email_merge_map.txt"))


# ---- block 8: integration tests (run inside main, not --test) -----

# Integration test 1.  Pick n_samples random sources from the plan;
# for each, locate (target_name, offset, size) and verify the bytes
# in target_dir/<target_name> at [offset, offset+size] match the
# source file's bytes.  Hard-exits on mismatch.
def integ_test_random_sample_in_merged(src_root, target_dir, plan,
                                       n_samples, seed=20260520):
    flat = []
    for b in plan:
        off = 0
        for s in b["list_src"]:
            flat.append((s["relpath"], b["target_name"],
                         off, s["size"]))
            off += s["size"]
    if not flat:
        print("integ test 1: no sources to verify; skipped")
        return
    rng  = random.Random(seed)
    n_ok = 0
    for _ in range(n_samples):
        rp, tn, off, sz = rng.choice(flat)
        with open(os.path.join(target_dir, tn), "rb") as f:
            f.seek(off)
            got = f.read(sz)
        with open(os.path.join(src_root, rp), "rb") as f:
            want = f.read()
        if got != want:
            print(
                f"integ test 1 FAILED: {rp} in {tn} "
                f"@ off={off} size={sz}")
            div = -1
            for i in range(min(len(got), len(want))):
                if got[i] != want[i]:
                    div = i
                    break
            print(f"  first diff offset: {div}")
            sys.exit(1)
        n_ok += 1
    print(f"integ test 1: {n_ok} samples verified; "
          f"seed={seed}")


# Integration test 2.  Verify
#   sum(originals under src_root)
#   == sum(sizes of merged blobs on disk).
# Hard-exits on mismatch.
def integ_test_size_accounting(src_root, target_dir):
    t_orig = 0
    for dp, _, fns in os.walk(src_root, followlinks=False):
        for fn in fns:
            full = os.path.join(dp, fn)
            if os.path.islink(full) or not os.path.isfile(full):
                continue
            t_orig += os.path.getsize(full)
    t_remain = sum(
        os.path.getsize(os.path.join(target_dir, n))
        for n in os.listdir(target_dir)
        if os.path.isfile(os.path.join(target_dir, n)))
    if t_orig != t_remain:
        print("integ test 2 FAILED: size accounting mismatch")
        print(f"  T_orig:    {t_orig}")
        print(f"  T_remain:  {t_remain}")
        print(f"  delta:     {t_orig - t_remain}")
        sys.exit(1)
    print(f"integ test 2: size accounting OK "
          f"(orig={t_orig}, remaining={t_remain})")


# ---- unit tests -----------------------------------------------------

class TestBlock1(unittest.TestCase):
    """Block 1: data-folder checks."""

    def setUp(self):
        self.tdir = tempfile.mkdtemp(dir=UNIT_TEST_TMP)

    # Happy path: missing target/records get created.
    def test_check_data_folders_ok(self):
        src = os.path.join(self.tdir, "src"); os.makedirs(src)
        tgt = os.path.join(self.tdir, "tgt")
        rec = os.path.join(self.tdir, "rec")
        check_data_folders(src, tgt, rec)
        self.assertTrue(os.path.isdir(tgt))
        self.assertTrue(os.path.isdir(rec))

    # Missing src is always fatal.
    def test_check_data_folders_missing_src(self):
        src = os.path.join(self.tdir, "missing")
        tgt = os.path.join(self.tdir, "tgt")
        rec = os.path.join(self.tdir, "rec")
        with self.assertRaises(SystemExit):
            check_data_folders(src, tgt, rec)


class TestBlock2(unittest.TestCase):
    """Block 2: canonical file list + manifest."""

    def setUp(self):
        self.tdir = tempfile.mkdtemp(dir=UNIT_TEST_TMP)

    # Build a tree where files are created in randomized order to
    # stress the canonicality of the enumerator.  Each (relpath,
    # content) pair is written in a shuffled order driven by seed.
    def _build_tree(self, root, files, seed):
        rng  = random.Random(seed)
        idxs = list(range(len(files)))
        rng.shuffle(idxs)
        for i in idxs:
            rp, data = files[i]
            full = os.path.join(root, rp)
            os.makedirs(os.path.dirname(full), exist_ok=True)
            with open(full, "wb") as f:
                f.write(data)

    # canonical_file_list is stable across creation orders, and the
    # resulting manifests are byte-identical (req: CANONICAL list).
    def test_canonical_file_list_stable(self):
        files = [
            ("a/b/c.txt",            b"abc"),
            ("a/b/d.txt",            b"dddd"),
            ("a/zz.txt",             b"z"),
            ("x.txt",                b"xxxxx"),
            ("subdir/inner/deep.txt", b"deep"),
        ]
        root1 = os.path.join(self.tdir, "r1")
        root2 = os.path.join(self.tdir, "r2")
        self._build_tree(root1, files, 1)
        self._build_tree(root2, files, 42)
        fl1 = canonical_file_list(root1)
        fl2 = canonical_file_list(root2)
        self.assertEqual(fl1, fl2)
        m1 = os.path.join(self.tdir, "m1.txt")
        m2 = os.path.join(self.tdir, "m2.txt")
        write_file_manifest(fl1, m1)
        write_file_manifest(fl2, m2)
        with open(m1, "r", encoding="utf-8") as f:
            t1 = f.read()
        with open(m2, "r", encoding="utf-8") as f:
            t2 = f.read()
        self.assertEqual(t1, t2)

    # Symlinks are excluded; nested files appear under their relpath.
    def test_canonical_file_list_filters(self):
        root = os.path.join(self.tdir, "root")
        os.makedirs(os.path.join(root, "sub"))
        with open(os.path.join(root, "real.txt"), "wb") as f:
            f.write(b"r")
        with open(os.path.join(root, "sub", "x.txt"), "wb") as f:
            f.write(b"x")
        os.symlink(os.path.join(root, "real.txt"),
                   os.path.join(root, "sym.txt"))
        fl  = canonical_file_list(root)
        rps = [r["relpath"] for r in fl]
        self.assertIn("real.txt", rps)
        self.assertIn(os.path.join("sub", "x.txt"), rps)
        self.assertNotIn("sym.txt", rps)

    # Manifest is human-readable UTF-8 with a sha256 trailer.
    def test_manifest_human_readable(self):
        fl = [{"relpath": "a", "size": 10},
              {"relpath": "b", "size": 20}]
        p  = os.path.join(self.tdir, "man.txt")
        write_file_manifest(fl, p)
        with open(p, "r", encoding="utf-8") as f:
            text = f.read()
        self.assertTrue(text.startswith("a\t10\nb\t20\n"))
        lines = text.splitlines()
        self.assertEqual(len(lines), 3)
        self.assertTrue(lines[-1].startswith("# sha256 = "))
        self.assertEqual(len(lines[-1].split("= ", 1)[1]), 64)
        self.assertTrue(text.endswith("\n"))

    # Read returns the original list; tampering raises ValueError.
    def test_manifest_roundtrip_and_tamper(self):
        fl = [{"relpath": "a/b", "size": 7},
              {"relpath": "x",   "size": 9}]
        p  = os.path.join(self.tdir, "man.txt")
        write_file_manifest(fl, p)
        self.assertEqual(read_file_manifest(p), fl)
        with open(p, "r", encoding="utf-8") as f:
            text = f.read()
        bad = text.replace("a/b\t7\n", "a/b\t8\n")
        with open(p, "w", encoding="utf-8", newline="\n") as f:
            f.write(bad)
        with self.assertRaises(ValueError):
            read_file_manifest(p)

    # Empty list -> manifest holds only the sha256 trailer.
    def test_manifest_empty(self):
        p = os.path.join(self.tdir, "man.txt")
        write_file_manifest([], p)
        self.assertEqual(read_file_manifest(p), [])

    # Atomic write leaves no .tmp sibling.
    def test_manifest_atomic(self):
        fl = [{"relpath": "z", "size": 1}]
        p  = os.path.join(self.tdir, "man.txt")
        write_file_manifest(fl, p)
        self.assertFalse(os.path.exists(p + ".tmp"))


class TestBlock3(unittest.TestCase):
    """Block 3: compute_merge_plan."""

    # All small files coalesce into one bin.
    def test_all_small(self):
        fl = [{"relpath": f"f{i}", "size": s}
              for i, s in enumerate([10, 20, 30, 40])]
        plan = compute_merge_plan(fl, 100)
        self.assertEqual(len(plan), 1)
        self.assertEqual([s["relpath"]
                          for s in plan[0]["list_src"]],
                         ["f0", "f1", "f2", "f3"])

    # Mixture of singletons and a multi-file bin.
    def test_tight_pack(self):
        fl = [{"relpath": "a", "size": 60},
              {"relpath": "b", "size": 50},
              {"relpath": "c", "size": 60},
              {"relpath": "d", "size": 10}]
        plan = compute_merge_plan(fl, 100)
        self.assertEqual(len(plan), 3)
        self.assertEqual([s["relpath"]
                          for s in plan[0]["list_src"]], ["a"])
        self.assertEqual([s["relpath"]
                          for s in plan[1]["list_src"]], ["b"])
        self.assertEqual([s["relpath"]
                          for s in plan[2]["list_src"]],
                         ["c", "d"])

    # Oversize file forms its own solo bin.
    def test_oversize_solo(self):
        fl = [{"relpath": "big", "size": 200},
              {"relpath": "a",   "size": 30},
              {"relpath": "b",   "size": 40}]
        plan = compute_merge_plan(fl, 100)
        self.assertEqual(len(plan), 2)
        self.assertEqual([s["relpath"]
                          for s in plan[0]["list_src"]], ["big"])
        self.assertEqual([s["relpath"]
                          for s in plan[1]["list_src"]],
                         ["a", "b"])

    # Single-file list.
    def test_single_file(self):
        fl   = [{"relpath": "only", "size": 50}]
        plan = compute_merge_plan(fl, 100)
        self.assertEqual(len(plan), 1)
        self.assertEqual(plan[0]["target_name"], "merged_00000")

    # Empty list.
    def test_empty_list(self):
        self.assertEqual(compute_merge_plan([], 100), [])

    # Two calls produce identical plans.
    def test_determinism(self):
        fl = [{"relpath": f"f{i:03d}",
               "size": (i * 7) % 41 + 1}
              for i in range(50)]
        self.assertEqual(compute_merge_plan(fl, 100),
                         compute_merge_plan(fl, 100))

    # Every source ends up in exactly one bin.
    def test_count_invariant(self):
        fl = [{"relpath": f"f{i}", "size": (i * 13) % 71 + 5}
              for i in range(200)]
        plan  = compute_merge_plan(fl, 256)
        total = sum(len(b["list_src"]) for b in plan)
        self.assertEqual(total, len(fl))

    # Multi-file bins never exceed target_size.
    def test_size_invariant(self):
        fl = [{"relpath": f"f{i}", "size": (i * 13) % 71 + 5}
              for i in range(200)]
        plan = compute_merge_plan(fl, 256)
        for b in plan:
            if len(b["list_src"]) > 1:
                self.assertLessEqual(
                    sum(s["size"] for s in b["list_src"]),
                    256)

    # Names are zero-padded; lex order == plan order.
    def test_name_width(self):
        fl   = [{"relpath": f"f{i:04d}", "size": 1}
                for i in range(2000)]
        plan = compute_merge_plan(fl, 1)
        names = [b["target_name"] for b in plan]
        self.assertEqual(names, sorted(names))
        self.assertEqual(names[0],  "merged_00000")
        self.assertEqual(names[-1], "merged_01999")


class TestBlock4(unittest.TestCase):
    """Block 4: exec_merge_plan."""

    def setUp(self):
        self.tdir = tempfile.mkdtemp(dir=UNIT_TEST_TMP)
        self.src  = os.path.join(self.tdir, "src")
        self.tgt  = os.path.join(self.tdir, "tgt")
        os.makedirs(self.src)

    def _write_src(self, rp, data):
        full = os.path.join(self.src, rp)
        os.makedirs(os.path.dirname(full) or ".",
                    exist_ok=True)
        with open(full, "wb") as f:
            f.write(data)

    def _build_basic(self):
        self._write_src("a", b"AAAA")
        self._write_src("b", b"BBBB")
        self._write_src("c", b"C" * 200)
        self._write_src("d", b"D")

    # Output is byte-exact concatenation in canonical order.
    def test_byte_exact(self):
        self._build_basic()
        plan = [
            {"target_name": "merged_00000",
             "list_src": [
                 {"relpath": "a", "size": 4},
                 {"relpath": "b", "size": 4},
                 {"relpath": "d", "size": 1}]},
            {"target_name": "merged_00001",
             "list_src": [{"relpath": "c", "size": 200}]},
            {"target_name": "merged_00002",
             "list_src": [{"relpath": "a", "size": 4}]},
        ]
        exec_merge_plan(self.src, self.tgt, plan)
        with open(os.path.join(self.tgt, "merged_00000"),
                  "rb") as f:
            self.assertEqual(f.read(), b"AAAABBBBD")
        with open(os.path.join(self.tgt, "merged_00001"),
                  "rb") as f:
            self.assertEqual(f.read(), b"C" * 200)
        with open(os.path.join(self.tgt, "merged_00002"),
                  "rb") as f:
            self.assertEqual(f.read(), b"AAAA")

    # Bin order on disk matches plan order (zero-padded names).
    def test_bin_order(self):
        self._build_basic()
        plan = [
            {"target_name": "merged_00000",
             "list_src": [{"relpath": "a", "size": 4}]},
            {"target_name": "merged_00001",
             "list_src": [{"relpath": "b", "size": 4}]},
        ]
        exec_merge_plan(self.src, self.tgt, plan)
        self.assertEqual(sorted(os.listdir(self.tgt)),
                         ["merged_00000", "merged_00001"])

    # Wipes target_dir before writing.
    def test_wipe(self):
        self._build_basic()
        os.makedirs(self.tgt, exist_ok=True)
        with open(os.path.join(self.tgt, "junk"), "wb") as f:
            f.write(b"x")
        plan = [{"target_name": "merged_00000",
                 "list_src": [{"relpath": "a", "size": 4}]}]
        exec_merge_plan(self.src, self.tgt, plan)
        self.assertEqual(os.listdir(self.tgt),
                         ["merged_00000"])

    # No extra files in target_dir, no .tmp leftovers.
    def test_no_extras(self):
        self._build_basic()
        plan = [{"target_name": "merged_00000",
                 "list_src": [{"relpath": "a", "size": 4}]}]
        exec_merge_plan(self.src, self.tgt, plan)
        names = os.listdir(self.tgt)
        self.assertEqual(len(names), len(plan))
        for n in names:
            self.assertFalse(n.endswith(".tmp"))

    # Idempotent: byte-identical outputs across two runs.
    def test_idempotent(self):
        self._build_basic()
        plan = [
            {"target_name": "merged_00000",
             "list_src": [
                 {"relpath": "a", "size": 4},
                 {"relpath": "b", "size": 4}]},
            {"target_name": "merged_00001",
             "list_src": [{"relpath": "c", "size": 200}]},
        ]

        def _hash_dir(d):
            out = {}
            for n in sorted(os.listdir(d)):
                with open(os.path.join(d, n), "rb") as f:
                    out[n] = hashlib.sha256(f.read()).hexdigest()
            return out

        exec_merge_plan(self.src, self.tgt, plan)
        h_a = _hash_dir(self.tgt)
        exec_merge_plan(self.src, self.tgt, plan)
        h_b = _hash_dir(self.tgt)
        self.assertEqual(h_a, h_b)


class TestBlock7(unittest.TestCase):
    """Block 7: merge map + write_all_records."""

    def setUp(self):
        self.tdir = tempfile.mkdtemp(dir=UNIT_TEST_TMP)

    def _basic_plan(self):
        return [
            {"target_name": "merged_00000",
             "list_src": [
                 {"relpath": "a",     "size": 4},
                 {"relpath": "sub/b", "size": 8}]},
            {"target_name": "merged_00001",
             "list_src": [{"relpath": "c", "size": 200}]},
            {"target_name": "merged_00002",
             "list_src": [
                 {"relpath": "d", "size": 1},
                 {"relpath": "e", "size": 1}]},
        ]

    # Exact canonical text on disk.
    def test_text_exact(self):
        plan = self._basic_plan()
        p    = os.path.join(self.tdir, "map.txt")
        write_merge_map(plan, p)
        with open(p, "r", encoding="utf-8") as f:
            text = f.read()
        expected = ("merged_00000\ta\tsub/b\n"
                    "merged_00001\tc\n"
                    "merged_00002\td\te\n")
        self.assertEqual(text, expected)

    # Plan order on disk; lex sort of lines equals file order.
    def test_plan_order(self):
        plan = self._basic_plan()
        p    = os.path.join(self.tdir, "map.txt")
        write_merge_map(plan, p)
        with open(p, "r", encoding="utf-8") as f:
            lines = f.read().splitlines()
        self.assertEqual(lines, sorted(lines))

    # Read returns plan shape (relpaths only, no sizes).
    def test_roundtrip(self):
        plan = self._basic_plan()
        p    = os.path.join(self.tdir, "map.txt")
        write_merge_map(plan, p)
        got = read_merge_map(p)
        expected = [
            {"target_name": b["target_name"],
             "list_src": [{"relpath": s["relpath"]}
                          for s in b["list_src"]]}
            for b in plan
        ]
        self.assertEqual(got, expected)

    # Two writes are byte-identical.
    def test_canonical_twice(self):
        plan = self._basic_plan()
        pa = os.path.join(self.tdir, "a.txt")
        pb = os.path.join(self.tdir, "b.txt")
        write_merge_map(plan, pa)
        write_merge_map(plan, pb)
        with open(pa, "r", encoding="utf-8") as f:
            ta = f.read()
        with open(pb, "r", encoding="utf-8") as f:
            tb = f.read()
        self.assertEqual(ta, tb)

    # Tab/newline in relpath rejected.
    def test_reject_tab_newline(self):
        for bad_rp in ("a\tb", "a\nb", "a\rb"):
            bad = [{"target_name": "merged_00000",
                    "list_src": [{"relpath": bad_rp,
                                  "size": 1}]}]
            with self.assertRaises(ValueError):
                write_merge_map(bad,
                                os.path.join(self.tdir, "m.txt"))

    # Corrupted map raises on read.
    def test_corrupted_map(self):
        p = os.path.join(self.tdir, "map.txt")
        with open(p, "w", encoding="utf-8", newline="\n") as f:
            f.write("merged_00005\ta\n")
            f.write("merged_00003\tb\n")
        with self.assertRaises(ValueError):
            read_merge_map(p)
        with open(p, "w", encoding="utf-8", newline="\n") as f:
            f.write("not_a_merged_name\ta\n")
        with self.assertRaises(ValueError):
            read_merge_map(p)

    # Atomic write leaves no .tmp sibling.
    def test_atomic(self):
        p = os.path.join(self.tdir, "map.txt")
        write_merge_map(self._basic_plan(), p)
        self.assertFalse(os.path.exists(p + ".tmp"))

    # write_all_records emits 2 files byte-identical across runs.
    def test_write_all_records_twice(self):
        plan = self._basic_plan()
        fl   = [{"relpath": "a",     "size": 4},
                {"relpath": "sub/b", "size": 8},
                {"relpath": "c",     "size": 200},
                {"relpath": "d",     "size": 1},
                {"relpath": "e",     "size": 1}]

        d_a = os.path.join(self.tdir, "ra")
        d_b = os.path.join(self.tdir, "rb")
        write_all_records(d_a, fl, plan)
        write_all_records(d_b, fl, plan)

        for fn in ("email_filelist.txt",
                   "email_merge_map.txt"):
            with open(os.path.join(d_a, fn), "r",
                      encoding="utf-8") as f:
                ta = f.read()
            with open(os.path.join(d_b, fn), "r",
                      encoding="utf-8") as f:
                tb = f.read()
            self.assertEqual(ta, tb, fn)

    # Emits filelist + map, never a remove list.
    def test_write_all_records_files(self):
        plan = self._basic_plan()
        fl   = [{"relpath": "a", "size": 4}]
        d    = os.path.join(self.tdir, "r")
        write_all_records(d, fl, plan)
        self.assertFalse(os.path.exists(
            os.path.join(d, "email_remove_list.txt")))
        self.assertTrue(os.path.exists(
            os.path.join(d, "email_filelist.txt")))
        self.assertTrue(os.path.exists(
            os.path.join(d, "email_merge_map.txt")))


# ---- runner ---------------------------------------------------------

# Wipe UNIT_TEST_TMP, run unittest, rmtree on exit.  Every test must
# create its own subdir via tempfile.mkdtemp(dir=UNIT_TEST_TMP) so the
# outer rmtree is the only cleanup needed.
def run_unit_tests():
    shutil.rmtree(UNIT_TEST_TMP, ignore_errors=True)
    os.makedirs(UNIT_TEST_TMP)
    try:
        prog = unittest.main(argv=[sys.argv[0], "-v"], exit=False)
    finally:
        shutil.rmtree(UNIT_TEST_TMP, ignore_errors=True)
    if not prog.result.wasSuccessful():
        sys.exit(1)


# Format n bytes as e.g. "8.62 GiB" for human-readable stats.
def _human_size(n):
    if n < 1024:
        return f"{n} B"
    x = float(n)
    for unit in ("KiB", "MiB", "GiB", "TiB", "PiB"):
        x /= 1024
        if x < 1024:
            return f"{x:.2f} {unit}"
    return f"{x:.2f} EiB"


# Execute steps [a]-[d], run integration tests, then stats.  Every
# major step is framed by step_enter / step_done with wall-clock.
def _run_pipeline(args):
    print("=" * 60)
    print("gen_merged128k_email.py  (merge-only)")
    print("=" * 60)
    print()

    check_data_folders(SRC_DIR, TARGET_DIR, RECORDS_DIR)

    t0 = step_enter("[a] canonical_file_list")
    fl = canonical_file_list(SRC_DIR)
    print(f"  files: {len(fl)}")
    step_done("[a] canonical_file_list", t0)

    t0 = step_enter("[b] compute_merge_plan")
    plan = compute_merge_plan(fl, TARGET_SIZE)
    print(f"  bins:  {len(plan)}")
    step_done("[b] compute_merge_plan", t0)

    t0 = step_enter("[c] exec_merge_plan")
    exec_merge_plan(SRC_DIR, TARGET_DIR, plan)
    step_done("[c] exec_merge_plan", t0)

    t0 = step_enter("[d] write_all_records")
    write_all_records(RECORDS_DIR, fl, plan)
    step_done("[d] write_all_records", t0)

    t0 = step_enter("integration tests")
    integ_test_random_sample_in_merged(
        SRC_DIR, TARGET_DIR, plan, args.integ_samples)
    integ_test_size_accounting(SRC_DIR, TARGET_DIR)
    step_done("integration tests", t0)

    # Final stats.
    n_orig    = len(fl)
    t_orig    = sum(r["size"] for r in fl)
    final_files = [
        n for n in os.listdir(TARGET_DIR)
        if os.path.isfile(os.path.join(TARGET_DIR, n))]
    n_final = len(final_files)
    t_final = sum(
        os.path.getsize(os.path.join(TARGET_DIR, n))
        for n in final_files)

    n_generated = len(plan)
    print()
    print("=== summary ===")
    print(f"original set:     {n_orig} files, "
          f"{t_orig} bytes ({_human_size(t_orig)})")
    print(f"merged generated: {n_generated} files")
    print(f"merged left:      {n_final} files, "
          f"{t_final} bytes ({_human_size(t_final)})")
    print(f"records: "
          f"{os.path.join(RECORDS_DIR, 'email_filelist.txt')}")
    print(f"         "
          f"{os.path.join(RECORDS_DIR, 'email_merge_map.txt')}")
    print("done.")


def main():
    parser = argparse.ArgumentParser(
        description="Merge maildir files into 128KB blobs.")
    parser.add_argument("--test", action="store_true",
                        help="run inline unit tests and exit")
    parser.add_argument("--integ-samples", type=int, default=100,
                        help="random samples for integ test 1")
    args = parser.parse_args()

    if args.test:
        run_unit_tests()
        return

    _run_pipeline(args)


if __name__ == "__main__":
    main()
