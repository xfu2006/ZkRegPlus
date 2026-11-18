# DLP_T1001: unit and stub-prover smoke tests for same_zombie.py
import os
import sys
import json
import shutil
import signal
import tempfile
import time
import threading
import textwrap
import unittest
import subprocess
from unittest import mock

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import same_zombie as sz  # noqa: E402
import run_zombie as rz  # noqa: E402

# DLP_T1001: real dirs this suite must leave unchanged (import-time paths,
# bound before any redirect); data/cache/logs is skipped, a live run writes it
_REAL_GUARD_DIRS = (os.path.join(sz.REPO, "data", "cache"), sz.RAW_DATA_ROOT,
                    sz.DOCS, "/tmp/bora_zombie_run", "/tmp/snark_start")
_REAL_GUARD_SKIP = os.path.join(sz.REPO, "data", "cache", "logs")
_GUARD = {}
# ALL_T1009: the real box-wide helpers, kept before setUpModule stubs them
_REAL_SCAN = sz.other_zombie_pids
_REAL_ORPHAN = sz.orphan_circ
_RZ_PRISTINE = dict(vars(rz))           # ALL_T1009: before any hook install


def _tree_state(*roots):
    """path -> (size, mtime_ns) per file, "dir" per dir (presence only, as
    PAPER_DATA does); the logs dir and everything in it are skipped."""
    out = {}
    for root in roots:
        for dp, dns, fns in os.walk(root):
            dns[:] = [d for d in dns if d != "__pycache__" and
                      os.path.join(dp, d) != _REAL_GUARD_SKIP]
            out[dp] = "dir"
            for n in fns:
                p = os.path.join(dp, n)
                try:
                    st = os.lstat(p)
                except OSError:
                    continue
                out[p] = (st.st_size, st.st_mtime_ns)
    return out


def setUpModule():
    _GUARD["before"] = _tree_state(*_REAL_GUARD_DIRS)
    tmp = _GUARD["tmp"] = tempfile.mkdtemp(prefix="sz_mod_", dir=os.environ.get(
        "TMPDIR"))
    # default redirects; Base re-points them per test
    for mod, name, base in ((rz, "PARTIAL_DIR", "run"),
                            (rz, "PARTIAL", "run/rz.partial.jsonl"),
                            (rz, "PARTIAL_DOCS", "docs/rz.partial.jsonl"),
                            (rz, "PAR_ROOT", "par"), (sz, "DOCS", "docs"),
                            (sz, "RAW_DATA_ROOT", "raw")):
        p = mock.patch.object(mod, name, os.path.join(tmp, base))
        p.start()
        _GUARD.setdefault("patches", []).append(p)
    for d in ("run", "docs", "raw", "par"):
        os.makedirs(os.path.join(tmp, d))
    # ALL_T1009: private lock name; no real scan, kill or mount probe
    for mod, name, val in (
            (sz, "DRIVER_LOCK", "sz_test_lock_%d_%s" % (
                os.getpid(), os.path.basename(tmp))),
            (sz, "other_zombie_pids", lambda *a, **k: []),
            (sz, "orphan_circ", lambda *a, **k: []),
            (rz, "_pick_scratch_base", lambda: os.path.join(tmp, "par")),
            (rz, "_candidate_mounts", lambda: [])):   # ALL_T1013 F5: no real
        p = mock.patch.object(mod, name, val)
        p.start()
        _GUARD["patches"].append(p)


def tearDownModule():
    for p in _GUARD.pop("patches", []):
        p.stop()
    shutil.rmtree(_GUARD.pop("tmp"), ignore_errors=True)
    after = _tree_state(*_REAL_GUARD_DIRS)
    before = _GUARD.pop("before")
    changed = sorted(k for k in set(before) | set(after)
                     if before.get(k) != after.get(k))
    if changed:
        raise AssertionError(
            "test_same_zombie changed %d REAL path(s) under data/cache, "
            "raw_data, ms_dlp/docs, /tmp/bora_zombie_run or /tmp/snark_start "
            "(or a live run wrote there meanwhile): %s"
            % (len(changed), changed[:20]))

STUB = textwrap.dedent('''\
    #!/usr/bin/env python3
    import os, sys, time
    n = int(sys.argv[1].rsplit("_", 1)[1])
    print("zreal start", flush=True)
    if os.environ.get("STUB_RC") and os.environ.get("ZREAL_EMAIL"):
        sys.exit(int(os.environ["STUB_RC"]))
    if "ZREAL_EMAIL" in os.environ:
        open(os.environ["ZREAL_EMAIL"], "rb").read()
    ms = int(os.environ.get("STUB_MS", "300"))
    if sys.argv[2:3] == ["true"] and os.path.isdir("keys"):   # ALL_T1013 R1
        for part in ("inst", "gens", "input_names", "term_arr",
                     "input_idxes", "var_idxes"):
            open("keys/policy%d_%s" % (n, part), "w").write("k")
    if os.environ.get("RAYON_NUM_THREADS") and os.environ.get("STUB_SLOW"):
        ms = int(ms * float(os.environ["STUB_SLOW"]))
    time.sleep(ms / 1000.0)
    print("policy%d circuit constraints cons %s inputs 1 vars 1"
          % (n, os.environ.get("STUB_CONS", "70000")))
    print("prove takes %d" % ms)
    print("proof size is 10 bytes")
    if os.environ.get("ZREAL_NO_VERIFY"):          # ALL_T1013 S2
        print("zreal verify_ok skipped")
        sys.exit(0)
    print("verify takes 5")
    ok = os.environ.get("STUB_VERIFY", "true")
    if os.environ.get("STUB_VF_EMAIL") and os.environ.get(
            "ZREAL_EMAIL", "").endswith(os.environ["STUB_VF_EMAIL"] + ".eml"):
        ok = "false"
    print("zreal verify_ok %s" % ok)
    sys.exit(0 if ok == "true" else 3)
    ''')


def fake_topo(n_nodes=1, cores=4, tpc=1, base=8, keep=0):
    nodes, c = {}, base
    for nd in range(n_nodes):
        nodes[nd] = []
        for _ in range(cores):
            nodes[nd].append(list(range(c, c + tpc)))
            c += tpc
    return sz.topo_from(nodes, keep)


class Base(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.mkdtemp(prefix="sz_t_", dir=os.environ.get(
            "TMPDIR"))
        self.saved = {k: getattr(rz, k) for k in ("PARTIAL_DIR", "PARTIAL",
                                                  "PARTIAL_DOCS")}
        self.saved_sz = {k: getattr(sz, k) for k in ("DOCS", "RAW_DATA_ROOT",
                                                     "LOG_FH", "ARGS")}
        rz.PARTIAL_DIR = os.path.join(self.tmp, "run")
        rz.PARTIAL = os.path.join(rz.PARTIAL_DIR, "rz.partial.jsonl")
        sz.DOCS = os.path.join(self.tmp, "docs")
        rz.PARTIAL_DOCS = os.path.join(sz.DOCS, "rz.partial.jsonl")
        sz.RAW_DATA_ROOT = os.path.join(self.tmp, "raw")
        os.makedirs(rz.PARTIAL_DIR)
        os.makedirs(sz.DOCS)
        sz.STOP.clear()
        sz.ARGS = sz.parse_args(["--sizes", "1000", "--n", "2", "--server",
                                 "t1", "--launcher", "prlimit",
                                 "--reserve-floor", "1"])
        sz.S.clear()
        sz.S.update(rows=[], pending=[], defer={}, keep=[], running=[],
                    attempts={}, notes=[], fails=[], serial=set(),
                    w_state={}, gates={}, k=0, launch_consec=0,
                    launcher="prlimit", props=[], exit6=None, t_start=0,
                    ids_sha="i", list_sha="l", fp="fp", commit="c",
                    sig="sig1", cap=4, R=1 << 30, er=set(),
                    topo=fake_topo(), full_mem=None, binp=None,
                    logdir=self.tmp)
        sz.S["pair"] = sz.pair_names(sz.ARGS)[1]

    def tearDown(self):
        for k, v in self.saved.items():
            setattr(rz, k, v)
        for k, v in self.saved_sz.items():
            setattr(sz, k, v)
        sz.STOP.clear()
        shutil.rmtree(self.tmp, ignore_errors=True)


class HelperTest(unittest.TestCase):
    def test_pow2(self):
        self.assertEqual([sz.up2(x) for x in (1, 2, 3, 5, 9)], [1, 2, 4, 8, 16])
        self.assertEqual([sz.down2(x) for x in (0, 1, 3, 7, 30)],
                         [1, 1, 2, 4, 16])

    def test_slots_and_c_cores(self):
        """m6/m10: 2 x 32 cores, keep-free 4: C_cores 60, slots 60/30/14."""
        t = fake_topo(n_nodes=2, cores=32, base=0, keep=4)
        self.assertEqual(t["c_cores"], 60)
        self.assertEqual([len(sz.make_slots(t, w)) for w in (1, 2, 4)],
                         [60, 30, 14])
        sl = sz.make_slots(t, 4)
        self.assertEqual([nd for nd, _ in sl[:4]], [0, 1, 0, 1])
        for nd, cpus in sl:          # whole cores inside one node
            self.assertEqual(len(cpus), 4)

    def test_fail_like_pins_paper_data(self):
        self.assertEqual(sz.selftest(), 0)

    def test_say_caveat(self):
        out = []
        with mock.patch.object(sys, "stdout") as so:
            so.write.side_effect = out.append
            sz.say("ok line\nprocess Killed by x\npanicked at y")
            sz.say("trace a\ntrace b", caveat=True)
        lines = "".join(out).splitlines()
        self.assertEqual(lines[0], "ok line")
        self.assertTrue(all(ln.startswith("CAVEAT: ") for ln in lines[1:]))
        for ln in lines:
            if sz.FAIL_LIKE.search(ln):
                self.assertTrue(ln.startswith("CAVEAT: "))

    def test_parse_cap(self):
        for v, want in (("4", 4), ("0", 0), ("-1", None), ("x", None),
                        ("2.5", None)):
            with mock.patch.dict(os.environ, {"ZKR_SAME_MAX_WIDTH_CORES": v}):
                self.assertEqual(sz.parse_cap(), want)
        with mock.patch.dict(os.environ, {}, clear=True):
            self.assertEqual(sz.parse_cap(), 16)       # owner default 11/17

    def test_classify_matrix(self):
        ok = ("zreal start\np circuit constraints cons 7 inputs 1 vars 1\n"
              "prove takes 5\nproof size is 1 bytes\nverify takes 1\n"
              "zreal verify_ok true\n")
        c = sz.classify
        self.assertEqual(c(0, ok, "", "", None, False, False, 7, 7), "ok")
        self.assertEqual(c(0, ok, "", "", None, True, False, 7, 7),
                         "expected_reject")
        self.assertEqual(c(0, ok, "", "", None, False, False, 7, 8),
                         "cons_mismatch")
        self.assertEqual(c(3, ok.replace("true", "false"), "", "", None,
                           False, False, 7, 7), "verify_false")
        self.assertEqual(c(-9, "zreal start", "", "", "watchdog", False,
                           False, 7, None), "watchdog")
        self.assertEqual(c(-9, "zreal start", "", "oom-kill", None, False,
                           False, 7, None), "resource")
        self.assertEqual(c(-6, "zreal start", "memory allocation of 9", "",
                           None, False, False, 7, None), "resource")
        self.assertEqual(c(-6, "zreal start", "", "", None, False, False, 7,
                           None), "crash_suspect")
        self.assertEqual(c(-11, "zreal start", "", "", None, False, False, 7,
                           None), "crash_suspect")
        self.assertEqual(c(1, "", "Failed to start transient scope unit", "",
                           None, False, False, 7, None), "launcher")
        self.assertEqual(c(1, "", "boom", "", None, False, False, 7, None),
                         "crash_suspect")
        self.assertEqual(c(-9, "zreal start", "", "", "timeout", False, True,
                           7, None), "resource")
        self.assertEqual(c(0, "zreal start\n", "", "", None, False, False, 7,
                           None), "resource")


class SigTest(unittest.TestCase):
    def test_body_edit_changes_launch_sig(self):
        """Invariant 35: editing a function body changes launch_sig."""
        a = sz.parse_args([])
        sz.S["zin"] = "z"
        base = sz.launch_sig(2, a)
        d = tempfile.mkdtemp(dir=os.environ.get("TMPDIR"))
        try:
            cp = os.path.join(d, "same_zombie.py")
            src = open(sz.SELF_PATH).read()
            old = "    return \",\".join(str(c) for c in cpus)"
            self.assertIn(old, src)
            open(cp, "w").write(src.replace(
                old, "    return \",\".join(str(c) for c in reversed(cpus))"))
            with mock.patch.object(sz, "SELF_PATH", cp):
                self.assertNotEqual(sz.launch_sig(2, a), base)
            self.assertNotEqual(sz.launch_sig(1, a), base)
            b = sz.parse_args(["--keep-free", "8"])
            self.assertNotEqual(sz.launch_sig(2, b), base)
            self.assertEqual(sz.launch_sig(2, a), base)
        finally:
            shutil.rmtree(d)
            sz.S.pop("zin", None)

    def test_inputs_hash_anchors_target_skip(self):
        """Fix round 2: circ/src/target is hashed, circ/target is not."""
        d = tempfile.mkdtemp(dir=os.environ.get("TMPDIR"))
        try:
            for rel in ("circ/target/x", "circ/src/target/y"):
                p = os.path.join(d, rel)
                os.makedirs(os.path.dirname(p), exist_ok=True)
                with open(p, "w") as f:
                    f.write("v0")
            with mock.patch.object(sz, "ZOMBIE_TREE", d):
                sz.S.pop("zin", None)
                h0 = sz.zombie_inputs_sha256()
                with open(os.path.join(d, "circ/target/x"), "w") as f:
                    f.write("v1")
                sz.S.pop("zin")
                self.assertEqual(sz.zombie_inputs_sha256(), h0)
                with open(os.path.join(d, "circ/src/target/y"), "w") as f:
                    f.write("v1")
                sz.S.pop("zin")
                self.assertNotEqual(sz.zombie_inputs_sha256(), h0)
        finally:
            sz.S.pop("zin", None)
            shutil.rmtree(d)

    def test_inputs_hash_skips_target_and_objects(self):
        d = tempfile.mkdtemp(dir=os.environ.get("TMPDIR"))
        try:
            for rel in ("circ/src/a.rs", "regex/bin/TestRegex",
                        "circ/target/x", "regex/bin/y.o"):
                p = os.path.join(d, rel)
                os.makedirs(os.path.dirname(p), exist_ok=True)
                open(p, "w").write(rel)
            with mock.patch.object(sz, "ZOMBIE_TREE", d):
                sz.S.pop("zin", None)
                h1 = sz.zombie_inputs_sha256()
                sz.S.pop("zin")
                open(os.path.join(d, "circ/target/x"), "w").write("changed")
                open(os.path.join(d, "regex/bin/y.o"), "w").write("changed")
                self.assertEqual(sz.zombie_inputs_sha256(), h1)
                sz.S.pop("zin")
                open(os.path.join(d, "regex/bin/TestRegex"), "w").write("q")
                self.assertNotEqual(sz.zombie_inputs_sha256(), h1)
        finally:
            sz.S.pop("zin", None)
            shutil.rmtree(d)


class PairTest(Base):
    def test_present_restore_rule2(self):
        """Invariant 39: either copy present; /tmp restored; rule 2."""
        sweep, sample = sz.pair_names(sz.ARGS)
        rz.PARTIAL, rz.PARTIAL_DOCS = sweep.tmp, sweep.docs
        sz._ORIG["load"] = lambda: {}
        self.assertFalse(sweep.present())
        sz.S["pair"].append([sz.stamp()])
        os.remove(sample.tmp)                      # simulated reboot
        self.assertTrue(sample.present())
        # sweep absent and sample present: read-only load ignores it
        self.assertEqual(sz.load_sample(sz.ARGS), [])
        self.assertTrue(sample.present())
        sz.load_partial_wrapped()                  # the run wipes it
        self.assertFalse(sample.present())
        # sweep present in docs only: restore both, no wipe
        open(sweep.docs, "w").write('{"x": 1}\n')
        sz.S["pair"].append([sz.stamp()])
        os.remove(sample.tmp)
        self.assertEqual(len(sz.load_sample(sz.ARGS)), 1)
        sz.load_partial_wrapped()
        self.assertTrue(os.path.getsize(sample.tmp) > 0)
        self.assertTrue(os.path.getsize(sweep.tmp) > 0)

    def test_rule1_abort(self):
        sz.S["pair"].append([dict(sz.stamp(), ids_sha="other")])
        sweep = sz.pair_names(sz.ARGS)[0]
        open(sweep.tmp, "w").write("{}\n")
        with self.assertRaises(SystemExit) as cm:
            sz.load_sample(sz.ARGS)
        self.assertEqual(cm.exception.code, 6)

    def test_no_write_after_stop(self):
        """Invariant 43: writers drop rows once stop is set."""
        sample = sz.S["pair"]
        sz.S["pair"].append([sz.stamp()])
        n = open(sample.tmp).read()
        sz.STOP.set()
        sz.put("prove", unit="u", size=1000)
        rz.PARTIAL = os.path.join(self.tmp, "p.jsonl")
        rz.PARTIAL_DOCS = os.path.join(self.tmp, "pd.jsonl")
        sz._ORIG["append"] = rz.__dict__.get("_append_partial")
        sz.append_partial_wrapped({"regex_name": "u", "str_len": 1})
        self.assertEqual(open(sample.tmp).read(), n)
        self.assertFalse(os.path.exists(rz.PARTIAL))

    def test_only_same_and_dry_names(self):
        a = sz.parse_args(["--only-same", "--server", "cl2x7542", "--dry", "4",
                           "--sizes", "1000"])
        sweep, sample = sz.pair_names(a)
        self.assertTrue(sweep.tmp.endswith("same_only_cl2x7542_dry.partial.jsonl"))
        self.assertTrue(sample.tmp.endswith(
            "same_zombie_only_cl2x7542_dry.partial.jsonl"))
        b = sz.parse_args(["--only-same", "--server", "cl2x7542"])
        self.assertTrue(sz.pair_names(b)[1].docs.endswith(
            os.path.join("docs", "same_zombie_only_cl2x7542.partial.jsonl")))


class AcceptTest(Base):
    def rows(self, sig_row="sig1", sig_gate="sig1", K_f=4, K_gate=4):
        b = dict(kind="base", unit="u", size=1000, base_uuid="b1")
        g = dict(kind="gate", gate_id="g1", size=1000, width=1, cons_bucket=16,
                 launcher="prlimit", launch_sig=sig_gate, K_gate=K_gate,
                 verdict="pass", fp="fp")
        p = dict(kind="prove", unit="u", size=1000, email_id="1000_01",
                 mode="packed", expected_reject=0, width=1, cons_bucket=16,
                 launcher="prlimit", launch_sig=sig_row, K_f=K_f,
                 base_uuid="b1", gate_id="g1", **{"class": "ok"})
        return [b, g, p]

    def test_coverage_key(self):
        """Invariants 20/24: a gate covers only its full key, K_gate >= K_f."""
        r = self.rows()
        base, gates = sz.index_rows(r)
        self.assertTrue(sz.is_accepted(r[2], base, gates))
        r = self.rows(sig_row="sig2")             # old gate, new row
        self.assertFalse(sz.is_accepted(r[2], *sz.index_rows(r)))
        r = self.rows(sig_row="sig0", sig_gate="sig0")   # history kept
        self.assertTrue(sz.is_accepted(r[2], *sz.index_rows(r)))
        r = self.rows(K_f=5)
        self.assertFalse(sz.is_accepted(r[2], *sz.index_rows(r)))
        r = self.rows()
        r.append(dict(r[0], base_uuid="b2"))      # re-keyed unit
        self.assertFalse(sz.is_accepted(r[2], *sz.index_rows(r)))
        r = self.rows()
        r[2]["expected_reject"] = 1
        self.assertFalse(sz.is_accepted(r[2], *sz.index_rows(r)))

    def test_gate_pass_counts_only_for_its_size(self):
        """Invariant 45 / m11, and the STOP row rule input."""
        r = self.rows()
        w, gates, stops = sz.state_from_rows(r, "sig1", "fp")
        self.assertEqual({k[0] for k in gates}, {1000})
        r.append(dict(kind="stop", size=2000, reason="x", cap=4, width=2,
                      launch_sig="sig1"))
        r.append(dict(kind="width", size=2000, width=2, launch_sig="sig1"))
        w, gates, stops = sz.state_from_rows(r, "sig1", "fp")
        self.assertIn(2000, stops)
        self.assertEqual(w, {2000: 2})
        w, gates, stops = sz.state_from_rows(r, "sig9", "fp")
        self.assertEqual((w, gates, stops), ({}, {}, {}))

    def _start(self, rows, sizes, cap=4, sc=(False, "none"), w0=""):
        sz.S["cap"] = cap
        sz.S["topo"] = fake_topo(cores=36)
        a = sz.parse_args(["--sizes", ",".join(map(str, sizes)),
                           "--server", "t1"])
        st = {"w0": w0, "commit": "c"} if sc[0] else None
        with mock.patch.object(sz, "read_scalecal", return_value=st), \
                mock.patch.object(sz, "valid_timing", return_value=sc), \
                mock.patch.object(sz, "print_stamp_view"):
            why = sz.start_check(a, rows)
        return why or next(iter(sz.S["refused"].values()), None)

    def test_start_check(self):
        """Invariants 18/19/25: per-size start check and STOP rows."""
        self.assertIn("speed check needs C_cores",
                      self._start([], [1000, 2000, 4000]))
        self.assertIsNone(self._start([], [1000]))
        self.assertEqual(sz.S["serial"], {1000})
        self.assertIsNone(self._start([], [1000, 2000, 4000], cap=0))
        self.assertIsNone(self._start([], [1000, 2000], sc=(True, None),
                                      w0="2"))
        self.assertEqual(sz.S["w_state"], {1000: 2, 2000: 2})
        self.assertEqual(sz.S["serial"], set())
        g1000 = self.rows()[1]
        self.assertIn("for 2000", self._start([g1000], [1000, 2000]))
        stop = dict(kind="stop", size=2000, reason="gate cannot pass", cap=4,
                    width=2, launch_sig="sig1")
        sc = (True, None)
        self.assertIn("cap unchanged", self._start([stop], [2000], sc=sc,
                                                   w0="1"))
        self.assertEqual(sz.S["refused_prior"], {2000})
        self.assertIsNone(self._start([stop], [2000], cap=8, sc=sc, w0="1"))
        self.assertEqual(sz.S["w_state"][2000], 3)   # ALL_T1013 S5: next rung
        self.assertIsNone(self._start([stop], [2000], cap=0, sc=sc, w0="1"))
        self.assertIn(2000, sz.S["serial"])
        old = dict(stop, launch_sig="sig0")       # another sig: no refusal
        self.assertIsNone(self._start([old], [2000], sc=sc, w0="1"))


class StampTest(Base):
    def test_valid_timing_git(self):
        repo = os.path.join(self.tmp, "repo")
        for rel in sz.LIST_TIMING:
            p = os.path.join(repo, rel)
            p = os.path.join(p, "f") if rel.endswith("/") else p
            os.makedirs(os.path.dirname(p), exist_ok=True)
            open(p, "w").write("x")
        open(os.path.join(repo, "TODO.md"), "w").write("t")
        g = ["git", "-C", repo, "-c", "user.email=t@t", "-c", "user.name=t"]
        subprocess.run(g[:3] + ["init", "-q"], check=True)
        subprocess.run(g + ["add", "-A"], check=True)
        subprocess.run(g + ["commit", "-qm", "a"], check=True)
        with mock.patch.object(sz, "REPO", repo):
            c = sz.git_head()
            sz.S["zin"] = "z"
            st = {"kind": "zombie_timing", "host": sz.socket.gethostname(),
                  "fingerprint": "fp", "dirty": "false",
                  "head_moved": "false", "commit": c,
                  "zombie_inputs_sha256": "z", "launch_sig": "sig1",
                  "overall": "PASS"}
            try:
                self.assertEqual(sz.valid_timing(st), (True, None))
                open(os.path.join(repo, "TODO.md"), "w").write("u")
                subprocess.run(g + ["commit", "-qam", "b"], check=True)
                self.assertEqual(sz.valid_timing(st), (True, None))
                for k, v in (("launch_sig", "x"), ("zombie_inputs_sha256",
                             "y"), ("overall", "FAIL"), ("fingerprint", "o"),
                             ("dirty", "true")):
                    self.assertFalse(sz.valid_timing(dict(st, **{k: v}))[0])
                new = os.path.join(repo, "data/src_sig/ms_dlp/"
                                   "regex_zombie_international/n.regex")
                open(new, "w").write("n")
                ok, why = sz.valid_timing(st)
                self.assertFalse(ok)
                self.assertIn("uncommitted", why)
                os.remove(new)
                open(os.path.join(repo, sz.LIST_TIMING[0]), "w").write("y")
                subprocess.run(g + ["commit", "-qam", "c"], check=True)
                ok, why = sz.valid_timing(st)
                self.assertIn("committed change", why)
            finally:
                sz.S.pop("zin", None)


class RenderTest(unittest.TestCase):
    def test_render_idempotent_and_arm_keys(self):
        orig = ("fn x() {}\nfn zk_test() {\n    match a {\n"
                "        _ => ()\n    }\n}\nfn main() {\n    zk_test()\n}\n")
        sz._ORIG.setdefault("render", rz._render_zkmb)
        a = sz.render_wrapped(orig, [1000, 2000])
        self.assertEqual(a, sz.render_wrapped(orig, [1000, 2000]))
        self.assertIn('"policy_real_2000" => zreal_one_circuit::<2000>'
                      '("policy2000"),', a)
        self.assertIn('"policy_1000" => benchmark_one_circuit("policy1000"',
                      a)
        self.assertLess(a.index("fn zreal_one_circuit"), a.index("fn zk_test"))
        self.assertLess(a.index(rz.SENT_END), a.index(sz.ZREAL_BEGIN))


class StubSetup(Base):
    """A stub circ binary that prints the zreal lines."""

    def setUp(self):
        super().setUp()
        self.stub = os.path.join(self.tmp, "circ_stub")
        with open(self.stub, "w") as f:
            f.write(STUB)
        os.chmod(self.stub, 0o755)
        sz.S["binp"] = self.stub
        sz.S["bus"] = None
        self.env = mock.patch.dict(os.environ, {"STUB_MS": "300"})
        self.env.start()

    def tearDown(self):
        self.env.stop()
        super().tearDown()

    def tasks(self, units=("ua", "ub"), size=1000, cons=70000):
        out = []
        for u in units:
            d = os.path.join(self.tmp, "w_" + u)
            os.makedirs(d, exist_ok=True)
            base = {"base_uuid": "b_" + u, "rss_c": 1 << 20, "wall_s": 1.0,
                    "u_c": 0.5, "cons": cons, "prove_ms": 300}
            sz.put("base", unit=u, size=size, **base)
            for eid, p, _ in sz.sample_emails(size, 2):
                out.append(sz.Task(u, size, eid, p, d, base, False))
        return out


class StubSmoke(StubSetup):
    """Packed sub-flush, gate, widen, serial and STOP with a stub prover."""

    def test_gate_pass_covers_rows(self):
        tasks = self.tasks()
        tail = sz.run_subflush(1000, 16, tasks)
        self.assertEqual(tail, [])
        rows = sz.S["pair"].load()
        base, gates = sz.index_rows(rows)
        g = [r for r in rows if r["kind"] == "gate"]
        self.assertEqual(len(g), 1)
        self.assertEqual(g[0]["verdict"], "pass")
        packed = [r for r in rows if r["kind"] == "prove"
                  and r["mode"] == "packed"]
        self.assertEqual(len(packed), 4)
        self.assertTrue(all(sz.is_accepted(r, base, gates) for r in packed))
        self.assertTrue(all(r["concurrency"] <= r["K_f"] for r in packed))
        ser = [r for r in rows if r.get("mode") == "gate_serial"]
        self.assertGreaterEqual(len(ser), 4)
        self.assertEqual(sz.complete_units(rows, 1000, 2, set()), {"ua", "ub"})
        # second sub-flush with the same key: no new gate event
        sz.run_subflush(1000, 16, self.tasks(units=("uc", "ud")))
        self.assertEqual(len([r for r in sz.S["pair"].load()
                              if r["kind"] == "gate"]), 1)

    def test_gate_fail_widen_then_stop_and_serial(self):
        """Invariant 22: FAIL widens, then STOP at 2000, SERIAL MODE at 1000."""
        os.environ["STUB_SLOW"] = "1.5"
        sz.S["topo"] = fake_topo(cores=4)
        with self.assertRaises(sz.StopFlush) as cm:
            sz.run_subflush(2000, 16, self.tasks(size=2000))
        # ALL_T1013 S5: two-rung stop rule, widths 1, 2, 4 all fail
        self.assertEqual(cm.exception.width, 4)    # the width that failed
        rows = sz.S["pair"].load()
        self.assertEqual([r["verdict"] for r in rows if r["kind"] == "gate"],
                         ["fail", "fail", "fail"])
        self.assertEqual([r["width"] for r in rows if r["kind"] == "width"],
                         [2, 4])
        sz.run_subflush(1000, 16, self.tasks())
        self.assertIn(1000, sz.S["serial"])
        rows = sz.S["pair"].load()
        self.assertEqual(sz.complete_units(rows, 1000, 2, set()), {"ua", "ub"})
        self.assertTrue(any(r.get("mode") == "serial" for r in rows))

    def test_verify_false_goes_to_tail(self):
        os.environ["STUB_VERIFY"] = "false"
        try:
            sz.S["gates"][(1000, 1, 16, "prlimit", "sig1")] = [
                dict(gate_id="gx", K_gate=8)]
            tail = sz.run_subflush(1000, 16, self.tasks())
            self.assertEqual(len(tail), 4)
            sz.run_tail(tail)
            self.assertTrue(any("verify_false" in f for f in sz.S["fails"]))
        finally:
            del os.environ["STUB_VERIFY"]

    def test_flush_stop_path_refuses_size_sweep_goes_on(self):
        """Invariants 22/23 (R1 rule): a flush exception persists a STOP
        row and refuses that size; no exit, so the sweep continues."""
        d = os.path.join(self.tmp, "w_x")
        os.makedirs(d)
        sz.ARGS.sizes = [1000, 2000]
        sz.S["pending"].append({"unit": "ux", "size": 2000, "dir": d,
                                "base": None})
        sz._ORIG["rmtree"] = shutil.rmtree
        sz.flush()
        self.assertEqual(sz.ARGS.sizes, [1000])
        self.assertIn("exception in flush", sz.S["refused"][2000])
        rows = sz.S["pair"].load()
        self.assertEqual(rows[-1]["kind"], "stop")
        self.assertEqual(rows[-1]["launch_sig"], "sig1")
        self.assertFalse(os.path.exists(d))

    def test_write_tsv_columns(self):
        sz.run_subflush(1000, 16, self.tasks())
        sz.write_tsv()
        with open(sz.out_paths()[0]) as f:
            lines = f.read().splitlines()
        self.assertEqual(lines[0].split("\t"), sz.TSV_COLS)
        acc = [ln.split("\t")[5] for ln in lines[1:]
               if ln.split("\t")[4] == "packed"]
        self.assertEqual(acc, ["1"] * 4)


class PipelineSmoke(StubSetup):
    """RZ run_pipeline with the hooks: keygen < base < sample < next keygen."""

    def test_order_and_defer(self):
        full = os.path.join(self.tmp, "rules")
        os.makedirs(full)
        for u in ("u1", "u2", "u3"):
            open(os.path.join(full, u + ".regex"), "w").write(
                "(a.{0,10}(b))|((b).{0,10}a)")
        ev = []

        def build_one(binp, idx, name, str_len, mem=None, timeout=0):
            ev.append(("keygen", name))
            d = os.path.join(rz.PAR_ROOT, "c%05d" % idx)
            os.makedirs(d, exist_ok=True)
            return {"name": name, "prox": 10, "dir": d, "status": "built",
                    "peak_rss": 1 << 20, "key_bytes": 1}
        real_launch = sz.launch

        def launch(t, mode, *a, **k):
            ev.append((mode, t.unit))
            return real_launch(t, mode, *a, **k)
        saved = {k: getattr(rz, k) for k in (
            "FULL_DIR", "PAR_ROOT", "_build_one", "_cpu_max_jobs", "shutil",
            "_time_one", "_load_partial", "_append_partial", "_render_zkmb",
            "run_pipeline")}
        rz.PARTIAL = os.path.join(self.tmp, "rz.jsonl")
        rz.PARTIAL_DOCS = os.path.join(self.tmp, "rzd.jsonl")
        try:
            rz.FULL_DIR, rz.PAR_ROOT = full, os.path.join(self.tmp, "par")
            rz._build_one = build_one
            rz._cpu_max_jobs = lambda: 2
            sz.install_rz_hooks()
            with mock.patch.object(sz, "launch", launch):
                rz.run_pipeline(self.stub, 1000, ["u1", "u2", "u3"], {})
        finally:
            for k, v in saved.items():
                setattr(rz, k, v)
        kinds = [e[0] for e in ev]
        k3 = kinds.index("keygen", 2)            # first keygen of batch 2
        self.assertEqual(kinds[:2], ["keygen", "keygen"])
        self.assertIn("packed", kinds[2:k3])
        self.assertIn("gate_serial", kinds[2:k3])
        self.assertLess(kinds.index("gate_serial"), kinds.index("packed"))
        rows = sz.S["pair"].load()
        self.assertEqual(len([r for r in rows if r["kind"] == "base"]), 3)
        self.assertEqual(sz.complete_units(rows, 1000, 2, set()),
                         {"u1", "u2", "u3"})
        self.assertEqual(os.listdir(os.path.join(self.tmp, "par")), [])
        done = [json.loads(ln) for ln in open(rz.PARTIAL)]
        self.assertEqual(sorted(r["status"] for r in done), ["ok"] * 3)
        self.assertNotIn("base_uuid", done[0])   # base rec unchanged


class Fix1Test(StubSetup):
    """Fix round 1 regressions (DLP_T1001)."""

    def test_pairs_never_complete_serial_at_1kb_stop_at_2kb(self):
        """Review R2: gate pairs never complete -> give_up()."""
        def never(self, queue):                   # every task can never fit
            self.tail.extend(queue)
            del queue[:]
            return False
        with mock.patch.object(sz.Packed, "can", lambda self, t: False), \
                mock.patch.object(sz.Packed, "idle_wait", never):
            sz.run_subflush(1000, 16, self.tasks())
            self.assertIn(1000, sz.S["serial"])
            with self.assertRaises(sz.StopFlush):
                sz.run_subflush(2000, 16, self.tasks(size=2000))
        rows = sz.S["pair"].load()
        self.assertEqual(sz.complete_units(rows, 1000, 2, set()), {"ua", "ub"})

    def test_listed_pair_over_B_is_proved_once_serially(self):
        """Review minor 3: a listed pair whose cap > B still gets one prove."""
        tasks = self.tasks(units=("ua",))
        t0 = tasks[0]
        sz.S["er"] = {(t0.unit, t0.eid, 1000)}
        big = dict(t0.base, rss_c=sz.memavail() * 2)
        sz.S["pending"].append({"unit": "ua", "size": 1000, "dir": t0.dir,
                                "base": big})
        sz.put("base", unit="ua", size=1000, **big)
        sz._ORIG["rmtree"] = shutil.rmtree
        sz.flush()
        er = [r for r in sz.S["pair"].load() if r["kind"] == "prove"
              and r["expected_reject"]]
        self.assertEqual([(r["mode"], r["attempt"]) for r in er], [("tail", 1)])

    def test_crash_first_seen_in_tail_gets_one_reproduce(self):
        """Review minor 5: crash_suspect gets 1 more attempt, then FAIL."""
        os.environ["STUB_RC"] = "1"
        t = self.tasks(units=("ua",))[0]
        self.assertEqual(sz.serial_until_done(t, "tail"), "crash_suspect")
        self.assertEqual(t.cls, ["crash_suspect", "crash_suspect"])
        self.assertTrue(any("reproduced crash" in f for f in sz.S["fails"]))

    def test_bus_result_off_the_main_loop(self):
        """Review minor 1: the scope Result comes from a pool future."""
        from concurrent.futures import ThreadPoolExecutor
        sz.S["bus"] = ThreadPoolExecutor(max_workers=4)
        calls = []

        def slow(unit):
            calls.append(unit)
            import time
            time.sleep(0.3)
            return "oom-kill"
        sz.S["gates"][(1000, 1, 16, "prlimit", "sig1")] = [
            dict(gate_id="gx", K_gate=8)]
        with mock.patch.object(sz, "needs_bus", lambda r: True), \
                mock.patch.object(sz, "bus_result", slow):
            sz.run_subflush(1000, 16, self.tasks())
        sz.S["bus"].shutdown()
        rows = [r for r in sz.S["pair"].load() if r["kind"] == "prove"
                and r["mode"] == "packed"]
        self.assertEqual(len(calls), 4)
        self.assertEqual({r["Result"] for r in rows}, {"oom-kill"})

    def test_scalecal_uses_4_emails_and_post_build_hash(self):
        """Review minor 4 and R1: 4 e-mails; stamp holds the post-build hash."""
        tasks = self.tasks(units=("ua",))
        sz.S["keep"].append({"unit": "ua", "size": 1000, "dir": tasks[0].dir,
                             "base": tasks[0].base})
        sz.ARGS.scalecal_min_cores = 1
        tree = os.path.join(self.tmp, "ztree")
        os.makedirs(os.path.join(tree, "circ"))
        open(os.path.join(tree, "circ", "a"), "w").write("pre")
        with mock.patch.object(sz, "ZOMBIE_TREE", tree):
            sz.S["zin"] = "stale-pre-build"
            sz.post_build(self.stub, sz.ARGS)
            self.assertNotEqual(sz.S["zin"], "stale-pre-build")
            self.assertEqual(sz.S["sig"], sz.launch_sig(
                sz.S["topo"]["tpc"], sz.ARGS))
            sz.scalecal()
        st = sz.read_scalecal("t1")
        self.assertEqual(st["zombie_inputs_sha256"], sz.S["zin"])
        self.assertEqual(st["launch_sig"], sz.S["sig"])
        ser = {r["email_id"] for r in sz.S["pair"].load()
               if r.get("mode") == "gate_serial"}
        self.assertEqual(len(ser), 4)

    def test_topology_line_full_sig(self):
        """Review W1: the log carries the full 64-hex launch_sig."""
        sz.S["sig"] = "ab" * 32
        self.assertIn("launch_sig=%s " % ("ab" * 32), sz.topology_line())


class CheckStartTest(Base):
    """Fix 5/6: clone, oomd and probes refuse at plan start."""

    def test_refusals(self):
        a = sz.parse_args(["--sizes", "1000", "--server", "t1"])
        with mock.patch.object(sz, "clone_check", return_value="clone bad"):
            self.assertEqual(sz.check_start_main(a), 6)
        with mock.patch.object(sz, "clone_check", return_value=None), \
                mock.patch.object(sz, "oomd_check", return_value="omit"), \
                mock.patch.object(sz, "launcher_probe") as lp:
            self.assertEqual(sz.check_start_main(a), 6)
            lp.assert_not_called()
        with mock.patch.object(sz, "clone_check", return_value=None), \
                mock.patch.object(sz, "oomd_check", return_value=None), \
                mock.patch.object(sz, "same_units_running",
                                  return_value=False), \
                mock.patch.object(sz, "launcher_probe",
                                  return_value=("prlimit", [], "x")) as lp:
            self.assertEqual(sz.check_start_main(a), 0)
            lp.assert_called_once()

    def test_clone_check(self):
        d = os.path.join(self.tmp, "ms")
        os.makedirs(os.path.join(d, "zombie", "circ", "src"))
        with mock.patch.object(sz, "MS_DLP", d), \
                mock.patch.object(rz, "CIRC_BUILD", os.path.join(self.tmp,
                                                                 "cb")):
            self.assertIn("download_zombie", sz.clone_check())
            os.makedirs(os.path.join(d, "zombie", "circ", "src", "target"))
            open(os.path.join(d, "zombie/circ/src/target/mod.rs"), "w").close()
            self.assertIsNone(sz.clone_check())
            os.makedirs(os.path.join(self.tmp, "cb", "src"))
            self.assertIn("stale circ build", sz.clone_check())

    def test_usage_states_outer_scope(self):
        out = []
        with mock.patch.object(sys, "stdout") as so, \
                self.assertRaises(SystemExit):
            so.write.side_effect = out.append
            sz.parse_args(["--help"])
        self.assertIn("ManagedOOMPreference=omit", "".join(out))
        self.assertIn("default 16", "".join(out))
        self.assertIn("<= 1.13", "".join(out))

    def test_judge_fixed_tau(self):
        """Round 3: tau is 1.13 (13%), no noise term."""
        self.assertEqual(sz.judge({1: 112}, {1: 100}, 0.3)[1:], (1.13, True))
        self.assertFalse(sz.judge({1: 114}, {1: 100}, 0.0)[2])


@unittest.skipUnless(shutil.which("systemd-run") and subprocess.run(
    ["systemctl", "--user", "show", "-p", "Version"],
    capture_output=True).returncode == 0, "no systemd user manager")
class PreflightRealTest(Base):
    """Fix 1: real probes, then a prove scope's argv (no MemoryMax=64M)."""

    def test_prove_argv_after_probes(self):
        if (sz.driver_lock_held(sz._REAL_DRIVER_LOCK) or _REAL_SCAN()
                or sz.same_units_running()):   # ALL_T1009: live run guard
            self.skipTest("a live Zombie driver runs on this box")
        lch, props, note = sz.launcher_probe()
        self.assertTrue(all(not q.startswith("MemoryMax") for q in props))
        if lch != "systemd":
            self.skipTest("probes chose prlimit: %s" % note)
        sz.S.update(launcher="systemd", props=props, binp="/bin/true")
        t = sz.Task("u", 1000, "1000_01", "/dev/null", self.tmp,
                    {"base_uuid": "b", "rss_c": 1 << 30, "wall_s": 1,
                     "u_c": 1, "cons": 1}, False)
        seen = []

        class P(object):
            pid = 0

            def __init__(self, cmd, **k):
                seen.append(cmd)
        with mock.patch.object(sz.subprocess, "Popen", P):
            sz.launch(t, "packed", slot=(0, [8]), w=1)
            sz.launch(t, "tail")
        packed, serial = seen
        mm = [packed[i + 1] for i, x in enumerate(packed) if x == "-p"
              and packed[i + 1].startswith("MemoryMax=")]
        self.assertEqual(mm, ["MemoryMax=%d" % t.cap])
        self.assertFalse(any(x.startswith("MemoryMax=") for x in serial))
        self.assertIn("--slice=bora-tail.slice", serial)


class ScalecalLadderTest(Base):
    """Round 3: scalecal widths follow the cap and the node size."""

    def test_widths(self):
        t16 = fake_topo(cores=16)
        # ALL_T1013 S5: rungs by slot count, top rung = min(cap, C)
        self.assertEqual(sz.scalecal_widths(t16, 16), [1, 2, 3, 4, 8, 16])
        self.assertEqual(sz.scalecal_widths(t16, 4), [1, 2, 3, 4])
        self.assertEqual(sz.scalecal_widths(t16, 0), [1, 2, 4])
        self.assertEqual(sz.scalecal_widths(fake_topo(cores=4), 16), [1, 2, 4])
        self.assertEqual(sz.scalecal_widths(fake_topo(cores=124), 16),
                         [1, 2, 3, 4, 6, 9, 13, 16])

    def test_scalecal_tries_8_and_16(self):
        sz.S["topo"] = fake_topo(cores=16)
        sz.S["cap"] = 16
        sz.ARGS.scalecal_min_cores = 1
        d = os.path.join(self.tmp, "u")
        os.makedirs(d)
        base = {"base_uuid": "b", "rss_c": 1 << 20, "wall_s": 1.0,
                "u_c": 1.0, "cons": 70000, "prove_ms": 100}
        sz.S["keep"].append({"unit": "u", "size": 1000, "dir": d,
                             "base": base})
        tried = []

        class FakePacked(object):
            def __init__(self, size, b, w, B, K_f, gid, pairs, mode=None):
                tried.append(w)
                self.pairs = pairs
                self.pair_ms = {}

            def run(self, queue):
                ms = 100 if tried[-1] < 8 else 100
                self.pair_ms = {c: (ms * 2 if tried[-1] < 8 else ms)
                                for c in self.pairs}
        with mock.patch.object(sz, "Packed", FakePacked), \
                mock.patch.object(sz, "serial_reference",
                                  lambda ts: ({id(t): 100 for t in ts}, 0.01)):
            sz.scalecal()
        self.assertEqual(tried, [1, 2, 3, 4, 8, 16])   # ALL_T1013 S5
        st = sz.read_scalecal("t1")
        self.assertEqual((st["overall"], st["w0"]), ("PASS", "8"))


class FullStartTest(Base):
    """Round 4: a full run without a PASS runs scalecal first."""

    def _run(self, verdict):
        sz.S["cap"] = 16
        sz.S["topo"] = fake_topo(cores=36)
        a = sz.parse_args(["--sizes", "1000,2000,4000", "--server", "t1"])
        st = {"w0": "4", "commit": "c", "overall": verdict}
        calls = []

        def scal():
            calls.append(1)
            self.wrote = True
        self.wrote = False
        vt = lambda s: ((False, "no scalecal stamp") if not self.wrote else
                        ((True, None) if verdict == "PASS" else
                         (False, "scalecal verdict FAIL")))
        with mock.patch.object(sz, "read_scalecal",
                               side_effect=lambda srv, dry=False: st
                               if self.wrote and not dry else None), \
                mock.patch.object(sz, "valid_timing", side_effect=vt), \
                mock.patch.object(sz, "in_run_scalecal", side_effect=scal), \
                mock.patch.object(sz, "print_stamp_view"):
            why = sz.full_start(a, [])
        self.assertEqual(calls, [1])
        return why or next(iter(sz.S["refused"].values()), None)

    def test_no_pass_then_scalecal_pass_allows_all_sizes(self):
        self.assertIsNone(self._run("PASS"))
        self.assertEqual(sz.S["serial"], set())
        self.assertEqual(sz.S["w_state"], {1000: 4, 2000: 4, 4000: 4})

    def test_no_pass_then_scalecal_fail_serial_and_refuse(self):
        why = self._run("FAIL")
        self.assertIn("no valid PASS for 2000", why)
        self.assertIn("already tried the speed check", why)
        self.assertNotIn("dry_run", why)
        self.assertEqual(sz.S["serial"], {1000})

    def test_check_start_pending_does_not_refuse(self):
        sz.S["topo"] = fake_topo(cores=36)
        a = sz.parse_args(["--sizes", "1000,2000,4000", "--server", "t1"])
        with mock.patch.object(sz, "read_scalecal", return_value=None), \
                mock.patch.object(sz, "valid_timing",
                                  return_value=(False, "no stamp")), \
                mock.patch.object(sz, "print_stamp_view"):
            self.assertIsNone(sz.start_check(a, [], pending=True))
        self.assertEqual(sz.S["serial"], set())

    def test_in_run_stamp_valid_after_full_run(self):
        """Stamp validity rules hold for a mode=full stamp."""
        st = {"kind": "zombie_timing", "host": sz.socket.gethostname(),
              "fingerprint": "fp", "dirty": "false", "head_moved": "false",
              "commit": sz.git_head(), "mode": "full",
              "zombie_inputs_sha256": sz.zombie_inputs_sha256(),
              "launch_sig": "sig1", "overall": "PASS"}
        with mock.patch.object(sz, "git_status", return_value=""):
            self.assertEqual(sz.valid_timing(st), (True, None))
            self.assertFalse(sz.valid_timing(dict(st, launch_sig="x"))[0])
        sz.S.pop("zin", None)


class OomdReadOnlyTest(unittest.TestCase):
    """Round 4: oomd_check(repair=False) never repairs and needs no logdir."""

    def test_repair_false_never_calls_sctl(self):
        saved = dict(sz.S)
        sz.S.clear()                              # no S["logdir"]
        ro = mock.Mock(side_effect=lambda cmd: mock.Mock(
            returncode=0, stdout="active\n" if cmd[0] == "systemctl" else
            "Memory Pressure Monitored CGroups:\n\tPath: /user.slice\n"))
        try:
            with mock.patch.object(sz, "sctl") as sc, \
                    mock.patch.object(sz, "run_logged") as rl, \
                    mock.patch.object(sz, "_run_ro", ro), \
                    mock.patch.object(sz, "_read",
                                      return_value="0::/user.slice/x.scope"), \
                    mock.patch.object(sz, "has_omit", return_value=False):
                why = sz.oomd_check(repair=False)
                sc.assert_not_called()
                rl.assert_not_called()
            self.assertIn("without user.oomd_omit", why)
            with mock.patch.object(sz, "sctl") as sc, \
                    mock.patch.object(sz, "_run_ro", ro), \
                    mock.patch.object(sz, "_read",
                                      return_value="0::/user.slice/x.scope"), \
                    mock.patch.object(sz, "has_omit", return_value=True):
                self.assertIsNone(sz.oomd_check(repair=False))
                sc.assert_not_called()
        finally:
            sz.S.clear()
            sz.S.update(saved)


class DryNamesTest(Base):
    """A dry run leaves the full run's docs outputs byte-identical."""

    def test_dry_main_keeps_full_outputs(self):
        full = sz.out_paths()
        for i, p in enumerate(full):
            with open(p, "w") as f:
                f.write("full output %d\n" % i)
        before = [open(p, "rb").read() for p in full]
        cwd, h = os.getcwd(), signal.getsignal(signal.SIGTERM)
        try:
            with mock.patch.object(sz, "run_main", return_value=0):
                rc = sz.main(["--dry", "4", "--sizes", "1000", "--n", "2",
                              "--server", "t1", "--scalecal"])
        finally:
            os.chdir(cwd)
            signal.signal(signal.SIGTERM, h)
        self.assertEqual(rc, 0)
        self.assertEqual([open(p, "rb").read() for p in full], before)
        dry = sz.out_paths()
        self.assertEqual([os.path.basename(p) for p in dry],
                         ["same_zombie_regex_zombie_international.dry.tsv",
                          "same_zombie_regex_zombie_international.dry.log"])
        self.assertTrue(all(os.path.isfile(p) for p in dry))


class Round5Test(StubSetup):
    """Fix round 5 (review 2) regressions (DLP_T1001)."""

    def _hooks_saved(self):
        return {k: getattr(rz, k) for k in (
            "FULL_DIR", "PAR_ROOT", "shutil", "_time_one", "_load_partial",
            "_append_partial", "_render_zkmb", "run_pipeline", "main",
            "ensure_zombie_built", "_pick_scratch_base", "VEC_SIZE",
            "list_policy_names", "PARTIAL", "PARTIAL_DOCS")}

    def _main(self, argv, extra=()):
        saved = self._hooks_saved()
        cwd, h = os.getcwd(), signal.getsignal(signal.SIGTERM)
        mains = []
        rz.ensure_zombie_built = lambda sizes: self.stub
        rz.main = lambda: mains.append(list(sz.ARGS.sizes))
        rz._pick_scratch_base = lambda: os.path.join(self.tmp, "scratch")
        try:
            with mock.patch.object(sz, "preflight",
                                   return_value=("prlimit", [], "")), \
                    mock.patch.object(sz, "clone_check", return_value=None):
                for m in extra:
                    m.start()
                try:
                    rc = sz.main(argv)
                finally:
                    for m in extra:
                        m.stop()
        finally:
            os.chdir(cwd)
            signal.signal(signal.SIGTERM, h)
            for k, v in saved.items():
                setattr(rz, k, v)
        return rc, mains

    def test_r1_missing_pass_runs_sweep_and_1kb_then_stop(self):
        def fs(a, rows):
            sz.S["serial"] = {1000}
            sz.S["refused"] = {2000: "no valid PASS for 2000 (x)",
                               4000: "no valid PASS for 4000 (x)"}
        rc, mains = self._main(
            ["--sizes", "1000,2000,4000", "--n", "2", "--server", "t1",
             "--launcher", "prlimit"],
            [mock.patch.object(sz, "full_start", side_effect=fs)])
        self.assertEqual(rc, 6)
        self.assertEqual(mains, [[1000]])          # sweep ran, 1 KB sample
        with open(sz.out_paths()[1]) as f:
            log = f.read()
        self.assertIn("SAME STOP at 2000: no valid PASS", log)
        self.assertIn("SAME STOP at 4000", log)
        stops = [r for r in sz.pair_names(sz.ARGS)[1].load()
                 if r["kind"] == "stop"]
        self.assertEqual(sorted((r["size"], r["cause"]) for r in stops),
                         [(2000, "nopass"), (4000, "nopass")])
        self.assertTrue(all(len(r["launch_sig"]) == 64 for r in stops))

    def test_r1_check_start_refuses_dirty_timing_list(self):
        sz.S["topo"] = fake_topo(cores=36)
        a = sz.parse_args(["--sizes", "1000,2000,4000", "--server", "t1",
                           "--launcher", "prlimit"])
        with mock.patch.object(sz, "clone_check", return_value=None), \
                mock.patch.object(sz, "oomd_check", return_value=None), \
                mock.patch.object(sz, "best_scalecal",
                                  return_value=(None, False, "no stamp")), \
                mock.patch.object(sz, "git_status",
                                  return_value="?? data/x.regex"):
            self.assertEqual(sz.check_start_main(a), 6)

    def test_r2_restore_before_in_run_scalecal(self):
        """Real ordering: docs-only pre-reboot rows survive the in-run
        scalecal (stub prover, real keygen path, no valid stamp)."""
        st = dict(ids_sha=sz.sha256_file(os.path.join(sz.FX, "ids.tsv")),
                  list_sha=sz.sha256_file(os.path.join(
                      sz.FX, "zombie_expected_reject.tsv")),
                  zok_gen=rz.ZOK_GEN, fp="old", commit="c", launch_sig="old")
        old = dict(st, kind="prove", unit="old_unit", size=1000,
                   email_id="1000_01", mode="tail", expected_reject=0,
                   **{"class": "ok"})
        sweep, sample = sz.pair_names(sz.ARGS)
        for p, text in ((sample.docs, json.dumps(old) + "\n"),
                        (sweep.docs, '{"regex_name": "u", "str_len": 1000, '
                         '"status": "ok", "zok_gen": "%s"}\n' % rz.ZOK_GEN)):
            with open(p, "w") as f:
                f.write(text)
        rc, mains = self._main(
            ["--sizes", "1000", "--n", "2", "--server", "t1",
             "--launcher", "prlimit", "--scalecal-min-cores", "1",
             "--reserve-floor", "1"])
        with open(sz.out_paths()[0]) as f:
            tsv = f.read()
        self.assertIn("old_unit", tsv)                # pre-reboot row kept
        self.assertTrue(any(r.get("scal") for r in sample.load()))
        self.assertEqual(len([ln for ln in tsv.splitlines()[1:]]), 1)
        self.assertEqual(mains, [[1000]])

    def test_r3_pause_does_not_dump_queue_to_tail(self):
        tasks = self.tasks(units=("ua",))
        t0 = [None]
        real = sz.memavail

        def fake():
            now = sz.time.time()
            if t0[0] is None:
                t0[0] = now
            return 0 if 0.15 < now - t0[0] < 1.2 else real()
        pk = sz.Packed(1000, 16, 1, 1 << 40, 1, "g", None)
        with mock.patch.object(sz, "memavail", fake):
            q = list(tasks)
            pk.run(q)
        self.assertEqual(pk.tail, [])
        rows = [r for r in sz.S["pair"].load() if r["kind"] == "prove"]
        self.assertEqual([r["mode"] for r in rows], ["packed", "packed"])

    def test_width_cap_bounds_first_width(self):
        sz.S["topo"] = fake_topo(n_nodes=2, cores=32, base=0, keep=4)
        sz.S["cap"] = 4
        t = self.tasks(units=("ua",))[:1]
        t[0].base["rss_c"] = 200 * sz.GIB          # memory-bound: w_mem 60
        self.assertEqual(sz.width_for(4000, t, 500 * sz.GIB), 4)

    def test_torn_last_line_and_hold(self):
        sweep, sample = sz.pair_names(sz.ARGS)
        with open(sample.tmp, "w") as f:
            f.write(json.dumps(sz.stamp()) + "\n" + '{"kind": "pro')
        self.assertEqual(len(sample.load()), 1)
        sample.repair_tail()
        with open(sample.tmp) as f:
            self.assertEqual(len(f.read().splitlines()), 1)
        with open(sample.tmp, "w") as f:
            f.write('{"bad\n' + json.dumps(sz.stamp()) + "\n")
        with self.assertRaises(ValueError):
            sample.load()
        os.remove(sample.tmp)
        sz.S["pair"].append([sz.stamp()])
        with open(sweep.docs + ".hold", "w") as f:
            f.write("{}\n")
        self.assertFalse(sz.rule2(sweep, sample))      # .hold = present
        os.remove(sweep.docs + ".hold")
        self.assertTrue(sz.rule2(sweep, sample))

    def test_scalecal_dry_then_full_and_full_then_dry(self):
        os.makedirs(os.path.join(sz.RAW_DATA_ROOT, "t1"))
        hdr = "\t".join(sz.SCAL_COLS) + "\n"
        row = lambda ov, mode: "\t".join(
            {"overall": ov, "mode": mode, "w0": "4"}.get(c, "x")
            for c in sz.SCAL_COLS) + "\n"
        with open(sz.scalecal_path("t1", dry=True), "w") as f:
            f.write(hdr + row("PASS", "dry"))
        vt = lambda st: ((st or {}).get("overall") == "PASS", "v")
        with mock.patch.object(sz, "valid_timing", vt):
            st, ok, _ = sz.best_scalecal("t1")      # dry then full: found
            self.assertEqual((ok, st["mode"]), (True, "dry"))
        full = sz.scalecal_path("t1")
        with open(full, "w") as f:
            f.write(hdr + row("PASS", "full"))
        before = open(full, "rb").read()
        sz.ARGS.dry, sz.ARGS.scalecal_min_cores = 4, 1
        sz.S["topo"] = fake_topo(cores=4)
        d = os.path.join(self.tmp, "u")
        os.makedirs(d)
        sz.S["keep"].append({"unit": "u", "size": 1000, "dir": d, "base": {
            "base_uuid": "b", "rss_c": 1 << 20, "wall_s": 1.0, "u_c": 1.0,
            "cons": 70000, "prove_ms": 100}})

        class FakePacked(object):
            def __init__(self, size, b, w, B, K_f, gid, pairs, mode=None):
                self.pairs, self.pair_ms = pairs, {}

            def run(self, queue):
                self.pair_ms = {c: 100 for c in self.pairs}
        with mock.patch.object(sz, "Packed", FakePacked), \
                mock.patch.object(sz, "serial_reference",
                                  lambda ts: ({id(t): 100 for t in ts}, 0.01)):
            sz.scalecal()                           # full then dry
        self.assertEqual(open(full, "rb").read(), before)
        self.assertEqual(sz.read_scalecal("t1", dry=True)["mode"], "dry")
        self.assertTrue(os.path.isfile(os.path.join(
            sz.DOCS, "same_zombie_scalecal.dry.tsv")))

    def test_verify_false_gate_pair_is_not_a_gate_stop(self):
        os.environ["STUB_VF_EMAIL"] = "1000_01"
        tail = sz.run_subflush(1000, 16, self.tasks())
        rows = sz.S["pair"].load()
        self.assertEqual([r["verdict"] for r in rows if r["kind"] == "gate"],
                         ["pass"])
        self.assertTrue(any("gate pair" in f for f in sz.S["fails"]))
        self.assertEqual(sz.S["serial"], set())
        self.assertTrue(all(t.eid == "1000_01" for t in tail))
        os.environ["STUB_VERIFY"] = "false"           # every pair rejects
        with self.assertRaises(sz.StopFlush) as cm:
            sz.run_subflush(2000, 16, self.tasks(size=2000))
        self.assertIn("verify_false", str(cm.exception))

    def test_launcher_switch_one_accepted_row_per_pair(self):
        calls = []
        real = sz.judge

        def judge(pm, ref, s):
            calls.append(1)
            if len(calls) == 1:
                sz.S["launcher"] = "prlimit2"         # switch mid-pass
            return real(pm, ref, s)
        with mock.patch.object(sz, "judge", judge):
            sz.run_subflush(1000, 16, self.tasks(units=("ua", "ub", "uc")))
        rows = sz.S["pair"].load()
        base, gates = sz.index_rows(rows)
        acc = {}
        for r in rows:
            if sz.is_accepted(r, base, gates):
                k = (r["unit"], r["email_id"])
                acc[k] = acc.get(k, 0) + 1
        self.assertEqual(len(acc), 6)
        self.assertEqual(set(acc.values()), {1})


class FakeClock(object):
    """time stand-in: sleep advances the clock, with a tiny real sleep."""

    def __init__(self):
        import time as _t
        self._t, self.now = _t, _t.time()

    def time(self):
        return self.now

    def sleep(self, x):
        self._t.sleep(min(x, 0.005))
        self.now += x

    def strftime(self, *a):
        return self._t.strftime(*a)


class MemWaitTest(StubSetup):
    """Bounded idle memory wait (DLP_T1001 R3 follow-up)."""

    def test_wait_times_out_with_logs_then_refuses_size(self):
        clk = FakeClock()
        lines = []
        pk = sz.Packed(2000, 16, 1, 1 << 40, 1, "g", None)
        q = self.tasks(units=("ua",), size=2000)
        with mock.patch.object(sz, "time", clk), \
                mock.patch.object(sz, "POLL_S", 1.0), \
                mock.patch.object(clk, "_t", mock.Mock(sleep=lambda x: None)), \
                mock.patch.object(sz, "memavail", lambda: 0), \
                mock.patch.object(sz, "say", lines.append):
            with self.assertRaises(sz.MemStop):
                pk.run(q)
        waits = [ln for ln in lines if ln.startswith("SAME WAIT memory")]
        self.assertEqual(len(waits),
                         sz.MEM_WAIT_MAX_S // sz.MEM_WAIT_LOG_S + 1)
        self.assertIn("2 tasks queued", waits[0])
        # the flush handler: 2 KB refused, the sweep goes on
        sz.ARGS.sizes = [1000, 2000]
        with mock.patch.object(sz, "memavail", lambda: 0):
            sz.mem_stop(2000, "idle memory wait", q)
        self.assertEqual(sz.ARGS.sizes, [1000])
        self.assertIn("resource stop", sz.S["refused"][2000])
        # at 1 KB with memory for one serial prove: serial mode, not refused
        sz.mem_stop(1000, "idle memory wait", self.tasks(units=("ub",)))
        self.assertIn(1000, sz.S["serial"])
        self.assertNotIn(1000, sz.S["refused"])

    def test_memory_returns_at_minute_30_tasks_launch_packed(self):
        clk = FakeClock()
        t0, real = clk.now, sz.memavail
        pk = sz.Packed(1000, 16, 1, 1 << 40, 1, "g", None)
        q = self.tasks(units=("ua",))
        with mock.patch.object(sz, "time", clk), \
                mock.patch.object(sz, "POLL_S", 1.0), \
                mock.patch.object(sz, "memavail",
                                  lambda: 0 if clk.now - t0 < 1800 else real()):
            pk.run(q)
        self.assertEqual(pk.tail, [])
        rows = [r for r in sz.S["pair"].load() if r["kind"] == "prove"]
        self.assertEqual([r["mode"] for r in rows], ["packed", "packed"])
        self.assertTrue(clk.now - t0 >= 1800)


class Round6Test(StubSetup):
    """Fix round 6 (review 3) regressions (DLP_T1001)."""

    def test_n2_newline_cut_and_whitespace_file(self):
        sweep, sample = sz.pair_names(sz.ARGS)
        with open(sample.tmp, "w") as f:
            f.write(json.dumps(sz.stamp()) + "\n" + json.dumps(sz.stamp()))
        with open(sample.docs, "w") as f:
            f.write("  \n\n")
        sample.repair_tail()
        sample.append([sz.stamp()])
        self.assertEqual(len(sample.load()), 3)       # no "}{" join
        with open(sample.docs) as f:
            self.assertEqual(len([ln for ln in f if ln.strip()]), 1)

    def _cs(self, sizes, cap, stt):
        sz.S["topo"] = fake_topo(cores=36)
        sz.S["cap"] = cap
        a = sz.parse_args(["--sizes", sizes, "--server", "t1",
                           "--launcher", "prlimit"])
        lines = []
        with mock.patch.object(sz, "clone_check", return_value=None), \
                mock.patch.object(sz, "oomd_check", return_value=None), \
                mock.patch.object(sz, "best_scalecal",
                                  return_value=(None, False, "no stamp")), \
                mock.patch.object(sz, "print_stamp_view"), \
                mock.patch.object(sz, "git_status", return_value=stt), \
                mock.patch.object(sz, "say", lines.append):
            return sz.check_start_main(a), "\n".join(lines)

    def test_n3_dirty_refusal_only_when_a_stamp_is_needed(self):
        self.assertEqual(self._cs("1000,2000,4000", 16, "?? x")[0], 6)
        rc, log = self._cs("1000", 16, "?? x")
        self.assertEqual(rc, 0)
        self.assertIn("WARNING", log)
        self.assertEqual(self._cs("1000,2000,4000", 0, "?? x")[0], 0)
        rc, log = self._cs("1000,2000,4000", 16, None)  # git failed
        self.assertEqual(rc, 6)                 # ALL_T1009: A6c refuses now
        self.assertIn("SAME check-start REFUSE: git status failed", log)
        rc, log = self._cs("1000", 16, None)    # no stamp needed: warn only
        self.assertEqual(rc, 0)
        self.assertIn("CAVEAT: SAME check-start WARNING: git status failed",
                      log)

    def test_n4_cap0_serial_and_stop_rows_on_resume(self):
        sz.S["cap"] = 0
        sz.ARGS.sizes = [1000, 2000]
        sz.mem_stop(2000, "idle memory wait", self.tasks(size=2000))
        self.assertIn(2000, sz.S["serial"])
        self.assertNotIn(2000, sz.S.get("refused", {}))
        sz.S["cap"], sz.S["serial"] = 16, set()
        with mock.patch.object(sz, "memavail", lambda: 0):
            sz.mem_stop(2000, "idle memory wait", self.tasks(size=2000))
        rows = sz.S["pair"].load()
        stop = [r for r in rows if r["kind"] == "stop"][-1]
        self.assertEqual((stop["size"], stop["cause"], stop["launch_sig"]),
                         (2000, "mem", "sig1"))
        # ALL_T1013 F10: one mem STOP is lifted once; a second one stays
        # refused (no re-keygen), and check-start only warns
        sz.S["topo"] = fake_topo(cores=36)
        a = sz.parse_args(["--sizes", "1000,2000", "--server", "t1"])
        sc = {"w0": "4", "commit": "c"}
        with mock.patch.object(sz, "read_scalecal", return_value=sc), \
                mock.patch.object(sz, "valid_timing",
                                  return_value=(True, None)), \
                mock.patch.object(sz, "print_stamp_view"):
            self.assertIsNone(sz.start_check(a, rows))
            self.assertNotIn(2000, sz.S["refused"])
            other = dict(stop, launch_sig="sig0")    # V11: own sig only
            self.assertIsNone(sz.start_check(a, rows + [other]))
            self.assertNotIn(2000, sz.S["refused"])
            err = dict(stop, cause="error", etype="OSError")
            self.assertIsNone(sz.start_check(a, rows + [err, stop]))
            self.assertIn(2000, sz.S["refused"])   # V11: counts mem rows only
            rows = rows + [dict(stop)]
            self.assertIsNone(sz.start_check(a, rows))
            self.assertIn(2000, sz.S["refused"])
            self.assertIn(2000, sz.S["refused_prior"])
            nopass = dict(stop, cause="nopass")      # nopass + PASS: lifted
            self.assertIsNone(sz.start_check(a, [nopass]))
            self.assertEqual(sz.S["refused"], {})

    def test_n5_in_run_scalecal_crash_takes_r1_path(self):
        sz.S["cap"] = 16
        sz.S["topo"] = fake_topo(cores=36)
        a = sz.parse_args(["--sizes", "1000,2000,4000", "--server", "t1"])
        lines = []
        with mock.patch.object(sz, "best_scalecal",
                               return_value=(None, False, "no stamp")), \
                mock.patch.object(sz, "in_run_scalecal",
                                  side_effect=OSError("disk full")), \
                mock.patch.object(sz, "print_stamp_view"), \
                mock.patch.object(sz, "say", lambda m, caveat=False:
                                  lines.append(m)):
            self.assertIsNone(sz.full_start(a, []))
        self.assertEqual(sz.S["serial"], {1000})
        self.assertEqual(sorted(sz.S["refused"]), [2000, 4000])
        self.assertIn("already tried", sz.S["refused"][2000])
        self.assertTrue(any("SCALECAL FAIL (crash" in m and "Traceback" in m
                            for m in lines))


class GateStopResumeTest(Base):
    """Round 6 follow-up: a gate STOP refuses only its size on resume."""

    def test_resume_after_gate_stop(self):
        stop = dict(kind="stop", size=4000, reason="gate cannot pass at 4000",
                    cap=16, width=4, launch_sig="sig1", cause="gate")
        sz.S["topo"] = fake_topo(cores=36)
        sz.S["cap"] = 16
        a = sz.parse_args(["--sizes", "1000,2000,4000", "--server", "t1",
                           "--launcher", "prlimit"])
        sz.S["pair"].append([dict(sz.stamp(), **stop)])
        sweep = sz.pair_names(a)[0]
        with open(sweep.docs, "w") as f:          # ALL_T1009: a row RZ loads
            f.write(json.dumps({"regex_name": "u", "str_len": 1000,
                                "zok_gen": rz.ZOK_GEN}) + "\n")
        sc = {"w0": "4", "commit": "c"}
        with mock.patch.object(sz, "read_scalecal", return_value=sc), \
                mock.patch.object(sz, "valid_timing",
                                  return_value=(True, None)), \
                mock.patch.object(sz, "print_stamp_view"), \
                mock.patch.object(sz, "clone_check", return_value=None), \
                mock.patch.object(sz, "oomd_check", return_value=None):
            self.assertEqual(sz.check_start_main(a), 0)     # warns only
            rows = sz.load_sample(a)
            self.assertIsNone(sz.start_check(a, rows))
            self.assertEqual(list(sz.S["refused"]), [4000])
            self.assertEqual(sz.S["serial"], set())         # 1 KB packed
            sz.S["cap"] = 32                                # raised cap
            self.assertIsNone(sz.start_check(a, rows))
            self.assertEqual(sz.S["refused"], {})
            self.assertEqual(sz.S["w_state"][4000], 6)   # ALL_T1013 S5


class Round7Test(StubSetup):
    """Fix round 7 (review 4) regressions (DLP_T1001)."""

    def test_m1_stop_at_1kb_under_scalecal_keeps_no_deleted_dir(self):
        d = os.path.join(self.tmp, "w_x")
        os.makedirs(d)
        sz.ARGS.scalecal = True
        sz.S["pending"].append({"unit": "ux", "size": 1000, "dir": d,
                                "base": None})          # raises in flush
        sz._ORIG["rmtree"] = shutil.rmtree
        sz.flush()
        self.assertEqual(sz.S["keep"], [])
        self.assertFalse(os.path.exists(d))

    def test_m2_error_stop_lifted_once_gate_stop_kept(self):
        d = os.path.join(self.tmp, "w_y")
        os.makedirs(d)
        sz._ORIG["rmtree"] = shutil.rmtree
        sz.ARGS.sizes = [1000, 2000, 4000]
        sz.S["pending"].append({"unit": "uy", "size": 2000, "dir": d,
                                "base": None})
        sz.flush()                                       # code bug: error
        with mock.patch.object(sz, "run_subflush", side_effect=sz.StopFlush(
                "gate cannot pass at 4000", 4)):
            sz.S["pending"].append(self._item(4000))
            sz.flush()                                   # real gate fail
        rows = sz.S["pair"].load()
        causes = {r["size"]: r["cause"] for r in rows if r["kind"] == "stop"}
        self.assertEqual(causes, {2000: "error", 4000: "gate"})
        sz.S["topo"] = fake_topo(cores=36)
        a = sz.parse_args(["--sizes", "1000,2000,4000", "--server", "t1"])
        sc = {"w0": "4", "commit": "c"}
        with mock.patch.object(sz, "read_scalecal", return_value=sc), \
                mock.patch.object(sz, "valid_timing",
                                  return_value=(True, None)), \
                mock.patch.object(sz, "print_stamp_view"):
            sz.start_check(a, rows)
            self.assertEqual(list(sz.S["refused"]), [4000])  # 2000 retried
            again = [r for r in rows if r["kind"] == "stop"
                     and r["size"] == 2000] * 2
            sz.start_check(a, rows + again)                # same error twice
            self.assertEqual(sorted(sz.S["refused"]), [2000, 4000])

    def _item(self, size):
        d = os.path.join(self.tmp, "w_%d" % size)
        os.makedirs(d, exist_ok=True)
        return {"unit": "uz", "size": size, "dir": d, "base": {
            "base_uuid": "b", "rss_c": 1 << 20, "wall_s": 1.0, "u_c": 0.5,
            "cons": 70000, "prove_ms": 300}}

    def test_m3_scalecal_crash_reaps_running_proves(self):
        sz.S["cap"] = 16
        sz.S["topo"] = fake_topo(cores=36)
        a = sz.parse_args(["--sizes", "1000", "--server", "t1"])
        p = subprocess.Popen(["sleep", "60"])

        def crash():
            sz.S["running"].append({"pid": p.pid, "p": p, "killed": None})
            raise OSError("disk full")
        with mock.patch.object(sz, "best_scalecal",
                               return_value=(None, False, "no stamp")), \
                mock.patch.object(sz, "in_run_scalecal", side_effect=crash), \
                mock.patch.object(sz, "print_stamp_view"):
            sz.full_start(a, [])
        self.assertEqual(sz.S["running"], [])
        self.assertIsNotNone(p.returncode)              # killed and reaped

    def test_guard_tree_state_sees_changes(self):
        d = os.path.join(self.tmp, "g")
        os.makedirs(d)
        before = _tree_state(d)
        os.makedirs(os.path.join(d, "empty"))           # empty dirs count
        self.assertNotEqual(_tree_state(d), before)


class Review5Test(StubSetup):
    """Review 5 F1/F2 (DLP_T1001)."""

    def _resume(self, rows, cap):
        sz.S["topo"] = fake_topo(cores=36)
        sz.S["cap"] = cap
        a = sz.parse_args(["--sizes", "1000,2000", "--server", "t1"])
        sc = {"w0": "4", "commit": "c"}
        with mock.patch.object(sz, "read_scalecal", return_value=sc), \
                mock.patch.object(sz, "valid_timing",
                                  return_value=(True, None)), \
                mock.patch.object(sz, "print_stamp_view"):
            self.assertIsNone(sz.start_check(a, rows))

    def _err(self, size, msg, etype="OSError"):
        return dict(kind="stop", size=size, cap=16, width=2, cause="error",
                    launch_sig="sig1", etype=etype,
                    reason="exception in flush: %s: %s" % (etype, msg))

    def test_f1_error_lift_beats_serial_at_1kb_and_cap0(self):
        self._resume([self._err(1000, "boom")], 16)
        self.assertEqual(sz.S["serial"], set())       # re-gate, not serial
        self._resume([self._err(2000, "boom")], 0)
        self.assertEqual(sz.S["serial"], set())
        self.assertEqual(sz.S["refused"], {})

    def test_f1_lift_count_by_exception_type_not_message(self):
        rows = [self._err(2000, "tmp 1"), self._err(2000, "tmp 2")]
        self._resume(rows, 16)                        # same type twice
        self.assertIn(2000, sz.S["refused"])
        rows = [self._err(2000, "x", "OSError"),
                self._err(2000, "y", "KeyError")]
        self._resume(rows, 16)                        # new type: retried
        self.assertEqual(sz.S["refused"], {})
        old = dict(self._err(2000, "z"))              # older row, no etype
        del old["etype"]
        self.assertEqual(sz.stop_etype(old), "OSError")

    def test_f1_flush_error_row_carries_etype(self):
        d = os.path.join(self.tmp, "w_e")
        os.makedirs(d)
        sz._ORIG["rmtree"] = shutil.rmtree
        sz.ARGS.sizes = [1000, 2000]
        sz.S["pending"].append({"unit": "ue", "size": 2000, "dir": d,
                                "base": None})
        sz.flush()
        stop = [r for r in sz.S["pair"].load() if r["kind"] == "stop"][-1]
        self.assertEqual((stop["cause"], stop["etype"]), ("error",
                                                           "TypeError"))

    def test_f2_logs_dir_and_dir_mtimes_never_trip(self):
        root = os.path.join(self.tmp, "cache")
        logs = os.path.join(root, "logs")
        os.makedirs(os.path.join(root, "dlp_neo_p0"))
        os.makedirs(logs)
        with mock.patch(__name__ + "._REAL_GUARD_SKIP", logs):
            before = _tree_state(root)
            with open(os.path.join(logs, "job_new.log"), "w") as f:
                f.write("x")                          # a live run's log
            self.assertEqual(_tree_state(root), before)
            open(os.path.join(root, "dlp_neo_p0", "f"), "w").close()
            self.assertNotEqual(_tree_state(root), before)


class SigtermSmoke(unittest.TestCase):
    def test_sigterm_kills_descendants_exit_143(self):
        """Invariant 31: SIGTERM leaves no descendant, exits 143."""
        drv = textwrap.dedent('''\
            import sys, signal, subprocess, time
            sys.path.insert(0, %r)
            import same_zombie as sz
            signal.signal(signal.SIGTERM, sz.on_sigterm)
            p = subprocess.Popen(["sleep", "60"])
            print(p.pid, flush=True)
            try:
                time.sleep(60)
            except SystemExit as e:
                time.sleep(1.5)
                sys.exit(e.code)
            ''' % HERE)
        p = subprocess.Popen([sys.executable, "-I", "-c", drv],
                             stdout=subprocess.PIPE, text=True)
        kid = int(p.stdout.readline())
        p.send_signal(signal.SIGTERM)
        self.assertEqual(p.wait(timeout=10), 143)
        self.assertFalse(os.path.exists("/proc/%d" % kid) and
                         open("/proc/%d/stat" % kid).read().split()[2] != "Z")


# ===========================================================================
# ALL_T1009 tests
# ===========================================================================
def _main_quiet(argv):
    """ALL_T1009: sz.main with init_state kept from Base; restores cwd/SIGTERM."""
    cwd, h = os.getcwd(), signal.getsignal(signal.SIGTERM)
    try:
        with mock.patch.object(sz, "init_state"):
            return sz.main(argv)
    finally:
        os.chdir(cwd)
        signal.signal(signal.SIGTERM, h)


class T1009RedirectTest(unittest.TestCase):
    """ALL_T1009 C1: ZKR_ZOMBIE_TMP_ROOT moves every Zombie /tmp path."""

    PROG = ("import json, sys; sys.path.insert(0, %r); import same_zombie as sz;"
            " rz = sz.rz; print(json.dumps([rz.PARTIAL_DIR, rz.PARTIAL,"
            " rz.BUILD_ROOT, rz.CIRC_BUILD, rz.BUILD_RS, rz.BUILD_RS_ORIG,"
            " rz.ZKMB_DIR, rz.KEYS_DIR, rz.CIRC_BIN, rz.PAR_ROOT%s]))")

    def _paths(self, env, probe=False):
        # ALL_T1009: only the redirected case calls _pick_scratch_base
        prog = self.PROG % (HERE, ", rz._pick_scratch_base()" if probe else "")
        r = subprocess.run([sys.executable, "-I", "-c", prog], env=env,
                           capture_output=True, text=True, timeout=60)
        self.assertEqual(r.returncode, 0, r.stderr)
        return json.loads(r.stdout.strip().splitlines()[-1])

    def test_tmp_root_env_redirects_every_tmp_path(self):
        root = tempfile.mkdtemp(prefix="sz_c1_", dir=os.environ.get("TMPDIR"))
        try:
            env = dict(os.environ, ZKR_ZOMBIE_TMP_ROOT=root)
            for p in self._paths(env, probe=True):
                self.assertTrue(p.startswith(root + "/"), p)
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_tmp_root_unset_keeps_defaults(self):
        env = {k: v for k, v in os.environ.items()
               if k != "ZKR_ZOMBIE_TMP_ROOT"}
        p = self._paths(env)
        self.assertEqual(p[0], "/tmp/bora_zombie_run")
        self.assertEqual(p[2], "/tmp/bora_zombie_circ")
        self.assertEqual(p[9], "/tmp/bora_zombie_par")


class T1009SmallTest(Base):
    """ALL_T1009 A7, A8, A10, git, B4 and the redirect note."""

    def test_tmp_root_note_said(self):
        out = []
        with mock.patch.object(sz, "TMP_ROOT", "/x/root"), \
                mock.patch.object(sz, "check_start_main", return_value=0), \
                mock.patch.object(sz, "say", side_effect=out.append):
            self.assertEqual(_main_quiet(["--sizes", "1000", "--server",
                                          "t1", "--check-start"]), 0)
        self.assertTrue(any("test redirect active, root /x/root" in m
                            for m in out))

    def test_selftest_fails_when_estimate_anchor_moves(self):
        with mock.patch.object(sz, "RZ_PINS",
                               sz.RZ_PINS + ("no_such_anchor_xyz(",)):
            with self.assertRaises(AssertionError) as cm:
                sz.selftest()
        self.assertIn("no_such_anchor_xyz", str(cm.exception))

    def test_rule2_not_rerun_after_run_main_writes(self):
        sweep, sample = sz.pair_names(sz.ARGS)
        sample.append([{"kind": "stop", "size": 2000, "launch_sig": "sig1"}])
        sz.S["rule2_done"] = True
        saved = sz._ORIG.get("load")
        sz._ORIG["load"] = lambda: {}
        out = []
        try:
            with mock.patch.object(sz, "say", side_effect=out.append):
                sz.load_partial_wrapped()
        finally:
            if saved is None:
                sz._ORIG.pop("load", None)
            else:
                sz._ORIG["load"] = saved
        self.assertTrue(sample.present())
        self.assertFalse(any("deleting" in m for m in out))

    def test_full_log_appends_dry_truncates(self):
        for argv, want in ((["--sizes", "1000", "--n", "2", "--server",
                             "t1"], 2),
                           (["--dry", "4", "--sizes", "1000", "--n", "2",
                             "--server", "t1"], 1)):
            sz.ARGS = sz.parse_args(argv)
            path = sz.out_paths()[1]
            for _ in range(2):
                with mock.patch.object(sz, "run_main", return_value=0), \
                        mock.patch.object(sz, "driver_guard",
                                          return_value=None, create=True):
                    _main_quiet(argv)
            self.assertEqual(open(path).read().count("SAME log start"),
                             want, argv)

    def test_check_start_oomd_read_only(self):
        a = sz.parse_args(["--dry", "4", "--sizes", "1000", "--n", "2",
                           "--server", "t1", "--launcher", "prlimit"])
        om = mock.Mock(return_value="refused")
        with mock.patch.object(sz, "oomd_check", om), \
                mock.patch.object(sz, "clone_check", return_value=None):
            self.assertEqual(sz.check_start_main(a), 6)
        om.assert_called_once_with(repair=False)

    def test_git_passes_safe_directory(self):
        seen = []

        def run(cmd, **k):
            seen.append(cmd)
            return mock.Mock(returncode=0, stdout="", stderr="")
        with mock.patch.object(sz.subprocess, "run", run):
            sz.git("status")
        self.assertEqual(seen[0][:5], ["git", "-c", "safe.directory=" +
                                       sz.REPO, "-C", sz.REPO])


def _hold_lock(name, secs=30):
    """ALL_T1009: a child python that binds @name, prints ready, sleeps."""
    p = subprocess.Popen([sys.executable, "-I", "-c",
                          "import socket, time; s = socket.socket(socket."
                          "AF_UNIX, socket.SOCK_DGRAM); s.bind('\\0' + %r); "
                          "print('ready', flush=True); time.sleep(%d)"
                          % (name, secs)], stdout=subprocess.PIPE, text=True)
    assert p.stdout.readline().strip() == "ready"
    return p


class T1009LockTest(Base):
    """ALL_T1009 A1: abstract-socket driver lock and hand-run scan."""

    def setUp(self):
        super().setUp()
        self.name = "sz_t1009_%d_%s" % (os.getpid(), os.path.basename(
            self.tmp))
        for obj, attr, val in ((sz, "DRIVER_LOCK", self.name),
                               (sz, "LOCK_POLL_S", 0.1)):
            p = mock.patch.object(obj, attr, val)
            p.start()
            self.addCleanup(p.stop)
        p = mock.patch.dict(sz._LOCK, {}, clear=True)
        p.start()
        self.addCleanup(self._release)
        self.addCleanup(p.stop)
        self.kids = []

    def _release(self):
        s = sz._LOCK.pop("sock", None)
        if s is not None:
            s.close()
        for k in self.kids:
            k.kill()
            k.wait()

    def _hold(self, secs=30):
        k = _hold_lock(self.name, secs)
        self.kids.append(k)
        return k

    def test_driver_lock_second_holder_refused_nowait(self):
        k = self._hold()
        why = sz.driver_lock(0)
        self.assertIn("@" + self.name, why)
        self.assertIn("pids [%d]" % k.pid, why)   # holder found by inode

    def test_driver_lock_waits_then_gets_it(self):
        self._hold(secs=1)
        t0 = time.time()
        self.assertIsNone(sz.driver_lock(10))
        self.assertGreater(time.time() - t0, 0.3)

    def test_driver_lock_released_on_sigkill(self):
        k = self._hold()
        self.assertIsNotNone(sz.driver_lock(0))
        k.kill()
        k.wait()
        self.assertIsNone(sz.driver_lock(0))

    def test_driver_lock_held_reads_proc_net_unix(self):
        self.assertFalse(sz.driver_lock_held(self.name))
        self.assertIsNone(sz.driver_lock(0))
        self.assertTrue(sz.driver_lock_held(self.name))
        self._release()
        self.assertFalse(sz.driver_lock_held(self.name))

    def test_main_refusal_touches_no_file(self):
        argv = ["--dry", "4", "--sizes", "1000", "--n", "2", "--server", "t1"]
        sz.ARGS = sz.parse_args(argv)
        paths = list(sz.out_paths()) + [sz.pair_names(sz.ARGS)[1].tmp,
                                        sz.pair_names(sz.ARGS)[1].docs]
        for p in paths:
            os.makedirs(os.path.dirname(p), exist_ok=True)
            with open(p, "w") as f:
                f.write("live\n")
        before = [(os.path.getsize(p), os.stat(p).st_mtime_ns) for p in paths]
        self._hold()
        with mock.patch.object(sz, "LOCK_WAIT_RUN_S", 0), \
                mock.patch.object(sz, "run_main") as rm:
            self.assertEqual(_main_quiet(argv), 6)
            rm.assert_not_called()
        self.assertEqual(before, [(os.path.getsize(p),
                                   os.stat(p).st_mtime_ns) for p in paths])

    def test_check_start_refuses_on_held_lock(self):
        self._hold()
        a = sz.parse_args(["--sizes", "1000", "--server", "t1"])
        with mock.patch.object(sz, "launcher_probe") as lp, \
                mock.patch.object(sz, "CHECK_LOCK_WAIT_S", 0):
            self.assertEqual(sz.check_start_main(a), 6)
            lp.assert_not_called()

    def test_selftest_ignores_lock(self):
        self._hold()
        self.assertEqual(sz.main(["--selftest"]), 0)

    def test_scan_argv_rules(self):
        sa = sz._script_of
        self.assertEqual(sa([b"python3", b"-u", b"/x/run_zombie.py"]),
                         b"/x/run_zombie.py")
        self.assertEqual(sa([b"python3", b"-W", b"ignore",
                             b"dry_run_zombie.py", b"4"]),
                         b"dry_run_zombie.py")
        self.assertEqual(sa([b"python3", b"-X", b"dev", b"a.py"]), b"a.py")
        self.assertIsNone(sa([b"python3", b"-c", b"import run_zombie"]))
        self.assertIsNone(sa([b"python3", b"-m", b"unittest"]))
        d = os.path.join(self.tmp, "scan")
        os.makedirs(d)
        kids = []
        # ALL_T1009: names a real driver never scans for
        for nm in ("zz_t1009_drv.py", "zz_t1009_other.py"):
            with open(os.path.join(d, nm), "w") as f:
                f.write("import time; time.sleep(30)\n")
        try:
            kids.append(subprocess.Popen([sys.executable, "-W", "ignore",
                                          os.path.join(d, "zz_t1009_drv.py"),
                                          "4"]))
            kids.append(subprocess.Popen([sys.executable,
                                          os.path.join(d, "zz_t1009_other.py"),
                                          "--check-start"]))
            time.sleep(0.5)
            with mock.patch.object(sz, "SCAN_DRIVERS", ("zz_t1009_drv.py",)):
                got = _REAL_SCAN()
            self.assertIn(kids[0].pid, got)
            self.assertNotIn(kids[1].pid, got)
            self.assertNotIn(os.getpid(), got)
        finally:
            for k in kids:
                k.kill()
                k.wait()


class T1009OrphanTest(Base):
    """ALL_T1009 A3: orphan circ_executable rules."""

    def test_zombie_cwd_component_rule(self):
        zc = sz._zombie_cwd
        with mock.patch.object(rz, "PAR_ROOT", "/r/par"):
            self.assertTrue(zc("/d/bora_zombie_scratch/c00003"))
            self.assertTrue(zc("/tmp/bora_zombie_par/c00000"))
            self.assertTrue(zc("/tmp/bora_zombie_par/c1 (deleted)"))
            self.assertTrue(zc("/r/par/c2"))
            self.assertFalse(zc("/x/bora_zombie_par_t/c0"))
            self.assertFalse(zc("/r/parx/c0"))
            self.assertFalse(zc("/home/u/elsewhere"))

    def test_live_python_ancestor_rules(self):
        tree = {10: ("S", 9), 9: ("S", 1), 20: ("S", 19), 19: ("Z", 1),
                30: ("S", 29), 29: ("S", 1)}
        exe = {9: "python3.12", 19: "python3", 29: "time"}
        with mock.patch.object(sz, "_stat_of", tree.get), \
                mock.patch.object(sz, "_exe_base",
                                  lambda p: exe.get(p, "x")):
            self.assertTrue(sz._live_python_ancestor(10))
            self.assertFalse(sz._live_python_ancestor(20))
            self.assertFalse(sz._live_python_ancestor(30))

    def test_orphan_rules_fake_proc(self):
        cwd = {101: "/d/bora_zombie_scratch/c00003",
               102: "/tmp/bora_zombie_par/c00000",
               103: "/x/bora_zombie_par_t/c0", 104: "/home/u/elsewhere",
               105: "/tmp/bora_zombie_par/c1 (deleted)", 106: "/tmp/x"}
        live = {102}
        killed = []
        with mock.patch.object(sz, "_owned", return_value=True), \
                mock.patch.object(sz, "_exe_base",
                                  lambda p: "circ_executable" if p != 106
                                  else "sleep"), \
                mock.patch.object(sz, "_cwd_of", cwd.get), \
                mock.patch.object(sz, "_live_python_ancestor",
                                  lambda p: p in live), \
                mock.patch.object(sz, "_sigkill", killed.append), \
                mock.patch.object(rz, "PAR_ROOT", "/r/par"):
            got = _REAL_ORPHAN(kill=False, pids=sorted(cwd))
            self.assertEqual([p for p, _ in got], [101, 105])
            self.assertEqual(killed, [])
            _REAL_ORPHAN(kill=True, pids=sorted(cwd))
            self.assertEqual(killed, [101, 105])

    def test_orphan_kill_real_own_child_only(self):
        d = os.path.join(self.tmp, "zz_t1009_par", "c0")  # ALL_T1009: no real
        os.makedirs(d)
        shutil.copy("/bin/sleep", os.path.join(d, "circ_executable"))
        r = subprocess.run(["sh", "-c", "cd %s && ./circ_executable 30 "
                            ">/dev/null 2>&1 </dev/null & echo $!" % d],
                           capture_output=True, text=True, timeout=10)
        pid = int(r.stdout.strip())
        try:
            time.sleep(0.3)
            with mock.patch.object(sz, "ZOMBIE_DIRS", ("zz_t1009_par",)):
                got = _REAL_ORPHAN(kill=True, pids={pid})
            self.assertEqual([p for p, _ in got], [pid])
            for _ in range(50):
                st = sz._stat_of(pid)
                if st is None or st[0] == "Z":
                    break
                time.sleep(0.1)
            st = sz._stat_of(pid)
            self.assertTrue(st is None or st[0] == "Z")
        finally:
            try:
                os.kill(pid, signal.SIGKILL)
            except OSError:
                pass

    def test_check_start_lists_orphans_with_kill_command(self):
        # ALL_T1013 F4: refuses only when an orphan survives the kill
        out = []
        a = sz.parse_args(["--sizes", "1000", "--server", "t1"])
        with mock.patch.object(sz, "orphan_circ",
                               return_value=[(77, "/x/bora_zombie_par/c1")]), \
                mock.patch.object(sz, "_alive", return_value=True), \
                mock.patch.object(sz, "say", side_effect=out.append):
            self.assertEqual(sz.check_start_main(a), 6)
        self.assertTrue(any("kill -9 77" in m and "cwd /x/bora_zombie_par/c1"
                            in m for m in out))


class T1009ParentTest(Base):
    """ALL_T1009 A4: parent-death signal."""

    def test_bind_parent_noop_without_env(self):
        with mock.patch.dict(os.environ, {}, clear=False), \
                mock.patch("ctypes.CDLL") as cd:
            os.environ.pop("ZKR_SAME_PARENT", None)
            sz.bind_parent()
            cd.assert_not_called()

    def test_bind_parent_exits_when_parent_gone(self):
        lib = mock.Mock()
        lib.prctl.return_value = 0
        with mock.patch.dict(os.environ, {"ZKR_SAME_PARENT": str(
                os.getppid() + 100000)}), \
                mock.patch("ctypes.CDLL", return_value=lib):
            with self.assertRaises(SystemExit) as cm:
                sz.bind_parent()
            self.assertNotIn("ZKR_SAME_PARENT", os.environ)
        self.assertEqual(cm.exception.code, 143)
        self.assertEqual(lib.prctl.call_args[0][:2], (1, signal.SIGTERM))

    def test_bind_parent_notes_prctl_failure(self):
        lib = mock.Mock()
        lib.prctl.return_value = -1
        out = []
        with mock.patch.dict(os.environ, {"ZKR_SAME_PARENT": str(
                os.getppid())}), \
                mock.patch("ctypes.CDLL", return_value=lib), \
                mock.patch.object(sz, "say", side_effect=out.append):
            sz.bind_parent()
        self.assertTrue(any("PR_SET_PDEATHSIG failed" in m for m in out))

    def test_bind_parent_pops_env(self):
        lib = mock.Mock()
        lib.prctl.return_value = 0
        with mock.patch.dict(os.environ, {"ZKR_SAME_PARENT": str(
                os.getppid())}), mock.patch("ctypes.CDLL", return_value=lib):
            sz.bind_parent()
            self.assertNotIn("ZKR_SAME_PARENT", os.environ)

    def test_pdeathsig_real_sigkill(self):
        mark = os.path.join(self.tmp, "term")
        child = textwrap.dedent("""\
            import os, sys, signal, time
            sys.path.insert(0, %r)
            import same_zombie as sz
            def h(*a):
                open(%r, "w").write("term")
                os._exit(0)
            signal.signal(signal.SIGTERM, h)
            os.environ["ZKR_SAME_PARENT"] = str(os.getppid())
            sz.bind_parent()
            print("ready", flush=True)
            time.sleep(30)
            """ % (HERE, mark))
        parent = ("import subprocess, sys, time; p = subprocess.Popen("
                  "[sys.executable, '-I', '-c', %r]); time.sleep(30)" % child)
        pp = subprocess.Popen([sys.executable, "-I", "-c", parent])
        try:
            for _ in range(100):
                kids = [int(x) for x in open("/proc/%d/task/%d/children"
                                             % (pp.pid, pp.pid)).read().split()]
                if kids:
                    break
                time.sleep(0.1)
            time.sleep(1.0)                    # child reached bind_parent
            pp.kill()
            pp.wait()
            for _ in range(50):
                if os.path.exists(mark):
                    break
                time.sleep(0.1)
            self.assertTrue(os.path.exists(mark))
        finally:
            for k in kids if "kids" in dir() else []:
                try:
                    os.kill(k, signal.SIGKILL)
                except OSError:
                    pass


class T1009ProbeTest(Base):
    """ALL_T1009 A9: the probe restores bora-same.slice."""

    def _run(self, fake):
        calls = []
        with mock.patch.object(sz, "_launcher_probe", fake), \
                mock.patch.object(sz, "sctl",
                                  side_effect=lambda *a, **k: calls.append(a)):
            try:
                sz.launcher_probe()
            except RuntimeError:
                pass
        return calls

    def test_probe_restores_slice_on_every_exit(self):
        def ret(st):
            st["slice"] = True
            return ("prlimit", [], "probe B")

        def boom(st):
            st["slice"] = True
            raise RuntimeError("x")

        def early(st):
            return ("prlimit", [], "linger off")
        want = ("set-property", "--runtime", "bora-same.slice",
                "MemoryMax=infinity")
        self.assertEqual(self._run(ret)[-1], want)
        self.assertEqual(self._run(boom)[-1], want)
        self.assertEqual(self._run(early), [])
        import inspect
        src = inspect.getsource(sz._launcher_probe)
        self.assertLess(src.index('st["slice"] = True'),
                        src.index("MemoryMax=1073741824"))
        self.assertLess(src.index("MemoryMax=1073741824"),
                        src.index("MemoryMax=2G"))

    def test_kill_quiet_closes_stderr(self):
        p = mock.Mock()
        sz._kill_quiet(p)
        p.stderr.close.assert_called_once()



class T1009HourZeroTest(Base):
    """ALL_T1009 A6: hour-0 checks in --check-start."""

    def _sweep(self, lines, copy="tmp", hold=False):
        p = getattr(sz.pair_names(sz.ARGS)[0], copy) + (".hold" if hold
                                                        else "")
        os.makedirs(os.path.dirname(p), exist_ok=True)
        with open(p, "w") as f:
            f.write("".join(lines))
        return p

    @staticmethod
    def _row(**kw):
        r = {"regex_name": "u", "str_len": 1000, "zok_gen": rz.ZOK_GEN}
        r.update(kw)
        return json.dumps(r) + "\n"

    def _cs(self, argv=("--sizes", "1000", "--server", "t1"), **patches):
        a = sz.parse_args(list(argv))
        sz.ARGS = a
        ps = [mock.patch.object(sz, "oomd_check", return_value=None),
              mock.patch.object(sz, "same_units_running", return_value=False),
              mock.patch.object(sz, "launcher_probe",
                                return_value=("prlimit", [], "x"))]
        ps += [mock.patch.object(sz, k, **v) for k, v in patches.items()]
        out = []
        ps.append(mock.patch.object(sz, "say", side_effect=out.append))
        for p in ps:
            p.start()
        try:
            return sz.check_start_main(a), "\n".join(out)
        finally:
            for p in ps:
                p.stop()

    def test_check_start_refuses_old_zok_gen_sweep(self):
        self._sweep([self._row(), self._row(zok_gen="fix11")])
        rc, out = self._cs()
        self.assertEqual(rc, 6)
        self.assertIn("cannot resume", out)

    def test_check_start_refuses_bad_middle_line_sweep(self):
        self._sweep([self._row(), "{bad\n", self._row()])
        self.assertIn("bad line", sz.sweep_refusal(sz.ARGS))

    def test_check_start_torn_last_sweep_line_passes(self):
        self._sweep([self._row(), '{"regex_name": "u", "str'])
        with mock.patch.object(sz, "say"):
            self.assertIsNone(sz.sweep_refusal(sz.ARGS))
        rc, out = self._cs()
        self.assertNotIn("sweep partial", out)

    def test_check_start_reads_parked_hold_sweep(self):
        self._sweep([self._row()])
        self._sweep([self._row(), "{bad\n", self._row()], hold=True)
        self.assertIn(".hold", sz.sweep_refusal(sz.ARGS))

    def test_check_start_reads_docs_copy_too(self):
        self._sweep([self._row()])
        self._sweep([self._row(zok_gen="old")], copy="docs")
        self.assertIn("cannot resume", sz.sweep_refusal(sz.ARGS))

    def test_check_start_refuses_fx_mismatch(self):
        rc, out = self._cs(fx_check={"return_value": "FX e-mail x differs"})
        self.assertEqual(rc, 6)
        self.assertIn("FX e-mail x differs", out)

    def test_check_start_git_status_failure_refuses_when_needed(self):
        rc, out = self._cs(("--sizes", "1000,2000", "--server", "t1",
                            "--scalecal-min-cores", "1"),
                           git_status={"return_value": None})
        self.assertEqual(rc, 6)
        self.assertIn("REFUSE: git status failed", out)

    def test_check_start_git_status_failure_warns_1kb_only(self):
        rc, out = self._cs(("--sizes", "1000", "--server", "t1",
                            "--scalecal-min-cores", "1"),
                           git_status={"return_value": None})
        self.assertIn("WARNING: git status failed", out)
        self.assertNotIn("REFUSE: git", out)

    def test_check_start_refuses_without_nightly(self):
        import download_zombie
        with mock.patch.object(download_zombie, "have_rust_nightly",
                               return_value=(False, "toolchain missing")):
            rc, out = self._cs(circ_rebuild_needed={"return_value": True})
            self.assertEqual(rc, 6)
            self.assertIn("Rust nightly", out)
            rc, out = self._cs(circ_rebuild_needed={"return_value": False})
            self.assertNotIn("REFUSE", out)   # ALL_T1009: no rebuild, warn
            self.assertIn("needs no rebuild", out)

    def test_zero_slot_cores_refused(self):
        sz.S["topo"] = {"nodes": {0: []}, "tpc": 1, "c_cores": 0}
        rc, out = self._cs()
        self.assertEqual(rc, 6)
        self.assertIn("no slot cores", out)

    def test_zero_slot_cores_cap0_passes(self):
        sz.S["topo"] = {"nodes": {0: []}, "tpc": 1, "c_cores": 0}
        sz.S["cap"] = 0
        self.assertIsNone(sz.cores_refusal())

    def test_check_start_refuses_on_selftest_assert(self):
        rc, out = self._cs(selftest={"side_effect": AssertionError("moved")})
        self.assertEqual(rc, 6)
        self.assertIn("selftest failed: moved", out)

    def test_scratch_view_refuse_warn_pass(self):
        full = sz.parse_args(["--sizes", "1000", "--server", "t1"])
        dry = sz.parse_args(["--dry", "4", "--sizes", "1000", "--server",
                             "t1"])
        out = []
        with mock.patch.object(sz, "jobs_fit", return_value=(8, 8, 10 ** 6)), \
                mock.patch.object(sz, "say", side_effect=out.append):
            for free, a, want_ref, want_warn in ((50, full, True, False),
                                                 (200, full, False, True),
                                                 (300, full, False, False),
                                                 (200, dry, False, False),
                                                 (50, dry, False, True)):
                del out[:]
                with mock.patch.object(sz, "scratch_free_gib",
                                       return_value=(free, "/b")):
                    txt, why = sz.host_views(a)
                self.assertEqual(bool(why), want_ref, (free, a.dry))
                self.assertEqual(any("scratch drive" in m for m in out),
                                 want_warn, (free, a.dry))
                self.assertIn("scratch=%dGiB(/b,mount)" % free, txt)

    def test_pids_limit_fake_cgroup_tree(self):
        fs = {"/proc/self/cgroup": "0::/a/b",
              "/sys/fs/cgroup/a/b/pids.max": "max",
              "/sys/fs/cgroup/a/b/pids.current": "5",
              "/sys/fs/cgroup/a/pids.max": "5000",
              "/sys/fs/cgroup/a/pids.current": "1000"}
        rd = lambda p, d="": fs.get(p, d)
        with mock.patch.object(sz, "_read", rd), \
                mock.patch.object(sz, "nproc_avail", return_value=None), \
                mock.patch.object(sz.os, "sched_getaffinity",
                                  return_value=set(range(128))):
            self.assertEqual(sz.pids_avail(), 4000)
            self.assertEqual(sz.jobs_fit(), (15, 64, 4000))
            fs["/sys/fs/cgroup/a/pids.max"] = "1100"
            self.assertEqual(sz.jobs_fit()[0], 0)
            with mock.patch.object(sz, "scratch_free_gib",
                                   return_value=(900, "/b")):
                self.assertIn("too few", sz.host_views(sz.ARGS)[1])
            for k in list(fs):
                if k.endswith("pids.max"):
                    fs[k] = "max"
            self.assertEqual(sz.jobs_fit(), (64, 64, None))

    def test_run_main_sets_jobs_cap(self):
        class Stop(Exception):
            pass
        with mock.patch.object(sz, "jobs_fit", return_value=(5, 8, 99)), \
                mock.patch.object(sz, "install_rz_hooks", side_effect=Stop), \
                mock.patch.object(sz, "say"):
            with self.assertRaises(Stop):
                sz.run_main(sz.ARGS)
        self.assertEqual(sz.S["jobs_cap"], 5)



_RZ_HOOKED = ("shutil", "_time_one", "_load_partial", "_append_partial",
              "_render_zkmb", "run_pipeline", "_as_cap", "_build_one",
              "ThreadPoolExecutor", "_estimate", "_median_at",
              "_cpu_max_jobs", "MIN_CPUS_PER_CIRC", "_run_keygen")


class HookBase(Base):
    """ALL_T1009: save and restore every rz attribute install_rz_hooks sets."""

    def setUp(self):
        super().setUp()
        self.rz_saved = {k: getattr(rz, k) for k in _RZ_HOOKED}
        self.orig_saved = dict(sz._ORIG)
        self.addCleanup(self._restore)
        for k in _RZ_HOOKED:                  # start from RZ's own functions
            setattr(rz, k, _RZ_PRISTINE[k])
        sz._ORIG.clear()

    def _restore(self):
        for k, v in self.rz_saved.items():
            setattr(rz, k, v)
        sz._ORIG.clear()
        sz._ORIG.update(self.orig_saved)


class T1009BuildLogTest(HookBase):
    """ALL_T1009 B1, N1, N2, O2, m4."""

    def setUp(self):
        super().setUp()
        self.out = []
        p = mock.patch.object(sz, "say", side_effect=self.out.append)
        p.start()
        self.addCleanup(p.stop)
        self.seen = []
        self.res = []

        def stub(binp, idx, name, str_len, mem=None, timeout=0):
            self.seen.append(mem)
            return self.res.pop(0)
        sz._ORIG["build"] = stub
        sz._ORIG["as_cap"] = _RZ_PRISTINE["_as_cap"]

    def test_rz_print_stamped_and_pd_regexes_match(self):
        sz._rz_print("[run_zombie] docs/x.log : 24 results, 24 ok across x")
        sz._rz_print("\n=== run_zombie r (sizes [1000]) ===")
        self.assertRegex(self.out[0], r"^\[\d\d-\d\d \d\d:\d\d:\d\d\] \[run_z")
        first, second = self.out[1].split("\n")
        self.assertEqual(first, "")
        self.assertRegex(second, r"^\[\d\d-\d\d \d\d:\d\d:\d\d\] ===")
        pd = open(os.path.join(sz.REPO, "scripts", "PAPER_DATA.py")).read()
        import re
        pat = re.search(r'ZOMBIE_OK_RE = re\.compile\(r"([^"]*)"\)', pd).group(1)
        m = re.search(pat, self.out[0])
        self.assertEqual(m.groups(), ("24", "24"))

    def test_build_wrapper_logs_each_attempt(self):
        cap = int(15 * sz.GIB + sz.arena_room())
        self.res = [{"status": "built", "peak_rss": 2 * sz.GIB, "as_cap": cap},
                    {"status": "oom_or_killed", "peak_rss": 3 * sz.GIB,
                     "as_cap": cap, "err": "killed"},
                    {"status": "built", "as_cap": 1}]
        for mem in (cap, cap, int(8 * sz.GIB + sz.arena_room())):
            sz.build_one_wrapped("b", 0, "u", 2000, mem)
        lines = [m for m in self.out if m.startswith("SAME build")]
        self.assertEqual(len(lines), 3)
        self.assertIn("-> built", lines[0])
        self.assertIn("rss=2.0GiB res=10.0GiB", lines[0])
        self.assertIn("res=<=5.3GiB", lines[2])
        self.assertIn("-> oom_or_killed", lines[1])
        self.assertIn("err=killed", lines[1])

    def test_build_wrapper_none_fields_and_say_failure(self):
        d = {"name": "u", "prox": 1, "dir": None, "status": "codegen_fail"}
        self.res = [d, dict(d)]
        self.assertIs(sz.build_one_wrapped("b", 0, "u", 1000, None), d)
        self.assertIn("rss=- res=- cap=-", self.out[-1])
        with mock.patch.object(sz, "say", side_effect=RuntimeError("io")):
            r = sz.build_one_wrapped("b", 0, "u", 1000, None)
        self.assertEqual(r["status"], "codegen_fail")

    def test_batch_line_once_per_batch(self):
        sz.S["cur_size"] = 4000
        with sz.BatchTPE(max_workers=3):
            self.assertEqual(sz.S["batch_n"], 3)
        lines = [m for m in self.out if m.startswith("SAME batch")]
        self.assertEqual(len(lines), 1)
        self.assertIn("size=4000 jobs=3", lines[0])

    def test_batch_n_cleared_on_exit(self):
        with sz.BatchTPE(2):
            self.assertEqual(sz.S["batch_n"], 2)
        self.assertNotIn("batch_n", sz.S)

    def _fail(self, mem, rss, err="ThreadPoolBuildError { kind: IOError(Os "
              "{ code: 11, message: \"Resource temporarily unavailable\" }) "
              "}', /r/rayon-core-1.9.3/src/registry.rs:170:10"):
        return {"status": "build_fail", "peak_rss": rss, "as_cap": mem,
                "err": "panicked: " + err}

    def test_build_wrapper_strips_arena_from_as_cap(self):
        mem = 20 * sz.GIB
        self.res = [self._fail(mem, 30 * sz.GIB, err="plain")]
        b = sz.build_one_wrapped("b", 0, "u", 1000, mem)
        self.assertEqual(b["as_cap"], mem - sz.arena_room())

    def test_arena_learn_on_thread_pool_error(self):
        mem = 20 * sz.GIB
        sz.S["batch_seq"] = 1
        self.res = [self._fail(mem, sz.GIB), self._fail(mem, sz.GIB)]
        sz.build_one_wrapped("b", 0, "u", 1000, mem)
        self.assertEqual(sz.S["arena_b"], 132 * 2 ** 20)
        sz.build_one_wrapped("b", 0, "u", 1000, mem)   # same batch: once
        self.assertEqual(sz.S["arena_b"], 132 * 2 ** 20)
        self.assertTrue(any("arena room raised to 132 MiB" in m
                            for m in self.out))

    def test_arena_not_raised_on_rss_overrun(self):
        mem = 20 * sz.GIB
        self.res = [self._fail(mem, 19 * sz.GIB,
                               err="memory allocation of 9 bytes failed")]
        sz.build_one_wrapped("b", 0, "u", 1000, mem)
        self.assertNotIn("arena_b", sz.S)

    def test_arena_raise_capped_at_264_mib(self):
        mem = 60 * sz.GIB
        for seq in range(1, 6):
            sz.S["batch_seq"] = seq
            self.res = [self._fail(mem, sz.GIB)]
            sz.build_one_wrapped("b", 0, "u", 1000, mem)
        self.assertEqual(sz.S["arena_b"], 264 * 2 ** 20)

    def test_as_cap_arena_room(self):
        g = sz.GIB
        with mock.patch.object(sz.os, "sched_getaffinity",
                               return_value=set(range(128))):
            self.assertEqual(sz.as_cap_wrapped(2 * g, 865 * g),
                             8 * g + 128 * 66 * 2 ** 20)
            self.assertEqual(sz.as_cap_wrapped(100 * g, 865 * g),
                             150 * g + 128 * 66 * 2 ** 20)
            self.assertEqual(sz.as_cap_wrapped(800 * g, 865 * g), 865 * g)
            self.assertIsNone(sz.as_cap_wrapped(2 * g, None))

    def test_lone_batch_gets_full_mem(self):
        sz.S["full_mem"] = 100 * sz.GIB
        self.res = [{"status": "built", "as_cap": 1}]
        with sz.BatchTPE(max_workers=1):
            sz.build_one_wrapped("b", 0, "u", 4000, 5 * sz.GIB)
        self.assertEqual(self.seen, [100 * sz.GIB])
        self.assertIn(" lone", [m for m in self.out
                                if m.startswith("SAME build")][0])

    def test_multi_batch_keeps_rz_cap(self):
        sz.S["full_mem"] = 100 * sz.GIB
        self.res = [{"status": "built", "as_cap": 1}]
        with sz.BatchTPE(max_workers=2):
            sz.build_one_wrapped("b", 0, "u", 4000, 5 * sz.GIB)
        self.assertEqual(self.seen, [5 * sz.GIB])

    def test_sz_bus_executor_unaffected(self):
        sz.install_rz_hooks()
        self.assertIs(rz.ThreadPoolExecutor, sz.BatchTPE)
        self.assertIsNot(sz.ThreadPoolExecutor, sz.BatchTPE)
        del self.out[:]
        with sz.ThreadPoolExecutor(max_workers=1):
            pass
        self.assertFalse(any(m.startswith("SAME batch") for m in self.out))

    def test_executor_subclass_install_twice_single_line(self):
        sz.install_rz_hooks()
        sz.install_rz_hooks()
        self.assertIs(rz.ThreadPoolExecutor, sz.BatchTPE)
        del self.out[:]
        with rz.ThreadPoolExecutor(max_workers=2):
            pass
        self.assertEqual(len([m for m in self.out
                              if m.startswith("SAME batch")]), 1)

    def test_install_rz_hooks_twice_no_recursion(self):
        sz.install_rz_hooks()
        sz.install_rz_hooks()
        self.assertIs(sz._ORIG["as_cap"], _RZ_PRISTINE["_as_cap"])
        self.assertIs(sz._ORIG["estimate"], _RZ_PRISTINE["_estimate"])
        self.assertGreater(rz._as_cap(2 * sz.GIB, 100 * sz.GIB), 8 * sz.GIB)
        self.assertEqual(rz._estimate("u", 2000, {}, 1, "peak_rss", 7),
                         max(7, sz.rz_cold()))

    def test_selftest_pins_after_hooks_installed(self):
        sz.install_rz_hooks()
        self.assertEqual(sz.selftest(), 0)


@unittest.skipUnless(os.environ.get("ZKR_T1009_REAL_BIN"),
                     "set ZKR_T1009_REAL_BIN to a circ_executable (real run)")
class T1009ArenaRealTest(Base):
    """ALL_T1009 N1, real: 128 rayon threads need the arena room."""

    def test_as_cap_arena_real(self):
        binp = os.environ["ZKR_T1009_REAL_BIN"]
        rs = rz.RULESETS[0]
        rz.FULL_DIR = os.path.join(sz.MS_DLP, rs)
        name = os.environ.get("ZKR_T1009_UNIT",
                              "sit-defn-japan-my-number-corporate")
        cwd = os.getcwd()
        os.chdir(sz.MS_DLP)
        try:
            zok, prox, cg = rz._codegen_zok(name, 1000)
        finally:
            os.chdir(cwd)
        self.assertEqual(cg, "ok")
        res = {}
        env = dict(os.environ, RAYON_NUM_THREADS="128")
        g = sz.GIB
        with mock.patch.object(sz.os, "sched_getaffinity",
                               return_value=set(range(128))), \
                mock.patch.dict(sz._ORIG, {"as_cap": _RZ_PRISTINE["_as_cap"]}):
            hooked = sz.as_cap_wrapped(0.4 * g, 865 * g)
        for tag, cap in (("6g", 6 * g), ("hooked", hooked)):
            d = os.path.join(self.tmp, "c_" + tag)
            os.makedirs(os.path.join(d, "zkmb"))
            os.makedirs(os.path.join(d, "keys"))
            with open(os.path.join(d, "zkmb", "policy1000.zok"), "w") as f:
                f.write(zok)
            os.symlink(os.path.join(os.path.dirname(os.path.dirname(
                os.path.dirname(binp))), "third_party", "ZoKrates"),
                os.path.join(d, "ZoKrates"))
            cmd = ["prlimit", "--as=%d" % cap, binp, "policy_1000", "true",
                   "prover"]
            r = subprocess.run(cmd, cwd=d, env=env, capture_output=True,
                               text=True, timeout=600)
            res[tag] = (r.returncode, r.stderr[-300:])   # what RZ keeps
            print("ALL_T1009 arena real: cap %.2f GiB rc %d" % (
                cap / g, r.returncode), flush=True)
        self.assertNotEqual(res["6g"][0], 0)
        self.assertTrue(sz.arena_failure(res["6g"][1]), res["6g"][1])
        self.assertEqual(res["hooked"][0], 0, res["hooked"][1])



def _rec(name, size, rss, status="ok", vkey="peak_rss"):
    return {"%s|%d" % (name, size): {"regex_name": name, "str_len": size,
                                     "status": status, vkey: rss}}


class T1009EstimateTest(HookBase):
    """ALL_T1009 B2, N3, B3."""

    def setUp(self):
        super().setUp()
        sz._ORIG["estimate"] = _RZ_PRISTINE["_estimate"]
        sz._ORIG["median_at"] = _RZ_PRISTINE["_median_at"]
        self.g = sz.GIB

    def est(self, name, size, done, vkey="peak_rss"):
        return sz.estimate_wrapped(name, size, done, 1, vkey, 7)

    def rz_est(self, name, size, done, vkey="peak_rss"):
        return _RZ_PRISTINE["_estimate"](name, size, done, 1, vkey, 7)

    def _pairs(self, ratios, a=1000, b=2000, vkey="peak_rss"):
        done = {}
        for i, q in enumerate(ratios):
            done.update(_rec("p%d" % i, a, 2 * self.g, vkey=vkey))
            done.update(_rec("p%d" % i, b, int(q * 2 * self.g), vkey=vkey))
        return done

    def test_estimate_first_doubling_default(self):
        done = _rec("u", 1000, 2 * self.g)
        self.assertAlmostEqual(self.est("u", 2000, done) / self.g, 10.0, 6)
        self.assertGreater(self.est("u", 2000, done),
                           self.rz_est("u", 2000, done))

    def test_estimate_uses_measured_median(self):
        done = self._pairs([4, 4, 4])
        done.update(_rec("u", 1000, 3 * self.g))
        self.assertEqual(self.est("u", 2000, done), 12 * self.g)

    def test_estimate_4kb_uses_1to2_ratio_before_any_4kb(self):
        done = self._pairs([4, 4, 4])
        done.update(_rec("t", 2000, 5 * self.g))
        self.assertEqual(self.est("t", 4000, done), 20 * self.g)

    def test_estimate_never_below_rz(self):
        done = _rec("u", 1000, 2 * self.g)
        done.update(_rec("u", 2000, 3 * self.g))
        self.assertEqual(self.est("u", 4000, done),
                         self.rz_est("u", 4000, done))

    def test_estimate_same_size_unchanged_cold_is_rz_own(self):
        done = _rec("u", 2000, 9 * self.g)
        self.assertEqual(self.est("u", 2000, done), 9 * self.g)
        self.assertEqual(self.est("v", 1000, done), max(7, sz.rz_cold()))

    def test_estimate_key_bytes_linear_until_3_pairs(self):
        done = self._pairs([4, 4], vkey="key_bytes")
        done.update(_rec("u", 1000, self.g, vkey="key_bytes"))
        self.assertEqual(self.est("u", 2000, done, "key_bytes"), 2 * self.g)
        done.update(self._pairs([4, 4, 4], vkey="key_bytes"))
        sz.S.pop("k_memo", None)
        self.assertEqual(self.est("u", 2000, done, "key_bytes"), 4 * self.g)

    def test_estimate_own_ratio_wins(self):
        done = self._pairs([3.4, 3.5])
        done.update(_rec("r", 1000, 2 * self.g))
        done.update(_rec("r", 2000, int(4.6 * 2 * self.g)))
        got = self.est("r", 4000, done)
        self.assertAlmostEqual(got / (4.6 * 2 * self.g), 4.6, places=3)

    def test_estimate_pooled_uses_p75(self):
        done = self._pairs([3.0, 3.2, 4.0, 5.0])
        done.update(_rec("u", 1000, self.g))
        self.assertAlmostEqual(self.est("u", 2000, done) / self.g, 4.0,
                               places=3)

    def test_estimate_own_ratio_clamped(self):
        done = _rec("r", 1000, self.g)
        done.update(_rec("r", 2000, 20 * self.g))
        self.assertEqual(self.est("r", 4000, done), 160 * self.g)

    def test_estimate_memo_keyed_on_done_id(self):
        d1, d2 = self._pairs([4, 4, 4]), self._pairs([3, 3, 3])
        d1.update(_rec("u", 1000, self.g))
        d2.update(_rec("u", 1000, self.g))
        self.assertNotEqual(self.est("u", 2000, d1), self.est("u", 2000, d2))

    def test_median_at_peak_rss_p90(self):
        done = {}
        for i in range(1, 11):
            done.update(_rec("u%d" % i, 1000, i))
        self.assertEqual(sz.median_at_wrapped(done, 1000, "peak_rss"), 9)

    def test_median_at_one_and_two_values(self):
        self.assertEqual(sz.median_at_wrapped(_rec("a", 1000, 5), 1000,
                                              "peak_rss"), 5)
        done = _rec("a", 1000, 3)
        done.update(_rec("b", 1000, 7))
        self.assertEqual(sz.median_at_wrapped(done, 1000, "peak_rss"), 7)
        self.assertIsNone(sz.median_at_wrapped({}, 1000, "peak_rss"))

    def test_median_at_key_bytes_unchanged(self):
        done = self._pairs([3, 4, 5], vkey="key_bytes")
        self.assertEqual(sz.median_at_wrapped(done, 2000, "key_bytes"),
                         _RZ_PRISTINE["_median_at"](done, 2000, "key_bytes"))

    def test_cpu_max_jobs_affinity_min2(self):
        sz.install_rz_hooks()
        self.assertIs(rz._cpu_max_jobs, sz.cpu_max_jobs)
        for n, want in ((16, 8), (128, 64), (1, 1)):
            with mock.patch.object(sz.os, "sched_getaffinity",
                                   return_value=set(range(n))):
                self.assertEqual(rz._cpu_max_jobs(), want)

    def test_cpu_max_jobs_honors_jobs_cap(self):
        sz.install_rz_hooks()
        sz.S["jobs_cap"] = 5
        with mock.patch.object(sz.os, "sched_getaffinity",
                               return_value=set(range(128))):
            self.assertEqual(rz._cpu_max_jobs(), 5)

    def test_cpu_max_jobs_harness_override_kept(self):
        rz._cpu_max_jobs = lambda: 3
        sz.install_rz_hooks()
        self.assertEqual(rz._cpu_max_jobs(), 3)


class T1009PipelineGrowthTest(HookBase):
    """ALL_T1009 B2+N1 through rz.run_pipeline: no resource retry."""

    def _run(self, hooked):
        stub = os.path.join(self.tmp, "circ_stub")
        with open(stub, "w") as f:
            f.write(STUB)
        os.chmod(stub, 0o755)
        full = os.path.join(self.tmp, "rules")
        os.makedirs(full, exist_ok=True)
        names = ["u1", "u2", "u3"]
        for u in names:
            open(os.path.join(full, u + ".regex"), "w").write(
                "(a.{0,10}(b))|((b).{0,10}a)")
        g = sz.GIB
        calls = []

        def build(binp, idx, name, str_len, mem=None, timeout=0):
            calls.append(name)
            true_rss = int(4.5 * 6 * g)
            d = os.path.join(rz.PAR_ROOT, "c%05d" % idx)
            os.makedirs(d, exist_ok=True)
            if mem and true_rss > mem - sz.arena_room():
                return {"name": name, "prox": 10, "dir": d, "status":
                        "oom_or_killed", "peak_rss": mem, "as_cap": mem}
            return {"name": name, "prox": 10, "dir": d, "status": "built",
                    "peak_rss": true_rss, "key_bytes": 1, "as_cap": mem}
        done = {}
        for u in names:
            done.update(_rec(u, 1000, 6 * g))
        rz.FULL_DIR, rz.PAR_ROOT = full, os.path.join(self.tmp, "par")
        rz.PARTIAL = os.path.join(self.tmp, "rz.jsonl")
        rz.PARTIAL_DOCS = os.path.join(self.tmp, "rzd.jsonl")
        rz._build_one = build
        sz.S["binp"] = stub
        sz.S["bus"] = None
        sz.install_rz_hooks()
        if not hooked:
            rz._estimate = _RZ_PRISTINE["_estimate"]
        saved = {k: getattr(rz, k) for k in ("FULL_DIR", "PAR_ROOT",
                                             "PARTIAL", "PARTIAL_DOCS")}
        try:
            with mock.patch.object(sz, "say"):
                res = rz.run_pipeline(stub, 2000, names, done)
        finally:
            for k, v in saved.items():
                setattr(rz, k, v)
        return calls, res

    def test_pipeline_growth_no_resource_retry(self):
        calls, res = self._run(True)
        self.assertEqual(sorted(calls), ["u1", "u2", "u3"])
        self.assertEqual([r["status"] for r in res], ["ok"] * 3)
        calls, res = self._run(False)
        self.assertEqual(len(calls), 6)          # RZ's linear estimate retries
        self.assertEqual([r["status"] for r in res], ["ok"] * 3)



class T1009FixRoundTest(HookBase):
    """ALL_T1009 fix round 1 (code reviews A and B)."""

    def setUp(self):
        super().setUp()
        self.out = []
        p = mock.patch.object(sz, "say", side_effect=self.out.append)
        p.start()
        self.addCleanup(p.stop)
        sz._ORIG["as_cap"] = _RZ_PRISTINE["_as_cap"]
        sz._ORIG["estimate"] = _RZ_PRISTINE["_estimate"]
        sz._ORIG["median_at"] = _RZ_PRISTINE["_median_at"]
        self.g = sz.GIB

    def _build(self, res, mem):
        sz._ORIG["build"] = lambda *a, **k: res
        return sz.build_one_wrapped("b", 0, "u", 1000, mem)

    def test_check_start_lock_wait_bounded(self):
        self.assertEqual(sz.CHECK_LOCK_WAIT_S, 120)
        a = sz.parse_args(["--sizes", "1000", "--server", "t1"])
        with mock.patch.object(sz, "driver_guard", return_value="held") as dg:
            self.assertEqual(sz.check_start_main(a), 6)
        dg.assert_called_once_with(120)

    def test_lock_wait_lines_rate_limited(self):
        name = "sz_t1009w_%d" % os.getpid()
        k = _hold_lock(name, secs=2)
        lines = []
        try:
            with mock.patch.object(sz, "DRIVER_LOCK", name), \
                    mock.patch.dict(sz._LOCK, {}, clear=True), \
                    mock.patch.object(sz, "LOCK_POLL_S", 0.1), \
                    mock.patch.object(sz, "LOCK_LOG_S", 0.5), \
                    mock.patch("builtins.print",
                               side_effect=lambda *a, **kw: lines.append(a[0])):
                self.assertIsNone(sz.driver_lock(10))
                sz._LOCK.pop("sock").close()
        finally:
            k.kill()
            k.wait()
        self.assertTrue(lines)
        self.assertTrue(all(x.startswith("SAME wait lock") for x in lines))
        self.assertLessEqual(len(lines), 5)

    def test_arena_plain_alloc_not_learned(self):
        """Review A2: a plain 20 GiB realloc failure is not an arena miss."""
        mem = int(30 * self.g + sz.arena_room())
        self._build({"status": "oom_or_killed", "peak_rss": 20 * self.g,
                     "as_cap": mem, "err": "memory allocation of "
                     "21474836480 bytes failed"}, mem)
        self.assertNotIn("arena_b", sz.S)

    def test_arena_not_raised_when_tasks_short(self):
        mem = int(30 * self.g + sz.arena_room())
        err = ("ThreadPoolBuildError Resource temporarily unavailable "
               "/r/rayon-core-1.9.3/src/registry.rs")
        with mock.patch.object(sz, "tasks_short", return_value=True):
            self._build({"status": "build_fail", "peak_rss": self.g,
                         "as_cap": mem, "err": err}, mem)
        self.assertNotIn("arena_b", sz.S)
        with mock.patch.object(sz, "tasks_free", return_value=100), \
                mock.patch.object(sz.os, "sched_getaffinity",
                                  return_value=set(range(128))):
            sz.S["batch_n"] = 2
            self.assertTrue(sz.tasks_short())
        with mock.patch.object(sz, "tasks_free", return_value=None):
            self.assertFalse(sz.tasks_short())

    def test_arena_raise_locked_threads(self):
        mem = int(30 * self.g + sz.arena_room())
        err = ("ThreadPoolBuildError Resource temporarily unavailable "
               "/r/rayon-core-1.9.3/src/registry.rs")
        sz.S["batch_seq"] = 7
        res = {"status": "build_fail", "peak_rss": self.g, "as_cap": mem,
               "err": err}
        sz._ORIG["build"] = lambda *a, **k: dict(res)
        with mock.patch.object(sz, "tasks_short", return_value=False):
            ts = [threading.Thread(target=sz.build_one_wrapped,
                                   args=("b", i, "u", 1000, mem))
                  for i in range(8)]
            for t in ts:
                t.start()
            for t in ts:
                t.join()
        self.assertEqual(sz.S["arena_b"], 132 * 2 ** 20)

    def test_cold_estimate_not_below_rz_own(self):
        """Review A5: the first-batch 1 KB cap stays at least 38 GiB."""
        g = self.g
        with mock.patch.object(rz, "_ram_budget_bytes",
                               return_value=int(0.85 * 961 * g)), \
                mock.patch.object(sz.os, "cpu_count", return_value=128), \
                mock.patch.object(sz.os, "sched_getaffinity",
                                  return_value=set(range(128))):
            b3_cold = int(0.85 * 961 * g / 64)
            e = sz.estimate_wrapped("u", 1000, {}, 1, "peak_rss", b3_cold)
            self.assertAlmostEqual(e / g, 0.85 * 961 / 32, places=2)
            self.assertGreaterEqual(_RZ_PRISTINE["_as_cap"](e, 865 * g),
                                    38 * g)
            self.assertGreaterEqual(sz.as_cap_wrapped(e, 865 * g), 46 * g)
            done = _rec("m", 1000, 2 * g)    # a measured median: RZ's own
            self.assertEqual(sz.estimate_wrapped("u", 1000, done, 1,
                                                 "peak_rss", 2 * g), 2 * g)

    def test_res_uses_room_at_cap_time(self):
        mem = int(15 * self.g + 2 * self.g)
        sz.S["cap_room"] = 2 * self.g
        sz.S["arena_b"] = 264 * 2 ** 20       # a later raise: not this cap
        self._build({"status": "built", "peak_rss": self.g, "as_cap": mem}, mem)
        self.assertIn("res=10.0GiB", [m for m in self.out
                                      if m.startswith("SAME build")][0])

    def test_live_python_ancestor_unreadable_spares(self):
        tree = {10: ("S", 9)}
        with mock.patch.object(sz, "_stat_of", tree.get):
            self.assertTrue(sz._live_python_ancestor(10))

    def test_jobs_fit_honors_nproc(self):
        with mock.patch.object(sz, "pids_avail", return_value=None), \
                mock.patch.object(sz, "nproc_avail", return_value=4000), \
                mock.patch.object(sz.os, "sched_getaffinity",
                                  return_value=set(range(128))):
            self.assertEqual(sz.jobs_fit(), (15, 64, 4000))
        self.assertEqual(sz.PIDS_SLACK, 2000)

    def test_nproc_avail_counts_uid_threads(self):
        import resource
        with mock.patch.object(resource, "getrlimit",
                               return_value=(10 ** 6, resource.RLIM_INFINITY)):
            v = sz.nproc_avail()
        self.assertTrue(0 < v < 10 ** 6)
        with mock.patch.object(resource, "getrlimit", return_value=(
                resource.RLIM_INFINITY, resource.RLIM_INFINITY)):
            self.assertIsNone(sz.nproc_avail())

    def test_circ_rebuild_needed_rules(self):
        d = os.path.join(self.tmp, "cb")
        os.makedirs(os.path.join(d, "src"))
        orig = open(os.path.join(sz.ZOMBIE_TREE, "circ", "src",
                                 "zkmb.rs")).read()
        a = sz.parse_args(["--sizes", "1000", "--server", "t1"])
        sz._ORIG["render"] = _RZ_PRISTINE["_render_zkmb"]
        with mock.patch.object(rz, "CIRC_BIN", os.path.join(d, "bin")), \
                mock.patch.object(rz, "BUILD_RS", os.path.join(d, "src",
                                                               "zkmb.rs")), \
                mock.patch.object(rz, "BUILD_RS_ORIG", os.path.join(
                    d, "src", "zkmb.rs.orig")):
            self.assertTrue(sz.circ_rebuild_needed(a))
            open(rz.CIRC_BIN, "w").close()
            open(rz.BUILD_RS_ORIG, "w").write(orig)
            open(rz.BUILD_RS, "w").write(sz.render_wrapped(orig, rz.VEC_SIZE))
            self.assertFalse(sz.circ_rebuild_needed(a))
            open(rz.BUILD_RS, "a").write("// edited\n")
            self.assertTrue(sz.circ_rebuild_needed(a))

    def test_git_safe_dir_skipped_on_old_git(self):
        seen = []
        with mock.patch.object(sz, "GIT_SAFE_OK", False), \
                mock.patch.object(sz.subprocess, "run",
                                  lambda cmd, **k: seen.append(cmd) or
                                  mock.Mock(returncode=0, stdout="")):
            sz.git("status")
        self.assertEqual(seen[0][:3], ["git", "-C", sz.REPO])

    def test_scratch_refusal_names_leftover(self):
        base = os.path.join(self.tmp, "bora_zombie_scratch")
        os.makedirs(base)
        a = sz.parse_args(["--sizes", "1000", "--server", "t1"])
        with mock.patch.object(sz, "scratch_free_gib",
                               return_value=(40, base)), \
                mock.patch.object(rz, "_dir_bytes",
                                  return_value=10 * sz.GIB), \
                mock.patch.object(sz, "jobs_fit", return_value=(8, 8, 9999)):
            txt, why = sz.host_views(a)
        self.assertIn("leftover", why)            # ALL_T1013 F5: counted
        self.assertIn("60 GiB", why)
        self.assertIn("scratch=50GiB", txt)

    def test_slice_reset_at_exit(self):
        sz.S["launcher"] = "systemd"
        calls = []
        with mock.patch.object(sz, "run_main", return_value=0), \
                mock.patch.object(sz, "driver_guard", return_value=None), \
                mock.patch.object(sz, "sctl",
                                  side_effect=lambda *a, **k: calls.append(a)):
            _main_quiet(["--sizes", "1000", "--n", "2", "--server", "t1"])
        self.assertIn(("set-property", "--runtime", "bora-same.slice",
                       "MemoryMax=infinity"), calls)

    def test_batch_exit_syncs_after_builds(self):
        """Review A4: one os.sync after every keygen of a batch returned."""
        order = []
        with mock.patch.object(sz, "sync_scratch",      # ALL_T1013 F9
                               side_effect=lambda: order.append("sync")
                               or "syncfs=1"):
            with sz.BatchTPE(max_workers=2) as ex:
                fs = [ex.submit(lambda i=i: (time.sleep(0.2),
                                             order.append("build"))[1])
                      for i in range(2)]
            self.assertEqual(order, ["build", "build", "sync"])
            del order[:]
            try:
                with sz.BatchTPE(max_workers=1):
                    raise RuntimeError("x")
            except RuntimeError:
                pass
        self.assertEqual(order, [])
        self.assertTrue(any(m.startswith("SAME sync") for m in self.out))
        self.assertTrue(all(f.done() for f in fs))



# ===========================================================================
# ALL_T1013 (zdrv2_d2.md)
# ===========================================================================
class T1013ProcTest(Base):
    """ALL_T1013 K1: F3 synchronous kill pass, F4 check-start kills."""

    def test_check_start_kills_orphans_and_goes_on(self):
        out, calls = [], []
        a = sz.parse_args(["--sizes", "1000", "--server", "t1"])

        def orph(kill, pids=None):
            calls.append(kill)
            return [(77, "/x/bora_zombie_par/c1")]
        with mock.patch.object(sz, "orphan_circ", orph), \
                mock.patch.object(sz, "_alive", return_value=False), \
                mock.patch.object(sz, "clone_check", return_value="K1 stop"), \
                mock.patch.object(sz, "say", side_effect=out.append):
            self.assertEqual(sz.check_start_main(a), 6)
        self.assertEqual(calls, [True])
        self.assertTrue(any("K1 stop" in m for m in out))
        self.assertFalse(any("orphan" in m for m in out))

    def test_alive_rules(self):
        with mock.patch.object(sz, "_stat_of", {1: ("S", 0), 2: ("Z", 0)}.get):
            self.assertTrue(sz._alive(1))
            self.assertFalse(sz._alive(2))
            self.assertFalse(sz._alive(3))

    def test_sigterm_kills_children_before_a_quick_exit(self):
        d = os.path.join(self.tmp, "k1")
        os.makedirs(d)
        slp = os.path.join(d, "zz_k1_sleep")
        shutil.copy("/bin/sleep", slp)
        prog = textwrap.dedent("""\
            import os, sys, signal, subprocess, time
            sys.path.insert(0, %r)
            import same_zombie as sz
            p = subprocess.Popen([%r, "30"])
            print(p.pid, flush=True)
            signal.signal(signal.SIGTERM, sz.on_sigterm)
            while True:
                time.sleep(0.05)
            """) % (HERE, slp)
        for _ in range(3):
            c = subprocess.Popen([sys.executable, "-c", prog],
                                 stdout=subprocess.PIPE, text=True)
            kid = int(c.stdout.readline())
            try:
                c.send_signal(signal.SIGTERM)
                self.assertEqual(c.wait(timeout=10), 143)
                gone = False
                for _ in range(40):
                    if not sz._alive(kid):
                        gone = True
                        break
                    time.sleep(0.05)
                self.assertTrue(gone, "child %d survived SIGTERM" % kid)
            finally:
                c.stdout.close()
                try:
                    os.kill(kid, signal.SIGKILL)
                except OSError:
                    pass



class T1013BuildTest(HookBase):
    """ALL_T1013 K2: F1 timed-out keygen kill, R1 keyless build."""

    def setUp(self):
        super().setUp()
        self.out = []
        p = mock.patch.object(sz, "say", side_effect=self.out.append)
        p.start()
        self.addCleanup(p.stop)
        sz._ORIG["as_cap"] = _RZ_PRISTINE["_as_cap"]

    def _keys(self, d, n, skip=None, empty=None):
        os.makedirs(os.path.join(d, "keys"), exist_ok=True)
        for part in sz.KEY_PARTS:
            if part == skip:
                continue
            with open(os.path.join(d, "keys", "policy%d_%s" % (n, part)),
                      "w") as f:
                f.write("" if part == empty else "k")

    def test_built_with_all_keys_stays_built(self):
        d = os.path.join(self.tmp, "c00000")
        self._keys(d, 1000)
        sz._ORIG["build"] = lambda *a, **k: {"name": "u", "dir": d,
                                             "status": "built"}
        self.assertEqual(sz.build_one_wrapped("b", 0, "u", 1000)["status"],
                         "built")

    def test_keyless_or_short_build_is_build_fail(self):
        for skip, empty in ((None, "gens"), ("var_idxes", None),
                            ("inst", "gens")):
            d = os.path.join(self.tmp, "c%s%s" % (skip, empty))
            self._keys(d, 2000, skip, empty)
            sz._ORIG["build"] = lambda *a, d=d, **k: {"name": "u", "dir": d,
                                                      "status": "built"}
            b = sz.build_one_wrapped("b", 0, "u", 2000)
            self.assertEqual(b["status"], "build_fail")
            self.assertIn("wrote no keys", b["err"])
        d = os.path.join(self.tmp, "empty")
        os.makedirs(os.path.join(d, "keys"))
        sz._ORIG["build"] = lambda *a, **k: {"name": "u", "dir": d,
                                             "status": "built"}
        self.assertEqual(sz.build_one_wrapped("b", 0, "u", 1000)["status"],
                         "build_fail")

    def test_stub_dir_without_keys_dir_untouched(self):
        d = os.path.join(self.tmp, "stub")
        os.makedirs(d)
        sz._ORIG["build"] = lambda *a, **k: {"name": "u", "dir": d,
                                             "status": "built"}
        self.assertEqual(sz.build_one_wrapped("b", 0, "u", 1000)["status"],
                         "built")

    def test_timeout_kill_matches_own_cwd_only(self):
        cwd = {11: "/p/c00001", 12: "/p/c00002", 13: "/p/c00001"}
        exe = {11: "circ_executable", 12: "circ_executable", 13: "time"}
        killed = []
        with mock.patch.object(sz, "_pids", lambda: sorted(cwd)), \
                mock.patch.object(sz, "_owned", return_value=True), \
                mock.patch.object(sz, "_exe_base", exe.get), \
                mock.patch.object(sz, "_cwd_of", cwd.get), \
                mock.patch.object(sz, "descendants", lambda p: []), \
                mock.patch.object(sz, "_sigkill", killed.append):
            self.assertEqual(sz._kill_cwd("/p/c00001"), [11])
        self.assertEqual(killed, [11])

    @unittest.skipUnless(os.path.isfile("/usr/bin/time"), "no GNU time")
    def test_timeout_orphan_killed_real(self):
        d = os.path.join(self.tmp, "c00007")
        os.makedirs(d)
        exe = os.path.join(self.tmp, "circ_executable")
        shutil.copy("/bin/sleep", exe)

        def build(*a, **k):
            try:
                subprocess.run(["/usr/bin/time", "-v", exe, "30"], cwd=d,
                               capture_output=True, text=True, timeout=1)
            except subprocess.TimeoutExpired:
                pass
            return {"name": "u", "prox": 1, "dir": d,
                    "status": "build_timeout"}
        sz._ORIG["build"] = build

        def mine():
            return [p for p in sz._pids() if sz._owned(p)
                    and sz._exe_base(p) == "circ_executable"
                    and sz._cwd_of(p) == os.path.realpath(d)
                    and sz._alive(p)]
        try:
            sz.build_one_wrapped("b", 7, "u", 1000)
            for _ in range(40):
                if not mine():
                    break
                time.sleep(0.05)
            self.assertEqual(mine(), [])
            self.assertTrue(any("killed timed-out keygen" in m
                                for m in self.out))
        finally:
            for p in mine():
                sz._sigkill(p)



class T1013ResumeTest(Base):
    """ALL_T1013 K3: F5 leftover scratch, F7 retry once."""

    def setUp(self):
        super().setUp()
        self.out = []
        p = mock.patch.object(sz, "say", side_effect=self.out.append)
        p.start()
        self.addCleanup(p.stop)

    def _left(self, root):
        os.makedirs(os.path.join(root, "c00003", "keys"))
        with open(os.path.join(root, "c00003", "keys", "k"), "w") as f:
            f.write("x" * 100)

    def test_reclaim_redirect_touches_par_root_only(self):
        par, m1 = os.path.join(self.tmp, "par"), os.path.join(self.tmp, "m1")
        self._left(par)
        self._left(os.path.join(m1, "bora_zombie_scratch"))
        with mock.patch.object(rz, "PAR_ROOT", par), \
                mock.patch.object(sz, "TMP_ROOT", self.tmp), \
                mock.patch.object(rz, "_candidate_mounts", lambda: [m1]):
            sz.reclaim_scratch()
        self.assertFalse(os.path.exists(par))
        self.assertTrue(os.path.isdir(os.path.join(m1, "bora_zombie_scratch")))
        self.assertTrue(any("removed leftover %s" % par in m for m in self.out))

    def test_reclaim_every_candidate_without_redirect(self):
        par = os.path.join(self.tmp, "par")
        ms = [os.path.join(self.tmp, "m%d" % i) for i in range(3)]
        for m in ms[:2]:
            self._left(os.path.join(m, "bora_zombie_scratch"))
        os.makedirs(ms[2])
        os.symlink(ms[0], os.path.join(ms[2], "bora_zombie_scratch"))
        with mock.patch.object(rz, "PAR_ROOT", par), \
                mock.patch.object(sz, "TMP_ROOT", None), \
                mock.patch.object(rz, "_candidate_mounts", lambda: ms):
            sz.reclaim_scratch()
        for m in ms[:2]:
            self.assertFalse(os.path.exists(os.path.join(m,
                                                         "bora_zombie_scratch")))
        self.assertTrue(os.path.islink(os.path.join(ms[2],
                                                    "bora_zombie_scratch")))
        self.assertEqual(sum("removed leftover" in m for m in self.out), 2)

    def test_host_views_counts_leftover_as_free(self):
        full = sz.parse_args(["--sizes", "1000", "--server", "t1"])
        base = os.path.join(self.tmp, "par")
        os.makedirs(base)
        with mock.patch.object(sz, "jobs_fit", return_value=(8, 8, 10 ** 6)), \
                mock.patch.object(sz, "scratch_free_gib",
                                  return_value=(50.0, base)), \
                mock.patch.object(rz, "_dir_bytes",
                                  return_value=20 * sz.GIB):
            txt, why = sz.host_views(full)
        self.assertIsNone(why)
        self.assertIn("scratch=70GiB", txt)
        self.assertTrue(any("leaf removes" in m for m in self.out))

    def test_retry_once_then_kept(self):
        sweep = sz.Pair(rz.PARTIAL, rz.PARTIAL_DOCS)
        rows = [{"regex_name": "g", "str_len": 4000, "status": "disk_full"},
                {"regex_name": "h", "str_len": 4000, "status": "build_fail"},
                {"regex_name": "h", "str_len": 4000,
                 "status": "oom_or_killed"},
                {"regex_name": "p", "str_len": 4000, "status": "prove_fail"},
                {"regex_name": "o", "str_len": 4000, "status": "ok"}]
        with open(rz.PARTIAL, "w") as f:
            f.writelines(json.dumps(r) + "\n" for r in rows)
        done = {"%s|%d" % (r["regex_name"], r["str_len"]): r for r in rows}
        sz.retry_once(done, sweep)
        self.assertEqual(sorted(done), ["h|4000", "o|4000", "p|4000"])
        self.assertTrue(any("retry once g 4000 (disk_full)" in m
                            for m in self.out))
        self.assertTrue(any("h 4000 given up 2 times, kept" in m
                            for m in self.out))



class T1013BuildOnlyTest(HookBase):
    """ALL_T1013 K4: S9 --build-only (R4 PAPER_DATA lock, redirect)."""

    def setUp(self):
        super().setUp()
        self.out = []
        p = mock.patch.object(sz, "say", side_effect=self.out.append)
        p.start()
        self.addCleanup(p.stop)
        self.addCleanup(self._unlock)
        self.lockf = os.path.join(self.tmp, "PAPER_DATA.lock")
        p = mock.patch.object(sz, "PD_RUN_LOCK", self.lockf)
        p.start()
        self.addCleanup(p.stop)
        self.rs = os.path.join(self.tmp, "zkmb.rs")
        open(self.rs, "w").write("fn main() {}\n")
        self.calls = []

    def _unlock(self):
        s = sz._LOCK.pop("sock", None)
        if s is not None:
            s.close()

    def _ensure(self, sizes):
        self.calls.append((list(sizes), rz._render_zkmb is sz.render_wrapped))
        return "/x/circ_executable"

    def _main(self, env=None, root=None):
        a = sz.parse_args(["--build-only"])
        with mock.patch.object(sz, "TMP_ROOT", root), \
                mock.patch.dict(os.environ, env or {}), \
                mock.patch.object(rz, "ensure_zombie_built", self._ensure), \
                mock.patch.object(rz, "BUILD_RS", self.rs):
            return sz.build_only_main(a)

    def test_builds_full_vec_size_with_hooks(self):
        self.assertEqual(self._main(), 0)
        self.assertEqual(self.calls, [(list(rz.VEC_SIZE), True)])
        self.assertTrue(any(m.startswith("SAME build-only OK /x/circ")
                            for m in self.out))

    def test_redirect_needs_opt_in(self):
        self.assertEqual(self._main(root=self.tmp), 0)
        self.assertEqual(self.calls, [])
        self._unlock()
        self.assertEqual(self._main({sz.BUILD_REDIRECT_ENV: "1"},
                                    root=self.tmp), 0)
        self.assertEqual(len(self.calls), 1)

    def test_paper_data_lock_held_skips(self):
        import fcntl
        fd = os.open(self.lockf, os.O_RDWR | os.O_CREAT, 0o644)
        try:
            fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
            self.assertTrue(sz.pd_lock_held())
            self.assertEqual(self._main(), 0)
        finally:
            os.close(fd)
        self.assertEqual(self.calls, [])
        self.assertTrue(any("PAPER_DATA run holds" in m for m in self.out))
        self.assertFalse(sz.pd_lock_held())

    def test_driver_lock_held_skips(self):
        s = socket_hold(sz.DRIVER_LOCK)
        try:
            self.assertEqual(self._main(), 0)
        finally:
            s.close()
        self.assertEqual(self.calls, [])
        self.assertTrue(any("circ build left to the leaf" in m
                            for m in self.out))

    def test_build_failure_is_rc7(self):
        def bad(sizes):
            raise SystemExit("cargo build failed; see output above.")
        a = sz.parse_args(["--build-only"])
        with mock.patch.object(sz, "TMP_ROOT", None), \
                mock.patch.object(rz, "ensure_zombie_built", bad):
            self.assertEqual(sz.build_only_main(a), 7)
        self.assertTrue(any("FAIL: SystemExit: cargo build failed" in m
                            for m in self.out))

    def test_check_start_pass_names_circ_state(self):
        a = sz.parse_args(["--dry", "4", "--sizes", "1000", "--server", "t1",
                           "--launcher", "prlimit"])
        for need, word in ((True, "circ=rebuild-at-leaf"),
                           (False, "circ=prebuilt")):
            del self.out[:]
            self._unlock()
            with mock.patch.object(sz, "clone_check", return_value=None), \
                    mock.patch.object(sz, "fx_check", return_value=None), \
                    mock.patch.object(sz, "nightly_refusal",
                                      return_value=None), \
                    mock.patch.object(sz, "selftest_refusal",
                                      return_value=None), \
                    mock.patch.object(sz, "oomd_check", return_value=None), \
                    mock.patch.object(sz, "host_views",
                                      return_value=("hv", None)), \
                    mock.patch.object(sz, "circ_rebuild_needed",
                                      return_value=need):
                self.assertEqual(sz.check_start_main(a), 0)
            self.assertTrue(any("PASS" in m and word in m for m in self.out),
                            self.out)


def socket_hold(name):
    import socket as so
    s = so.socket(so.AF_UNIX, so.SOCK_DGRAM)
    s.bind("\0" + name)
    return s



class T1013KeysArmTest(HookBase):
    """ALL_T1013 K5: S3 keygen-only arm through rz._run_keygen."""

    def setUp(self):
        super().setUp()
        self.seen = []
        sz._ORIG["run_keygen"] = lambda cmd, cwd, timeout=0: (
            self.seen.append(cmd) or (0, "", "", 1))

    def test_rewrites_only_the_keygen_circuit_arg(self):
        pre = ["/usr/bin/prlimit", "--as=9", "--"]
        sz.run_keygen_wrapped(pre + ["/b/circ", "policy_2000", "true",
                                     "prover"], "/d", 5)
        sz.run_keygen_wrapped(["/b/circ", "policy_1000", "true", "prover"],
                              "/d")
        sz.run_keygen_wrapped(["/b/circ", "policy_1000", "false",
                               "prover_verifier"], "/d")
        sz.run_keygen_wrapped(["/b/circ", "policy_real_1000", "true",
                               "prover"], "/d")
        self.assertEqual(self.seen, [
            pre + ["/b/circ", "policy_keys_2000", "true", "prover"],
            ["/b/circ", "policy_keys_1000", "true", "prover"],
            ["/b/circ", "policy_1000", "false", "prover_verifier"],
            ["/b/circ", "policy_real_1000", "true", "prover"]])

    def test_installed_hook_reaches_rz_build_one(self):
        sz.install_rz_hooks()
        sz.install_rz_hooks()
        self.assertIs(rz._run_keygen, sz.run_keygen_wrapped)
        self.assertIs(sz._ORIG["run_keygen"], _RZ_PRISTINE["_run_keygen"])
        src = open(sz.RZ_PATH).read()
        self.assertIn("rc, _out, errtxt, rss = _run_keygen(", src)

    def test_render_has_keys_arm_per_size(self):
        orig = "fn zk_test() {\n    match x {\n        _ => ()\n    }\n}\n"
        sz._ORIG["render"] = _RZ_PRISTINE["_render_zkmb"]
        out = sz.render_wrapped(orig, [1000, 4000])
        for n in (1000, 4000):
            self.assertEqual(out.count('"policy_keys_%d" => compile_one_'
                                       'circuit("policy%d"),' % (n, n)), 1)
        self.assertLess(out.index("policy_keys_4000"), out.index("_ => ()"))



class T1013ZrealArmTest(unittest.TestCase):
    """ALL_T1013 K6: S1 one key load, timers unchanged (selftest pins)."""

    def _fn(self, arm=None):
        fn = (arm or sz.ARM_T).split("\n//@@ARM\n")[0]
        return fn

    def test_timer_blocks_once_in_order(self):
        fn = self._fn()
        idx = [fn.index(p) for p in sz.S1_PINS]
        self.assertEqual([fn.count(p) for p in sz.S1_PINS], [1, 1])
        self.assertEqual(idx, sorted(idx))
        self.assertNotIn("zkmb_get_verifier", fn)
        self.assertEqual(fn.count("Box::from_raw(prover_p)"), 1)
        self.assertLess(fn.index("prove takes"), fn.index("Box::from_raw"))
        self.assertLess(fn.index("Box::from_raw"),
                        fn.index("let ok = verifier.verify"))

    def test_selftest_catches_a_moved_timer(self):
        bad = sz.ARM_T.replace(
            "    let timer = Instant::now();\n    let proof = prover.prove",
            "    let proof0 = 0;\n    let timer = Instant::now();\n"
            "    let proof = prover.prove", 1)
        bad = bad.replace("let verifier = &verifier;\n    let timer",
                          "let verifier = &verifier;\n    drop(0);\n"
                          "    let timer", 1)
        with mock.patch.object(sz, "ARM_T", bad):
            with self.assertRaises(AssertionError):
                sz.selftest()



class T1013LadderTest(Base):
    """ALL_T1013 K8: S5 width ladder by slot count, R6, two-rung stop, F16."""

    def test_ladders(self):
        jet = fake_topo(n_nodes=2, cores=32, tpc=2, keep=4)   # C = 30
        self.assertEqual(sz.ladder(jet, 16), [1, 2, 3, 4, 6, 10, 15, 16])
        self.assertEqual(sz.ladder(fake_topo(cores=4), 16), [1, 2, 4])
        self.assertEqual(sz.ladder(fake_topo(cores=6), 16), [1, 2, 3, 6])
        self.assertEqual(sz.ladder(fake_topo(cores=60), 16),
                         [1, 2, 3, 4, 6, 8, 12, 16])
        self.assertEqual(sz.ladder(fake_topo(cores=1), 16), [1])
        for t in (jet, fake_topo(cores=36), fake_topo(cores=7)):
            for w in sz.ladder(t, 16):
                self.assertTrue(sz.make_slots(t, w), w)

    def test_snap_and_next_rung(self):
        L = [1, 2, 3, 4, 6, 10, 15, 16]
        self.assertEqual(sz.snap_up(L, 5), 6)
        self.assertEqual(sz.snap_up(L, 40), 16)        # R6: clamp to top
        self.assertEqual(sz.snap_down(L, 9), 6)
        self.assertEqual(sz.snap_down(L, 0), 1)
        self.assertEqual(sz.next_rung(L, 8), 10)       # R6: w not a rung
        self.assertEqual(sz.next_rung(L, 4), 6)
        self.assertIsNone(sz.next_rung(L, 16))

    def test_width_for_snaps_state_to_a_rung(self):
        sz.S["topo"] = fake_topo(n_nodes=2, cores=32, tpc=2, keep=4)
        sz.S["cap"] = 16
        sz.S["w_state"] = {4000: 8}                   # old powers-of-two row
        ts = [sz.Task("u%d" % i, 4000, "e", "p", "d", {"u_c": 1.0, "rss_c": 1,
                                                       "wall_s": 1}, False)
              for i in range(30)]                 # w_mem = 60 // 30 = 2
        self.assertEqual(sz.width_for(4000, ts, 1 << 40), 10)

    def test_two_rung_stop_rule(self):
        sz.S["topo"] = fake_topo(n_nodes=2, cores=32, tpc=2, keep=4)
        sz.S["cap"] = 16
        self.assertEqual(sz.widen_next([1.30], 0.004, 4), 6)
        self.assertEqual(sz.widen_next([1.30, 1.299], 0.004, 6), 10)
        self.assertIsNone(sz.widen_next([1.30, 1.299, 1.298], 0.004, 10))
        self.assertEqual(sz.widen_next([1.20, 1.17, 1.14], 0.05, 10), 15)
        self.assertIsNone(sz.widen_next([1.2, 1.1], 0.004, 16))
        sz.S["cap"] = 0
        self.assertIsNone(sz.widen_next([1.3], 0.004, 4))

    def test_scalecal_verify_false_copy_is_a_failed_width(self):
        sz.S["topo"] = fake_topo(cores=4)
        sz.S["cap"] = 4
        sz.ARGS.scalecal_min_cores = 1
        d = os.path.join(self.tmp, "u")
        os.makedirs(d)
        base = {"base_uuid": "b", "rss_c": 1 << 20, "wall_s": 1.0,
                "u_c": 1.0, "cons": 70000, "prove_ms": 100}
        sz.S["keep"].append({"unit": "u", "size": 1000, "dir": d,
                             "base": base})

        class FakePacked(object):
            def __init__(self, size, b, w, B, K_f, gid, pairs, mode=None):
                self.pairs, self.pair_ms = pairs, {}

            def run(self, queue):
                self.pair_ms = {c: 100 for c in self.pairs}
                self.pair_ms[self.pairs[0]] = "verify_false"
        with mock.patch.object(sz, "Packed", FakePacked), \
                mock.patch.object(sz, "serial_reference",
                                  lambda ts: ({id(t): 100 for t in ts}, 0.01)):
            sz.scalecal()                             # F16: no TypeError
        self.assertEqual(sz.read_scalecal("t1")["overall"], "FAIL")



class T1013RobustTest(HookBase):
    """ALL_T1013 K9: F8, F9/V13, F11/V12, F12, F14."""

    def setUp(self):
        super().setUp()
        self.out = []
        p = mock.patch.object(sz, "say", side_effect=self.out.append)
        p.start()
        self.addCleanup(p.stop)
        sz._ORIG["as_cap"] = _RZ_PRISTINE["_as_cap"]

    def test_oserror_in_keygen_becomes_resource_status(self):
        import errno
        for err, st in ((errno.ENOSPC, "disk_full"), (errno.EDQUOT,
                                                      "disk_full"),
                        (errno.EAGAIN, "build_fail")):
            def bad(*a, err=err, **k):
                raise OSError(err, os.strerror(err))
            sz._ORIG["build"] = bad
            b = sz.build_one_wrapped("b", 3, "u", 1000)
            self.assertEqual(b["status"], st)
            self.assertIn(st, rz.RESOURCE_FAIL)
            self.assertEqual(b["dir"], os.path.join(rz.PAR_ROOT, "c00003"))

    def test_sync_scratch_syncfs_each_fs_once(self):
        calls = []

        class Libc(object):
            def syncfs(self, fd):
                calls.append(fd)
                return 0
        os.makedirs(os.path.join(self.tmp, "par"), exist_ok=True)
        with mock.patch.object(rz, "PAR_ROOT", os.path.join(self.tmp, "par")), \
                mock.patch("ctypes.CDLL", lambda *a, **k: Libc()), \
                mock.patch.object(sz.os, "sync") as osync:
            self.assertEqual(sz.sync_scratch(), "syncfs=1")   # one fs here
            osync.assert_not_called()
        self.assertEqual(len(calls), 1)

    def test_sync_scratch_falls_back_to_os_sync(self):
        class Libc(object):
            def syncfs(self, fd):
                return -1
        with mock.patch("ctypes.CDLL", lambda *a, **k: Libc()), \
                mock.patch.object(sz.os, "sync") as osync:
            self.assertEqual(sz.sync_scratch(), "sync")
            osync.assert_called_once()

    def test_sync_scratch_real(self):
        self.assertTrue(sz.sync_scratch().startswith("syncfs="))

    def test_torn_middle_line_dropped_and_unit_redone(self):
        p = sz.Pair(os.path.join(self.tmp, "a.jsonl"),
                    os.path.join(self.tmp, "b.jsonl"))
        good = json.dumps({"kind": "base", "unit": "u1", "size": 1000})
        torn = '{"base_uuid": "x", "kind": "base", "size": 2000, "unit": "u2'
        torn2 = '{"base_uuid": "y", "co'
        text = "\n".join([good, torn + '", "w', torn2, good]) + "\n"
        for f in (p.tmp, p.docs):
            open(f, "w").write(text)
        sz.S.pop("force_redo", None)
        p.repair_tail()
        self.assertEqual(open(p.tmp).read(), good + "\n" + good + "\n")
        self.assertEqual(p.load(), [json.loads(good)] * 2)
        self.assertEqual(sz.S["force_redo"], {("u2", 2000)})
        self.assertTrue(any("2 unparsable line(s) removed" in m
                            for m in self.out))
        self.assertTrue(any("names no unit" in m for m in self.out))

    def test_force_redo_and_sig_note_in_load(self):
        sz.ARGS = sz.parse_args(["--sizes", "1000", "--n", "2", "--server",
                                 "t1"])
        sz.S["rule2_done"] = True
        sz.S["force_redo"] = {("u2", 2000)}
        rows = {"u2|2000": {"regex_name": "u2", "str_len": 2000,
                            "status": "ok", "launch_sig": "sig0"},
                "u3|2000": {"regex_name": "u3", "str_len": 2000,
                            "status": "ok", "launch_sig": "sig1"}}
        sz._ORIG["load"] = lambda: dict(rows)
        done = sz.load_partial_wrapped()
        self.assertNotIn("u2|2000", done)
        self.assertIn("u3|2000", done)
        self.assertTrue(any("u2 2000 redone" in m for m in self.out))
        self.assertFalse(any("launch_sig value" in m for m in self.out))
        rows["u4|2000"] = {"regex_name": "u4", "str_len": 2000,
                           "status": "ok"}
        sz.load_partial_wrapped()
        self.assertTrue(any("2 launch_sig value(s)" in m for m in self.out))

    def test_append_stamps_launch_sig(self):
        got = []
        sz._ORIG["append"] = got.append
        sz.append_partial_wrapped({"regex_name": "u"})
        self.assertEqual(got, [{"regex_name": "u", "launch_sig": "sig1"}])

    def test_watchdog_requeue_bounded(self):
        pk = sz.Packed.__new__(sz.Packed)
        pk.tail, pk.done_ok, pk.pairs, pk.pair_ms = [], [], None, {}
        t = sz.Task("u", 1000, "e", "p", "d", {"rss_c": 1, "wall_s": 1},
                    False)
        q = []
        for _ in range(3):
            pk.after(t, "watchdog", {}, q)
        self.assertEqual((len(q), pk.tail), (2, [t]))



class T1013SkipVerifyTest(StubSetup):
    """ALL_T1013 K10: S2 gate serial references skip the verify."""

    def test_only_gate_serial_skips(self):
        t = self.tasks(units=("ua",))[0]
        envs = {}
        real = subprocess.Popen

        def pop(cmd, **k):
            envs[k["env"].get("ZREAL_NO_VERIFY")] = cmd
            return real(cmd, **k)
        with mock.patch.object(sz.subprocess, "Popen", pop):
            for mode in ("gate_serial", "serial", "tail"):
                cls, row = sz.run_one_serial(t, mode)
                self.assertEqual(cls, "ok", mode)
                if mode == "gate_serial":
                    self.assertIsNone(row["verify_ok"])
                    self.assertIsNone(row["verify_ms"])
                    self.assertEqual(row["prove_ms"], 300)
                else:
                    self.assertIs(row["verify_ok"], True)
                    self.assertEqual(row["verify_ms"], 5)
        self.assertEqual(sorted(envs, key=str), ["1", None])

    def test_skip_line_counts_only_for_gate_serial(self):
        out = "prove takes 3\nproof size is 1 bytes\nzreal verify_ok skipped\n"
        self.assertTrue(sz.skip_view(out, "gate_serial")[1])
        self.assertFalse(sz.skip_view(out, "packed")[1])
        self.assertEqual(sz.classify(0, sz.skip_view(out, "packed")[0], "",
                                     "", None, False, False, 1, 1), "resource")

    def test_verify_false_pair_found_in_packed_wave(self):
        os.environ["STUB_VF_EMAIL"] = "1000_01"
        try:
            sz.run_subflush(1000, 16, self.tasks())
        finally:
            os.environ.pop("STUB_VF_EMAIL", None)
        rows = sz.S["pair"].load()
        ser = [r for r in rows if r.get("mode") == "gate_serial"]
        self.assertTrue(ser and all(r["class"] == "ok" for r in ser))
        self.assertTrue(any("verify_false" in f for f in sz.S["fails"]))



class T1013CloneScratchTest(Base):
    """ALL_T1013 K13: the clone's own fs is a scratch candidate."""

    def setUp(self):
        super().setUp()
        self.out = []
        p = mock.patch.object(sz, "say", side_effect=self.out.append)
        p.start()
        self.addCleanup(p.stop)
        self.ms = os.path.join(self.tmp, "vol", "ms_dlp")
        os.makedirs(self.ms)
        for k, v in (("MS_DLP", self.ms), ("CLONE_SCRATCH", os.path.join(
                self.ms, "bora_zombie_scratch")), ("TMP_ROOT", None)):
            p = mock.patch.object(sz, k, v)
            p.start()
            self.addCleanup(p.stop)

    def _pick(self, mounts, free, dev):
        """mounts: list of mount roots; free: path -> GiB or None (not
        writable); dev: path -> st_dev."""
        with mock.patch.object(rz, "_candidate_mounts", lambda: mounts), \
                mock.patch.object(rz, "_writable_free_gb", free.get), \
                mock.patch.object(sz, "_fs_dev", dev.get):
            return sz.pick_scratch()

    def test_clone_fs_picked_when_roomiest(self):
        got = self._pick(["/", "/data"], {"/": 40, "/data": 300,
                                          self.ms: 3000},
                         {"/": 1, "/data": 2, self.ms: 3})
        self.assertEqual(got, sz.CLONE_SCRATCH)
        self.assertEqual(sz.scratch_src(got), "clone")
        self.assertTrue(any("(the clone's fs)" in m for m in self.out))

    def test_unwritable_mount_root_skipped_clone_used(self):
        vol = "/media/volume/v1"
        got = self._pick(["/", vol], {"/": None, vol: None, self.ms: 900},
                         {"/": 1, vol: 7, self.ms: 7})
        self.assertEqual(got, sz.CLONE_SCRATCH)

    def test_same_fs_counts_once_clone_first(self):
        # ALL_T1013 K15: K14 binds /tmp/bora and /tmp/bora_zombie_par from the
        # clone's fs; the clone dir stands for that fs, a bigger disk wins
        vol, b1, b2 = "/media/volume/v1", "/tmp/bora", "/tmp/bora_zombie_par"
        seen = []
        free = {"/": 40, vol: 900, b1: 900, b2: 900, self.ms: 900}

        def wf(p):
            seen.append(p)
            return free.get(p)
        with mock.patch.object(rz, "_candidate_mounts",
                               lambda: ["/", vol, b1, b2]), \
                mock.patch.object(rz, "_writable_free_gb", wf), \
                mock.patch.object(sz, "_fs_dev", {"/": 1, vol: 7, b1: 7,
                                                  b2: 7, self.ms: 7}.get):
            got = sz.pick_scratch()
        self.assertEqual(got, sz.CLONE_SCRATCH)
        self.assertEqual(seen, [self.ms, "/"])      # same fs probed once
        got = self._pick(["/", "/big", b2], {"/": 40, "/big": 2000, b2: 900,
                                             self.ms: 900},
                         {"/": 1, "/big": 9, b2: 7, self.ms: 7})
        self.assertEqual(got, "/big/bora_zombie_scratch")

    def test_reclaim_bind_mount_point_keeps_mount(self):
        # F5 empties a dead run's PAR_ROOT even when it is a mount point;
        # rmdir of the mount point itself fails and is ignored
        par = os.path.join(self.tmp, "par")
        os.makedirs(os.path.join(par, "c00001"))
        real = shutil.rmtree

        def rm(p, ignore_errors=False):
            for n in os.listdir(p):
                real(os.path.join(p, n))
            if not ignore_errors:
                raise OSError(16, "busy")
        with mock.patch.object(rz, "PAR_ROOT", par), \
                mock.patch.object(rz, "_candidate_mounts", lambda: []), \
                mock.patch.object(sz.shutil, "rmtree", rm):
            sz.reclaim_scratch()
        self.assertEqual(os.listdir(par), [])

    def test_small_disks_fall_back_to_par_root(self):
        got = self._pick(["/"], {"/": 40, self.ms: 50},
                         {"/": 1, self.ms: 1})
        self.assertEqual(got, rz.PAR_ROOT)

    def test_redirect_respected(self):
        with mock.patch.object(sz, "TMP_ROOT", self.tmp):
            got = self._pick(["/"], {"/": 4000, self.ms: 4000},
                             {"/": 1, self.ms: 2})
        self.assertEqual(got, rz.PAR_ROOT)

    def test_reclaim_covers_the_clone_dir(self):
        d = os.path.join(sz.CLONE_SCRATCH, "c00001")
        os.makedirs(d)
        with mock.patch.object(rz, "PAR_ROOT", os.path.join(self.tmp, "p")), \
                mock.patch.object(rz, "_candidate_mounts", lambda: []):
            sz.reclaim_scratch()
        self.assertFalse(os.path.exists(sz.CLONE_SCRATCH))
        with mock.patch.object(sz, "TMP_ROOT", self.tmp):
            os.makedirs(d)
            sz.reclaim_scratch()
        self.assertTrue(os.path.isdir(d))         # redirect: PAR_ROOT only

    def test_hook_installed_at_import_without_redirect(self):
        src = open(sz.SELF_PATH).read()
        self.assertIn("rz._pick_scratch_base = pick_scratch", src)
        self.assertIn("bora_zombie_scratch/", open(os.path.join(
            os.path.dirname(sz.SELF_PATH), "..", ".gitignore")).read())



class T1013FaultFixTest(StubSetup):
    """ALL_T1013 K16: r4_faults.md FI1 to FI5."""

    def _pair(self):
        return sz.Pair(os.path.join(self.tmp, "a.jsonl"),
                       os.path.join(self.tmp, "b.jsonl"))

    def test_append_after_a_torn_fragment_starts_a_new_line(self):
        p = self._pair()
        for f in (p.tmp, p.docs):
            open(f, "w").write('{"kind": "base"}\n{"kind": "pro')
        p.append([{"kind": "stop", "size": 2000}])
        lines = open(p.tmp).read().splitlines()
        self.assertEqual(lines[1], '{"kind": "pro')
        self.assertEqual(json.loads(lines[2]), {"kind": "stop", "size": 2000})
        open(p.tmp, "w").write("")
        p.append([{"k": 1}])                     # empty file: no blank line
        self.assertEqual(open(p.tmp).read(), '{"k": 1}\n')

    def test_load_skips_a_bad_middle_line_when_the_other_copy_exists(self):
        p = self._pair()
        open(p.tmp, "w").write('{"a": 1}\n{"b": \n{"c": 3}\n')
        open(p.docs, "w").write('{"a": 1}\n{"c": 3}\n')
        out = []
        with mock.patch.object(sz, "say", side_effect=out.append):
            self.assertEqual(p.load(), [{"a": 1}, {"c": 3}])
        self.assertTrue(any("1 bad middle line(s)" in m for m in out))
        os.remove(p.docs)
        with self.assertRaises(ValueError):
            p.load()

    def test_restore_takes_docs_when_it_has_more_valid_rows(self):
        p = self._pair()
        open(p.tmp, "w").write('{"a": 1}\n{"b": 2')
        open(p.docs, "w").write('{"a": 1}\n{"b": 2}\n{"c": 3}\n')
        p.restore()
        self.assertEqual(open(p.tmp).read(), open(p.docs).read())
        open(p.docs, "w").write('{"a": 1}\n')
        p.restore()                               # /tmp has more: kept
        self.assertEqual(len(p.load()), 3)

    def test_gate_reference_resource_death_retried_once(self):
        t = self.tasks(units=("ua",))[0]
        seq = [("resource", None), ("ok", {"prove_ms": 300}),
               ("ok", {"prove_ms": 301})]
        with mock.patch.object(sz, "run_one_serial",
                               lambda t, mode: seq.pop(0)), \
                mock.patch.object(sz, "say"):
            ref, s = sz.serial_reference([t])
        self.assertEqual(ref[id(t)], 300.5)
        seq = [("resource", None), ("resource", None)]
        with mock.patch.object(sz, "run_one_serial",
                               lambda t, mode: seq.pop(0)), \
                mock.patch.object(sz, "say"):
            self.assertEqual(sz.serial_reference([t]), (None, None))

    def test_ref_stop_has_cause_ref_and_is_lifted_once(self):
        sz.S["cap"] = 16
        sz.S["topo"] = fake_topo(cores=36)
        sz.ARGS.sizes = [1000, 2000]
        with mock.patch.object(sz, "serial_reference",
                               return_value=(None, None)):
            sz.S["pending"][:] = []
            ts = self.tasks(size=2000)
            with self.assertRaises(sz.StopFlush) as cm:
                sz.run_subflush(2000, 16, ts)
        self.assertEqual(cm.exception.cause, "ref")
        sz.stop_path(2000, str(cm.exception), [], cm.exception.width,
                     cause=cm.exception.cause)
        rows = sz.S["pair"].load()
        stop = [r for r in rows if r["kind"] == "stop"][-1]
        self.assertEqual(stop["cause"], "ref")
        a = sz.parse_args(["--sizes", "1000,2000", "--server", "t1"])
        sc = {"w0": "4", "commit": "c"}
        with mock.patch.object(sz, "read_scalecal", return_value=sc), \
                mock.patch.object(sz, "valid_timing",
                                  return_value=(True, None)), \
                mock.patch.object(sz, "print_stamp_view"):
            sz.start_check(a, rows)
            self.assertNotIn(2000, sz.S["refused"])          # lifted once
            sz.start_check(a, rows + [dict(stop)])
            self.assertIn(2000, sz.S["refused"])             # second: kept

    def test_serial_batch_killed_base_prove_rerun_once(self):
        calls = []
        recs = [({"status": "oom_or_killed"}, None),
                ({"status": "ok"}, {"base_uuid": "u2"})]

        def bt(*a, **k):
            calls.append(1)
            return recs.pop(0)
        sz.S["last_batch_n"] = 1
        sz.ARGS.sizes = []
        with mock.patch.object(sz, "base_time", bt), \
                mock.patch.object(sz, "say"):
            rec = sz.time_one("b", {"name": "u", "dir": "/d"}, 1000)
        self.assertEqual((rec["status"], len(calls)), ("ok", 2))
        sz.S["last_batch_n"] = 4                  # RZ requeues these itself
        recs[:] = [({"status": "oom_or_killed"}, None)]
        calls[:] = []
        with mock.patch.object(sz, "base_time", bt):
            sz.time_one("b", {"name": "u", "dir": "/d"}, 1000)
        self.assertEqual(len(calls), 1)

    def test_relaunch_retries_every_resource_class_once(self):
        self.assertEqual(set(sz.RETRY_ONCE), set(rz.RESOURCE_FAIL))


if __name__ == "__main__":
    unittest.main()
