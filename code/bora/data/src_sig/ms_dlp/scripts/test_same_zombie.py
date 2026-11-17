# DLP_T1001: unit and stub-prover smoke tests for same_zombie.py
import os
import sys
import json
import shutil
import signal
import tempfile
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
    if os.environ.get("RAYON_NUM_THREADS") and os.environ.get("STUB_SLOW"):
        ms = int(ms * float(os.environ["STUB_SLOW"]))
    time.sleep(ms / 1000.0)
    print("policy%d circuit constraints cons %s inputs 1 vars 1"
          % (n, os.environ.get("STUB_CONS", "70000")))
    print("prove takes %d" % ms)
    print("proof size is 10 bytes")
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
        self.assertEqual(sz.S["w_state"][2000], 4)
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
        self.assertEqual(cm.exception.width, 2)    # the width that failed
        rows = sz.S["pair"].load()
        self.assertEqual([r["verdict"] for r in rows if r["kind"] == "gate"],
                         ["fail", "fail"])
        self.assertEqual([r["width"] for r in rows if r["kind"] == "width"],
                         [2])
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
        self.assertEqual(sz.scalecal_widths(t16, 16), [1, 2, 4, 8, 16])
        self.assertEqual(sz.scalecal_widths(t16, 4), [1, 2, 4])
        self.assertEqual(sz.scalecal_widths(t16, 0), [1, 2, 4])
        self.assertEqual(sz.scalecal_widths(fake_topo(cores=4), 16), [1, 2, 4])
        self.assertEqual(sz.scalecal_widths(fake_topo(cores=124), 16),
                         [1, 2, 4, 8, 16])

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
        self.assertEqual(tried, [1, 2, 4, 8, 16])
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
        # resume: 2000 stays refused (no re-keygen), check-start only warns
        sz.S["topo"] = fake_topo(cores=36)
        a = sz.parse_args(["--sizes", "1000,2000", "--server", "t1"])
        sc = {"w0": "4", "commit": "c"}
        with mock.patch.object(sz, "read_scalecal", return_value=sc), \
                mock.patch.object(sz, "valid_timing",
                                  return_value=(True, None)), \
                mock.patch.object(sz, "print_stamp_view"):
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
        with open(sweep.docs, "w") as f:
            f.write("{}\n")
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
            self.assertEqual(sz.S["w_state"][4000], 8)


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


if __name__ == "__main__":
    unittest.main()
