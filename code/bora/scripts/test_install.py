# ALL_T1009: unit tests for INSTALL.py's Linger step (no host change).
import os
import sys
import subprocess
import unittest
import importlib.util
from unittest import mock

HERE = os.path.dirname(os.path.abspath(__file__))
_spec = importlib.util.spec_from_file_location(
    "install_t1009", os.path.join(HERE, "INSTALL.py"))
IN = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(IN)


PLAIN = ["loginctl", "--no-ask-password", "enable-linger", "u"]


class LingerTest(unittest.TestCase):
    """ALL_T1009 A5b: enable-linger by default, warn-only, --skip-linger."""

    def setUp(self):
        p = mock.patch.multiple(IN, _SKIP_LINGER=False, _LINGER_WARN="",
                                _LINGER_DONE=False)
        p.start()
        self.addCleanup(p.stop)
        self.calls = []

    def _run(self, linger_after, rc=0, euid=1000, works=("loginctl",)):
        state = {"on": False}

        def run(cmd, **k):
            self.calls.append(cmd)
            if cmd[:2] == ["loginctl", "show-user"]:
                return subprocess.CompletedProcess(cmd, 0, stdout=(
                    "Linger=yes\n" if state["on"] else "Linger=no\n"))
            if cmd[0] in works:
                state["on"] = linger_after
            return subprocess.CompletedProcess(cmd, rc)
        with mock.patch.object(IN.subprocess, "run", run), \
             mock.patch.object(IN.os, "geteuid", return_value=euid), \
             mock.patch.object(IN, "_linger_user", return_value="u"), \
             mock.patch("builtins.print"):
            IN.enable_linger()

    def test_enable_linger_success_probe(self):
        self._run(True)
        self.assertIn(PLAIN, self.calls)
        self.assertNotIn(["sudo", "-n", "loginctl", "enable-linger", "u"],
                         self.calls)       # ALL_T1009: plain loginctl first
        self.assertEqual(IN._LINGER_WARN, "")

    def test_plain_fails_then_sudo(self):
        self._run(True, works=("sudo",))
        self.assertEqual([c for c in self.calls if "enable-linger" in c],
                         [PLAIN,
                          ["sudo", "-n", "loginctl", "enable-linger", "u"]])
        self.assertEqual(IN._LINGER_WARN, "")

    def test_plain_attempt_never_prompts(self):
        self._run(False, rc=1)
        plain = [c for c in self.calls
                 if c[0] == "loginctl" and "enable-linger" in c]
        self.assertTrue(plain)
        self.assertTrue(all("--no-ask-password" in c for c in plain))

    def test_enable_linger_runs_once(self):
        self._run(False, rc=1)
        n = len(self.calls)
        self._run(False, rc=1)
        self.assertEqual(len(self.calls), n)

    def test_enable_linger_warn_only_on_failure(self):
        self._run(False, rc=1)
        self.assertIn("could not enable Linger for u (rc 1", IN._LINGER_WARN)
        self.assertIn("--skip-linger", IN._LINGER_WARN)

    def test_skip_linger_flag(self):
        IN._SKIP_LINGER = True
        self._run(True)
        self.assertEqual(self.calls, [])
        with mock.patch.object(sys, "argv", ["INSTALL.py", "--skip-linger",
                                             "--verify"]), \
             mock.patch.object(IN, "restore_bigfiles"), \
             mock.patch.object(IN, "verify_installed", return_value=0):
            with self.assertRaises(SystemExit):
                IN.main()
        self.assertTrue(IN._SKIP_LINGER)

    def test_enable_linger_uses_sudo_user_as_root(self):
        self._run(True, euid=0)
        self.assertIn(PLAIN, self.calls)
        with mock.patch.object(IN.os, "geteuid", return_value=0), \
             mock.patch.dict(os.environ, {"SUDO_USER": "owner"}):
            self.assertEqual(IN._linger_user(), "owner")

    def test_already_on_runs_nothing(self):
        def run(cmd, **k):
            self.calls.append(cmd)
            return subprocess.CompletedProcess(cmd, 0, stdout="Linger=yes\n")
        with mock.patch.object(IN.subprocess, "run", run), \
             mock.patch.object(IN, "_linger_user", return_value="u"), \
             mock.patch("builtins.print"):
            IN.enable_linger()
        self.assertEqual(len(self.calls), 1)


class PrebuildTest(unittest.TestCase):
    """ALL_T1013 S9: INSTALL prebuilds circ through same_zombie --build-only."""

    def setUp(self):
        p = mock.patch.multiple(IN, _SKIP_ZOMBIE_BUILD=False)
        p.start()
        self.addCleanup(p.stop)
        self.calls, self.out = [], []

    def _run(self, rc=0, euid=1000, exc=None):
        def run(cmd, **k):
            self.calls.append((cmd, k))
            if exc:
                raise exc
            return subprocess.CompletedProcess(cmd, rc)
        with mock.patch.object(IN.subprocess, "run", run), \
             mock.patch.object(IN.os, "geteuid", return_value=euid), \
             mock.patch("builtins.print",
                        lambda *a, **k: self.out.append(" ".join(map(str, a)))):
            IN.prebuild_zombie_circ()

    def test_calls_build_only_with_cargo_path(self):
        self._run()
        (cmd, k), = self.calls
        self.assertEqual(cmd[1:], ["-I", IN.ZOMBIE_SAME, "--build-only"])
        self.assertTrue(k["env"]["PATH"].startswith(
            os.path.expanduser("~/.cargo/bin") + os.pathsep))
        self.assertFalse(any("WARN" in m for m in self.out))

    def test_failure_only_warns(self):
        self._run(rc=7)
        self.assertTrue(any("WARN: circ_executable not prebuilt (rc 7)" in m
                            for m in self.out))
        self._run(exc=OSError("no python"))
        self.assertTrue(any("no python" in m for m in self.out))

    def test_root_and_flag_skip(self):
        self._run(euid=0)
        self.assertEqual(self.calls, [])
        IN._SKIP_ZOMBIE_BUILD = True
        self._run()
        self.assertEqual(self.calls, [])
        self.assertTrue(any("--skip-zombie-build" in m for m in self.out))

    def test_kept_tree_branch_prebuilds(self):
        seen = []
        with mock.patch.object(IN, "check_zombie_dep_drift", lambda: None), \
             mock.patch.object(IN.os.path, "isdir", return_value=True), \
             mock.patch.multiple(IN, _FORCE_ZOMBIE=False), \
             mock.patch.object(IN, "zombie_commit", return_value="c"), \
             mock.patch.object(IN, "run_cmd_in",
                               lambda argv, cwd: seen.append(argv)), \
             mock.patch.object(IN, "prebuild_zombie_circ",
                               lambda: seen.append("prebuild")), \
             mock.patch("builtins.print"):
            IN.install_dataset_zombie()
        self.assertEqual(seen[-1], "prebuild")
        self.assertIn("--patch-only", seen[0])

    def test_flag_parsed(self):
        self.assertIn("--skip-zombie-build", open(IN.__file__).read())



class TmpBindTest(unittest.TestCase):
    """ALL_T1013 K15: small /tmp, bind /tmp/bora_install and
    /tmp/bora_zombie_circ from the clone's disk; warn-only."""

    def setUp(self):
        import tempfile
        self.d = tempfile.mkdtemp(prefix="in_k15_")
        self.addCleanup(lambda: __import__("shutil").rmtree(
            self.d, ignore_errors=True))
        self.tmp = os.path.join(self.d, "tmp")
        self.root = os.path.join(self.d, "clone")
        os.makedirs(self.tmp)
        os.makedirs(self.root)
        self.out = []
        p = mock.patch.object(IN, "sudo_status", return_value=None)  # K14d
        p.start()
        self.addCleanup(p.stop)

    def _trig(self, same, ft, fr, mounted=(), srcs=()):
        dev = {self.tmp: 1, self.root: 1 if same else 2}
        st = lambda p: mock.Mock(st_dev=dev[p])
        with mock.patch.object(IN.os, "stat", st), \
             mock.patch.object(IN.os.path, "isdir",
                               lambda p: os.path.basename(p) in srcs), \
             mock.patch.object(IN, "_free_gib",
                               lambda p: ft if p == self.tmp else fr), \
             mock.patch.object(IN.os.path, "ismount",
                               lambda p: os.path.basename(p) in mounted):
            return IN.tmp_bind_names(self.root, self.tmp)

    def test_trigger_rule(self):
        both = ["bora_install", "bora_zombie_circ"]
        self.assertEqual(self._trig(False, 40, 900), both)
        self.assertEqual(self._trig(True, 40, 900), [])          # same fs
        self.assertEqual(self._trig(False, 300, 900), [])        # big /tmp
        self.assertEqual(self._trig(False, 40, 30), [])          # clone smaller
        self.assertEqual(self._trig(False, 40, 900, ("bora_install",)),
                         ["bora_zombie_circ"])                    # mounted
        # K15b M4: an existing .bora_tmp/<name> binds whatever the space
        self.assertEqual(self._trig(False, 300, 900,
                                    srcs=("bora_zombie_circ",)),
                         ["bora_zombie_circ"])
        self.assertEqual(self._trig(True, 40, 900, srcs=("bora_install",)),
                         [])                                      # same fs

    def test_no_sudo_warns_with_cause_and_fix(self):
        """ALL_T1013 K14d: missing passwordless sudo is named, with the
        sudoers fix and the by-hand commands; nothing is mounted."""
        prints, calls = [], []
        with mock.patch.object(IN, "sudo_status",
                               return_value="sudo: a password is required"), \
             mock.patch.object(IN, "_git_root", return_value=self.root), \
             mock.patch.object(IN, "tmp_bind_names",
                               return_value=["bora_install"]), \
             mock.patch.object(IN, "_free_gib", return_value=5.0), \
             mock.patch.object(IN.subprocess, "run",
                               lambda c, **k: calls.append(c)), \
             mock.patch.object(IN.os, "geteuid", return_value=1000), \
             mock.patch.object(IN, "_zombie_driver_live", return_value=False), \
             mock.patch.object(IN, "PD_RUN_LOCK",
                               os.path.join(self.d, "none.lock")), \
             mock.patch("builtins.print",
                        lambda *a, **k: prints.append(" ".join(map(str, a)))):
            why = IN.install_tmp_bind(self.tmp)
        text = "\n".join(prints)
        self.assertIn("WARN: passwordless sudo is not available", text)
        self.assertIn("a password is required", why)
        self.assertIn("NOPASSWD:ALL", text)
        self.assertIn("visudo -cf", text)
        self.assertIn("sudo mount --bind", text)
        self.assertIn("the install goes on", text)
        self.assertEqual(calls, [])

    def test_mount_failure_warns_with_hand_commands(self):
        def run(cmd, **k):
            self.out.append(cmd)
            return subprocess.CompletedProcess(cmd, 1, stdout="",
                                               stderr="sudo: a password is "
                                               "required")
        prints = []
        with mock.patch.object(IN, "_git_root", return_value=self.root), \
             mock.patch.object(IN, "tmp_bind_names",
                               return_value=["bora_install",
                                             "bora_zombie_circ"]), \
             mock.patch.object(IN, "_free_gib", return_value=5.0), \
             mock.patch.object(IN.subprocess, "run", run), \
             mock.patch.object(IN.os, "geteuid", return_value=1000), \
             mock.patch.object(IN, "_zombie_driver_live", return_value=False), \
             mock.patch.object(IN, "PD_RUN_LOCK",
                               os.path.join(self.d, "none.lock")), \
             mock.patch("builtins.print",
                        lambda *a, **k: prints.append(" ".join(map(str, a)))):
            why = IN.install_tmp_bind(self.tmp)
        self.assertIn("password is required", why)
        self.assertEqual(self.out[0][:4], ["sudo", "-n", "mount", "--bind"])
        text = "\n".join(prints)
        src = os.path.join(self.root, ".bora_tmp", "bora_install")
        dst = os.path.join(self.tmp, "bora_install")
        self.assertIn("rsync -a --ignore-existing %s/ %s/ && sudo mount "
                      "--bind %s %s" % (dst, src, src, dst), text)   # M6
        self.assertIn("install goes on", text)
        self.assertIn("only 5.0 GiB free", text)

    def test_mount_success_is_verified(self):
        mounted = set()

        def run(cmd, **k):
            if "mount" in cmd:
                mounted.add(cmd[-1])
            return subprocess.CompletedProcess(cmd, 0, stdout="", stderr="")
        real_ismount = os.path.ismount
        os.makedirs(os.path.join(self.tmp, "bora_install"))
        open(os.path.join(self.tmp, "bora_install", "old"), "w").write("x")
        with mock.patch.object(IN.subprocess, "run", run), \
             mock.patch.object(IN.os.path, "ismount",
                               lambda p: p in mounted or real_ismount(p)), \
             mock.patch.object(IN.os, "geteuid", return_value=1000), \
             mock.patch.object(IN, "_dir_users", return_value=[]):
            why = IN.bind_tmp_dirs(["bora_install", "bora_zombie_circ"],
                                   self.root, True, self.out.append, self.tmp)
        self.assertIsNone(why)
        self.assertEqual(mounted, {os.path.join(self.tmp, n) for n in
                                   ("bora_install", "bora_zombie_circ")})
        self.assertTrue(any("copying the contents" in m for m in self.out))
        self.assertTrue(any("is now on" in m for m in self.out))
        self.assertFalse(os.path.exists(os.path.join(
            self.tmp, "bora_install", ".bora_tmp_probe")))

    def test_copy_never_replaces_a_source_file(self):
        # K15b R4: the source copy wins; only missing files are added
        src = os.path.join(self.root, ".bora_tmp", "bora_install")
        dst = os.path.join(self.tmp, "bora_install")
        os.makedirs(src)
        os.makedirs(dst)
        open(os.path.join(src, "part"), "w").write("new 3 rows")
        open(os.path.join(dst, "part"), "w").write("old 1 row")
        open(os.path.join(dst, "extra"), "w").write("e")
        real = subprocess.run
        calls = []

        def run(cmd, **k):
            calls.append(cmd)
            if cmd[0] in ("rsync", "cp"):
                return real(cmd, **k)
            return subprocess.CompletedProcess(cmd, 1, "", "no mount here")
        with mock.patch.object(IN.subprocess, "run", run), \
             mock.patch.object(IN, "_dir_users", return_value=[]):
            why = IN.bind_tmp_dirs(["bora_install"], self.root, True,
                                   self.out.append, self.tmp)
        self.assertIn("could not be bind-mounted", why)
        self.assertIn("--ignore-existing", calls[0])
        self.assertEqual(open(os.path.join(src, "part")).read(), "new 3 rows")
        self.assertTrue(os.path.isfile(os.path.join(src, "extra")))

    def test_symlink_target_refused(self):
        # K15b R1
        os.makedirs(os.path.join(self.d, "elsewhere"))
        os.symlink(os.path.join(self.d, "elsewhere"),
                   os.path.join(self.tmp, "bora_zombie_circ"))
        with mock.patch.object(IN.subprocess, "run") as run:
            why = IN.bind_tmp_dirs(["bora_zombie_circ"], self.root, True,
                                   self.out.append, self.tmp)
        self.assertIn("is a symlink", why)
        run.assert_not_called()

    def test_unwritable_after_mount_refused(self):
        # K15b R3: a read-only source fails the probe write
        mounted = set()

        def run(cmd, **k):
            mounted.add(cmd[-1])
            return subprocess.CompletedProcess(cmd, 0, "", "")
        real_open = open

        def ro_open(p, *a, **k):
            if str(p).endswith(".bora_tmp_probe"):
                raise OSError(30, "Read-only file system")
            return real_open(p, *a, **k)
        real_ismount = os.path.ismount
        with mock.patch.object(IN.subprocess, "run", run), \
             mock.patch.object(IN.os.path, "ismount",
                               lambda p: p in mounted or real_ismount(p)), \
             mock.patch.object(IN, "_dir_users", return_value=[]), \
             mock.patch("builtins.open", ro_open):
            why = IN.bind_tmp_dirs(["bora_install"], self.root, True,
                                   self.out.append, self.tmp)
        self.assertIn("not writable", why)

    def test_held_run_lock_refuses_and_open_error_is_clean(self):
        # K15b W1 and M1
        import fcntl
        lk = os.path.join(self.d, "PAPER_DATA.lock")
        fd = os.open(lk, os.O_RDWR | os.O_CREAT, 0o644)
        try:
            fcntl.flock(fd, fcntl.LOCK_EX)
            with mock.patch.object(IN.subprocess, "run") as run:
                why = IN.bind_tmp_dirs(["bora_install"], self.root, True,
                                       self.out.append, self.tmp, lk)
            self.assertIn("held by a running PAPER_DATA.py", why)
            run.assert_not_called()
        finally:
            os.close(fd)
        os.chmod(lk, 0)
        try:
            if os.geteuid() != 0:
                why = IN.bind_tmp_dirs(["bora_install"], self.root, True,
                                       self.out.append, self.tmp, lk)
                self.assertIn("cannot open", why)
        finally:
            os.chmod(lk, 0o644)

    def test_dir_users_counts_cwd_exe_and_write_fds_only(self):
        # K15b R2 and M7, with real children
        d = os.path.join(self.tmp, "bora_zombie_circ")
        os.makedirs(d)
        f = os.path.join(d, "log")
        open(f, "w").write("x")
        exe = os.path.join(d, "zz_k15b_sleep")
        __import__("shutil").copy("/bin/sleep", exe)
        reader = subprocess.Popen([sys.executable, "-c",
                                   "import time; f = open(%r); time.sleep(30)"
                                   % f], cwd=self.d)
        writer = subprocess.Popen([sys.executable, "-c",
                                   "import time; f = open(%r, 'a'); "
                                   "time.sleep(30)" % f], cwd=self.d)
        runner = subprocess.Popen([exe, "30"], cwd=self.d)
        try:
            import time
            time.sleep(0.5)
            got = IN._dir_users(d)
            self.assertNotIn(reader.pid, got)
            self.assertIn(writer.pid, got)
            self.assertIn(runner.pid, got)
        finally:
            for p in (reader, writer, runner):
                p.kill()
                p.wait()

    def test_root_and_live_driver_skip(self):
        # K15b R5 and M7: never root-owned sources, never beside a driver
        prints = []
        for euid, live in ((0, False), (1000, True)):
            with mock.patch.object(IN, "_git_root", return_value=self.root), \
                 mock.patch.object(IN, "tmp_bind_names",
                                   return_value=["bora_install"]), \
                 mock.patch.object(IN.os, "geteuid", return_value=euid), \
                 mock.patch.object(IN, "_zombie_driver_live",
                                   return_value=live), \
                 mock.patch.object(IN, "bind_tmp_dirs") as b, \
                 mock.patch("builtins.print",
                            lambda *a, **k: prints.append(" ".join(a))):
                self.assertIsNone(IN.install_tmp_bind(self.tmp))
            b.assert_not_called()
        self.assertTrue(any("running as root" in m for m in prints))
        self.assertTrue(any("Zombie driver runs" in m for m in prints))

    def test_busy_target_refuses_before_mount(self):
        os.makedirs(os.path.join(self.tmp, "bora_install"))
        calls = []
        with mock.patch.object(IN, "_dir_users", return_value=[4242]), \
             mock.patch.object(IN.subprocess, "run",
                               lambda cmd, **k: calls.append(cmd)):
            why = IN.bind_tmp_dirs(["bora_install"], self.root, True,
                                   self.out.append, self.tmp)
        self.assertIn("in use by pid [4242]", why)
        self.assertEqual(calls, [])

    def test_same_fs_does_nothing(self):
        with mock.patch.object(IN, "_git_root", return_value=self.root), \
             mock.patch.object(IN, "bind_tmp_dirs") as b:
            self.assertIsNone(IN.install_tmp_bind(self.tmp))
        b.assert_not_called()

    def test_runs_first_and_covers_the_circ_build(self):
        src = open(IN.__file__).read()
        self.assertIn('"bora_zombie_circ"', src.split("TMP_BIND_NAMES = ")[1]
                      .split("\n")[0])
        main = src[src.index("def main():"):]
        self.assertLess(main.index("install_tmp_bind()"),
                        main.index("ensure_toolchain(selected)"))
        self.assertIn("if not args.verify:\n        install_tmp_bind()", main)


if __name__ == "__main__":
    unittest.main()
