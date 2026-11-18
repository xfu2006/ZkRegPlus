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
        self.assertIn("could not enable Linger for u (rc 1)", IN._LINGER_WARN)
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


if __name__ == "__main__":
    unittest.main()
