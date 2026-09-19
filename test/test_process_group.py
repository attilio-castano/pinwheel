"""Timeout cleanup uses disposable Python children, never Lean or CAD tools."""
import ctypes
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import time
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
import process_group


@unittest.skipUnless(os.name == "posix", "Process-group runner targets POSIX hosts")
class GroupLivenessTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.proc = Path(self.tmp.name)
        self.group = 1234
        self.member("self", "S", group=os.getpgrp(), record_pid=os.getpid())
        (self.proc / "self/mountinfo").write_text(f"1 0 0:1 / {self.proc} rw - proc proc rw\n")
        for change in (patch.object(process_group, "_PROC", self.proc),
                       patch.object(process_group.sys, "platform", "linux"),
                       patch.object(process_group.os, "killpg", return_value=None)):
            change.start()
            self.addCleanup(change.stop)

    def member(self, pid, state, group=None, threads=1, record_pid=None):
        folder = self.proc / str(pid)
        folder.mkdir(exist_ok=True)
        # The comm field can contain both whitespace and closing parentheses.
        fields = [state, "1", str(self.group if group is None else group), *("0" for _ in range(14)), str(threads)]
        (folder / "stat").write_text(f"{pid if record_pid is None else record_pid} (fixture ) name) {' '.join(fields)}\n")

    def test_zombies_and_dead_members_do_not_keep_a_group_alive(self):
        self.member(10, "Z")
        self.member(11, "X")
        self.member(12, "x")
        self.member(13, "R", group=9999)
        self.assertIs(process_group._group_alive(self.group), False)

    def test_every_nonterminal_state_keeps_a_group_alive(self):
        self.member(10, "Z")
        for state in ("R", "S", "D", "T", "t", "W", "K", "P", "I"):
            with self.subTest(state=state):
                self.member(11, state)
                self.assertIs(process_group._group_alive(self.group), True)

    def test_missing_or_hidden_members_are_unknown(self):
        self.member(10, "Z", group=9999)
        self.assertIsNone(process_group._group_alive(self.group))

    def test_restricted_or_unidentified_proc_mount_is_unknown(self):
        self.member(10, "Z")
        for mount in ("", f"1 0 0:1 / {self.proc} rw - proc proc rw,hidepid=2\n",
                      f"1 0 0:1 / {self.proc} rw,hidepid=1 - proc proc rw\n",
                      f"1 0 0:1 / {self.proc} rw - tmpfs tmpfs rw\n"):
            with self.subTest(mount=mount):
                (self.proc / "self/mountinfo").write_text(mount)
                self.assertIsNone(process_group._group_alive(self.group))

    def test_incompatible_pid_view_is_unknown(self):
        self.member(10, "Z")
        self.member("self", "S", group=os.getpgrp(), record_pid=os.getpid() + 1)
        self.assertIsNone(process_group._group_alive(self.group))

    def test_zombie_leader_with_other_threads_is_not_confirmed(self):
        self.member(10, "Z", threads=2)
        self.assertIsNone(process_group._group_alive(self.group))

    def test_vanished_member_does_not_invalidate_observed_zombies(self):
        self.member(10, "Z")
        (self.proc / "11").mkdir()  # stat disappeared after directory enumeration.
        self.assertIs(process_group._group_alive(self.group), False)

    def test_vanished_members_alone_do_not_confirm_termination(self):
        (self.proc / "10").mkdir()
        self.assertIsNone(process_group._group_alive(self.group))

    def test_unreadable_member_is_unknown(self):
        self.member(10, "Z")
        read_text = Path.read_text

        def read(path, *args, **kwargs):
            if path == self.proc / "10/stat":
                raise PermissionError("Member state is inaccessible")
            return read_text(path, *args, **kwargs)

        with patch.object(Path, "read_text", read):
            self.assertIsNone(process_group._group_alive(self.group))

    def test_unreadable_process_table_is_unknown(self):
        with patch.object(Path, "iterdir", side_effect=PermissionError):
            self.assertIsNone(process_group._group_alive(self.group))

    def test_malformed_or_unknown_state_is_unknown(self):
        self.member(10, "Z")
        self.member(11, "?")
        self.assertIsNone(process_group._group_alive(self.group))
        for text in ("truncated", "11 (fixture) Z 1 invalid", "11 (fixture) Z"):
            with self.subTest(record=text):
                (self.proc / "11/stat").write_text(text)
                self.assertIsNone(process_group._group_alive(self.group))

    def test_absent_group_is_terminated(self):
        with patch.object(process_group.os, "killpg", side_effect=ProcessLookupError):
            self.assertIs(process_group._group_alive(self.group), False)

    def test_probe_failure_is_unknown(self):
        for error in (PermissionError, OSError):
            with self.subTest(error=error), patch.object(process_group.os, "killpg", side_effect=error):
                self.assertIsNone(process_group._group_alive(self.group))

    def test_other_hosts_require_group_disappearance(self):
        with patch.object(process_group.sys, "platform", "darwin"):
            self.assertIsNone(process_group._group_alive(self.group))
            with patch.object(process_group.os, "killpg", side_effect=ProcessLookupError):
                self.assertIs(process_group._group_alive(self.group), False)


@unittest.skipUnless(os.name == "posix", "Process-group runner targets POSIX hosts")
class ProcessGroupTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.log = self.root / "command.log"
        if sys.platform == "linux":
            # Only the test fixture adopts orphans. Hold killed descendants as
            # zombies until assertions finish, then reap our named fixtures;
            # never rely on the container's PID 1 and never change production
            # process_group's ownership policy.
            libc = ctypes.CDLL(None, use_errno=True)
            libc.prctl.argtypes = [ctypes.c_int, *([ctypes.c_ulong] * 4)]
            libc.prctl.restype = ctypes.c_int

            def prctl(option, argument):
                if libc.prctl(option, argument, 0, 0, 0) != 0:
                    error = ctypes.get_errno()
                    raise OSError(error, os.strerror(error))

            previous = ctypes.c_int()
            prctl(37, ctypes.addressof(previous))  # PR_GET_CHILD_SUBREAPER
            prctl(36, 1)  # PR_SET_CHILD_SUBREAPER
            self.addCleanup(prctl, 36, previous.value)

    def assert_descendant_terminated(self, pid):
        if sys.platform == "linux":
            # An independent observation: the fixture deliberately has not
            # waited on its adopted child yet, so it must still be a zombie.
            state = Path(f"/proc/{pid}/stat").read_text().rpartition(") ")[2].split()[0]
            self.assertEqual(state, "Z")
        else:
            with self.assertRaises(ProcessLookupError):
                os.kill(pid, 0)

    def clean_fixture(self, pid):
        if sys.platform != "linux":
            try:
                os.kill(pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            return
        try:
            reaped, _ = os.waitpid(pid, os.WNOHANG)
        except ChildProcessError:
            return  # The direct child was already reaped by Popen.
        if reaped:
            return
        # Also clean up if an assertion failed with a fixture still alive.
        os.kill(pid, signal.SIGKILL)
        deadline = time.monotonic() + 2
        while time.monotonic() < deadline:
            if os.waitpid(pid, os.WNOHANG)[0]:
                return
            time.sleep(0.01)
        self.fail(f"Fixture {pid} did not terminate for cleanup")

    def invoke(self, source, timeout=3, grace=0.2):
        return process_group.run_captured([sys.executable, "-u", "-c", source], cwd=self.root,
                                          timeout=timeout, log_path=self.log, terminate_grace=grace)

    def test_normal_nonzero_exit_preserves_result_and_diagnostics(self):
        result = self.invoke("import sys; print('standard output'); print('diagnostic', file=sys.stderr); sys.exit(7)")
        self.assertEqual(result.returncode, 7)
        self.assertEqual(result.stdout, "standard output\n")
        self.assertEqual(result.stderr, "diagnostic\n")
        self.assertEqual(self.log.read_text(), result.stdout + result.stderr)

    def test_timeout_collects_termination_diagnostics_and_waits_for_child(self):
        child = """
import os, signal, sys, time
def stop(*_):
    print('child terminated', file=sys.stderr, flush=True)
    raise SystemExit(0)
signal.signal(signal.SIGTERM, stop)
print('child ready', flush=True)
while True: time.sleep(1)
"""
        source = f"""
import json, os, signal, subprocess, sys, time
child = subprocess.Popen([sys.executable, '-u', '-c', {child!r}])
def stop(*_):
    child.wait()
    print('parent reaped child', flush=True)
    raise SystemExit(0)
signal.signal(signal.SIGTERM, stop)
print(json.dumps({{'parent': os.getpid(), 'child': child.pid}}), flush=True)
while True: time.sleep(1)
"""
        with self.assertRaises(subprocess.TimeoutExpired) as caught:
            self.invoke(source, timeout=0.8)
        error = caught.exception
        self.assertTrue(error.process_group_stopped)
        self.assertIn("child terminated", error.stderr)
        self.assertIn("parent reaped child", error.output)
        self.assertIn("Timeout after", self.log.read_text())
        for line in error.output.splitlines():
            if line.startswith("{"):
                for pid in json.loads(line).values():
                    with self.assertRaises(ProcessLookupError):
                        os.kill(pid, 0)

    def test_parent_exit_does_not_leave_term_ignoring_redirected_descendant(self):
        # With redirected output, communicate can finish as soon as the parent
        # dies. The descendant still needs a group SIGKILL and an exit wait.
        child = """
import os, pathlib, signal, time
signal.signal(signal.SIGTERM, signal.SIG_IGN)
pathlib.Path('child.pid').write_text(str(os.getpid()))
while True: time.sleep(1)
"""
        source = f"""
import os, pathlib, subprocess, sys, time
subprocess.Popen([sys.executable, '-u', '-c', {child!r}], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
while not pathlib.Path('child.pid').exists(): time.sleep(0.01)
print('parent diagnostic', flush=True)
while True: time.sleep(1)
"""
        try:
            with self.assertRaises(subprocess.TimeoutExpired) as caught:
                self.invoke(source, timeout=0.8, grace=1)
            self.assertTrue(caught.exception.process_group_stopped)
            self.assertIn("parent diagnostic", caught.exception.output)
            pid = int((self.root / "child.pid").read_text())
            self.assert_descendant_terminated(pid)
            self.assertIn(": stopped.", self.log.read_text())
        finally:
            if (self.root / "child.pid").exists():
                self.clean_fixture(int((self.root / "child.pid").read_text()))

    def test_sigkill_escalation_keeps_output_when_the_whole_tree_ignores_term(self):
        child = """
import signal, time
signal.signal(signal.SIGTERM, signal.SIG_IGN)
print('child diagnostic before kill', flush=True)
while True: time.sleep(1)
"""
        source = f"""
import json, os, pathlib, signal, subprocess, sys, time
signal.signal(signal.SIGTERM, signal.SIG_IGN)
child = subprocess.Popen([sys.executable, '-u', '-c', {child!r}])
pathlib.Path('tree.json').write_text(json.dumps([os.getpid(), child.pid]))
print('parent diagnostic before kill', flush=True)
while True: time.sleep(1)
"""
        try:
            with self.assertRaises(subprocess.TimeoutExpired) as caught:
                self.invoke(source, timeout=0.8)
            self.assertTrue(caught.exception.process_group_stopped)
            self.assertIn("parent diagnostic before kill", caught.exception.output)
            self.assertIn("child diagnostic before kill", caught.exception.output)
            parent, child = json.loads((self.root / "tree.json").read_text())
            with self.assertRaises(ProcessLookupError):
                os.kill(parent, 0)
            self.assert_descendant_terminated(child)
        finally:
            if (self.root / "tree.json").exists():
                for pid in json.loads((self.root / "tree.json").read_text()):
                    self.clean_fixture(pid)

    def test_timeout_cannot_confirm_an_unknown_group_state(self):
        with patch.object(process_group, "_group_alive", return_value=None):
            with self.assertRaises(subprocess.TimeoutExpired) as caught:
                self.invoke("import time; print('before timeout', flush=True); time.sleep(10)", timeout=0.8)
        self.assertFalse(caught.exception.process_group_stopped)
        self.assertIn("before timeout", caught.exception.output)
        self.assertIn("termination unconfirmed", self.log.read_text())

    @unittest.skipUnless(sys.platform == "linux", "Linux /proc zombie observation")
    def test_zombie_group_remains_addressable_but_has_no_live_members(self):
        child = subprocess.Popen([sys.executable, "-c", "pass"], start_new_session=True)
        try:
            deadline = time.monotonic() + 2
            while time.monotonic() < deadline:
                state = Path(f"/proc/{child.pid}/stat").read_text().rpartition(") ")[2].split()[0]
                if state == "Z":
                    break
                time.sleep(0.01)
            self.assertEqual(state, "Z")
            os.killpg(child.pid, 0)  # PID/group existence still succeeds.
            self.assertIs(process_group._group_alive(child.pid), False)
        finally:
            child.kill()
            child.wait(timeout=2)


@unittest.skipUnless(sys.platform == "linux", "Linux thread-group leader state")
class ThreadLivenessTests(unittest.TestCase):
    def test_exited_leader_does_not_hide_a_live_worker_thread(self):
        source = """
import ctypes, threading, time
threading.Thread(target=lambda: time.sleep(30)).start()
libc = ctypes.CDLL(None)
libc.pthread_exit.argtypes = [ctypes.c_void_p]
libc.pthread_exit.restype = None
libc.pthread_exit(None)
"""
        child = subprocess.Popen([sys.executable, "-c", source], start_new_session=True)
        try:
            deadline = time.monotonic() + 2
            while time.monotonic() < deadline:
                fields = Path(f"/proc/{child.pid}/stat").read_text().rpartition(") ")[2].split()
                if fields[0] == "Z":
                    break
                time.sleep(0.01)
            self.assertEqual(fields[0], "Z")
            self.assertGreater(int(fields[17]), 1)
            self.assertIsNone(child.poll())
            self.assertIsNone(process_group._group_alive(child.pid))
        finally:
            child.kill()
            child.wait(timeout=2)


if __name__ == "__main__":
    unittest.main()
