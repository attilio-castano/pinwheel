"""Timeout cleanup uses disposable Python children, never Lean or CAD tools."""
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
import process_group


@unittest.skipUnless(os.name == "posix", "Process-group runner targets POSIX hosts")
class ProcessGroupTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.log = self.root / "command.log"

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
            with self.assertRaises(ProcessLookupError):
                os.kill(pid, 0)
            self.assertIn(": stopped.", self.log.read_text())
        finally:
            if (self.root / "child.pid").exists():
                try:
                    os.kill(int((self.root / "child.pid").read_text()), signal.SIGKILL)
                except ProcessLookupError:
                    pass

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
            for pid in json.loads((self.root / "tree.json").read_text()):
                with self.assertRaises(ProcessLookupError):
                    os.kill(pid, 0)
        finally:
            if (self.root / "tree.json").exists():
                for pid in json.loads((self.root / "tree.json").read_text()):
                    try:
                        os.kill(pid, signal.SIGKILL)
                    except ProcessLookupError:
                        pass


if __name__ == "__main__":
    unittest.main()
