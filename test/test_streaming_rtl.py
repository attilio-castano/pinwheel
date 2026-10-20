"""Process-exit controls; these synthetic children are not RTL qualification."""
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
from streaming_rtl import QuadRTL


class LifecycleTests(unittest.TestCase):
    def child(self, source):
        folder = tempfile.TemporaryDirectory()
        self.addCleanup(folder.cleanup)
        path = Path(folder.name) / 'child.py'
        path.write_text(source)
        return path

    def test_clean_eof_exit_is_accepted(self):
        path = self.child('import sys\nsys.stdin.read()\nsys.exit(0)\n')
        with QuadRTL(sys.executable, path) as rtl:
            pass
        self.assertEqual(rtl.process.returncode, 0)

    def test_nonzero_eof_exit_refuses_a_clean_context(self):
        path = self.child('import sys\nsys.stdin.read()\nsys.exit(7)\n')
        with self.assertRaisesRegex(RuntimeError, 'status 7'):
            with QuadRTL(sys.executable, path):
                pass

    def test_context_preserves_original_exception_on_nonzero_cleanup(self):
        path = self.child('import sys\nsys.stdin.read()\nsys.exit(9)\n')
        with self.assertRaisesRegex(ValueError, 'original failure'):
            with QuadRTL(sys.executable, path) as rtl:
                raise ValueError('original failure')
        self.assertEqual(rtl.process.returncode, 9)

    def test_malformed_edge_keeps_its_original_error(self):
        path = self.child('import sys\nsys.stdin.readline()\nprint("STREAM_QUAD broken",flush=True)\nsys.exit(11)\n')
        rtl = QuadRTL(sys.executable, path)
        with self.assertRaises(ValueError): rtl.tick(csn=1, sck=0, mosi=0)
        self.assertTrue(rtl.closed)
        self.assertEqual(rtl.process.returncode, 11)

    def test_edge_timeout_is_preserved_and_child_is_reaped(self):
        path = self.child('import sys\nsys.stdin.read()\nsys.exit(12)\n')
        rtl = QuadRTL(sys.executable, path, timeout_seconds=0.02)
        with self.assertRaises(TimeoutError): rtl.tick(csn=1, sck=0, mosi=0)
        self.assertTrue(rtl.closed)
        self.assertEqual(rtl.process.returncode, 12)


if __name__ == '__main__': unittest.main()
