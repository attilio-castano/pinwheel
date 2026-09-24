import importlib.util
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
from validation_run import Commands, fresh_directory


class ValidationCommandsTest(unittest.TestCase):
    def test_reasoned_rejection_and_no_overwrite(self):
        with tempfile.TemporaryDirectory() as temp:
            out = fresh_directory(temp, 'case')
            run = Commands(ROOT, out)
            cmd = [sys.executable, '-c', "print('behavior mismatch'); raise SystemExit(1)"]
            run(cmd, 'mutant', reject='behavior mismatch')
            self.assertEqual(run.records[0]['exit_code'], 1)
            self.assertIn('behavior mismatch', (out / 'mutant.log').read_text())
            with self.assertRaises(FileExistsError):
                run(cmd, 'mutant', reject='behavior mismatch')
            with self.assertRaises(RuntimeError):
                run(cmd, 'wrong-reason', reject='different failure')
            with self.assertRaises(RuntimeError):
                run([sys.executable, '-c', "print('behavior mismatch')"], 'false-positive',
                    reject='behavior mismatch')
            with self.assertRaises(FileExistsError):
                fresh_directory(temp, 'case')
            with self.assertRaises(ValueError):
                fresh_directory(temp, '../escape')

    def test_timeout_keeps_diagnostics_and_failure_record(self):
        with tempfile.TemporaryDirectory() as temp:
            run = Commands(ROOT, temp)
            with self.assertRaises(subprocess.TimeoutExpired):
                run([sys.executable, '-u', '-c', "import time; print('started'); time.sleep(30)"],
                    'timeout', timeout=0.2)
            self.assertEqual(run.records[0]['error'], 'TimeoutExpired')
            text = (Path(temp) / 'timeout.log').read_text()
            self.assertIn('started', text)
            self.assertIn('Timeout', text)

    def test_runners_import_without_executing(self):
        for name in ['check-prefetch', 'check-sampled', 'check-backend', 'check-bank-select']:
            spec = importlib.util.spec_from_file_location(name, ROOT / 'scripts' / (name + '.py'))
            module = importlib.util.module_from_spec(spec)
            spec.loader.exec_module(module)
            self.assertTrue(callable(module.main))


if __name__ == '__main__':
    unittest.main()
