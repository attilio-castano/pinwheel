"""The replay switch reports omissions and never converts missing data to pass."""
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from historical_evidence import ENVIRONMENT, historical_evidence


class HistoricalEvidenceControls(unittest.TestCase):
    def check(self, enabled, path):
        with patch.dict(os.environ, {ENVIRONMENT: enabled}):
            class Replay(unittest.TestCase):
                @historical_evidence
                def test_required_input(self):
                    self.assertEqual(path.read_bytes(), b'authenticated fixture')
            result = unittest.TestResult()
            Replay('test_required_input').run(result)
            return result

    def test_default_reports_unexecuted_replay_without_reading_missing_data(self):
        with tempfile.TemporaryDirectory() as directory:
            result = self.check('', Path(directory) / 'missing')
        self.assertEqual(len(result.skipped), 1)
        self.assertIn('not requested', result.skipped[0][1])
        self.assertEqual(result.errors, [])

    def test_explicit_replay_fails_on_missing_or_changed_input(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'input'
            missing = self.check('1', path)
            self.assertEqual(len(missing.errors), 1)
            self.assertEqual(missing.skipped, [])
            path.write_bytes(b'changed')
            changed = self.check('1', path)
            self.assertEqual(len(changed.failures), 1)
            self.assertEqual(changed.skipped, [])
            path.write_bytes(b'authenticated fixture')
            complete = self.check('1', path)
            self.assertTrue(complete.wasSuccessful())
            self.assertEqual(complete.skipped, [])


if __name__ == '__main__':
    unittest.main()
