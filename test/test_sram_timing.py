"""Reject incomplete STA evidence without confusing violations with run failure."""
import importlib.util
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
spec = importlib.util.spec_from_file_location('sram_timing', ROOT / 'scripts/check-sram-timing.py')
timing = importlib.util.module_from_spec(spec)
spec.loader.exec_module(timing)

LOG = '''PINWHEEL_SETUP_CHECK
PINWHEEL_MAX_SLACK
worst slack max 10.26
PINWHEEL_MIN_SLACK
worst slack min -0.86
PINWHEEL_ELECTRICAL
max fanout
pin 10 11 -1 (VIOLATED)
max capacitance
pin 0.04 0.05 -0.01 (VIOLATED)
PINWHEEL_SRAM_TO_SRAM
Startpoint: memory.storage0
 10.26 slack (MET)
PINWHEEL_CACHED_TO_ADDRESS
Startpoint: cached
 12.00 slack (MET)
PINWHEEL_ADDRESS_PATHS
Startpoint: memory.storage0
 10.26 slack (MET)
PINWHEEL_STA_COMPLETE
'''


class TimingEvidence(unittest.TestCase):
    def test_real_violations_are_diagnostic_results(self):
        result = timing.parse_timing(LOG, require_fetch_paths=True)
        self.assertEqual(result['hold_slack_ns'], -0.86)
        self.assertEqual(result['electrical_violations']['max fanout'], 1)
        self.assertEqual(result['electrical_violations']['max capacitance'], 1)
        self.assertEqual(result['sram_to_sram_slack_ns'], 10.26)

    def test_reject_incomplete_or_ambiguous_analysis(self):
        for log in (LOG.replace('PINWHEEL_STA_COMPLETE', ''), LOG + LOG,
                    LOG.replace('PINWHEEL_MIN_SLACK', ''),
                    LOG.replace('worst slack min -0.86', 'No paths found.'),
                    LOG.replace('PINWHEEL_CACHED_TO_ADDRESS', 'OTHER'),
                    LOG.replace('Startpoint:', 'Missing:'),
                    LOG.replace('max capacitance', 'unknown category'),
                    LOG.replace('PINWHEEL_SETUP_CHECK', 'PINWHEEL_SETUP_CHECK\nWarning: unconstrained pins'),
                    LOG + '\nError: bad library'):
            with self.subTest(log=log), self.assertRaises(ValueError):
                timing.parse_timing(log, require_fetch_paths=True)


if __name__ == '__main__':
    unittest.main()
