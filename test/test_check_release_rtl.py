"""The release RTL check must read the pins correctly and catch a changed file.

The end-to-end mutation test needs the pinned CIRCT and Icarus installs; set
PINWHEEL_TOOLS to a build/tools directory (it is skipped otherwise).
"""
import importlib.util
import json
import os
from pathlib import Path
import sys
import unittest
from unittest import mock

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
spec = importlib.util.spec_from_file_location('check_release_rtl', ROOT / 'scripts/check-release-rtl.py')
R = importlib.util.module_from_spec(spec)
spec.loader.exec_module(R)


class ReleaseRtlCheck(unittest.TestCase):
    def test_pins_match_source_replay(self):
        import streaming_8x4_jane_street_source as replay
        self.assertEqual(R.pinned_hashes(), replay.RTL)

    def test_compare_flags_one_difference(self):
        pins = R.pinned_hashes()
        generated = dict(pins, **{'tt.sv': '0' * 64})
        rows = R.compare(pins, generated)
        self.assertEqual([row['file'] for row in rows if not row['equal']], ['tt.sv'])

    def test_missing_pin_is_rejected(self):
        broken = ROOT / 'build/test-release-rtl-workflow.yml'
        broken.parent.mkdir(exist_ok=True)
        text = R.RELEASE_WORKFLOW.read_text()
        broken.write_text('\n'.join(line for line in text.splitlines() if 'src/tt.sv' not in line))
        try:
            with self.assertRaises(ValueError):
                R.pinned_hashes(broken)
        finally:
            broken.unlink()

    @unittest.skipUnless((R.DEFAULT_TOOLS / R.CIRCT_RELEASE / 'bin/circt-opt').is_file(),
                         'needs the pinned CIRCT install (set PINWHEEL_TOOLS)')
    def test_changed_wrapper_is_caught(self):
        import streaming_ready_wrapper
        original = streaming_ready_wrapper.tt_source
        tag = f'mutation-{os.getpid()}'
        with mock.patch.object(streaming_ready_wrapper, 'tt_source', lambda depth: original(depth) + '\n'):
            status = R.main(['--tag', tag])
        report = json.loads((ROOT / 'build/release-rtl' / tag / 'report.json').read_text())
        self.assertEqual(status, 1)
        self.assertFalse(report['passed'])
        self.assertEqual([row['file'] for row in report['rtl'] if not row['equal']], ['tt.sv'])


if __name__ == '__main__':
    unittest.main()
