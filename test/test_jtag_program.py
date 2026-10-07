"""Admission and public source shape of the bounded resident JTAG helper."""
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))

from pinwheel_host import RESIDENT_FORMAT
from pinwheel_jtag import resident_jtag_scan
from pinwheel_program import resource_report


class JTAGProgramTests(unittest.TestCase):
    def test_fixed_program_admission_and_declared_capture_layout(self):
        program = resident_jtag_scan()
        report = resource_report(program)
        self.assertEqual(program.image_format, RESIDENT_FORMAT)
        self.assertEqual((program.idle_levels, program.idle_enabled), (0, 7))
        self.assertEqual(report['positions'], 40)
        self.assertEqual(report['upload_words'], 290)
        self.assertEqual(report['capture_slots'], list(range(8)))
        self.assertLessEqual(report['used_parameters'], 32)
        self.assertEqual(resident_jtag_scan(), program)

    def test_duration_admission_uses_existing_builder_bounds(self):
        for period in (1, 4, 256):
            self.assertEqual(resource_report(resident_jtag_scan(period))['positions'], 40)
        for period in (0, 257, True, 4.0):
            with self.assertRaises(ValueError):
                resident_jtag_scan(period)


if __name__ == '__main__':
    unittest.main()
