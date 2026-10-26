"""HOST-only exact physical-coordinate and failed-prefix controls."""
from fractions import Fraction
import importlib.util
import json
from pathlib import Path
import re
import tempfile
import unittest
from unittest.mock import patch

SCRIPTS = Path(__file__).resolve().parents[1] / 'scripts'
spec = importlib.util.spec_from_file_location('streaming_8x4_rc_consumer_units', SCRIPTS / 'streaming_8x4_rc_consumer_units.py')
U = importlib.util.module_from_spec(spec); spec.loader.exec_module(U)
spec = importlib.util.spec_from_file_location('streaming_8x4_rc_consumer_units_readback', SCRIPTS / 'streaming_8x4_rc_consumer_units_readback.py')
R = importlib.util.module_from_spec(spec); spec.loader.exec_module(R)


class UnitControls(unittest.TestCase):
    def fixture(self):
        mapping = dict(zip(U.C.VIA_FIXTURES, ('Via1', 'Via1', 'Via2', 'Via3', 'TopVia1')))
        rows = U.C.fixtures({'explicit_vias': {name: {'cut_layer': layer} for name, layer in mapping.items()}})
        return U.C.fixture_def(rows)

    def test_actual_LEF_units_are_unique_positive_database_units(self):
        text = 'UNITS\n DATABASE MICRONS 1000 ;\nEND UNITS\n'
        self.assertEqual(U.lef_dbu(text), 1000)
        for bad in ('', text + text, text.replace('1000', '0'), text.replace('DATABASE', 'OTHER')):
            with self.assertRaises(ValueError): U.lef_dbu(bad)

    def test_every_actual_fixture_coordinate_has_exact_physical_identity(self):
        old = self.fixture(); new, witness = U.correct_def(old, 1000)
        self.assertIn('UNITS DISTANCE MICRONS 1000 ;', new)
        self.assertEqual(witness['coordinate_pair_count'], 148)
        # Independent integer cross multiplication over every coordinate token.
        old_pairs = re.findall(r'\(\s*(-?\d+)\s+(-?\d+)\s*\)', old)
        new_pairs = re.findall(r'\(\s*(-?\d+)\s+(-?\d+)\s*\)', new)
        self.assertEqual(len(old_pairs), len(new_pairs))
        self.assertTrue(all(int(a) * 1000 == int(b) * 2000
                            for before, after in zip(old_pairs, new_pairs) for a, b in zip(before, after)))
        self.assertIn('( -50 -50 ) ( 50 50 )', new)
        self.assertIn('DIEAREA ( 0 0 ) ( 150000 400000 )', new)
        self.assertTrue('( 10000 20000 ) ( 60000 20000 )' in new)
        self.assertTrue(witness['all_physical_coordinates_exactly_equal'])
        self.assertFalse(witness['rounding_used'])

    def test_header_only_correction_changes_physical_geometry(self):
        old = self.fixture(); correct, _ = U.correct_def(old, 1000)
        header_only = old.replace('UNITS DISTANCE MICRONS 2000 ;', 'UNITS DISTANCE MICRONS 1000 ;')
        self.assertNotEqual(header_only, correct)
        self.assertTrue('+ ROUTED Metal1 ( 20000 40000 ) ( 120000 40000 )' in header_only)
        self.assertTrue('+ ROUTED Metal1 ( 10000 20000 ) ( 60000 20000 )' in correct)

    def test_nonintegral_coordinate_is_rejected_instead_of_rounded(self):
        old = self.fixture().replace('( 0 0 )', '( 1 0 )', 1)
        with self.assertRaisesRegex(ValueError, 'would round'): U.correct_def(old, 1000)
        with self.assertRaisesRegex(ValueError, 'DEF units'): U.correct_def(self.fixture().replace('UNITS DISTANCE MICRONS 2000 ;', ''), 1000)

    def test_inner_policy_rules_and_dimensions_stay_equal(self):
        base = {'files_sha256': {'fixture.def': 'old', 'rules.txt': 'immutable'},
                'producer_sha256': {'frozen.py': 'abc'}, 'protocol': {'wire_relative_tolerance': '.001'},
                'fixture_rows': [{'name': 'Metal1_L50', 'segments': [['Metal1', '50', '.16']]}]}
        adapted = U.inner_plan(base, 'new DEF bytes', {'new.py': 'def'})
        self.assertEqual(adapted['protocol'], base['protocol'])
        self.assertEqual(adapted['fixture_rows'], base['fixture_rows'])
        self.assertEqual(adapted['files_sha256']['rules.txt'], 'immutable')
        self.assertEqual(base['files_sha256']['fixture.def'], 'old')

    def test_independent_reader_rejects_sparse_prefix_before_SPEF(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory); (root / 'native').mkdir(); (root / 'native/report.json').write_text('{}')
            report = {'schema': 'pinwheel.streaming-8x4-rc-consumer-units-execution.v1', 'plan_sha256': 'seal',
                'qualified': False, 'model_qualified': False, 'all_six_native_calls_closed': False,
                'consumer_policy_unchanged': True, 'inputs_unchanged': True}
            (root / 'report.json').write_text(json.dumps(report))
            with patch.object(R.U, 'verify', return_value={}):
                with self.assertRaisesRegex(ValueError, 'six-call membership'): R.readback(root, 'seal', root)


if __name__ == '__main__': unittest.main()
