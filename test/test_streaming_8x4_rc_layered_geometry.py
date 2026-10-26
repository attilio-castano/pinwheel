"""HOST exact geometry checks; no native solver or matrix fitting."""
import copy
import json
import importlib.util
from fractions import Fraction
from pathlib import Path
import unittest

SPEC = importlib.util.spec_from_file_location('layered_geometry', Path(__file__).resolve().parents[1] / 'scripts/streaming_8x4_rc_layered_geometry.py')
G = importlib.util.module_from_spec(SPEC); SPEC.loader.exec_module(G)


def case():
    return {'name': 'TYP-w.16-s.18', 'rectangles': [
        {'name': 'W1', 'bounds_um': ['-.25', '-.09', '1.04', '1.46']},
        {'name': 'W2', 'bounds_um': ['.09', '.25', '1.04', '1.46']}],
        'epsilon_layers': [['0', '.4', '3.95'], ['.4', '.45', '6.5'], ['.45', '9.3', '4.1'], ['9.3', '1000', '1']]}


class GeometryTests(unittest.TestCase):
    def test_exact_closed_interfaces_and_si_units(self):
        files, report = G.from_plan(case(), '10', '20')
        self.assertEqual(set(report['conductors']), {'GND_SUB', 'W1', 'W2'})
        self.assertTrue(report['boundary']['every_material_adjacency_tile_covered_once'])
        self.assertEqual(report['coordinate_unit_m'], G.COORDINATE_UNIT_M)
        bounds = list(map(Fraction, report['conductors']['W1']['bounds_m']))
        self.assertAlmostEqual(float(bounds[1] - bounds[0]), .16e-6, delta=1e-13)
        self.assertTrue(any(line.startswith('D ') for line in files['geometry.lst'].splitlines()))
        self.assertEqual(sum(line.startswith('C ') for line in files['geometry.lst'].splitlines()), 4)
        unit = json.loads(files['unit-map.json'])
        self.assertEqual(unit['S'], 1048576)
        self.assertTrue(unit['capacitance_physical_F_equals_raw_times_coordinate_unit_m'])
        witnessed = set()
        for witness in unit['all_coordinate_and_reference_witnesses']:
            physical = list(map(Fraction, witness['SI_m']))
            emitted = list(map(Fraction, witness['emitted_coordinate']))
            self.assertEqual(physical, [x / G.S20 for x in emitted])
            fields = files[witness['file']].splitlines()[witness['line'] - 1].split()
            actual = fields[2:] if fields[0] == 'Q' else fields[7:]
            self.assertEqual(emitted, [Fraction.from_float(G.f32(float(x))) for x in actual])
            witnessed.add((witness['file'], witness['line']))
        expected = {(n, i) for n, text in files.items() if n != 'unit-map.json'
                    for i, line in enumerate(text.splitlines(), 1) if line.startswith(('Q ', 'D '))}
        self.assertEqual(witnessed, expected)

    def test_unquantized_input_cannot_silently_change_physical_geometry(self):
        with self.assertRaisesRegex(ValueError, 'not exact parser binary32'):
            G.normalize_s20({'panel.qui': 'Q W1 0.1 0 0  1 0 0  1 1 0  0 1 0\n'})

    def test_unpredeclared_extension_rejected(self):
        with self.assertRaisesRegex(ValueError, 'extension/length'):
            G.from_plan(case(), '10', '30')

    def test_non_air_exterior_rejected(self):
        value = case(); value['epsilon_layers'][-1][2] = '2'
        with self.assertRaisesRegex(ValueError, 'external air'):
            G.from_plan(value, '20', '20')


if __name__ == '__main__':
    unittest.main()
