"""Scientific admission controls for the separately frozen 8x4 RC pilot."""
from copy import deepcopy
from decimal import Decimal
from fractions import Fraction
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
import streaming_8x4_rc_protocol as P
import streaming_8x4_rc_reference as R


def manual_log(matrix=None):
    matrix = matrix or [['4', '-1'], ['-1', '2']]
    return ('Running FasterCap version 6.0.7\n'
            'Solution scheme (-g): Galerkin, GMRES tolerance (-t): 0.0005\n'
            'Potential interaction coefficient to mesh refinement ratio (-d): 1\n'
            'Mesh refinement (-m): 0.000383703\n'
            'Capacitance matrix is:\nDimension 2 x 2\n'
            'g1_GND_SUB ' + ' '.join(matrix[0]) + '\n'
            'g2_SIGNAL ' + ' '.join(matrix[1]) + '\n'
            'Total time: 1.25s (0 days, 0 hours, 0 mins, 1 s)\n')


class ProtocolTests(unittest.TestCase):
    def test_protocol_keeps_claim_boundaries(self):
        plan = P.frozen_protocol()
        self.assertFalse(plan['qualified'])
        self.assertFalse(plan['held_out']['tuning_permitted'])
        P.validate_protocol(plan)
        plan['manual_solver']['all_warnings_fatal'] = False
        with self.assertRaises(ValueError):
            P.validate_protocol(plan)

    def test_all_declared_geometries_fit_the_panel_cap(self):
        plan = P.frozen_protocol()
        for width in ('0.16', '0.32'):
            for length in ('10', '20', '30'):
                files = P.finite_wire_files(plan, width, length)
                self.assertEqual(set(files), {'geometry.lst', 'ground.qui', 'signal.qui', 'certificate.json'})
                self.assertGreater(files['ground.qui'].count(b'\nQ '), 100)
                self.assertNotEqual(files['ground.qui'], files['signal.qui'])
        for width in ('0.16', '0.32'):
            for length in ('20', '30'):
                P.finite_wire_files(plan, width, length, margin_um='30')

    def test_closed_box_orientation_volume_and_edges(self):
        text = P.box_panels('BOX', ((0, 2), (0, 3), (0, 4)), (2, 3, 4)).decode()
        from collections import Counter
        edges = Counter()
        volume = Fraction(0)
        for line in text.splitlines()[1:]:
            values = [Fraction(x) for x in line.split()[2:]]
            q = [tuple(values[i:i + 3]) for i in range(0, 12, 3)]
            for a, b in zip(q, q[1:] + q[:1]):
                edges[a, b] += 1
            e = [q[1][i] - q[0][i] for i in range(3)]
            f = [q[2][i] - q[1][i] for i in range(3)]
            normal = [e[1] * f[2] - e[2] * f[1], e[2] * f[0] - e[0] * f[2], e[0] * f[1] - e[1] * f[0]]
            volume += sum(q[0][i] * normal[i] for i in range(3)) / 3
        self.assertEqual(volume, 24)
        self.assertTrue(all(count == edges[b, a] == 1 for (a, b), count in edges.items()))

    def test_strict_manual_log_accepts_complete_positive_case(self):
        result = P.parse_manual_log(manual_log(), ['g1_GND_SUB', 'g2_SIGNAL'], '0.000383703', '0.0005')
        self.assertEqual(result['matrix'][1][1], '2')

    def test_captured_native_footer_and_exact_matrix_are_admitted(self):
        path = Path(__file__).resolve().parent / 'fixtures/streaming-8x4-rc-manual-U-20261022.log'
        import hashlib
        self.assertEqual(hashlib.sha256(path.read_bytes()).hexdigest(),
                         '421cf2188f14265f768ab37629817336c7f55e150a4f78ae4197fbb3448a5f92')
        result = P.parse_manual_log(path.read_text(), ['g1_GND_SUB', 'g2_SIGNAL'], '0.000383703', '0.0005')
        self.assertEqual(result['solver_seconds'], '0.166423')
        self.assertEqual(result['matrix'][1][1], '1.16966E-9')

    def test_duration_decomposition_and_trailing_garbage_are_refused(self):
        for sample in (manual_log().replace('1 s)', '2 s)'),
                       manual_log().replace('1.25s (0 days, 0 hours, 0 mins, 1 s)', '1.25s'),
                       manual_log().replace('1 s)', '1 s) trailing garbage')):
            with self.assertRaises(ValueError):
                P.parse_manual_log(sample, ['g1_GND_SUB', 'g2_SIGNAL'], '0.000383703', '0.0005')

    def test_warning_anywhere_is_fatal(self):
        for extra in ('Warning: early iteration bad\n', 'Error: cannot go out-of-core\n', 'timeout\n'):
            with self.assertRaises(ValueError):
                P.parse_manual_log(extra + manual_log(), ['g1_GND_SUB', 'g2_SIGNAL'], '0.000383703', '0.0005')

    def test_truncation_duplicate_auto_and_changed_flags_are_refused(self):
        samples = [manual_log().replace('Total time: 1.25s', ''),
                   manual_log() + manual_log(),
                   'Auto calculation with max error: 0.01\n' + manual_log(),
                   manual_log().replace('(-d): 1', '(-d): 0.1'),
                   manual_log().replace('g1_GND_SUB', 'g2_SIGNAL'),
                   manual_log().replace('4 -1', 'NaN -1')]
        for sample in samples:
            with self.assertRaises(ValueError):
                P.parse_manual_log(sample, ['g1_GND_SUB', 'g2_SIGNAL'], '0.000383703', '0.0005')

    def test_physics_detects_the_historical_kind_of_failure(self):
        for a in ([['4', '-1'], ['-1', '0.9']],
                  [['4', '1'], ['1', '2']],
                  [['4', '-1'], ['-2', '3']],
                  [['1', '-1'], ['-1', '1']]):
            with self.assertRaises(ValueError):
                P.matrix_physics(['G', 'S'], a)

    def test_two_successive_mesh_pairs_and_membership_required(self):
        plan = P.frozen_protocol()
        first = P.parse_manual_log(manual_log(), ['g1_GND_SUB', 'g2_SIGNAL'], '0.000383703', '0.0005')
        rows = []
        for mesh in plan['manual_solver']['mesh_ladder'][:3]:
            row = deepcopy(first); row['mesh'] = mesh; rows.append(row)
        P.admit_mesh_sequence(plan, rows)
        bad = deepcopy(rows); bad[1]['matrix'][1][1] = '2.1'
        with self.assertRaises(ValueError):
            P.admit_mesh_sequence(plan, bad)
        with self.assertRaises(ValueError):
            P.admit_mesh_sequence(plan, rows[:2])
        bad = deepcopy(rows); bad[1]['mesh'] = plan['manual_solver']['mesh_ladder'][3]
        with self.assertRaises(ValueError):
            P.admit_mesh_sequence(plan, bad)

    def test_parallel_plate_series_dielectric_reference(self):
        # Two equal-thickness eps=2/6 layers have effective epsilon=3.
        value = P.layered_parallel_plate_per_area([('0.000001', '2'), ('0.000001', '6')])
        self.assertAlmostEqual(float(value / (P.EPS0 * Decimal('1500000'))), 1.0, places=14)

    def test_reference_linear_solver_against_exact_two_unknown_solution(self):
        values, _, residual = R._cg([2., 2.], [[(1, 1.)], [(0, 1.)]], [1., 0.], 1e-12, 10)
        self.assertAlmostEqual(values[0], 2 / 3)
        self.assertAlmostEqual(values[1], 1 / 3)
        self.assertLess(residual, 1e-12)

    def test_reference_dielectric_edges_use_series_and_parallel_laws(self):
        layers = ((0., 1., 2.), (1., 2., 6.))
        self.assertEqual(R._layer_integral(layers, 0., 2.), 8.)
        self.assertAlmostEqual(R._layer_integral(layers, 0., 2., inverse=True), 2 / 3)
        with self.assertRaises(ValueError):
            R._layer_integral(layers, -1., 2.)

    def test_small_reference_energy_flux_and_epsilon_scaling(self):
        # A small independent equation control, not a process-model pilot.
        a = R.solve_wire(1., .5, .5, 8., .25, layers=((0., 1000., 2.),))
        b = R.solve_wire(1., .5, .5, 8., .25, layers=((0., 1000., 4.),))
        self.assertLess(a['energy_flux_relative_error'], 1e-7)
        self.assertAlmostEqual(b['capacitance_per_length_F_per_m'] / a['capacitance_per_length_F_per_m'], 2., places=8)
        self.assertFalse(a['continuum_error_enclosure'])


if __name__ == '__main__':
    unittest.main()
