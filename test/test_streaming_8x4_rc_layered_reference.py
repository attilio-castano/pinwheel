"""HOST geometry/equation controls only; no CG or field solver runs here."""
import copy
import importlib.util
from pathlib import Path
import unittest

SCRIPTS = Path(__file__).resolve().parents[1] / 'scripts'
def module(name):
    spec = importlib.util.spec_from_file_location(name, SCRIPTS / (name + '.py'))
    result = importlib.util.module_from_spec(spec); spec.loader.exec_module(result); return result
L = module('streaming_8x4_rc_layered_plan')
R = module('streaming_8x4_rc_layered_reference')
W = module('streaming_8x4_rc_layered_run')


class LayeredTests(unittest.TestCase):
    def test_axis_retains_interfaces_and_wire_boundaries(self):
        anchors = [-16, -.25, -.09, .09, .25, 16]
        xs = R._axis(anchors, .04)
        self.assertEqual(xs, sorted(set(xs)))
        self.assertTrue(set(anchors) <= set(xs))
        central = [x for x in xs if -.25 <= x <= .25]
        self.assertLessEqual(max(b - a for a, b in zip(central, central[1:])), .04 + 1e-12)

    def test_reflected_endpoint_roundoff_cannot_make_sliver_cells(self):
        anchors = [0, .4, .45, 1.04, 1.46, 2, 3.03, 4.06, 5.4, 8.9, 9.3, 32]
        ys = R._axis(anchors, .02)
        self.assertTrue(set(anchors) <= set(ys))
        self.assertGreater(min(b - a for a, b in zip(ys, ys[1:])), 1e-8)
        with self.assertRaisesRegex(ValueError, 'near-duplicate/sliver'):
            R._axis([0, .1, .10000000000000003, 1], .02)

    def test_layered_series_exact_and_uniform_limit(self):
        self.assertAlmostEqual(R._layer_integral([(0, 1, 2), (1, 3, 4)], 0, 3, inverse=True), 1)
        self.assertAlmostEqual(R._layer_integral([(0, 1, 4.1), (1, 3, 4.1)], .2, 2.2, inverse=True), 2 / 4.1)
        with self.assertRaisesRegex(ValueError, 'overlap or do not cover'):
            R._layer_integral([(0, 1, 2), (2, 3, 4)], 0, 3)

    def test_invalid_unpredeclared_geometry_rejected_before_solver(self):
        for rectangles, extent, step in (([], 16, .04), ([{'name': 'W1', 'bounds_um': [0, 1, 1, 2]}], 17, .04),
                                        ([{'name': 'W1', 'bounds_um': [0, .01, 1, 2]}], 16, .04)):
            with self.assertRaises(ValueError):
                R.solve(rectangles, [(0, 1000, 4.1)], extent, step)

    def test_complete_matrix_comparison_keeps_coupling(self):
        a = {'matrix_F_per_m': [[2, -1], [-1, 2]], 'ground_C_F_per_m': [1, 1]}
        b = {'matrix_F_per_m': [[2, -.9], [-.9, 2]], 'ground_C_F_per_m': [1.1, 1.1]}
        self.assertGreater(W.relative_change(W.flatten(a), W.flatten(b)), .10)
        with self.assertRaises(ValueError):
            W.relative_change([1, 0], [1, 0])

    def test_empty_missing_or_reordered_excitations_cannot_pass_vacuously(self):
        for values in ([], [{'name': 'W1'}], [{'name': 'W2'}, {'name': 'W1'}]):
            with self.assertRaisesRegex(ValueError, 'excitation membership'):
                W.validate_excitation_membership(['W1', 'W2'], values)
        W.validate_excitation_membership(['W1', 'W2'], [{'name': 'W1'}, {'name': 'W2'}])

    def test_uniform_limit_binds_material_geometry_excitation_and_plan(self):
        bounds = ['-.08', '.08', '1.04', '1.46']
        plan = {'cases': [{'name': 'uniform_case', 'rectangles': [{'name': 'W1', 'bounds_um': bounds}]}],
                'controls': {'uniform_limit': {'case': 'uniform_case', 'epsilon_layers': [['0', '1000', '4.1']],
                                               'mesh_step_um': '.02', 'extent_um': '32'}},
                'protocol': {'maximum_reference_nodes': 40000, 'true_residual_relative_tolerance': '1e-9',
                             'energy_flux_relative_tolerance': '1e-7', 'maximum_cg_iterations': 6000}}
        row = {'plan_sha256': 'seal', 'case_id': 'uniform_case', 'names': ['W1'],
               'rectangles': [{'name': 'W1', 'bounds_um': list(map(float, bounds))}],
               'epsilon_layers': [[0., 1000., 4.1]], 'mesh_step_um': .02, 'extent_um': 32.,
               'declared_mesh': '.02', 'declared_extent': '32', 'qualified': False,
               'continuum_error_enclosure': False, 'nodes': 1000, 'matrix_F_per_m': [[8.5e-11]],
               'excitations': [{'name': 'W1', 'true_residual_relative': 9e-10,
                                'energy_flux_relative_error': 1e-12, 'cg_iterations': 500}]}
        W.validate_uniform_control(plan, row, 'seal')
        changes = [('epsilon_layers', [[0., 1000., 4.2]]), ('excitations', []),
                   ('plan_sha256', 'wrong'), ('extent_um', 16.),
                   ('rectangles', [{'name': 'W1', 'bounds_um': [-.16, .16, 1.04, 1.46]}])]
        for key, value in changes:
            bad = copy.deepcopy(row); bad[key] = value
            with self.assertRaises(ValueError):
                W.validate_uniform_control(plan, bad, 'seal')


if __name__ == '__main__':
    unittest.main()
