"""HOST membership/resource/readback controls; never run a field solver."""
import copy
from decimal import Decimal as D
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest

SCRIPTS = Path(__file__).resolve().parents[1] / 'scripts'
def module(name):
    spec = importlib.util.spec_from_file_location(name, SCRIPTS / (name + '.py'))
    result = importlib.util.module_from_spec(spec); spec.loader.exec_module(result); return result
A = module('streaming_8x4_rc_all_layers_plan')
W = module('streaming_8x4_rc_all_layers_execute')
H = module('streaming_8x4_rc_all_layers_analyze')


def nominal_stack():
    # Minimal exact nominal source-field fixture, not a new physical authority.
    stack = {}
    for name, thickness, er in [('fox', '.4', '3.95'), ('nitride', '.05', '6.5'),
            ('dummyOx', '.59', '4.1'), ('ox1', '.960', '4.1'), ('ox2', '1.03', '4.1'),
            ('ox3', '1.03', '4.1'), ('ox4', '1.34', '4.1'), ('oxTopMetal1', '3.5', '4.1'),
            ('nitTop', '.4', '6.6'), ('air', '5', '1')]:
        stack['DIELECTRIC', name] = {'THICKNESS': D(thickness), 'ER': D(er)}
    for name, thickness, width, spacing, r in [('Metal1', '.420', '.16', '.18', '.110'),
            ('Metal2', '.490', '.2', '.21', '.088'), ('Metal3', '.490', '.2', '.21', '.088'),
            ('Metal4', '.490', '.2', '.21', '.088'), ('TopMetal1', '2', '1.64', '1.64', '.018')]:
        stack['CONDUCTOR', name] = {k: D(v) for k, v in zip(('THICKNESS', 'WMIN', 'SMIN', 'RPSQ'),
                                                         (thickness, width, spacing, r))}
    return stack


class AllLayerControls(unittest.TestCase):
    def test_linear_endpoint_sliver_regression(self):
        for h in (.04, .02):
            anchors = [-16, -.82, -.1, .1, .82, 16]
            values = A.F._axis(anchors, h)
            self.assertTrue(set(anchors) <= set(values))
            self.assertGreater(min(b-a for a, b in zip(values, values[1:])), 1e-8)
        with self.assertRaisesRegex(ValueError, 'near-duplicate/sliver'):
            A.F._axis([0, .1, .10000000000000003, 1], .02)

    def test_exact_eight_case_universe_and_32_grid_resource_census(self):
        cases = A.case_universe(nominal_stack()); grids = A.grid_inventory(cases)
        self.assertEqual([c['name'] for c in cases], A.BATCHES['first5'] + A.BATCHES['remaining3'])
        self.assertEqual(len(grids), 32); self.assertEqual(max(r['nodes'] for r in grids), 61897)
        self.assertEqual(max(r['nodes'] for r in grids if r['batch'] == 'first5'), 39389)
        self.assertEqual(sum(not r['within_reviewed_50000_node_cap'] for r in grids), 2)
        self.assertTrue(all(r['within_reviewed_65000_node_cap'] for r in grids))
        self.assertEqual(cases[-1]['rectangles'][1]['bounds_um'], ['-0.82', '0.82', '5.400', '7.400'])

    def test_byte_identical_operator_body_and_conservative_storage(self):
        self.assertTrue(A.operator_derivation()['solve_body_byte_identical'])
        bound = A.reference_storage_budget()
        self.assertEqual(bound['conservative_total_bytes'], 1467613184)
        self.assertGreater(bound['headroom_bytes'], 600000000)
        self.assertIs(bound['measured_RSS'], False)

    def fixture(self):
        case = A.case_universe(nominal_stack())[3]
        plan = {'grid_inventory': A.grid_inventory(A.case_universe(nominal_stack())),
                'protocol': {'maximum_cg_iterations': 6000, 'true_residual_relative_tolerance': '1e-9',
                 'energy_flux_relative_tolerance': '1e-7', 'reciprocity_relative_tolerance': '1e-7'}}
        row = {'schema': 'pinwheel.streaming-8x4-rc-layered-reference.v1', 'names': ['W1', 'W2'],
               'rectangles': [{'name': r['name'], 'bounds_um': list(map(float, r['bounds_um']))} for r in case['rectangles']],
               'epsilon_layers': [list(map(float, r)) for r in case['epsilon_layers']],
               'mesh_step_um': .02, 'extent_um': 32., 'qualified': False, 'continuum_error_enclosure': False,
               'nodes': 36179, 'unknown_nodes': 35000, 'excitations': [{'name': n, 'cg_iterations': 500,
                    'true_residual_relative': 9e-10, 'energy_flux_relative_error': 1e-12} for n in ('W1', 'W2')],
               'matrix_F_per_m': [[2e-10, -1e-10], [-1e-10, 2e-10]],
               'ground_C_F_per_m': [1e-10, 1e-10], 'coupling_C_F_per_m': 1e-10}
        return plan, case, row

    def test_ordered_excitation_and_strict_residual(self):
        plan, case, row = self.fixture(); W.validate_reference_row(plan, 'seal', case, row, '.02', '32')
        for value in ([], row['excitations'][:1], list(reversed(row['excitations']))):
            bad = copy.deepcopy(row); bad['excitations'] = value
            with self.assertRaisesRegex(ValueError, 'excitation membership'):
                W.validate_reference_row(plan, 'seal', case, bad, '.02', '32')
        bad = copy.deepcopy(row); bad['excitations'][0]['true_residual_relative'] = 1.0000000001e-9
        with self.assertRaisesRegex(ValueError, 'numerical contract'):
            W.validate_reference_row(plan, 'seal', case, bad, '.02', '32')

    def test_foreign_material_geometry_and_ground_semantics_rejected(self):
        plan, case, row = self.fixture()
        for key, value in [('epsilon_layers', [[0., 1000., 4.1]]), ('rectangles', []),
                           ('ground_C_F_per_m', [2e-10, 2e-10]), ('coupling_C_F_per_m', 2e-10),
                           ('nodes', 36178), ('unknown_nodes', 36180)]:
            bad = copy.deepcopy(row); bad[key] = value
            with self.assertRaises(ValueError):
                W.validate_reference_row(plan, 'seal', case, bad, '.02', '32')

    def test_native_leaf_must_match_declared_mesh_before_other_readback(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory); (root / 'report.json').write_text(json.dumps({'mesh': '.wrong'}))
            with self.assertRaisesRegex(ValueError, 'mesh differs'):
                H.read_native({}, 'seal', {}, '.expected', root, root, root)

    def test_reference_sparse_membership_rejected_before_numerics(self):
        plan = {'cases': [], 'protocol': {'reference_mesh_steps_um': ['.04', '.02'],
                                        'reference_domain_extents_um': ['16', '32']}}
        # Real membership is case-bound, not inferred from an empty observed list.
        plan['cases'] = A.case_universe(nominal_stack())
        with self.assertRaisesRegex(ValueError, 'Incomplete reference batch membership'):
            W.reference_analysis(plan, 'seal', 'first5', [])

    def test_geometry_missing_duplicate_or_reordered_length_case_rejected(self):
        cases = A.case_universe(nominal_stack())
        rows = [{'name': c['name'] + '-L' + length + '-E' + extension,
                 'case': c['name'], 'batch': c['batch'], 'length_um': length, 'extension_um': extension}
                for c in cases for length, extension in A.LENGTH_EXTENSIONS]
        for bad in (rows[:-1], rows[:-1] + [rows[-2]], [rows[1], rows[0]] + rows[2:]):
            with self.assertRaisesRegex(ValueError, 'forty-case geometry universe'):
                W.verify_geometry({'cases': cases, 'geometry_cases': bad}, Path('/unread-because-early-reject'))

    def test_full_M1_prerequisite_cannot_be_a_point_or_foreign_plan(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'm1.json'
            full = {'schema': 'pinwheel.streaming-8x4-rc-layered-independent-readback.v1',
                    'limited_layered_M1_pilot_passed': True, 'qualified': False, 'model_qualified': False,
                    'continuum_error_enclosure': False, 'native_plan_sha256': A.M1_NATIVE_HASH,
                    'reference_plan_sha256': A.M1_REFERENCE_HASH}
            plan = {'batches': {'first5': {'all_case_grids_within_node_admission': True}}}
            path.write_text(json.dumps(full)); W.prerequisites(plan, 'seal', 'first5', path, W.E.sha(path))
            for key, value in [('limited_layered_M1_pilot_passed', False), ('native_plan_sha256', 'wrong'),
                               ('model_qualified', True)]:
                bad = dict(full); bad[key] = value; path.write_text(json.dumps(bad))
                with self.assertRaises(ValueError):
                    W.prerequisites(plan, 'seal', 'first5', path, W.E.sha(path))

    def test_second_batch_needs_exact_closed_first_batch(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory); m1 = root / 'm1.json'; first = root / 'first.json'
            m1.write_text(json.dumps({'schema': 'pinwheel.streaming-8x4-rc-layered-independent-readback.v1',
                'limited_layered_M1_pilot_passed': True, 'qualified': False, 'model_qualified': False,
                'continuum_error_enclosure': False, 'native_plan_sha256': A.M1_NATIVE_HASH,
                'reference_plan_sha256': A.M1_REFERENCE_HASH}))
            plan = {'batches': {'remaining3': {'all_case_grids_within_node_admission': True}}}
            with self.assertRaisesRegex(ValueError, 'requires closed first5'):
                W.prerequisites(plan, 'seal', 'remaining3', m1, W.E.sha(m1))
            receipt = {'schema': 'pinwheel.streaming-8x4-rc-all-layers-independent-readback.v1',
                'batch': 'first5', 'plan_sha256': 'seal', 'limited_batch_passed': True,
                'qualified': False, 'model_qualified': False, 'declared_case_names': A.BATCHES['first5'][:-1]}
            first.write_text(json.dumps(receipt))
            with self.assertRaisesRegex(ValueError, 'incomplete/foreign/promoted'):
                W.prerequisites(plan, 'seal', 'remaining3', m1, W.E.sha(m1), first, W.E.sha(first))


if __name__ == '__main__':
    unittest.main()
