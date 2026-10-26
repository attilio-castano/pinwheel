"""Fixed-branch HOST controls. Synthetic headers are grammar tests, not runs."""
import copy
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
def module(name):
    spec = importlib.util.spec_from_file_location(name, ROOT / 'scripts' / (name + '.py'))
    value = importlib.util.module_from_spec(spec); spec.loader.exec_module(value); return value
W = module('streaming_8x4_rc_conditioning')
Q = module('streaming_8x4_rc_conditioning_parser')
R = module('streaming_8x4_rc_conditioning_readback')
GOOD = (ROOT / 'test/fixtures/streaming-8x4-rc-wire-coarse-20261022.log').read_text()
BAD = (ROOT / 'test/fixtures/streaming-8x4-rc-wire-nonconvergence-20261022.log').read_text()
M1_BAD = (ROOT / 'test/fixtures/streaming-8x4-rc-layered-coarse-physics-failure-20261022.log').read_text()
NAMES = ['g1_GND_SUB', 'g2_SIGNAL']


class ConditioningControls(unittest.TestCase):
    def synthetic_log(self, branch):
        raw = GOOD.replace('Potential interaction coefficient to mesh refinement ratio (-d): 1',
            'Potential interaction coefficient to mesh refinement ratio (-d): ' + branch['interaction_ratio'])
        raw = raw.replace('Mesh refinement (-m): 0.000383703', 'Mesh refinement (-m): ' + branch['mesh'])
        if branch['preconditioner'] != 'jacobi':
            raw = raw.replace('Precond Type(s) (-p): Jacobi ',
                'Precond Type(s) (-p): Two-levels, two-levels preconditioner dimension (-ps): 128 ')
        return raw

    def test_two_profiles_have_exact_fixed_policy_and_no_branch_override(self):
        a, b = Q.PROFILES
        self.assertEqual([(x['preconditioner'], x['interaction_ratio']) for x in Q.branches(a)], [('jacobi', '1'), ('jacobi', '0.25')])
        self.assertEqual([x['mesh'] for x in Q.branches(b)], Q.MESHES)
        self.assertEqual(W.policy(a)['outer_seconds'], 330); self.assertEqual(W.policy(b)['outer_seconds'], 720)
        for branch in Q.branches(b):
            self.assertEqual(Q.argv(branch, b)[-2:], ['-pn', '-ps128'])
            self.assertIn('-d0.25', Q.argv(branch, b)); self.assertIn('-t0.0005', Q.argv(branch, b))
        with self.assertRaises(ValueError): Q.branches('choose-best')

    def test_strict_parser_binds_headers_mesh_unit_and_preconditioner(self):
        for profile in Q.PROFILES:
            unit = '0.00000095367431640625' if profile == Q.PROFILES[0] else '0.000001'
            for branch in Q.branches(profile):
                raw = self.synthetic_log(branch)
                value = Q.parse(raw, NAMES, branch, profile, unit)
                self.assertFalse(value['model_qualified']); self.assertFalse(value['independent_true_residual_enclosure'])
                for wrong in (raw + '\nprogress Warning: bad\n', raw + '\nPrecond Type(s) (-p): Jacobi\n',
                              raw.replace('GMRES Iteration: 0 1 ', 'GMRES Iteration: 0 3 ', 1)):
                    with self.assertRaises(ValueError): Q.parse(wrong, NAMES, branch, profile, unit)
                with self.assertRaises(ValueError): Q.parse(raw, NAMES, branch, profile, '1')

    def test_raw_observation_cannot_qualify_warning_or_negative_rows(self):
        names = ['g1_GND_SUB', 'g2_W1', 'g3_W2']; observation = Q.observations(M1_BAD, names)
        self.assertFalse(observation['numeric_acceptance']); self.assertEqual(len(observation['warning_or_error_lines']), 2)
        self.assertFalse(observation['raw_matrix']['physics_passed'])
        self.assertEqual(observation['raw_matrix']['printed_row_sums'][1:], ['-1.595E-12', '-1.053E-12'])
        self.assertEqual(W.E.sha(ROOT / 'test/fixtures/streaming-8x4-rc-layered-coarse-physics-failure-20261022.log'),
            W.BASELINES[Q.PROFILES[0]]['observed_log'])
        with self.assertRaises(ValueError): Q.parse(M1_BAD, names, Q.branches(Q.PROFILES[0])[0], Q.PROFILES[0], '0.00000095367431640625')

    def test_exit_zero_nonconvergence_stays_failed_in_independent_readback(self):
        profile = Q.PROFILES[0]; branch = Q.branches(profile)[0]
        plan = {'profile': profile, 'case': {'name': W.BASELINES[profile]['case'], 'matrix_names': NAMES, 'coordinate_unit_m': '0.00000095367431640625'}}
        row = {'schema': 'pinwheel.streaming-8x4-rc-conditioning-leaf.v1', 'profile': profile,
            'case': plan['case']['name'], 'branch': branch, 'argv': Q.argv(branch, profile), 'environment': W.ENVIRONMENT,
            'qualified': False, 'model_qualified': False, 'full_pilot_passed': False, 'timeout_seconds': 120,
            'exit_code': 0, 'timed_out': False, 'passed': False, 'numeric': None,
            'error': 'ValueError: Warning/failure marker anywhere in conditioning solver log', 'observations': Q.observations(BAD, NAMES)}
        self.assertFalse(R.numeric_readback(BAD, row, plan, branch)['passed'])
        with self.assertRaises(ValueError): R.numeric_readback(BAD, dict(row, passed=True), plan, branch)

    def test_no_packet_prefix_reorder_or_promotion(self):
        for profile in Q.PROFILES:
            row = {'schema': 'pinwheel.streaming-8x4-rc-conditioning-execution.v1', 'profile': profile,
                'plan_sha256': 'seal', 'policy': W.policy(profile), 'qualified': False, 'model_qualified': False,
                'full_pilot_passed': False, 'measurement_packet_completed': True, 'inputs_runtime_unchanged': True,
                'passed': False, 'jobs': [{'branch': b} for b in Q.branches(profile)]}
            R.membership(row, 'seal', profile)
            for jobs in (row['jobs'][:-1], list(reversed(row['jobs'])), row['jobs'] + [row['jobs'][0]]):
                with self.assertRaises(ValueError): R.membership(dict(row, jobs=jobs), 'seal', profile)
            with self.assertRaises(ValueError): R.membership(dict(row, model_qualified=True), 'seal', profile)

    def test_five_mesh_aggregate_retains_failure_and_original_two_percent_gate(self):
        profile = Q.PROFILES[1]
        rows = [{'branch': b, 'passed': True, 'numeric': Q.parse(self.synthetic_log(b), NAMES, b, profile, '0.000001')} for b in Q.branches(profile)]
        self.assertTrue(Q.aggregate(profile, rows)['mesh_stability_passed'])
        failed = copy.deepcopy(rows); failed[2]['passed'] = False; failed[2]['numeric'] = None
        self.assertFalse(Q.aggregate(profile, failed)['mesh_stability_passed'])
        jump = copy.deepcopy(rows); jump[-1]['numeric']['matrix'] = [[str(W.P.number(x) * 2) for x in row] for row in jump[-1]['numeric']['matrix']]
        result = Q.aggregate(profile, jump); self.assertFalse(result['mesh_stability_passed']); self.assertEqual(result['mesh_error'], 'Cellwise mesh stability failed')

    def test_reaping_and_source_seals_required_before_advancing_failed_branch(self):
        row = {'exit_code': 0, 'solver_executed': True, 'process_tree_reaped': True,
               'copied_inputs_unchanged': True, 'source_runtime_unchanged': True, 'producer_plan_unchanged': True}
        W.D.closed_leaf(row)
        for key in row:
            with self.assertRaises(ValueError): W.D.closed_leaf(dict(row, **{key: None if key == 'exit_code' else False}))

    def test_container_policy_preserves_offline_readonly_bounded_resources(self):
        with tempfile.TemporaryDirectory() as temporary:
            owner = Path(temporary).resolve()
            for profile in Q.PROFILES:
                plan = {'profile': profile, 'producer_sha256': {}}
                with patch.object(W, 'verify', return_value=plan), patch.object(W, 'runtime_unchanged', return_value=True):
                    proposal = W.container_proposal(owner, 'seal', owner, owner)
                argv = proposal['argv']
                for flag, expected in (('--memory', '6g'), ('--memory-swap', '6g'), ('--cpus', '1'),
                                       ('--network', 'none'), ('--pids-limit', '128'), ('--pull', 'never')):
                    self.assertEqual(argv[argv.index(flag) + 1], expected)
                self.assertIn('--read-only', argv); self.assertIn(W.D.IMAGE, argv)
                self.assertEqual(sum(x.endswith(',readonly') for x in argv), 3)
                self.assertEqual(proposal['timeout_seconds'], W.policy(profile)['outer_seconds'])

    def test_resource_reopener_requires_exact_cleanup_timeout_and_source_seals(self):
        with tempfile.TemporaryDirectory() as temporary:
            owner = Path(temporary).resolve(); proposal_path = owner / 'proposal.json'; proposal_path.write_text('{}')
            plan_path = owner / 'plan.json'; plan_path.write_text('{}')
            producer = Path(W.__file__).resolve()
            plan = {'profile': Q.PROFILES[0], 'policy': W.policy(Q.PROFILES[0]),
                    'producer_sha256': {producer.name: W.E.sha(producer)}}
            proposal = {'argv': ['exact', 'command'], 'plan_sha256': W.E.sha(plan_path)}
            report = {'passed': False}
            resource = {'schema': 'pinwheel.streaming-tt-resource-job.v1', 'cleanup_confirmed': True,
                'inputs_unchanged': True, 'containers_remaining': [], 'owned_processes_remaining': [], 'cleanup_errors': [],
                'argv': proposal['argv'], 'timeout_seconds': 330, 'exit_code': 2, 'status': 'failed',
                'input_sha256': {str(proposal_path): W.E.sha(proposal_path), str(plan_path): W.E.sha(plan_path), str(producer): W.E.sha(producer)}}
            resource_path = owner / 'resource.json'
            for change in ({}, {'cleanup_confirmed': False}, {'timeout_seconds': 331}, {'owned_processes_remaining': [123]},
                           {'exit_code': 0}, {'input_sha256': {}}):
                resource_path.write_text(json.dumps(dict(resource, **change)))
                if change:
                    with self.assertRaises((ValueError, KeyError)): R.resource_join(resource_path, proposal_path, proposal, owner, plan, report)
                else: self.assertTrue(R.resource_join(resource_path, proposal_path, proposal, owner, plan, report)['cleanup_confirmed'])


if __name__ == '__main__': unittest.main()
