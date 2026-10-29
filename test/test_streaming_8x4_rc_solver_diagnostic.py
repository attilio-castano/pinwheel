"""Captured-log and membership HOST controls; no recovered executable runs."""
import copy
import importlib.util
import json
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]; SCRIPTS = ROOT / 'scripts'
def module(name):
    spec = importlib.util.spec_from_file_location(name, SCRIPTS / (name + '.py'))
    result = importlib.util.module_from_spec(spec); spec.loader.exec_module(result); return result
W = module('streaming_8x4_rc_solver_diagnostic')
Q = module('streaming_8x4_rc_solver_diagnostic_parser')
R = module('streaming_8x4_rc_solver_diagnostic_readback')
GOOD = (ROOT / 'test/fixtures/streaming-8x4-rc-wire-coarse-20261022.log').read_text()
BAD = (ROOT / 'test/fixtures/streaming-8x4-rc-wire-nonconvergence-20261022.log').read_text()
NAMES = ['g1_GND_SUB', 'g2_SIGNAL']


class DiagnosticControls(unittest.TestCase):
    def test_exact_four_branch_factorial_and_explicit_default_clear(self):
        self.assertEqual([(b['preconditioner'], b['interaction_ratio']) for b in Q.BRANCHES],
            [('jacobi', '1'), ('two-level-128', '1'), ('jacobi', '0.25'), ('two-level-128', '0.25')])
        self.assertEqual(Q.argv(Q.BRANCHES[1])[-2:], ['-pn', '-ps128'])
        for branch in Q.BRANCHES:
            self.assertIn('-m0.000383703', Q.argv(branch)); self.assertIn('-t0.0005', Q.argv(branch))

    def test_captured_valid_Jacobi_log_and_source_derived_header_controls(self):
        for branch in Q.BRANCHES:
            text = GOOD
            # These three modified headers are synthetic grammar controls only,
            # not observations that the new solver branches have executed.
            if branch['preconditioner'] != 'jacobi':
                text = text.replace('Precond Type(s) (-p): Jacobi ',
                    'Precond Type(s) (-p): Two-levels, two-levels preconditioner dimension (-ps): 128 ')
            if branch['interaction_ratio'] != '1':
                text = text.replace('Potential interaction coefficient to mesh refinement ratio (-d): 1',
                    'Potential interaction coefficient to mesh refinement ratio (-d): 0.25')
            parsed = Q.parse(text, NAMES, branch, '0.000001')
            self.assertEqual(parsed['actual_preconditioner'], branch['preconditioner'])
            self.assertFalse(parsed['model_qualified']); self.assertFalse(parsed['independent_true_residual_enclosure'])

    def test_actual_nonconvergence_exit_zero_stays_failed_and_JSON_roundtrips(self):
        branch = Q.BRANCHES[0]
        row = {'argv': Q.argv(branch), 'environment': W.ENVIRONMENT, 'branch': branch, 'case': W.CASE,
               'exit_code': 0, 'timed_out': False, 'passed': False,
               'error': 'ValueError: Warning/failure marker anywhere in diagnostic solver log',
               'failure_evidence': json.loads(json.dumps(Q.failure_evidence(BAD)))}
        plan = {'case': {'matrix_names': NAMES, 'coordinate_unit_m': '0.000001'}}
        result = R.numeric_readback(BAD, row, plan, branch)
        self.assertFalse(result['numeric_passed']); self.assertEqual(result['exit_code'], 0)
        self.assertEqual(result['failure_evidence']['nonconvergence_reports'][0][0], '1000')
        bad = dict(row, passed=True)
        with self.assertRaisesRegex(ValueError, 'numeric/error readback'): R.numeric_readback(BAD, bad, plan, branch)

    def test_warning_anywhere_and_mixed_or_duplicate_preconditioner_rejected(self):
        for text in (GOOD + '\nprogress Warning: synthetic\n',
                     GOOD.replace('Precond Type(s) (-p): Jacobi ', 'Precond Type(s) (-p): Jacobi Two-levels '),
                     GOOD + '\nPrecond Type(s) (-p): Jacobi\n'):
            with self.assertRaises(ValueError): Q.parse(text, NAMES, Q.BRANCHES[0], '0.000001')

    def test_factor_unit_matrix_and_iteration_binding_reject_mismatch(self):
        for text, names, unit in ((GOOD, NAMES, '1'), (GOOD, list(reversed(NAMES)), '0.000001'),
                (GOOD.replace('(-d): 1', '(-d): 0.25'), NAMES, '0.000001'),
                (GOOD.replace('GMRES Iteration: 0 1 ', 'GMRES Iteration: 0 2 ', 1), NAMES, '0.000001')):
            with self.assertRaises(ValueError): Q.parse(text, names, Q.BRANCHES[0], unit)

    def test_no_prefix_duplicate_or_reordered_packet_pass(self):
        record = {'schema': 'pinwheel.streaming-8x4-rc-solver-diagnostic-execution.v1', 'plan_sha256': 'seal',
            'protocol': W.protocol(), 'qualified': False, 'model_qualified': False,
            'uniform_finite_wire_pilot_passed': False, 'measurement_packet_completed': True,
            'inputs_runtime_unchanged': True, 'passed': False, 'jobs': [{'branch': b} for b in Q.BRANCHES]}
        R.membership(record, 'seal')
        for jobs in (record['jobs'][:3], record['jobs'][:3] + [record['jobs'][2]], list(reversed(record['jobs']))):
            bad = copy.deepcopy(record); bad['jobs'] = jobs
            with self.assertRaisesRegex(ValueError, 'four-call diagnostic'): R.membership(bad, 'seal')
        bad = dict(record, model_qualified=True)
        with self.assertRaises(ValueError): R.membership(bad, 'seal')

    def test_cannot_advance_factorial_before_reaping_and_custody(self):
        complete = {'exit_code': 0, 'solver_executed': True, 'process_tree_reaped': True,
            'copied_inputs_unchanged': True, 'source_runtime_unchanged': True, 'producer_plan_unchanged': True}
        W.closed_leaf(complete)
        for key in complete:
            bad = dict(complete); bad[key] = None if key == 'exit_code' else False
            with self.assertRaisesRegex(ValueError, 'Cannot advance factorial'): W.closed_leaf(bad)


if __name__ == '__main__': unittest.main()
