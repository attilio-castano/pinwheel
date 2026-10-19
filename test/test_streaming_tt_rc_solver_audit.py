"""Failure controls for the prepared pure solver-log gate; no native solver runs."""
from copy import deepcopy
from decimal import Decimal
import hashlib
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
import streaming_tt_rc_solver_audit as S


NAMES = ['wire_M1_w1', 'wire_M1_w2']
FRAME = ('Dimension 2 x 2\nwire_M1_w1 2e-15 -1e-15\nwire_M1_w2 -1e-15 2e-15\n'
         'Weighted Frobenius norm of the difference between capacitance (auto option): {norm}\n')
LOG = FRAME.format(norm='.2') + FRAME.format(norm='.005') + 'Total time: 3.2s\n'


def plan(index=1):
    return {'input_sha256': str(index) * 64, 'solver_sha256': 'a' * 64, 'runner_sha256': 'b' * 64,
            'run_id': 'pilot_fresh_run_' + str(index), 'wire_length_um': 10 * index,
            'not_before_utc': '2026-10-18T16:00:00Z', 'not_after_utc': '2026-10-18T17:00:00Z'}


def receipt(log=LOG, expected=None):
    expected = expected or plan()
    return dict(expected, schema='pinwheel.rc-solver-execution.v1', exit_code=0, timed_out=False,
                process_tree_reaped=True, log_sha256=hashlib.sha256(log.encode()).hexdigest(),
                started_utc='2026-10-18T16:01:00Z', ended_utc='2026-10-18T16:01:04Z')


class SolverAuditTests(unittest.TestCase):
    def admit(self, log=LOG, record=None, expected=None, names=NAMES):
        return S.admit_run(log, record or receipt(log, expected), expected or plan(), names, Decimal('.01'))

    def test_only_terminal_converged_matrix_is_admitted_without_qualification(self):
        result = self.admit()
        self.assertEqual(result['iterations'], 2)
        self.assertEqual(result['frobenius_relative_change'], Decimal('.005'))
        self.assertEqual(result['matrix'][0][0], Decimal('2e-15'))
        self.assertFalse(result['qualified'])
        self.assertFalse(result['calibrated'])

    def test_nonzero_timeout_unreaped_or_bool_exit_never_uses_last_matrix(self):
        for key, value in [('exit_code', 1), ('exit_code', True), ('timed_out', True),
                           ('timed_out', None), ('process_tree_reaped', False)]:
            record = receipt(); record[key] = value
            with self.subTest(key=key, value=value), self.assertRaises(ValueError): self.admit(record=record)

    def test_stale_run_inputs_solver_runner_or_log_content_refuse(self):
        for key in ('input_sha256', 'solver_sha256', 'runner_sha256', 'run_id', 'log_sha256'):
            record = receipt(); record[key] = 'c' * 64
            with self.subTest(key=key), self.assertRaises(ValueError): self.admit(record=record)

    def test_old_out_of_window_inverted_or_naive_timestamps_refuse(self):
        for key, value in [('started_utc', '2026-10-17T16:01:00Z'), ('ended_utc', '2026-10-18T17:01:00Z'),
                           ('ended_utc', '2026-10-18T16:00:00Z'), ('started_utc', '2026-10-18T16:01:00')]:
            record = receipt(); record[key] = value
            with self.subTest(key=key, value=value), self.assertRaises(ValueError): self.admit(record=record)

    def test_wrong_dimensions_missing_cells_names_duplicates_or_reordering_refuse(self):
        for log in (LOG.replace('2 x 2', '2 x 3'), LOG.replace('2 x 2', '3 x 3'),
                    LOG.replace('2e-15 -1e-15', '2e-15'), LOG.replace('wire_M1_w2', 'wire_other'),
                    LOG.replace('wire_M1_w2', 'wire_M1_w1'),
                    LOG.replace('wire_M1_w1', 'temporary').replace('wire_M1_w2', 'wire_M1_w1').replace('temporary', 'wire_M1_w2')):
            with self.subTest(log=log[:80]), self.assertRaises(ValueError): self.admit(log)

    def test_nan_inf_and_nonfinite_convergence_refuse(self):
        for log in (LOG.replace('2e-15', 'NaN'), LOG.replace('-1e-15', '-Inf'),
                    LOG.replace('.005', 'nan'), LOG.replace('.005', 'Infinity')):
            with self.subTest(log=log[:80]), self.assertRaises(ValueError): self.admit(log)

    def test_last_metric_above_accuracy_refuses_even_after_good_earlier_iteration(self):
        log = FRAME.format(norm='.001') + FRAME.format(norm='.02') + 'Total time: 3s\n'
        with self.assertRaisesRegex(ValueError, 'convergence'): self.admit(log)

    def test_truncated_or_failed_tail_cannot_upgrade_completed_prefix(self):
        for log in (LOG.replace('Total time: 3.2s\n', ''),
                    FRAME.format(norm='.005') + 'Dimension 2 x 2\nwire_M1_w1 1 2\n',
                    LOG + 'Dimension 2 x 2\n', LOG + 'Killed after 600 s\n', LOG + 'Fatal error\n'):
            with self.subTest(log=log[-80:]), self.assertRaises(ValueError): self.admit(log)

    def test_unbound_metric_duplicate_footer_and_duplicate_iteration_metric_refuse(self):
        for log in ('Weighted Frobenius: .001\n' + LOG, LOG + 'Total time: 4s\n',
                    FRAME.format(norm='.005') + 'Weighted Frobenius: .001\nTotal time: 3s\n'):
            with self.subTest(log=log[:80]), self.assertRaises(ValueError): self.admit(log)

    def test_wire_length_is_bound_to_separate_plan(self):
        record = receipt(); record['wire_length_um'] = 20
        with self.assertRaisesRegex(ValueError, 'length'): self.admit(record=record)

    def test_distinct_length_pair_has_no_cancellation_or_calibration_claim(self):
        second_log = LOG.replace('2e-15', '4e-15').replace('-1e-15', '-2e-15')
        result = S.admit_pair(LOG, receipt(), plan(), second_log, receipt(second_log, plan(2)), plan(2), NAMES, Decimal('.01'))
        self.assertEqual(result['matrix_difference_per_um'][0][0], Decimal('2e-16'))
        self.assertFalse(result['end_effect_cancellation_validated'])
        self.assertFalse(result['qualified'])

    def test_reused_job_input_or_mismatched_solver_and_bad_length_pair_refuse(self):
        for change in ('run_id', 'input_sha256', 'solver_sha256', 'wire_length_um'):
            expected2 = deepcopy(plan(2))
            expected2[change] = plan()[change] if change != 'solver_sha256' else 'c' * 64
            with self.subTest(change=change), self.assertRaises(ValueError):
                S.admit_pair(LOG, receipt(), plan(), LOG, receipt(LOG, expected2), expected2, NAMES, Decimal('.01'))


if __name__ == '__main__':
    unittest.main()
