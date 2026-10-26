"""Refuse incomplete or relabelled independent-reference evidence."""
from copy import deepcopy
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
import streaming_8x4_rc_protocol as P
import streaming_8x4_rc_analyze as A


def reference():
    p = P.frozen_protocol(); cases = []
    for width in ('0.16', '0.32'):
        for step in ('0.04', '0.02'):
            for extent in ('16', '32'):
                cases.append({'case_id': 'w' + width + '-h' + step + '-E' + extent,
                              'width_um': float(width), 'gap_um': 1.04, 'thickness_um': .42,
                              'mesh_step_um': float(step), 'extent_um': float(extent),
                              'epsilon_layers': [[0., 1000., 4.1]],
                              'qualified': False, 'continuum_error_enclosure': False,
                              'true_residual_relative': 1e-10, 'energy_flux_relative_error': 1e-10,
                              'nodes': 2000, 'cg_iterations': 100,
                              'capacitance_per_length_F_per_m': 1e-10 if width == '0.16' else 1.2e-10})
    return {'schema': 'pinwheel.streaming-8x4-rc-reference-execution.v1', 'passed': True,
            'inputs_unchanged': True, 'qualified': False, 'cases': cases}


class ReferenceAdmissionTests(unittest.TestCase):
    def test_complete_stable_reference_has_two_widths(self):
        result = A.reference_stability({'protocol': P.frozen_protocol()}, reference())
        self.assertEqual(set(result), {'0.16', '0.32'})

    def test_missing_reordered_and_duplicate_reference_cases_fail(self):
        for kind in ('missing', 'reordered', 'duplicate'):
            r = reference()
            if kind == 'missing': r['cases'].pop()
            elif kind == 'reordered': r['cases'].reverse()
            else: r['cases'][-1] = deepcopy(r['cases'][-2])
            with self.assertRaises(ValueError):
                A.reference_stability({'protocol': P.frozen_protocol()}, r)

    def test_case_label_cannot_hide_wrong_width_or_dielectric(self):
        for key, value in [('width_um', .16), ('epsilon_layers', [[0., 1000., 8.2]])]:
            r = reference(); r['cases'][-1][key] = value
            with self.assertRaises(ValueError):
                A.reference_stability({'protocol': P.frozen_protocol()}, r)

    def test_actual_residual_energy_and_domain_instability_are_fatal(self):
        for key, value in [('true_residual_relative', 1e-5), ('energy_flux_relative_error', 1e-4),
                           ('capacitance_per_length_F_per_m', 2e-10), ('qualified', True)]:
            r = reference(); r['cases'][-1][key] = value
            with self.assertRaises(ValueError):
                A.reference_stability({'protocol': P.frozen_protocol()}, r)

    def test_positive_reference_required(self):
        with self.assertRaises(ValueError): A.relative('0', '1')
        with self.assertRaises(ValueError): A.relative('1', '-1')

    def test_borderline_true_residual_cannot_use_a_roundoff_allowance(self):
        r = reference(); r['cases'][-1]['true_residual_relative'] = 1.02e-9
        with self.assertRaisesRegex(ValueError, 'actual residual'):
            A.reference_stability({'protocol': P.frozen_protocol()}, r)
        r['cases'][-1]['true_residual_relative'] = 1e-9
        A.reference_stability({'protocol': P.frozen_protocol()}, r)


if __name__ == '__main__': unittest.main()
