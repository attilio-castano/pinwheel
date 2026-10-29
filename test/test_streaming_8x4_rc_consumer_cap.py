"""Focused HOST controls for the distinct capacitance diagnostic; no Native."""
from decimal import Decimal as D
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
import streaming_8x4_rc_consumer_cap as W
import streaming_8x4_rc_consumer_cap_spef as Q
import streaming_8x4_rc_consumer_cap_readback as R


def spef(unit='FF', factor=D(1)):
    text = '*SPEF "ieee 1481-1999"\n*DESIGN_FLOW "NAME_SCOPE LOCAL" "PIN_CAP NONE"\n*C_UNIT 1 ' + unit + '\n'
    for name, other, ground in (('a', 'b', 2), ('b', 'a', 3)):
        # Deliberately reverse mirrored endpoint order; identity is unordered.
        text += (f'*D_NET {name} {D(ground + 5) * factor}\n\n*CONN\n*P {name}_A I\n*P {name}_B O\n'
                 f'*CAP\n1 {name}_A {D(ground) * factor}\n2 {name}_A {other}_A {D(5) * factor}\n'
                 f'*RES\n1 {name}_A {name}_B 1\n*END\n')
    return text


def values(job, perturb=False):
    row = W.definition(job); groups = []
    for length in (50, 100, 150):
        names = [r['net'] for r in row['rows'] if r['length_um'] == length]
        c = D(length) * D('1e-6') * D('1e-10')
        if perturb and length == 150:
            c *= D('1.2')
        matrix = [[c]] if len(names) == 1 else [[2 * c, -c], [-c, 2 * c]]
        groups.append({'names': names, 'matrix_F': [[str(x) for x in v] for v in matrix]})
    return {'groups': groups}


class CapControls(unittest.TestCase):
    def test_full_incident_total_and_single_mirror_count(self):
        got = Q.parse(spef(), ['a', 'b'], {'a': 'b', 'b': 'a'})
        self.assertEqual(got['unique_coupling_segments'], 1)
        self.assertEqual([[D(x) for x in r] for r in got['groups'][0]['matrix_F']],
                         [[D('7e-15'), D('-5e-15')], [D('-5e-15'), D('8e-15')]])
        self.assertEqual([D(x) for x in got['groups'][0]['ground_F']], [D('2e-15'), D('3e-15')])

    def test_FF_PF_unit_conversion_and_writer_rounding(self):
        a = Q.parse(spef(), ['a', 'b'], {'a': 'b', 'b': 'a'})
        b = Q.parse(spef('PF', D('.001')), ['a', 'b'], {'a': 'b', 'b': 'a'})
        self.assertEqual([[D(x) for x in r] for r in a['groups'][0]['matrix_F']],
                         [[D(x) for x in r] for r in b['groups'][0]['matrix_F']])
        self.assertEqual(Q.rounding(D('2e-5')), D('5e-11'))

    def test_missing_unequal_and_duplicate_mirrors_reject(self):
        for bad in (spef().replace('2 b_A a_A 5\n', ''),
                    spef().replace('2 b_A a_A 5', '2 b_A a_A 4'),
                    spef().replace('2 b_A a_A 5', '2 b_A a_A 5\n3 b_A a_A 5')):
            with self.assertRaises(ValueError):
                Q.parse(bad, ['a', 'b'], {'a': 'b', 'b': 'a'})

    def test_half_coupling_total_and_unknown_net_reject(self):
        for bad in (spef().replace('*D_NET a 7', '*D_NET a 4.5'),
                    spef().replace('a_A b_A 5', 'a_A foreign:1 5')):
            with self.assertRaises(ValueError):
                Q.parse(bad, ['a', 'b'], {'a': 'b', 'b': 'a'})

    def test_missing_unit_negative_disconnected_and_ITerm_reject(self):
        for bad in (spef().replace('*C_UNIT 1 FF', '*C_UNIT 1 NF'),
                    spef().replace('1 a_A 2', '1 a_A -2'),
                    spef().replace('1 a_A a_B 1', '1 a_A a:1 1'),
                    spef().replace('*P a_A I', '*I a_A I')):
            with self.assertRaises(ValueError):
                Q.parse(bad, ['a', 'b'], {'a': 'b', 'b': 'a'})

    def test_exact_four_geometries_and_default_width_physical_units(self):
        for job in W.JOBS:
            row = W.definition(job); self.assertTrue(W.validate_geometry(W.fixture(row), row))
            self.assertEqual(sorted(set(r['length_um'] for r in row['rows'])), [50, 100, 150])
            for r in row['rows']:
                self.assertEqual(r['end_DBU'][0] - r['start_DBU'][0], r['length_um'] * 1000)
            with self.assertRaises(ValueError):
                W.validate_geometry(W.fixture(row).replace('MICRONS 1000', 'MICRONS 2000'), row)
        self.assertIn('-coupling_threshold 0', W.tcl())
        self.assertNotIn('-lef_rc', W.tcl())

    def test_complete_length_slopes_isolation_and_missing_membership(self):
        rows = [{'job': j, 'values': values(j)} for j in W.JOBS]
        self.assertTrue(W.measurements(rows)['measurement_controls_passed'])
        rows[0]['values'] = values(W.JOBS[0], perturb=True)
        self.assertFalse(W.measurements(rows)['measurement_controls_passed'])
        with self.assertRaises(ValueError): W.measurements(rows[:-1])

    def test_absent_reference_accuracy_is_unmeasured(self):
        got = R.accuracy(None, None, None, None)
        self.assertEqual(got['accuracy_status'], 'unmeasured')
        self.assertFalse(got['independent_accuracy_passed'])
        with self.assertRaises(ValueError): R.accuracy(None, None, None, {'reference_directory': Path('/unused')})


if __name__ == '__main__': unittest.main()
