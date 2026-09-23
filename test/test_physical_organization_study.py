from copy import deepcopy
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
from physical_organization_study import timing_budget, replication_cost


def matched(kind='max', source='launch/Q', sink='out'):
    spec = dict(delay=kind, source=source, sink=sink,
                source_kind='pin' if '/' in source else 'port',
                sink_kind='pin' if '/' in sink else 'port',
                expected_data_path=[dict(pin=p, edge='^', cell='cell') for p in (source, sink)])
    comp = dict(before={}, after={}, data_arc_deltas=[], clock_arc_deltas={})
    for label in ('before', 'after'):
        comp[label] = dict(arrival_ns=3., required_ns=4. if kind == 'max' else 2., slack_ns=1.,
                           launch_clock_ns=1. if '/' in source else 0.,
                           capture_clock_ns=1. if '/' in sink else None)
    for row in spec['expected_data_path']:
        comp['data_arc_deltas'].append(dict(before=row.copy(), after=row.copy()))
    for name, endpoint in [('launch_clock', source), ('capture_clock', sink)]:
        row = dict(pin=endpoint.split('/')[0] + '/CLK', edge='^', cell='ff', arrival_ns=1.)
        comp['clock_arc_deltas'][name] = [dict(before=row.copy(), after=row.copy())] if '/' in endpoint else []
    return comp, spec


class TimingWindows(unittest.TestCase):
    def test_output_setup_bounds_launch_clock_lateness(self):
        report = timing_budget(*matched(), .2)
        self.assertEqual(report['clock_shift_coefficients'], {'launch/CLK': -1})
        self.assertEqual(report['isolated_clock_shift_bounds_ns']['launch/CLK'],
                         dict(lower_ns=None, upper_ns=.8))
        self.assertFalse(report['complete_clock_window'])

    def test_input_hold_bounds_capture_clock_lateness(self):
        report = timing_budget(*matched('min', 'input', 'capture/D'), .2)
        self.assertEqual(report['clock_shift_coefficients'], {'capture/CLK': -1})
        self.assertEqual(report['isolated_clock_shift_bounds_ns']['capture/CLK']['upper_ns'], .8)

    def test_setup_and_hold_have_opposite_relative_clock_signs(self):
        for kind, expected in [('max', {'launch/CLK': -1, 'capture/CLK': 1}),
                               ('min', {'launch/CLK': 1, 'capture/CLK': -1})]:
            r = timing_budget(*matched(kind, 'launch/Q', 'capture/D'), .2)
            self.assertEqual(r['clock_shift_coefficients'], expected)
            self.assertEqual(r['isolated_clock_shift_bounds_ns'], {})

    def test_shared_clock_identity_cancels(self):
        r = timing_budget(*matched('min', 'same/Q', 'same/D'), .2)
        self.assertTrue(r['common_clock_shift_cancels'])
        self.assertEqual(r['clock_shift_coefficients'], {})

    def test_package_path_does_not_claim_shared_clock_cancellation(self):
        r = timing_budget(*matched('max', 'in', 'out'), .2)
        self.assertFalse(r['common_clock_shift_cancels'])

    def test_positive_slack_can_miss_reserve(self):
        r = timing_budget(*matched(), 1.2)
        self.assertTrue(r['meets_zero_slack'])
        self.assertFalse(r['meets_retained_floor'])
        self.assertAlmostEqual(r['required_slack_gain_ns'], .2)
        self.assertAlmostEqual(r['isolated_clock_shift_bounds_ns']['launch/CLK']['upper_ns'], -.2)

    def test_replay_changes_clock_environment_and_keeps_current_data(self):
        c, s = matched()
        c['before'].update(arrival_ns=2.5, launch_clock_ns=.5, slack_ns=1.5)
        c['clock_arc_deltas']['launch_clock'][0]['before']['arrival_ns'] = .5
        r = timing_budget(c, s, 1.2)
        self.assertAlmostEqual(r['restored_saved_clock_environment_slack_ns'], 1.5)
        self.assertTrue(r['restored_environment_meets_floor'])

    def test_changed_path_clock_or_scalar_rejected(self):
        mutations = [lambda c: c['data_arc_deltas'][0]['after'].update(edge='v'),
                     lambda c: c['clock_arc_deltas']['launch_clock'][0]['after'].update(pin='other/CLK'),
                     lambda c: c['clock_arc_deltas']['launch_clock'].clear(),
                     lambda c: c['after'].update(slack_ns=2),
                     lambda c: c['after'].update(arrival_ns=float('nan')),
                     lambda c: c['after'].update(launch_clock_ns=.1)]
        for mutate in mutations:
            c, s = matched(); mutate(c)
            with self.assertRaises(ValueError): timing_budget(c, s, .2)
        for bad in [-1, float('inf'), True]:
            with self.assertRaises(ValueError): timing_budget(*matched(), bad)


class Replication(unittest.TestCase):
    def fixture(self):
        class Library:
            def capacitance_edges(self, corner, cell, pin):
                return dict(rise=[.01, .03 if pin == 'A' else .01],
                            fall=[.01, .01 if pin == 'A' else .03])
        context = dict(dbu_per_micron=1,
                       instances={'decode': dict(cell='xor', macro=False, bbox_dbu=[0, 0, 3, 2])},
                       nets={'in': dict(type='SIGNAL', terminals=[
                           dict(instance='decode', pin=p, direction='INPUT') for p in ['A', 'B']]),
                             'out': dict(type='SIGNAL', terminals=[
                                 dict(instance='decode', pin='X', direction='OUTPUT')])})
        return context, Library()

    def test_shared_input_caps_aggregate_by_edge_and_area_is_exact(self):
        c, lib = self.fixture(); before = deepcopy(c)
        r = replication_cost(c, lib, 'decode', ['fast'], 2)
        self.assertEqual(r['extra_cell_area_um2'], 12)
        self.assertAlmostEqual(r['extra_upstream_pin_capacitance_pf']['fast']['in'], .08)
        self.assertIsNone(r['extra_wire_capacitance_pf'])
        self.assertEqual(c, before)

    def test_state_macro_and_clock_replication_rejected(self):
        c, lib = self.fixture(); c['instances']['decode']['macro'] = True
        with self.assertRaises(ValueError): replication_cost(c, lib, 'decode', ['fast'])
        c, lib = self.fixture(); c['nets']['in']['type'] = 'CLOCK'
        with self.assertRaises(ValueError): replication_cost(c, lib, 'decode', ['fast'])
        for copies in [0, -1, True]:
            with self.assertRaises(ValueError): replication_cost(c, lib, 'decode', ['fast'], copies)

    def test_missing_corners_rejected(self):
        c, lib = self.fixture()
        for corners in [[], ['fast', 'fast']]:
            with self.assertRaises(ValueError): replication_cost(c, lib, 'decode', corners)


if __name__ == '__main__':
    unittest.main()
