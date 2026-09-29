"""Acceptance regressions for false-clean and partially restored route imports."""
from copy import deepcopy
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
from physical_route_import import compare_grids, compare_routes, control_verdict, parse_segments


def grid(capacity=None, usage=None):
    cap = capacity or [[2, 2], [2, 2]]
    use = usage or [[3, 1], [0, 0]]
    return dict(grid_x=[0, 10], grid_y=[0, 10], layers=dict(Metal3=dict(
        capacity=cap, usage=use, total_capacity=sum(map(sum, cap)),
        total_usage=sum(map(sum, use)),
        overflow=sum(max(0, u - c) for cs, us in zip(cap, use) for c, u in zip(cs, us)))))


ROUTES = 'clk\n(\n0 0 Metal3 10 0 Metal3\n)\ndata\n(\n0 0 Metal2 0 10 Metal2\n)\n'


class RouteImportTests(unittest.TestCase):
    def test_exact_control(self):
        routes = parse_segments(ROUTES)
        result = control_verdict(compare_routes(routes, routes, ['clk']), compare_grids(grid(), grid()),
                                 physical_identity=True, measurements_equal=True)
        self.assertEqual(result['status'], 'passed')

    def test_zero_demand_is_not_improvement(self):
        routes = parse_segments(ROUTES)
        empty = grid(usage=[[0, 0], [0, 0]])
        result = control_verdict(compare_routes(routes, routes, ['clk']), compare_grids(grid(), empty),
                                 physical_identity=True, measurements_equal=True)
        self.assertEqual(result['failures'], ['resource_accounting'])
        self.assertFalse(result['candidate_admitted'])

    def test_same_overflow_does_not_admit_capacity_drift(self):
        changed = grid(capacity=[[2, 3], [2, 2]])
        self.assertEqual(changed['layers']['Metal3']['overflow'], 1)
        self.assertFalse(compare_grids(grid(), changed)['equal'])

    def test_same_total_does_not_admit_spatial_drift(self):
        changed = grid(usage=[[3, 0], [1, 0]])
        diff = compare_grids(grid(), changed)
        self.assertEqual(diff['layers']['Metal3']['usage']['net_change'], 0)
        self.assertFalse(diff['equal'])

    def test_clock_route_change(self):
        routes = parse_segments(ROUTES)
        other = parse_segments(ROUTES.replace('10 0 Metal3', '20 0 Metal3'))
        self.assertEqual(compare_routes(routes, other, ['clk'])['changed_clock_nets'], ['clk'])

    def test_route_order_and_direction_are_immaterial(self):
        routes = parse_segments(ROUTES)
        other = parse_segments(ROUTES.replace('0 0 Metal3 10 0 Metal3', '10 0 Metal3 0 0 Metal3'))
        self.assertTrue(compare_routes(routes, other, ['clk'])['equal'])

    def test_duplicate_segment_is_not_dropped(self):
        routes = parse_segments(ROUTES)
        other = deepcopy(routes)
        other['data'].append(other['data'][0])
        self.assertEqual(compare_routes(routes, other, ['clk'])['changed_nets'], ['data'])

    def test_missing_clock_and_net_are_rejected(self):
        routes = parse_segments(ROUTES)
        with self.assertRaises(ValueError):
            compare_routes(routes, routes, ['missing'])
        self.assertFalse(compare_routes(routes, {'clk': routes['clk']}, ['clk'])['equal'])

    def test_incomplete_or_invalid_exports(self):
        for text in ['', ROUTES[:-2], ROUTES + ROUTES, ROUTES.replace('0 10 Metal2', '10 10 Metal2')]:
            with self.subTest(text=text), self.assertRaises(ValueError):
                parse_segments(text)

    def test_stale_grid_summary_and_bad_values(self):
        for value in [-1, float('nan'), 1.5, True, 100]:
            changed = grid()
            changed['layers']['Metal3']['usage'][0][0] = value
            with self.subTest(value=value), self.assertRaises(ValueError):
                compare_grids(grid(), changed)

    def test_grid_and_layer_mismatch(self):
        changed = grid()
        changed['grid_x'] = [0, 11]
        self.assertFalse(compare_grids(grid(), changed)['equal'])
        changed = grid()
        changed['layers']['Metal4'] = changed['layers'].pop('Metal3')
        self.assertFalse(compare_grids(grid(), changed)['equal'])

    def test_timing_or_identity_failure_blocks(self):
        for physical, timing in [(False, True), (True, False)]:
            self.assertEqual(control_verdict({'equal': True}, {'equal': True},
                physical_identity=physical, measurements_equal=timing)['status'], 'rejected')
        with self.assertRaises(ValueError):
            control_verdict({'equal': True}, {'equal': True}, physical_identity=True, measurements_equal=None)


if __name__ == '__main__':
    unittest.main()
