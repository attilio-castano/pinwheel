"""Evidence integrity and exact geometric counterexamples for routing screens."""
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
from routing_evidence import (reconcile_iterations, transform_rect, to_dbu,
    centerline_crosses, geometry_checks, compare_passes, screen_candidate, pin_access_summary)


def log(pass_counts):
    return "".join("Start detail routing.\n" + "".join(
        f"Start {i}th optimization iteration.\nNumber of violations = {v}\n" for i, v in counts)
        for counts in pass_counts)


class RoutingEvidenceTests(unittest.TestCase):
    def test_truncated_step_log_recovers_completed_outer_iteration_only(self):
        a = log([[(64, 73)], [(35, 230)]]) + "Start 36th optimization iteration.\n"
        b = log([[(64, 73)], [(35, 230), (36, 225), (38, 198)]]) + "Start 39th optimization iteration.\n"
        self.assertEqual(list(reconcile_iterations(a, b).items())[-1], ((1, 38), 198))
        self.assertEqual(reconcile_iterations(b, a), reconcile_iterations(a, b))

    def test_disagreeing_counts_or_missing_middle_are_not_cherry_picked(self):
        for a, b in [(log([[(1, 3)]]), log([[(1, 4)]])),
                     (log([[(1, 3), (3, 1)]]), log([[(1, 3), (2, 2), (3, 1)]]))]:
            with self.assertRaisesRegex(ValueError, "disagree"):
                reconcile_iterations(a, b)

    def test_exact_coordinates_and_all_orientation_transforms(self):
        self.assertEqual(to_dbu([252, 94.36, 1036.48, 119.18], 1000), [252000, 94360, 1036480, 119180])
        with self.assertRaises(ValueError):
            to_dbu([0, 0, .0001, 1], 1000)
        expected = {"R0": [11, 22, 13, 25], "R90": [5, 21, 8, 23],
                    "R180": [7, 15, 9, 18], "R270": [12, 17, 15, 19],
                    "MX": [11, 15, 13, 18], "MY": [7, 22, 9, 25],
                    "MXR90": [12, 21, 15, 23], "MYR90": [5, 17, 8, 19]}
        for orientation, box in expected.items():
            self.assertEqual(transform_rect([1, 2, 3, 5], orientation, [10, 20]), box)

    def test_centerline_must_cross_interior_and_match_marker_location(self):
        segment = dict(net="signal", layer="Metal4", start=[5, 0], end=[5, 20])
        self.assertTrue(centerline_crosses(segment, [4, 3, 8, 12]))
        self.assertFalse(centerline_crosses(segment, [5, 3, 8, 12]))
        self.assertFalse(centerline_crosses(segment, [4, 20, 8, 25]))
        context = dict(schema=2, dbu_per_micron=1,
            instances={"ram": dict(macro=True, bbox_dbu=[0, 0, 20, 20])},
            macro_pins=[dict(instance="ram", type="POWER", net="VPWR", layer="Metal4", bbox_dbu=[2, 0, 8, 20])],
            power_shapes=[], signal_segments=[segment], route_coverage={},
            nets={"signal": dict(type="SIGNAL"), "VPWR": dict(type="POWER")})
        marker = dict(rule="Short", layer="Metal4", nets=["VPWR", "signal"], bbox=[3, 1, 4, 19])
        self.assertEqual(geometry_checks([marker], context)["markers_with_fixed_power_centerline_crossing"], 0)
        marker["bbox"] = [4, 1, 6, 19]
        self.assertEqual(geometry_checks([marker], context)["markers_with_fixed_power_centerline_crossing"], 1)

    def test_duplicate_markers_do_not_become_new_physical_causes(self):
        a = dict(rule="Short", layer="Metal4", nets=["a", "b"], bbox=[0, 0, 1, 1])
        b = dict(a, bbox=[1, 1, 2, 2])
        old = dict(instances={}, nets={})
        new = dict(instances={"diode": dict(cell="antenna", bbox_dbu=[0, 0, 1, 1])}, nets={})
        result = compare_passes([a], [a, a, b], old, new)
        self.assertEqual(result["persistent_exact_markers"], 1)
        self.assertEqual(result["new_groups"], 0)
        self.assertEqual(result["added_cell_types"], {"antenna": 1})

    def test_metal4_improvement_cannot_hide_total_congestion_regression(self):
        base = dict(overflow={"Total": 1255}, metal4_guides=129, wirelength_um=1869386,
                    instance_area=483417, repair_area=64128, power_violations=0,
                    slew=0, capacitance=0, fanout=210, setup_slack=11, hold_slack=.25, timing_stage="post-cts-sta")
        full = dict(base, overflow={"Total": 1686}, metal4_guides=87)
        half = dict(base, overflow={"Total": 870}, metal4_guides=45)
        self.assertEqual(screen_candidate(base, full)["decision"], "reject")
        self.assertEqual(screen_candidate(base, half)["decision"], "eligible_for_bounded_trial")
        self.assertEqual(screen_candidate(base, dict(half, timing_stage="resizer"))["decision"], "reject")
        with self.assertRaises(ValueError):
            screen_candidate(base, dict(half, wirelength_um=float("nan")))

    def test_pin_access_requires_completed_counts_and_keeps_grid_warnings_separate(self):
        log = "[WARNING DRT-0418] Term ram/A has no pins on routing grid\nComplete pin access.\n"
        log += "#stdCellPinCnt = 100\n#stdCellPinNoAp = 0\n#macroGenAp = 10\n#macroValidPlanarAp = 8\n#macroValidViaAp = 0\n#macroNoAp = 0\n"
        result = pin_access_summary(log)
        self.assertEqual(result["decision"], "pass")
        self.assertEqual(result["off_grid_warnings"], 1)
        self.assertEqual(pin_access_summary(log.replace("#macroNoAp = 0", "#macroNoAp = 1"))["decision"], "reject")
        self.assertEqual(pin_access_summary(log.replace("Complete pin access.", ""))["decision"], "inconclusive")


if __name__ == "__main__":
    unittest.main()
