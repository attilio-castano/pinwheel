import importlib.util
from pathlib import Path
import sys
import unittest

TOOLS = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(TOOLS))
from drc import compare_native_stages, parse_native_log, parse_report_subset

REPO = TOOLS.parents[1]
HISTORY = REPO / "build/physical"


class NativeDRCTest(unittest.TestCase):
    def test_actual_four_row_native_final_and_capped_report(self):
        root = HISTORY / "tt-p2-drt-onepass-route-01"
        result = parse_native_log((root / "native.log").read_text(),
                                  (root / "drt/violations.rpt").read_text(), category_limit=10000)
        self.assertEqual(result["completed_native_final_count"], 30218)
        self.assertEqual(result["completed_native_type_counts"],
                         {"Short": 17252, "Cut Short": 690, "Metal Spacing": 6829,
                          "Cut Spacing": 7, "Recheck": 5440})
        self.assertEqual(result["report_subset"]["record_count"], 22966)
        self.assertEqual(result["report_subset"]["native_minus_report_by_type"]["Short"], 7252)
        self.assertFalse(result["report_subset"]["report_is_complete_native_ledger"])
        self.assertEqual(result["report_subset"]["categories_at_known_limit"], ["Short"])
        self.assertFalse(result["all_native_terminal_connectivity_proven"])

    def test_actual_three_row_control_not_error_or_fixed_row_crash(self):
        root = HISTORY / "tt-p2-legalization-trial-02/control"
        result = parse_native_log((root / "native.log").read_text(), producer_status="failed")
        self.assertEqual(result["completed_native_final_count"], 22149)
        self.assertEqual(len(result["completed_native_final_table"]["rows"]), 3)
        self.assertEqual(result["producer_status_retained"], "failed")
        self.assertFalse(result["physical_signoff_or_acceptance_claim"])
        self.assertFalse(result["native_modified_mapped_pin_checker_failure_lines"])

    def test_actual_partial_progress_is_not_native_final(self):
        text = (HISTORY / "tt-p2-drt-probe-02/native.log").read_text()
        result = parse_native_log(text)
        self.assertTrue(result["progress_observations"])
        self.assertIsNone(result["completed_native_final_count"])

    def test_truncated_or_inconsistent_table_never_falls_back(self):
        text = """Start 0th optimization iteration.
Number of violations = 3.
Viol/Layer Metal2 Via2
Short 2 1
Start 1st optimization iteration.
Number of violations = 10.
Viol/Layer Metal2 Via2
Short 2 1
Complete detail routing.
"""
        result = parse_native_log(text)
        self.assertIsNone(result["completed_native_final_count"])
        self.assertTrue(result["native_table_observations"][0]["sum_verified"])
        self.assertFalse(result["native_table_observations"][1]["sum_verified"])
        self.assertIsNone(parse_native_log(text.split("Complete detail routing.")[0])["completed_native_final_count"])

    def test_zero_rows_omitted_and_successful_zero_table(self):
        text = """Start 3rd optimization iteration.
Number of violations = 0.
Viol/Layer Metal1 Via1 Metal2
[INFO DRT-0267] cpu time = 00:00:01
Complete detail routing.
"""
        self.assertEqual(parse_native_log(text)["completed_native_final_count"], 0)

    def test_marker_cap_is_never_implicit_full_coverage(self):
        report = "violation type: Short\n srcs: net:a net:b\n bbox = (0,0) - (1,1) on Layer Metal2\n"
        self.assertFalse(parse_report_subset(report)["report_is_complete_native_ledger"])

    def test_sentinel_does_not_look_like_pin_access_failure(self):
        result = parse_native_log("PINWHEEL_NO_ECO_DRT_PINACCESS_BEGIN\n[ERROR DRT-0206] failed\ncheckConnectivity break net:a\n")
        self.assertEqual(len(result["native_error_lines"]), 1)
        self.assertEqual(len(result["native_modified_mapped_pin_checker_failure_lines"]), 2)

    def test_later_unfinished_stage_does_not_reuse_old_final(self):
        text = """Start 0th optimization iteration.
Number of violations = 1.
Viol/Layer Metal2
Short 1
Complete detail routing.
Start 0th optimization iteration.
Completing 10% with 0 violations.
"""
        result = parse_native_log(text)
        self.assertFalse(result["latest_native_route_completed"])
        self.assertIsNone(result["completed_native_final_count"])

    def test_comparison_never_promotes_failed_control_or_stage_reach_to_acceptance(self):
        control = parse_native_log("Start 0th optimization iteration.\nNumber of violations = 3.\nViol/Layer Metal2 Via2\nShort 2 1\nComplete detail routing.\n", producer_status="failed")
        candidate = parse_native_log("Start 3rd optimization iteration.\nNumber of violations = 1.\nViol/Layer Metal2 Via2\nShort 1 0\nComplete detail routing.\n", producer_status="passed")
        comparison = compare_native_stages(control, candidate, required_candidate_iteration=3)
        self.assertEqual(comparison["candidate_minus_control_count"], -2)
        self.assertTrue(comparison["required_candidate_iteration_observed"])
        self.assertEqual(comparison["control_producer_status_retained"], "failed")
        self.assertFalse(comparison["physical_acceptance_claim"])

    def test_incomplete_report_record_cannot_claim_complete_coverage(self):
        table = {"rows": {"Short": {"Metal2": 1}}}
        result = parse_report_subset("violation type: Short\n srcs: net:a\n", table)
        self.assertEqual(result["record_count"], 1)
        self.assertFalse(result["report_is_complete_native_ledger"])
        self.assertEqual(result["incomplete_record_start_lines"], [1])


if __name__ == "__main__":
    unittest.main()
