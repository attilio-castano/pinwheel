"""Router reports must not silently discard malformed or duplicate markers."""
import importlib.util
from pathlib import Path
import sys
import unittest

SCRIPTS = Path(__file__).resolve().parents[1] / "scripts"
sys.path.insert(0, str(SCRIPTS))
spec = importlib.util.spec_from_file_location("diagnosis", SCRIPTS / "diagnose-routing.py")
diagnosis = importlib.util.module_from_spec(spec)
spec.loader.exec_module(diagnosis)

MARKER = """violation type: Metal Spacing
 srcs: net:data net:VPWR
 bbox = (9.5, 12.0) - (10.0, 12.2) on Layer Metal2
"""


class RoutingDiagnosisTests(unittest.TestCase):
    def test_parser_keeps_raw_marker_count_and_net_identity(self):
        markers = diagnosis.parse_report(MARKER * 2)
        self.assertEqual(len(markers), 2)
        self.assertEqual(markers[0]["nets"], ["VPWR", "data"])
        self.assertEqual(markers[0]["bbox"], [9.5, 12.0, 10.0, 12.2])
        self.assertEqual(diagnosis.parse_report("\n"), [])

    def test_truncation_unknown_lines_and_invalid_boxes_are_rejected(self):
        for text in [MARKER[:-20], "warning\n" + MARKER, MARKER + "partial",
                     MARKER.replace("9.5,", "10.5,"), MARKER.replace("9.5,", "1e999,")]:
            with self.subTest(text=text), self.assertRaises(ValueError):
                diagnosis.parse_report(text)

    def test_counts_proximity_and_connectivity_do_not_merge_causes(self):
        context = dict(instances={"macro0": dict(macro=True, bbox=[10, 10, 20, 20]),
                                  "macro1": dict(macro=True, bbox=[10, 10, 20, 20])},
                       nets={"VPWR": dict(type="POWER"), "data": dict(type="SIGNAL")})
        result = diagnosis.summarize(diagnosis.parse_report(MARKER * 2), context)
        self.assertEqual(result["marker_count"], 2)
        self.assertEqual(result["exact_unique_markers"], 1)
        self.assertEqual(result["involving_power_net"], 2)
        self.assertEqual(result["near_macros"], {"0": 2, "5": 2, "20": 2})
        self.assertEqual(result["by_rule_layer"], {"Metal Spacing / Metal2": 2})
        self.assertEqual(result["hottest_50um_tiles"][0]["bbox"], [0, 0, 50, 50])

    def test_log_counts_distinguish_reroutes_and_incomplete_iterations(self):
        text = """[INFO DRT] Start detail routing.
[INFO DRT] Start 1st optimization iteration.
[INFO DRT] Number of violations = 42
[INFO DRT] Start 2nd optimization iteration.
[INFO DRT] Start detail routing.
[INFO DRT] Start 1st optimization iteration.
[INFO DRT] Number of violations = 17
"""
        self.assertEqual(diagnosis.iteration_counts(text), {(0, 1): 42, (1, 1): 17})


if __name__ == "__main__":
    unittest.main()
