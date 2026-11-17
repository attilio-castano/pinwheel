"""Fail-closed tests for STA receipt output and constraint conventions."""
import copy
import importlib.util
from pathlib import Path
import sys
import json
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
spec = importlib.util.spec_from_file_location("host_sta_tests", ROOT / "scripts/check-memory-transfer-host-sta.py")
sta = importlib.util.module_from_spec(spec)
spec.loader.exec_module(sta)

INV = {"ports": {"input": ["clk", "data"], "output": ["out"]},
       "registers": {"ff": sta.FF}, "clock_pins": ["ff/CLK"], "data_pins": ["ff/D"],
       "async_pins": ["ff/RESET_B"], "required_endpoints": ["ff/D", "out"]}
MODEL = {"library": "cells"}


def fixture(hold=.2, electrical=""):
    lines = ["STA_VERSION\t2.7.0", "STA_CLOCK\t0\t1",
             "STA_PORT\tinput\tclk", "STA_PORT\tinput\tdata", "STA_PORT\toutput\tout",
             "STA_REGISTER\tff\t" + sta.FF, "STA_CLOCKED\tff", "STA_PIN\tclock\tff/CLK",
             "STA_PIN\tdata\tff/D", "STA_PIN\tdata\tff/RESET_B", "STA_PIN\tasync\tff/RESET_B",
             "STA_WIRE_CONFIGURED\tcells\tZero\ttop\tmin_max", "STA_SLACK\tmax\t5", f"STA_SLACK\tmin\t{hold}"]
    for kind, slack in (("max", 5), ("min", hold)):
        for endpoint in INV["required_endpoints"]:
            lines.append(f"STA_PATH\t{kind}\t{endpoint}\tff/Q\t{slack}")
    bodies = {"UNITS": " time 1ns\n capacitance 1pF\n resistance 1kohm", "CHECK_SETUP": "", "ELECTRICAL": electrical}
    for name, kind in (("SETUP", "max"), ("HOLD", "min"), ("REG_SETUP", "max"), ("REG_HOLD", "min")):
        bodies[name] = f"Startpoint: ff\nEndpoint: ff\nPath Type: {kind}\nff/CLK\nff/Q\nff/D\n" + \
            ("library setup time" if kind == "max" else "library hold time") + "\n0.2 slack (MET)"
    for name in sta.SECTIONS:
        lines += ["STA_SECTION_BEGIN\t" + name, bodies[name], "STA_SECTION_END\t" + name]
    return "\n".join(lines + ["STA_COMPLETE", ""])


class HostSTATests(unittest.TestCase):
    def test_complete_analysis_meets_constraints(self):
        r = sta.parse_timing(fixture(), INV, MODEL)
        self.assertTrue(r["analysis_completed"])
        self.assertTrue(r["constraints_met"])
        self.assertEqual(r["required_endpoint_count"], 2)

    def test_negative_hold_is_completed_measurement_not_parse_failure(self):
        r = sta.parse_timing(fixture(hold=-.1), INV, MODEL)
        self.assertTrue(r["analysis_completed"])
        self.assertFalse(r["constraints_met"])
        self.assertEqual(set(r["violating_endpoints"]["min"]), {"ff/D", "out"})

    def test_electrical_violation_is_retained(self):
        r = sta.parse_timing(fixture(electrical="max fanout\nPin Limit Fanout Slack\nff/Q 8 9 -1 (VIOLATED)"), INV, MODEL)
        self.assertFalse(r["constraints_met"])
        self.assertEqual(len(r["electrical_violations"]["max fanout"]), 1)
        failure = r["electrical_violations"]["max fanout"][0]
        self.assertEqual((failure["type"], failure["endpoint"], failure["limit"], failure["actual"]),
                         ("max fanout", "ff/Q", 8, 9))
        self.assertTrue(r["setup_hold_met"])
        self.assertFalse(r["electrical_constraints_met"])

    def test_truncation_and_extra_output_rejected(self):
        for text in (fixture().replace("STA_COMPLETE\n", ""), fixture()+"STA_COMPLETE\n",
                     fixture()+"surprise\n", fixture().replace("STA_SECTION_END\tHOLD", "STA_SECTION_END\tSETUP")):
            with self.assertRaises(ValueError):
                sta.parse_timing(text, INV, MODEL)

    def test_missing_duplicate_wrong_endpoint_rejected(self):
        row = "STA_PATH\tmax\tff/D\tff/Q\t5"
        for altered in (fixture().replace(row+"\n", ""), fixture().replace(row, row+"\n"+row),
                        fixture().replace(row, row.replace("ff/D", "lost/D"))):
            with self.assertRaises(ValueError):
                sta.parse_timing(altered, INV, MODEL)

    def test_clock_and_complete_inventory_rejected(self):
        for old, new in (("STA_CLOCK\t0\t1", "STA_CLOCK\t1\t1"), ("STA_CLOCKED\tff\n", ""),
                         ("STA_PORT\tinput\tdata\n", ""), ("STA_PIN\tasync\tff/RESET_B\n", ""),
                         ("STA_REGISTER\tff\t"+sta.FF, "STA_REGISTER\tff\tother")):
            with self.assertRaises(ValueError):
                sta.parse_timing(fixture().replace(old, new), INV, MODEL)

    def test_unconstrained_warning_and_missing_arc_rejected(self):
        for altered in (fixture().replace("STA_SECTION_BEGIN\tCHECK_SETUP\n", "STA_SECTION_BEGIN\tCHECK_SETUP\nWarning: no clock\n"),
                        fixture().replace("library setup time", "unknown setup"),
                        fixture().replace("library hold time", "unknown hold")):
            with self.assertRaises(ValueError):
                sta.parse_timing(altered, INV, MODEL)

    def test_nonfinite_wrong_units_or_inconsistent_worst_rejected(self):
        for old, new in (("STA_SLACK\tmax\t5", "STA_SLACK\tmax\tNaN"),
                         ("STA_SLACK\tmax\t5", "STA_SLACK\tmax\t6"),
                         ("capacitance 1pF", "capacitance 1fF"),
                         ("\tZero\ttop\tmin_max", "\tother\ttop\tmin_max")):
            with self.assertRaises(ValueError):
                sta.parse_timing(fixture().replace(old, new), INV, MODEL)

    def test_unknown_electrical_row_rejected(self):
        for row in ("unparsed failure", "ff/Q x 3 (VIOLATED)", "junk (VIOLATED)"):
            with self.assertRaises(ValueError):
                sta.parse_timing(fixture(electrical="max slew\n"+row), INV, MODEL)

    def test_single_bit_vector_ports_keep_native_index(self):
        text = ("module tiny;\ninput clk;\ninput [0:0] data;\noutput [0:0] out;\n" + sta.FF +
                " ff (.CLK(clk), .D(data[0]), .Q(out[0]), .RESET_B(1'h1));\nendmodule\n")
        graph = {"modules": {"tiny": {"ports": {"clk": {"direction": "input", "bits": [2]},
                  "data": {"direction": "input", "bits": [3]}, "out": {"direction": "output", "bits": [4]}},
                  "cells": {"ff": {"type": sta.FF, "connections": {"CLK": [2], "D": [3], "Q": [4], "RESET_B": ["1"]}}}}}}
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory)
            (path/"mapped.v").write_text(text)
            (path/"mapped.json").write_text(json.dumps(graph))
            inv = sta.inventory(path/"mapped.v", path/"mapped.json", "tiny")
            self.assertEqual(inv["ports"], {"input": ["clk", "data[0]"], "output": ["out[0]"]})
            (path/"mapped.v").write_text(text.replace("input [0:0]", "input [1:0]"))
            with self.assertRaises(ValueError):
                sta.inventory(path/"mapped.v", path/"mapped.json", "tiny")

    def test_signed_output_hold_policy_and_no_exceptions(self):
        sdc = sta.constraints(INV, MODEL)
        self.assertIn("set_output_delay -clock clk -min -0.2", sdc)
        self.assertIn("set_input_delay -clock clk -min 0.2", sdc)
        self.assertIn("set_wire_load_model -name Zero -library cells", sdc)
        self.assertNotIn("false_path", sdc)
        self.assertNotIn("case_analysis", sdc)

    def test_tcl_name_and_receipt_containment(self):
        for value in ("x} ; exit", "x\ny"):
            with self.assertRaises(ValueError):
                sta.tcl_list([value])
        with self.assertRaises(ValueError):
            sta.contained(ROOT / "build", "../outside")


if __name__ == "__main__":
    unittest.main()
