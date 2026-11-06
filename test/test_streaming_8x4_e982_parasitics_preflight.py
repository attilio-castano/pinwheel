import hashlib
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch


sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
import streaming_8x4_e982_parasitics_preflight as preflight


SPEF = r'''*SPEF "ieee 1481-1999"
*DESIGN "tt_um_pinwheel_streaming_ready_d2"
*DATE "original"
*DESIGN_FLOW "NAME_SCOPE LOCAL" "PIN_CAP NONE"
*DIVIDER /
*DELIMITER :
*BUS_DELIMITER []
*T_UNIT 1 NS
*C_UNIT 1 PF
*R_UNIT 1 OHM
*NAME_MAP
*1 clk
*2 uo_out[0]
*3 engine\.front
*PORTS
clk I
uo_out[0] O

*D_NET *1 0.007
*CONN
*P clk I
*I *3:A I *D sg13cmos5l_buf_1
*CAP
1 clk 0.004
2 *1:8 *2:9 3e-3
*RES
1 clk *1:8 0.5
2 *1:8 *3:A 1
*END

*D_NET *2 0.003
*CONN
*I *3:X O *D sg13cmos5l_buf_1
*P uo_out[0] O
*CAP
1 *2:9 *1:8 0.003
*RES
1 *3:X *2:9 1
2 *2:9 uo_out[0] 1
*END
'''


def inventory():
    terms = {"A": {"signal_type": "SIGNAL", "direction": "INPUT"},
             "X": {"signal_type": "SIGNAL", "direction": "OUTPUT"},
             "Z": {"signal_type": "SIGNAL", "direction": "OUTPUT"}}
    return {
        "schema": "pinwheel.streaming-tt-odb-inventory.v1",
        "top": preflight.TOP,
        "nets": {"clk": {"signal_type": "CLOCK", "wire": 1},
                 "uo_out[0]": {"signal_type": "SIGNAL", "wire": 2}},
        "masters": {"sg13cmos5l_buf_1": terms},
        "instances": {"engine.front": {"master": "sg13cmos5l_buf_1",
                      "terminals": {name: dict(term, net=net) for (name, term), net
                                    in zip(terms.items(), ("clk", "uo_out[0]", None))}}},
        "public_bterms": {"clk": {"direction": "input", "net": "clk"},
                          "uo_out[0]": {"direction": "output", "net": "uo_out[0]"}},
        "power_bterms": {},
        "unconnected_signal_outputs": {"engine.front/Z": 3},
    }


def raw_annotation(corner, driver="engine.front/Z", partial=0):
    return (f"==================== {corner} Corner ====================\n"
            "report_parasitic_annotation -report_unannotated\n"
            "======================================================\n"
            f"Found 1 unannotated drivers.\n {driver}\nFound {partial} partially unannotated drivers.\n"
            "======================================================\n")


class ParasiticsPreflightTests(unittest.TestCase):
    def setUp(self):
        self.inventory = inventory()
        self.context, self.disconnected = preflight.inventory_context(self.inventory)
        self.layout = preflight.expected_nets(self.inventory, self.context)

    def parse(self, spef=SPEF):
        return preflight.spef_evidence(spef.splitlines(), self.inventory, self.layout)

    def test_openrcx_spef_with_escaped_names_and_coupling(self):
        observed = self.parse()
        self.assertEqual(observed["units"]["*C_UNIT"], ["1", "PF"])
        self.assertEqual(observed["consumed_nets"], 2)
        self.assertEqual(observed["connections"], 4)
        self.assertEqual(observed["resistors"], 4)
        self.assertEqual(observed["capacitors"], 3)
        self.assertEqual(self.parse(SPEF.replace("original", "new date")
                                   .replace("3e-3", ".003"))["graph_sha256"], observed["graph_sha256"])

    def test_wrong_top_unmapped_terminal_and_bad_direction(self):
        for old, new, message in (
            (preflight.TOP, "stale", "wrong top"),
            ("*3:A I", "*4:A I", "Unresolved SPEF name"),
            ("*3:A I", "*3:A O", "terminal mismatch"),
        ):
            with self.subTest(new=new), self.assertRaisesRegex(ValueError, message):
                self.parse(SPEF.replace(old, new))

    def test_missing_graph_edge_bad_capacitor_and_truncation(self):
        for old, new, message in (
            ("2 *1:8 *3:A 1\n", "", "Disconnected SPEF resistance graph"),
            ("2 *1:8 *2:9 3e-3", "2 *1:8 *2:10 3e-3", "missing graph node"),
            ("1 clk 0.004", "1 clk -0.004", "Invalid SPEF scalar"),
            ("*END\n", "", "Malformed SPEF D_NET"),
        ):
            with self.subTest(new=new), self.assertRaisesRegex(ValueError, message):
                self.parse(SPEF.replace(old, new))

    def test_missing_consumed_net_and_unsupported_pin_cap(self):
        first, _ = SPEF.split("*D_NET *2", 1)
        first = first.replace("2 *1:8 *2:9 3e-3\n", "")
        with self.assertRaisesRegex(ValueError, "omits 1 consumed nets"):
            self.parse(first)
        with self.assertRaisesRegex(ValueError, "Unsupported SPEF header"):
            self.parse(SPEF.replace("PIN_CAP NONE", "PIN_CAP INCLUDED"))

    def test_annotation_requires_correct_corner_and_no_consumed_or_partial_drivers(self):
        def assess(text):
            return preflight.annotation_evidence(text, "slow", self.context, self.disconnected)

        self.assertEqual(assess(raw_annotation("slow"))["unused_drivers"], ["engine.front/Z"])
        for report, message in (
            (raw_annotation("fast"), "corner differs"),
            (raw_annotation("slow", "clk"), "incomplete annotation"),
            (raw_annotation("slow", partial=1), "incomplete annotation"),
            (raw_annotation("slow", "unmapped"), "Unresolved unannotated driver"),
            (raw_annotation("slow").replace("Found 1", "Found 0"), "count differs"),
            (raw_annotation("slow").replace("drivers.\n====", "drivers.\n stale-pin\n===="), "trailing rows"),
        ):
            with self.subTest(message=message), self.assertRaisesRegex(ValueError, message):
                assess(report)

    def test_request_custody_and_disguised_nominal_reuse(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)

            def save(name, content):
                if isinstance(content, dict):
                    content = json.dumps(content)
                (root / name).write_text(content)
                return {"path": name, "sha256": hashlib.sha256(content.encode()).hexdigest()}

            target = {role: save(role, role) for role in ("odb", "gds", "netlist")}
            target["inventory"] = save("inventory.json", self.inventory)
            hashes = {role: item["sha256"] for role, item in target.items()}
            request = {"schema": preflight.REQUEST, "target": target, "scenarios": {}}
            sdc = save("design.sdc", "create_clock")
            liberty = save("slow.lib", "liberty")

            def scenario(name, rc, text, **override):
                spef = save(f"{name}.spef", text)
                report = save(f"{name}.rpt", raw_annotation(name))
                run = save(f"{name}.json", dict({
                    "schema": preflight.ANALYSIS, "top": preflight.TOP, "scenario": name,
                    "rc_corner": rc, "sta_corner": name, "mode": "functional",
                    "odb_sha256": hashes["odb"], "gds_sha256": hashes["gds"], "netlist_sha256": hashes["netlist"],
                    "sdc_sha256": sdc["sha256"], "liberty_sha256": [liberty["sha256"]],
                    "spef_sha256": spef["sha256"], "annotation_sha256": report["sha256"],
                    "runtime_sha256": "a" * 64, "annotation_mode": "read_spef", "exit_code": 0,
                }, **override))
                return {"rc_corner": rc, "sta_corner": name, "mode": "functional", "sdc": sdc,
                        "liberties": [liberty], "spef": spef, "annotation": report, "run": run}

            with patch.object(preflight, "TARGET", hashes):
                request["scenarios"]["slow"] = scenario("slow", "rmax", SPEF)
                self.assertFalse(preflight.preflight(root, request)["qualified_timing"])
                request["scenarios"]["fast"] = scenario("fast", "rmin", SPEF.replace("original", "different date"))
                with self.assertRaisesRegex(ValueError, "Identical SPEF graphs"):
                    preflight.preflight(root, request)
                request["scenarios"]["fast"] = scenario("fast", "rmin", SPEF.replace("0.5", "0.4"),
                                                         annotation_sha256="a" * 64)
                with self.assertRaisesRegex(ValueError, "Analysis custody differs for scenario fast"):
                    preflight.preflight(root, request)
                request["scenarios"]["fast"] = scenario("fast", "rmin", SPEF.replace("0.5", "0.4"))
                self.assertEqual(set(preflight.preflight(root, request)["scenarios"]), {"fast", "slow"})
                target["gds"] = save("stale.gds", "older gds")
                with self.assertRaisesRegex(ValueError, "another frozen target"):
                    preflight.preflight(root, request)


if __name__ == "__main__":
    unittest.main()
