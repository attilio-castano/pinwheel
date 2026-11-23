"""Portable complete-descriptor, strict-trace and initialization regressions."""
import copy
import importlib.util
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import mmio_oracle as oracle
SPEC = importlib.util.spec_from_file_location("mmio_checks", ROOT / "scripts/check-processor-mmio.py")
checks = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(checks)


def fixture():
    data = {"schema": 1, "clock": "clk", "module": "processor_mmio", "roles": {}, "register_roles": {},
            "response_codes": {"read": 0, "stored": 1, "register_hole": 2, "direction": 3, "tx_busy": 4, "rx_empty": 5},
            "device_codes": {"gpio": 0, "timer": 1, "uart": 2, "invalid": 3}, **checks.BOUNDARIES}
    for group, roles, widths in (("inputs", oracle.INPUT_ROLES, oracle.INPUT_WIDTHS),
                                 ("outputs", oracle.OUTPUT_ROLES, oracle.OUTPUT_WIDTHS),
                                 ("registers", oracle.REGISTER_ROLES, oracle.REGISTER_WIDTHS)):
        data[group] = []
        for k, (role, width) in enumerate(zip(roles, widths, strict=True)):
            name = "r_"+role if group == "registers" else role
            port = {"index": k, "name": name, "width": width}
            if group == "registers":
                port["reference"] = name
            data[group].append(port)
            data["register_roles" if group == "registers" else "roles"][role] = name
    return data


def trace(rows):
    return "".join(",".join(map(str, row))+"\n" for row in rows)+"MMIO_DONE\nfixture: $finish called at 123 (1ns)\n"


class DescriptorTests(unittest.TestCase):
    def test_complete_interface(self):
        checks.validate_descriptor(fixture())

    def test_reject_omission_alias_width_order_codes_and_boundary(self):
        variants = []
        d = fixture(); d["outputs"].pop(); variants.append(d)
        d = fixture(); d["registers"].pop(); variants.append(d)
        d = fixture(); d["register_roles"]["timer"] = "r_gpio"; variants.append(d)
        d = fixture(); d["registers"][0]["reference"] = "other"; variants.append(d)
        d = fixture(); d["inputs"][0]["width"] = True; variants.append(d)
        d = fixture(); d["outputs"][0]["index"] = False; variants.append(d)
        d = fixture(); d["schema"] = True; variants.append(d)
        d = fixture(); d["outputs"][0], d["outputs"][1] = d["outputs"][1], d["outputs"][0]; variants.append(d)
        d = fixture(); d["roles"]["unused"] = "extra"; variants.append(d)
        d = fixture(); d["response_codes"]["read"] = False; variants.append(d)
        d = fixture(); d["device_codes"]["invalid"] = 2; variants.append(d)
        d = fixture(); d["startup"] = "zero initialized"; variants.append(d)
        for d in variants:
            with self.subTest(descriptor=d), self.assertRaises(ValueError):
                checks.validate_descriptor(d)


class TraceTests(unittest.TestCase):
    def setUp(self):
        self.data = fixture()
        self.startup, self.rows, _ = oracle.stimulus()
        self.rows = self.rows[:3]
        self.frames, _, _ = oracle.oracle(self.startup, self.rows)
        self.want = checks.expected(self.frames, True)

    def test_exact_and_concrete_mismatch(self):
        self.assertEqual(checks.check_trace(trace(self.want), self.want, self.data), 9)
        changed = self.want.copy()
        changed[0] = ("PRE", 0, 1, 0, 0, 0, 0, 0, 0)
        with self.assertRaises(checks.ConcreteMismatch) as error:
            checks.check_trace(trace(changed), self.want, self.data)
        self.assertEqual(error.exception.witness, {"observation": "PRE", "cycle": 0, "signal": "request_ready", "expected": 0, "actual": 1})

    def test_malformed_unknown_incomplete_and_late_failure_are_not_negatives(self):
        good, prefix = trace(self.want), "PRE,0,0,0,0,0,0,0,0"
        bad = [good.replace(prefix, "PRE,0,x,0,0,0,0,0,0"), trace(self.want[:-1]), trace(self.want+[self.want[-1]]),
               trace(list(reversed(self.want))), good.replace("MMIO_DONE\n", ""), good.replace("MMIO_DONE", "MMIO_DONE\nMMIO_DONE"),
               good+"diagnostic\n", good+prefix+"\n", good.replace(prefix, "PRE,0,2,0,0,0,0,0,0"),
               good.replace(prefix, "PRE,0,0,0,0"), good.replace(prefix, "PRE,0,٠,0,0,0,0,0,0"),
               "fixture: $finish called at 123 (1ns)\n"+good, good+"fixture: $finish called at 123 (1ns)\n"]
        for candidate in bad:
            with self.subTest(trace=candidate), self.assertRaises(checks.TraceError):
                checks.check_trace(candidate, self.want, self.data)
        changed = self.want.copy(); changed[0] = ("PRE", 0, 1, 0, 0, 0, 0, 0, 0)
        with self.assertRaises(checks.TraceError):
            checks.check_trace(trace(changed).replace("MMIO_DONE", "POST,100,x,0,0,0\nMMIO_DONE"), self.want, self.data)

    def test_frame_json_types_widths_complete_state(self):
        checks.validate_frames(self.rows, self.frames)
        variants = []
        for field, value in (("pre", False), ("registers", -1), ("post", 2)):
            d = copy.deepcopy(self.frames); d[0][field][0] = value; variants.append(d)
        d = copy.deepcopy(self.frames); d[0]["input"]["reset"] = 1; variants.append(d)
        d = copy.deepcopy(self.frames); d[0]["registers"].pop(); variants.append(d)
        for d in variants:
            with self.assertRaises(ValueError):
                checks.validate_frames(self.rows, d)

    def test_synthesis_requires_reset_and_has_no_forced_registers(self):
        result = checks.initialization_evidence(self.rows)
        self.assertFalse(result["synthesized_registers_forced"])
        raw = checks.testbench(self.data, self.startup, self.rows, True)
        synth = checks.testbench(self.data, self.startup, self.rows, False)
        self.assertEqual(raw.count("force dut."), 8)
        self.assertNotIn("force dut.", synth)
        self.assertNotIn("REG,", synth)
        for rows in ([], [dict(self.rows[0], reset=False)]):
            with self.assertRaises(ValueError):
                checks.initialization_evidence(rows)
        with self.assertRaises(ValueError):
            checks.testbench(self.data, self.startup, self.rows, False, segments=oracle.raw_cases())

    def test_raw_segments_force_all_registers_and_keep_global_edge_order(self):
        segments = oracle.raw_cases()[:2]
        tb = checks.testbench(self.data, self.startup, self.rows, True, segments=segments)
        self.assertEqual(tb.count("force dut."), 16)
        self.assertIn('"PRE,9,', tb)
        self.assertEqual(tb.count('"PRE,0,'), 1)

    def test_mutations_change_exact_actual_endpoint_assignments(self):
        source = "module processor_mmio();\n"+"\n".join(
            [f"assign {p['name']} = '0;" for p in self.data["outputs"]] +
            [f"always @(posedge clk) {p['name']} <= {p['name']};" for p in self.data["registers"]])+"\nendmodule\n"
        mutants = list(checks.mutations(source, self.data))
        self.assertEqual(len(mutants), 12)
        self.assertEqual(len({name for name, _ in mutants}), 12)
        for _, mutated in mutants:
            self.assertNotEqual(source, mutated)
            self.assertNotIn("&&", mutated)
        with self.assertRaises(ValueError):
            list(checks.mutations("module processor_mmio(); endmodule", self.data))


if __name__ == "__main__":
    unittest.main()
