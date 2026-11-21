"""Portable descriptor, complete-trace, and explicit-loading gate regressions."""
import copy
import importlib.util
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import byte_adapter_oracle as oracle

SPEC = importlib.util.spec_from_file_location("byte_adapter_checks", ROOT / "scripts/check-memory-byte-adapter.py")
checks = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(checks)


def fixture(a=1):
    data = {"schema": 1, "address_width": a, "data_width": 32, "depth": 1 << a,
            "clock": "clk", "module": f"byte_adapter_a{a}_w32", "roles": {}, "register_roles": {},
            "response_codes": {"read": 0, "stored": 1, "reserved_size": 2, "misaligned": 3},
            "startup": "arbitrary words, Q, six retained metadata fields and pending; no power-up initialization",
            "reset_behavior": "suppresses both handshakes and clears pending only; preserves words, Q and all request metadata",
            "commit_behavior": "valid store changes memory only on response acceptance; faulting requests issue no memory command"}
    for group, roles, widths in (("inputs", oracle.INPUT_ROLES, checks.widths(a)[0]),
                                 ("outputs", oracle.OUTPUT_ROLES, checks.widths(a)[1])):
        data[group] = [{"index": k, "name": role, "width": width} for k, (role, width) in enumerate(zip(roles, widths, strict=True))]
        data["roles"].update({role: role for role in roles})
    names = [f"r_state_{index}" for index in range((1 << a)+8)]
    data["register_roles"] = {"words": names[:1 << a], "q": names[1 << a],
                              **dict(zip(oracle.METADATA_ROLES, names[(1 << a)+1:], strict=True))}
    data["registers"] = [{"index": index, "name": name, "reference": name, "width": width}
                         for index, (name, width) in enumerate(zip(names, oracle.register_widths(a), strict=True))]
    return data


def trace(rows):
    return "".join(",".join(map(str, row))+"\n" for row in rows)+"BYTE_ADAPTER_DONE\nfixture: $finish called at 123 (1ns)\n"


class DescriptorTests(unittest.TestCase):
    def test_complete_typed_interfaces(self):
        for a in checks.MATRIX:
            self.assertIs(checks.validate_descriptor(fixture(a), a).__class__, dict)
        for a in (0, -1, True):
            with self.assertRaises(ValueError):
                checks.widths(a)

    def test_semantic_role_does_not_assume_physical_identifier(self):
        data = fixture()
        data["inputs"][3]["name"] = "signed_load"
        data["roles"]["signed"] = "signed_load"
        checks.validate_descriptor(data, 1)
        startup, rows, _ = oracle.stimulus(1)
        bench = checks.testbench(data, startup, rows[:1], True)
        self.assertIn(".signed_load(signed_load)", bench)
        self.assertIn("signed_load = 1'h1;", bench)
        self.assertNotIn(".signed(signed)", bench)

    def test_reject_incomplete_aliased_or_changed_interface(self):
        variants = []
        data = fixture(); data["registers"].pop(); variants.append(data)
        data = fixture(); data["register_roles"]["words"].reverse(); variants.append(data)
        data = fixture(); data["register_roles"]["q"] = data["register_roles"]["pending"]; variants.append(data)
        data = fixture(); data["registers"][0]["reference"] = "other"; variants.append(data)
        data = fixture(); data["inputs"][0]["width"] = True; variants.append(data)
        data = fixture(); data["outputs"][0]["index"] = False; variants.append(data)
        data = fixture(); data["schema"] = True; variants.append(data)
        data = fixture(); data["outputs"][0], data["outputs"][1] = data["outputs"][1], data["outputs"][0]; variants.append(data)
        data = fixture(); data["roles"]["unused"] = "extra"; variants.append(data)
        data = fixture(); data["response_codes"]["read"] = False; variants.append(data)
        data = fixture(); data["response_codes"]["misaligned"] = 2; variants.append(data)
        data = fixture(); data["startup"] = "zero initialized RAM"; variants.append(data)
        for data in variants:
            with self.subTest(descriptor=data), self.assertRaises(ValueError):
                checks.validate_descriptor(data, 1)


class TraceTests(unittest.TestCase):
    def setUp(self):
        self.data = fixture()
        self.startup, self.rows, _ = oracle.stimulus(1)
        self.frames, _, _ = oracle.oracle(1, self.startup, self.rows[:3])
        self.want = checks.expected(self.frames, True)

    def test_exact_and_concrete_mismatch(self):
        self.assertEqual(checks.check_trace(trace(self.want), self.want, self.data), 9)
        changed = self.want.copy()
        changed[0] = ("PRE", 0, 1, 0, 0, 0)
        with self.assertRaises(checks.ConcreteMismatch) as error:
            checks.check_trace(trace(changed), self.want, self.data)
        self.assertEqual(error.exception.witness,
                         {"observation": "PRE", "cycle": 0, "signal": "request_ready", "expected": 0, "actual": 1})

    def test_unknown_missing_extra_order_width_and_text_rejected(self):
        good = trace(self.want)
        malformed = [good.replace("PRE,0,0,0,0,0", "PRE,0,x,0,0,0"), trace(self.want[:-1]),
                     trace(self.want+[self.want[-1]]), trace(list(reversed(self.want))),
                     good.replace("BYTE_ADAPTER_DONE\n", ""), good.replace("BYTE_ADAPTER_DONE", "BYTE_ADAPTER_DONE\nBYTE_ADAPTER_DONE"),
                     good+"unexpected diagnostic\n", good+"PRE,3,0,0,0,0\n",
                     good.replace("PRE,0,0,0,0,0", "PRE,0,2,0,0,0"),
                     good.replace("PRE,0,0,0,0,0", "PRE,0,0,0,0"),
                     good.replace("PRE,0,0,0,0,0", "PRE,0,٠,0,0,0"),
                     "fixture: $finish called at 123 (1ns)\n"+good,
                     good+"fixture: $finish called at 123 (1ns)\n"]
        for candidate in malformed:
            with self.subTest(trace=candidate), self.assertRaises(checks.TraceError):
                checks.check_trace(candidate, self.want, self.data)

    def test_late_malformed_output_cannot_count_as_negative(self):
        changed = self.want.copy()
        changed[0] = ("PRE", 0, 1, 0, 0, 0)
        candidate = trace(changed).replace("BYTE_ADAPTER_DONE", "POST,100,x,0,0,0\nBYTE_ADAPTER_DONE")
        with self.assertRaises(checks.TraceError):
            checks.check_trace(candidate, self.want, self.data)

    def test_frame_validation_preserves_json_types_and_raw_state(self):
        checks.validate_frames(1, self.rows[:3], self.frames)
        for field, value in (("pre", False), ("registers", -1), ("post", 2)):
            changed = copy.deepcopy(self.frames)
            changed[0][field][0] = value
            with self.assertRaises(ValueError):
                checks.validate_frames(1, self.rows[:3], changed)
        changed = copy.deepcopy(self.frames); changed[0]["input"]["reset"] = 1
        with self.assertRaises(ValueError):
            checks.validate_frames(1, self.rows[:3], changed)
        changed = copy.deepcopy(self.frames); changed[0]["registers"].pop()
        with self.assertRaises(ValueError):
            checks.validate_frames(1, self.rows[:3], changed)


class InitializationTests(unittest.TestCase):
    def test_explicit_loading_all_configurations(self):
        for a in checks.MATRIX:
            startup, rows, coverage = oracle.stimulus(a)
            result = checks.initialization_evidence(a, rows, coverage["initialization_edges"])
            self.assertEqual([x["address"] for x in result["full_word_commits"]], list(range(1 << a)))
            self.assertTrue(result["q_primed"])
            self.assertFalse(result["synthesized_registers_forced"])
            data = fixture(a)
            raw = checks.testbench(data, startup, rows[:3], True)
            synth = checks.testbench(data, startup, rows[:3], False)
            self.assertEqual(raw.count("force dut."), len(startup))
            self.assertNotIn("force dut.", synth)
            self.assertNotIn("REG,", synth)

    def test_reject_implicit_initialization_partial_stores_and_early_reads(self):
        _, rows, coverage = oracle.stimulus(1)
        count = coverage["initialization_edges"]
        mutations = []
        changed = copy.deepcopy(rows); changed[0]["reset"] = False; mutations.append((changed, count))
        changed = copy.deepcopy(rows); changed[1]["size"] = 0; mutations.append((changed, count))
        changed = copy.deepcopy(rows); changed[1]["write"] = False; mutations.append((changed, count))
        changed = copy.deepcopy(rows); changed[1]["request_valid"] = False; mutations.append((changed, count))
        changed = copy.deepcopy(rows); changed[3]["address"] = 0; mutations.append((changed, count))
        mutations.extend(((rows, count-1), (rows, 0), (rows, True)))
        for changed, length in mutations:
            with self.subTest(rows=changed[:count], length=length), self.assertRaises(ValueError):
                checks.initialization_evidence(1, changed, length)

    def test_all_mutations_require_real_matching_assignments(self):
        data = fixture()
        source = "module byte_adapter_a1_w32();\n" + "\n".join(
            ["assign request_ready = ~reset & ~r_state_9;", "assign response_data = 32'd0;"] +
            [f"always @(posedge clk) {port['name']} <= response_ready ? {port['name']} : '0;"
             for port in data["registers"]]) + "\nendmodule\n"
        mutants = list(checks.mutations(source, data))
        self.assertEqual(len(mutants), 8)
        self.assertEqual(len({name for name, _ in mutants}), 8)
        for _, mutated in mutants:
            self.assertNotEqual(source, mutated)
            self.assertNotIn("&&", mutated)
        with self.assertRaises(ValueError):
            list(checks.mutations("module byte_adapter_a1_w32(); endmodule", data))


if __name__ == "__main__":
    unittest.main()
