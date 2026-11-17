"""Portable checks for the generic typed descriptor and restricted RTL reader.

These tests need neither CAD tools nor retained artifacts. Semantic mutations
that remain valid RTL must survive parsing so the separate Lean certificate can
reject them; this suite does not mistake parser acceptance for equivalence.
"""
import importlib.util
import json
from pathlib import Path
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location("typed_circuit_readback", ROOT / "scripts/typed_circuit_readback.py")
readback = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = readback
SPEC.loader.exec_module(readback)


def descriptor():
    # Deliberately not lexicographic: ordinal order is the typed interface order.
    return {"module": "typed_pair", "inputs": [
        {"name": "z_data", "width": 3, "index": 0},
        {"name": "a_data", "width": 3, "index": 1}],
        "registers": [
            {"name": "z_word", "reference": "q_word", "width": 3, "index": 0},
            {"name": "a_word", "reference": "q_other", "width": 3, "index": 1}],
        "outputs": [{"name": "z_result", "width": 3, "index": 0},
                    {"name": "a_result", "width": 3, "index": 1}]}


def fixture():
    ports = {"clk": {"direction": "input", "bits": [1]},
             "z_data": {"direction": "input", "bits": [2, 3, 4]},
             "a_data": {"direction": "input", "bits": [5, 6, 7]},
             "z_result": {"direction": "output", "bits": [8, 9, 10]},
             "a_result": {"direction": "output", "bits": [11, 12, 13]}}
    cells, nets = {}, {}
    for name, data, output in (("q_word", "z_data", "z_result"), ("q_other", "a_data", "a_result")):
        q = ports[output]["bits"][:]
        nets[name] = {"bits": q, "attributes": {}}
        cells[name] = {"type": "$dff", "parameters": {"WIDTH": "11", "CLK_POLARITY": "1"},
                       "connections": {"CLK": [1], "D": ports[data]["bits"][:], "Q": q[:]},
                       "port_directions": {"CLK": "input", "D": "input", "Q": "output"}}
    return {"ports": ports, "cells": cells, "netnames": nets, "attributes": {}}


HINTS = """module {
  hw.module @typed_pair(in %clk : i1, in %z_data : i3, in %a_data : i3, out z_result : i3, out a_result : i3) {
    %clock = seq.to_clock %clk
    %q_word = seq.compreg %z_data, %clock : i3
    %q_other = seq.compreg %a_data, %clock : i3
    hw.output %q_word, %q_other : i3, i3
  }
}
"""


class TypedCircuitReadback(unittest.TestCase):
    def setUp(self):
        self.descriptor = descriptor()
        self.reader = readback.importer(self.descriptor)

    def read(self, module, reader=None):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "rtl.json"
            path.write_text(json.dumps({"modules": {"typed_pair": module}}))
            return (reader or self.reader).read_rtl(path)

    def hints(self, text, reader=None):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "source.mlir"
            path.write_text(text)
            return (reader or self.reader).read_hints(path)

    def test_shared_expression_is_named_once(self):
        node = (3, "var", (), 0)
        for _ in range(20):
            node = (3, "xor", (node, node), None)
        text = readback.render_shared(self.reader, node)
        self.assertEqual(text.count("let "), 20)
        self.assertIn("g18 ^^^ g18", text)
        self.assertEqual(readback.tree_size(node), 2 ** 21 - 1)

    def test_descriptor_order_and_explicit_register_references(self):
        self.assertEqual(list(self.reader.INPUTS.items()), [
            ("z_data", (3, "input_0")), ("a_data", (3, "input_1"))])
        self.assertEqual(list(self.reader.REGISTERS.items()), [
            ("q_word", (3, "register_0")), ("q_other", (3, "register_1"))])
        self.assertEqual(list(self.reader.OUTPUTS.items()), [
            ("z_result", (3, "output_0")), ("a_result", (3, "output_1"))])
        actual, source = self.read(fixture()), self.hints(HINTS)
        self.assertEqual(actual.next, {"q_word": "z_data", "q_other": "a_data"})
        self.assertEqual(actual.outputs, {"z_result": "q_word", "a_result": "q_other"})
        self.assertEqual(actual.next, source.next)
        self.assertEqual(actual.outputs, source.outputs)

    def test_optional_ordinal_and_default_reference(self):
        d = descriptor()
        for kind in ("inputs", "registers", "outputs"):
            for port in d[kind]:
                del port["index"]
        for port in d["registers"]:
            del port["reference"]
        reader = readback.importer(d)
        self.assertEqual(list(reader.REGISTERS), ["r_z_word", "r_a_word"])

    def test_missing_descriptor_enumeration(self):
        for kind in ("inputs", "registers", "outputs"):
            for value in (None, {}, "not an enumeration"):
                with self.subTest(kind=kind, value=value):
                    d = descriptor()
                    d[kind] = value
                    with self.assertRaisesRegex(ValueError, "Missing typed"):
                        readback.validate_descriptor(d)
            d = descriptor()
            del d[kind]
            with self.assertRaisesRegex(ValueError, "Missing typed"):
                readback.validate_descriptor(d)

    def test_invalid_modules_names_and_duplicate_names(self):
        for name in (None, "", "has space", "x; run_cmd", "0starts_wrong"):
            with self.subTest(module=name):
                d = descriptor()
                d["module"] = name
                with self.assertRaises(ValueError):
                    readback.validate_descriptor(d)
        for name in ("clk", "a_data", "a_word", "a_result", "bad-name", None):
            with self.subTest(signal=name):
                d = descriptor()
                d["inputs"][0]["name"] = name
                with self.assertRaises(ValueError):
                    readback.validate_descriptor(d)

    def test_widths_and_indices_require_positive_width_and_exact_integer_ordinal(self):
        for kind in ("inputs", "registers", "outputs"):
            for width in (0, -1, True, 3.0, "3", None):
                with self.subTest(kind=kind, width=width):
                    d = descriptor()
                    d[kind][0]["width"] = width
                    with self.assertRaises(ValueError):
                        readback.validate_descriptor(d)
            for index in (-1, 1, False, 0.0, "0", None):
                with self.subTest(kind=kind, index=index):
                    d = descriptor()
                    d[kind][0]["index"] = index
                    with self.assertRaises(ValueError):
                        readback.validate_descriptor(d)

    def test_reference_aliases_and_reserved_parser_nodes(self):
        for reference in ("q_other", "z_data", "z_result", "clk", "clock", "n0", "n001", "v39", "bad-ref", None):
            with self.subTest(reference=reference):
                d = descriptor()
                d["registers"][0]["reference"] = reference
                with self.assertRaises(ValueError):
                    readback.validate_descriptor(d)
        for name in ("clock", "n0", "n001", "v39"):
            with self.subTest(input=name):
                d = descriptor()
                d["inputs"][0]["name"] = name
                with self.assertRaises(ValueError):
                    readback.validate_descriptor(d)
        d = descriptor()
        d["inputs"][0]["name"] = "r_z_word"
        del d["registers"][0]["reference"]
        with self.assertRaises(ValueError):
            readback.validate_descriptor(d)

    def test_missing_or_extra_physical_endpoints_fail_closed(self):
        for kind in ("inputs", "registers", "outputs"):
            with self.subTest(omitted_descriptor_endpoint=kind):
                d = descriptor()
                d[kind].pop()
                with self.assertRaises(ValueError):
                    self.read(fixture(), readback.importer(d))
        for container, name in (("ports", "a_data"), ("ports", "a_result"),
                                ("cells", "q_other"), ("netnames", "q_other")):
            with self.subTest(omitted_rtl_endpoint=name, container=container):
                module = fixture()
                del module[container][name]
                with self.assertRaises(ValueError):
                    self.read(module)
        module = fixture()
        module["ports"]["extra"] = {"direction": "input", "bits": [999]}
        with self.assertRaisesRegex(ValueError, "Changed port contract"):
            self.read(module)

    def test_hint_omission_width_change_and_register_exchange_fail_closed(self):
        mutations = (HINTS.replace("    %q_other = seq.compreg %a_data, %clock : i3\n", ""),
                     HINTS.replace("out a_result : i3", "out a_result : i2"),
                     HINTS.replace("%q_other = seq.compreg %a_data, %clock : i3",
                                   "%q_other = seq.compreg %a_data, %clock : i2"),
                     HINTS.replace("%q_other = seq.compreg", "%unknown = seq.compreg"))
        for text in mutations:
            with self.subTest(hints=text), self.assertRaises(ValueError):
                self.hints(text)

    def test_clock_unknown_and_aliased_register_corruptions_fail_closed(self):
        def opposite_edge(m): m["cells"]["q_word"]["parameters"]["CLK_POLARITY"] = "0"
        def clock_data(m): m["cells"]["q_word"]["connections"]["D"] = [1, "0", "0"]
        def undefined(m): m["cells"]["q_word"]["connections"]["D"] = ["x", "0", "0"]
        def unconnected(m): m["ports"]["z_result"]["bits"] = [997, 998, 999]
        def initial(m): m["netnames"]["q_word"]["attributes"]["init"] = "000"
        def aliased_state(m): m["netnames"]["q_other"]["bits"] = m["netnames"]["q_word"]["bits"][:]
        def aliased_input(m): m["ports"]["a_data"]["bits"] = m["ports"]["z_data"]["bits"][:]
        for mutate in (opposite_edge, clock_data, undefined, unconnected, initial, aliased_state, aliased_input):
            with self.subTest(corruption=mutate.__name__):
                module = fixture()
                mutate(module)
                with self.assertRaises(ValueError):
                    self.read(module)

    def test_semantic_pin_exchanges_and_state_corruption_are_not_silently_repaired(self):
        # These are legal RTL shapes, so certification (not parsing) rejects them.
        module = fixture()
        a, b = module["ports"]["z_data"], module["ports"]["a_data"]
        a["bits"], b["bits"] = b["bits"], a["bits"]
        swapped = self.read(module)
        self.assertEqual(swapped.nodes[swapped.next["q_word"]].value, "a_data")
        self.assertEqual(swapped.nodes[swapped.next["q_other"]].value, "z_data")
        module = fixture()
        a, b = module["ports"]["z_result"], module["ports"]["a_result"]
        a["bits"], b["bits"] = b["bits"], a["bits"]
        swapped = self.read(module)
        self.assertEqual(swapped.outputs, {"z_result": "q_other", "a_result": "q_word"})
        module = fixture()
        module["cells"]["q_word"]["connections"]["D"] = ["1", "0", "1"]
        altered = self.read(module)
        node = altered.nodes[altered.next["q_word"]]
        self.assertEqual((node.width, node.op, node.value), (3, "lit", 5))


if __name__ == "__main__":
    unittest.main()
