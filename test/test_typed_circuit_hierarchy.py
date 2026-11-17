"""Portable hierarchy binding checks, without CAD tools or retained artifacts.

The normalizer only adds canonical net-name aliases. The existing restricted
reader remains responsible for rejecting missing, extra, or aliased physical
state; neither layer may silently alter the actual wire graph.
"""
from copy import deepcopy
import json
from pathlib import Path
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import typed_circuit_hierarchy as hierarchy
import typed_circuit_readback as readback


def descriptor():
    # Ordinal order deliberately differs from lexicographic order.
    result = {"module": "nested_pair", "inputs": [
        {"name": "z_data", "width": 3, "index": 0},
        {"name": "a_flag", "width": 1, "index": 1}],
        "registers": [
            {"name": "r_z_word", "flat_reference": "r_z_word", "reference": "fifo_2.bank.r_data", "width": 3, "index": 0},
            {"name": "r_a_flag", "flat_reference": "r_a_flag", "reference": "control.r_flag", "width": 1, "index": 1}],
        "outputs": [{"name": "z_result", "width": 3, "index": 0},
                    {"name": "a_result", "width": 1, "index": 1}]}
    update_maps(result)
    return result


def update_maps(d):
    d["register_map"] = {r["flat_reference"]: r["reference"] for r in d["registers"]}
    d["hierarchical_registers"] = [r["reference"] for r in d["registers"]]


def fixture():
    ports = {"clk": {"direction": "input", "bits": [1]},
             "z_data": {"direction": "input", "bits": [2, 3, 4]},
             "a_flag": {"direction": "input", "bits": [5]},
             "z_result": {"direction": "output", "bits": [6, 7, 8]},
             "a_result": {"direction": "output", "bits": [9]}}
    nets, cells = {}, {}
    for name, width, data, q in (("fifo_2.bank.r_data", 3, [2, 3, 4], [6, 7, 8]),
                                 ("control.r_flag", 1, [5], [9])):
        nets[name] = {"bits": q, "hide_name": 0, "attributes": {"src": "example.sv:3", "keep": "1"}}
        cells[name + "_ff"] = {"type": "$dff", "parameters": {"WIDTH": f"{width:b}", "CLK_POLARITY": "1"},
                              "connections": {"CLK": [1], "D": data, "Q": q[:]},
                              "port_directions": {"CLK": "input", "D": "input", "Q": "output"}}
    return {"modules": {"nested_pair": {"ports": ports, "cells": cells, "netnames": nets,
                                        "attributes": {"top": "1"}}}, "creator": "synthetic portable fixture"}


class TypedCircuitHierarchy(unittest.TestCase):
    def prepare(self, document=None, d=None, *, parse=False):
        document = fixture() if document is None else document
        d = descriptor() if d is None else d
        with tempfile.TemporaryDirectory() as directory:
            original, destination = Path(directory) / "raw.json", Path(directory) / "normalized.json"
            original.write_text(json.dumps(document))
            before = original.read_bytes()
            flat = hierarchy.prepare_json(original, destination, d)
            self.assertEqual(original.read_bytes(), before)
            result = json.loads(destination.read_text())
            graph = readback.importer(flat).read_rtl(destination) if parse else None
            return flat, result, graph

    def test_complete_ordered_mapping_and_input_immutability(self):
        d = descriptor()
        saved = deepcopy(d)
        flat = hierarchy.normalize_descriptor(d)
        self.assertEqual(d, saved)
        self.assertEqual([r["reference"] for r in flat["registers"]], ["r_z_word", "r_a_flag"])
        self.assertEqual([r["index"] for r in flat["registers"]], [0, 1])
        self.assertEqual(flat["inputs"], d["inputs"])
        self.assertEqual(flat["outputs"], d["outputs"])
        self.assertEqual(flat["register_map"], d["register_map"])
        # A JSON object's insertion order does not change its mapping meaning.
        d["register_map"] = dict(reversed(list(d["register_map"].items())))
        self.assertEqual(hierarchy.normalize_descriptor(d)["registers"], flat["registers"])

    def test_aliasing_preserves_all_actual_ports_cells_bits_and_attributes(self):
        original = fixture()
        flat, result, graph = self.prepare(original, parse=True)
        module, old = result["modules"]["nested_pair"], original["modules"]["nested_pair"]
        self.assertEqual(module["ports"], old["ports"])
        self.assertEqual(module["cells"], old["cells"])
        self.assertEqual(module["attributes"], old["attributes"])
        self.assertEqual(result["creator"], original["creator"])
        for r in descriptor()["registers"]:
            self.assertEqual(module["netnames"][r["flat_reference"]], old["netnames"][r["reference"]])
            del module["netnames"][r["flat_reference"]]
        self.assertEqual(result, original)
        self.assertEqual(list(readback.importer(flat).REGISTERS), ["r_z_word", "r_a_flag"])
        self.assertEqual(graph.next, {"r_z_word": "z_data", "r_a_flag": "a_flag"})
        self.assertEqual(graph.outputs, {"z_result": "r_z_word", "a_result": "r_a_flag"})

    def test_already_canonical_reference_is_allowed_without_graph_changes(self):
        d, document = descriptor(), fixture()
        for register in d["registers"]:
            nets = document["modules"]["nested_pair"]["netnames"]
            nets[register["flat_reference"]] = nets.pop(register["reference"])
            register["reference"] = register["flat_reference"]
        update_maps(d)
        _, result, _ = self.prepare(document, d, parse=True)
        self.assertEqual(result, document)

    def test_map_and_list_must_match_every_register_in_order(self):
        for field in ("register_map", "hierarchical_registers"):
            for missing in (True, False):
                with self.subTest(field=field, missing=missing):
                    d = descriptor()
                    if missing: del d[field]
                    else: d[field] = {} if field == "register_map" else []
                    with self.assertRaisesRegex(ValueError, "complete register enumeration"):
                        hierarchy.normalize_descriptor(d)
        d = descriptor()
        d["register_map"]["extra"] = "unmodeled.r_state"
        with self.assertRaises(ValueError): hierarchy.normalize_descriptor(d)
        d = descriptor()
        d["hierarchical_registers"].reverse()
        with self.assertRaises(ValueError): hierarchy.normalize_descriptor(d)
        d = descriptor()
        d["register_map"]["r_z_word"] = "other.r_data"
        with self.assertRaises(ValueError): hierarchy.normalize_descriptor(d)

    def test_canonical_and_hierarchical_names_must_both_be_bijective(self):
        for field in ("flat_reference", "reference"):
            with self.subTest(field=field):
                d = descriptor()
                d["registers"][1][field] = d["registers"][0][field]
                update_maps(d)
                with self.assertRaisesRegex(ValueError, "bijective"):
                    hierarchy.normalize_descriptor(d)

    def test_invalid_paths_and_flat_descriptor_contracts_are_rejected(self):
        for path in (None, "", ".leaf", "leaf.", "leaf..state", "leaf/state", "leaf.r-state", "leaf.0state"):
            with self.subTest(path=path):
                d = descriptor()
                d["registers"][0]["reference"] = path
                update_maps(d)
                with self.assertRaises(ValueError): hierarchy.normalize_descriptor(d)
        for field, value in (("flat_reference", "bad.path"), ("flat_reference", "clk"),
                             ("flat_reference", "n0"), ("width", 0), ("width", True), ("index", 1)):
            with self.subTest(field=field, value=value):
                d = descriptor()
                d["registers"][0][field] = value
                update_maps(d)
                with self.assertRaises(ValueError): hierarchy.normalize_descriptor(d)

    def test_missing_or_wrong_width_nets_fail_before_output_is_written(self):
        for mode in ("missing", "short", "long"):
            with self.subTest(mode=mode), tempfile.TemporaryDirectory() as directory:
                document = fixture()
                nets = document["modules"]["nested_pair"]["netnames"]
                if mode == "missing": del nets["control.r_flag"]
                else: nets["control.r_flag"]["bits"] = [] if mode == "short" else [9, 10]
                original, target = Path(directory) / "raw.json", Path(directory) / "normalized.json"
                original.write_text(json.dumps(document))
                before = original.read_bytes()
                with self.assertRaisesRegex(ValueError, "Missing or wrong-width"):
                    hierarchy.prepare_json(original, target, descriptor())
                self.assertFalse(target.exists())
                self.assertEqual(original.read_bytes(), before)

    def test_even_identical_preexisting_canonical_alias_is_ambiguous(self):
        for same_bits in (True, False):
            with self.subTest(same_bits=same_bits):
                document = fixture()
                names = document["modules"]["nested_pair"]["netnames"]
                names["r_z_word"] = deepcopy(names["fifo_2.bank.r_data"])
                if not same_bits: names["r_z_word"]["bits"] = [90, 91, 92]
                with self.assertRaisesRegex(ValueError, "Ambiguous canonical state alias"):
                    self.prepare(document)

    def test_exactly_one_selected_flattened_module_is_required(self):
        for mode in ("missing", "renamed", "extra"):
            with self.subTest(mode=mode):
                document = fixture()
                if mode == "missing": document["modules"].clear()
                elif mode == "renamed": document["modules"]["other"] = document["modules"].pop("nested_pair")
                else: document["modules"]["extra"] = {}
                with self.assertRaisesRegex(ValueError, "one flattened top module"):
                    self.prepare(document)

    def test_omitted_state_or_duplicate_wire_alias_cannot_escape_the_reader(self):
        d = descriptor()
        d["registers"].pop()
        update_maps(d)
        with self.assertRaisesRegex(ValueError, "Changed state mapping"):
            self.prepare(d=d, parse=True)
        document = fixture()
        names = document["modules"]["nested_pair"]["netnames"]
        # Distinct legal names alone do not establish distinct storage bits.
        names["control.r_flag"]["bits"] = [names["fifo_2.bank.r_data"]["bits"][0]]
        with self.assertRaises(ValueError): self.prepare(document, parse=True)

    def test_semantic_d_mutation_is_preserved_for_kernel_certification(self):
        document = fixture()
        document["modules"]["nested_pair"]["cells"]["fifo_2.bank.r_data_ff"]["connections"]["D"] = ["1", "0", "1"]
        _, result, graph = self.prepare(document, parse=True)
        self.assertEqual(result["modules"]["nested_pair"]["cells"], document["modules"]["nested_pair"]["cells"])
        node = graph.nodes[graph.next["r_z_word"]]
        self.assertEqual((node.width, node.op, node.value), (3, "lit", 5))


if __name__ == "__main__":
    unittest.main()
