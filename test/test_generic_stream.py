"""Portable stream adapter and independent scoreboard rejection checks."""
import copy
import importlib.util
import json
from pathlib import Path
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import generic_stream_readback as readback

spec = importlib.util.spec_from_file_location("stream_check", ROOT / "scripts/check-stream-hardware.py")
check = importlib.util.module_from_spec(spec)
spec.loader.exec_module(check)


def descriptor(width=2):
    def fields(items):
        return [{"name": name, "width": w, "index": k} for k, (name, w) in enumerate(items)]
    return {"inputs": fields((("reset", 1), ("in_valid", 1), ("out_ready", 1), ("in_data", width * 2))),
            "outputs": fields((("in_ready", 1), ("out_valid", 1), ("out_data", width))),
            "registers": fields((("state_0", 1), ("state_1", width * 2), ("state_2", 1), ("state_3", width))),
            "hierarchical_registers": ["core.left.r_slot_0", "core.left.r_slot_1",
                                       "core.right.r_slot_0", "core.right.r_slot_1"]}


def fixture(desc):
    counter = 2

    def bits(width):
        nonlocal counter
        result = list(range(counter, counter + width))
        counter += width
        return result

    ports = {"clk": {"direction": "input", "bits": bits(1)}}
    for p in desc["inputs"]:
        ports[p["name"]] = {"direction": "input", "bits": bits(p["width"])}
    cells, names = {}, {}
    for p in desc["registers"]:
        name, width = "r_" + p["name"], p["width"]
        q = bits(width)
        names[name] = {"bits": q, "attributes": {}}
        cells[name] = {"type": "$dff", "parameters": {"WIDTH": f"{width:b}", "CLK_POLARITY": "1"},
                       "connections": {"CLK": ports["clk"]["bits"], "D": q[:], "Q": q[:]},
                       "port_directions": {"CLK": "input", "D": "input", "Q": "output"}}
    for p in desc["outputs"]:
        ports[p["name"]] = {"direction": "output", "bits": ["0"] * p["width"]}
    return {"modules": {"pinwheel_stream": {"ports": ports, "cells": cells, "netnames": names, "attributes": {}}}}


class GenericStream(unittest.TestCase):
    def read(self, doc, desc):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "import.json"
            path.write_text(json.dumps(doc))
            return readback.importer(desc).read_rtl(path)

    def test_parameterized_importer_instances_are_independent(self):
        a, b = readback.importer(descriptor(1)), readback.importer(descriptor(17))
        self.assertEqual(a.INPUTS["in_data"][0], 2)
        self.assertEqual(b.INPUTS["in_data"][0], 34)
        self.assertEqual(len(self.read(fixture(descriptor()), descriptor()).next), 4)

    def test_reject_changed_clock_state_and_interface(self):
        desc = descriptor()
        for kind in ("clock", "missing", "alias", "width", "unknown", "extra", "cycle"):
            with self.subTest(kind=kind):
                doc = fixture(desc)
                m = doc["modules"]["pinwheel_stream"]
                if kind == "clock": m["cells"]["r_state_0"]["parameters"]["CLK_POLARITY"] = "0"
                if kind == "missing": del m["cells"]["r_state_0"]
                if kind == "alias": m["netnames"]["r_state_2"] = m["netnames"]["r_state_0"]
                if kind == "width": m["ports"]["in_data"]["bits"].pop()
                if kind == "unknown": m["ports"]["out_valid"]["bits"] = ["x"]
                if kind == "extra": m["ports"]["extra"] = {"direction": "input", "bits": [999]}
                if kind == "cycle":
                    m["cells"]["loop"] = {"type": "$not",
                        "parameters": {"A_SIGNED": "0", "A_WIDTH": "1", "Y_WIDTH": "1"},
                        "connections": {"A": [999], "Y": [999]},
                        "port_directions": {"A": "input", "Y": "output"}}
                    m["ports"]["out_valid"]["bits"] = [999]
                with self.assertRaises(ValueError): self.read(doc, desc)

    def test_hierarchy_mapping_requires_exact_nonaliased_state(self):
        desc = descriptor()
        doc = fixture(desc)
        names = doc["modules"]["pinwheel_stream"]["netnames"]
        for p, path in zip(desc["registers"], desc["hierarchical_registers"], strict=True):
            names[path] = names.pop("r_" + p["name"])
        with tempfile.TemporaryDirectory() as tmp:
            src, dst = Path(tmp) / "raw.json", Path(tmp) / "mapped.json"
            src.write_text(json.dumps(doc))
            readback.prepare_json(src, dst, desc, True)
            self.assertEqual(len(readback.importer(desc).read_rtl(dst).next), 4)
            bad = copy.deepcopy(desc)
            bad["hierarchical_registers"][2] = bad["hierarchical_registers"][0]
            readback.prepare_json(src, dst, bad, True)
            with self.assertRaises(ValueError): readback.importer(desc).read_rtl(dst)
            bad["hierarchical_registers"][2] = "missing"
            with self.assertRaises(ValueError): readback.prepare_json(src, dst, bad, True)

    def test_scoreboard_rejects_loss_duplication_and_wrong_latency(self):
        stimulus = [(1, 0, 1, 0), (0, 1, 1, 3), (0, 0, 1, 0), (0, 0, 1, 0)]
        good = [(0, 0, 0, 0, 0, 0, 0), (1, 1, 0, 0, 1, 0, 0),
                (2, 1, 0, 0, 1, 1, 3), (3, 1, 1, 3, 1, 0, 0)]
        self.assertEqual(check.scoreboard(stimulus, good, 2, 1)["emitted_across_epochs"], 1)
        for bad in (good[:-1], good[:3] + [(3, 1, 1, 2, 1, 0, 0)],
                    good[:2] + [(2, 1, 1, 3, 1, 0, 0), good[3]],
                    good[:3] + [(3, 1, 0, 0, 1, 0, 0)]):
            with self.assertRaises(AssertionError): check.scoreboard(stimulus, bad, 2, 1)


if __name__ == "__main__":
    unittest.main()
