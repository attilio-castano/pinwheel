"""Boundary checks for experiment proof hints and sequential cone analysis."""
import importlib.util
from pathlib import Path
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import backend_readback as rb
import bank_select_readback as banks

SPEC = importlib.util.spec_from_file_location("bank_cones", ROOT / "scripts/report-bank-select.py")
report = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(report)


class BankSelect(unittest.TestCase):
    def test_cut_hints_reject_aliases_wrong_roles_and_widths(self):
        graph = rb.Graph()
        roles = [("address", 8), ("selection", 1), ("index0", 6), ("word0", 64),
                 ("index1", 6), ("word1", 64), ("successorValue", 64), ("pcValue", 8)]
        rows = [f"{role}\t%v{k}" for k, (role, _) in enumerate(roles)]
        for k, (_, width) in enumerate(roles): graph.nodes[f"v{k}"] = rb.Node(width, "lit", value=0)
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "cuts.tsv"
            path.write_text("\n".join(rows))
            self.assertEqual(list(banks.read_cuts(path, graph, "late-bank").values()), [r for r, _ in roles])
            invalid = [rows[:-1], rows + [rows[0]], [rows[1], rows[0], *rows[2:]],
                       [*rows[:4], "index1\t%v2", *rows[5:]],
                       ["address\t%v999", *rows[1:]], ["address\t%v1", *rows[1:]]]
            for candidate in invalid:
                with self.subTest(rows=candidate):
                    path.write_text("\n".join(candidate))
                    with self.assertRaises(ValueError): banks.read_cuts(path, graph, "late-bank")

    def test_cones_stop_at_registers_and_count_buffers_separately(self):
        def cell(kind, ins, out, clock=False):
            connections = {**ins, "Q" if clock else "X": [out]}
            if clock: connections["CLK"] = [100]
            return {"type": kind, "connections": connections,
                    "port_directions": {p: "output" if p in ("Q", "X") else "input" for p in connections}}
        module = {"netnames": {"r_loader_cursor": {"bits": [1]}, "r_cached_word": {"bits": [20, 21]}},
            "ports": {p: {"bits": [b]} for p, b in (("data", 2), ("incoming", 3), ("init", 4), ("reset", 5), ("command", 6))},
            "cells": {
                "buffer": cell("fake_buf_1", {"A": [1]}, 10),
                "first": cell("fake_and", {"A": [10], "B": [2]}, 11),
                "middle": cell("fake_ff", {"D": [1]}, 15, True),
                "second": cell("fake_and", {"A": [15], "B": [3]}, 16),
                "cache0": cell("fake_ff", {"D": [11]}, 20, True),
                "cache1": cell("fake_ff", {"D": [16]}, 21, True)}}
        result = report.inspect(module, {"fake_ff"}, set())["families"]
        self.assertEqual(result["cursor"]["reached_cache_pins"], 1)
        self.assertEqual(result["cursor"]["maximum_cell_depth"], 2)
        self.assertEqual(result["cursor"]["maximum_logic_depth"], 1)
        self.assertEqual(result["protocol"]["example_pins"], ["cache1/D"])
        self.assertEqual(result["reset"]["reached_cache_pins"], 0)
        module["cells"]["second"]["connections"]["A"] = [16]
        with self.assertRaisesRegex(ValueError, "cycle"): report.inspect(module, {"fake_ff"}, set())


if __name__ == "__main__": unittest.main()
