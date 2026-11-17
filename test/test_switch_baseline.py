"""Portable checks for the generic netlist path metric's sequential boundaries."""
import importlib.util
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
spec = importlib.util.spec_from_file_location("switch_baseline_checks", ROOT / "scripts/check-switch-baseline.py")
baseline = importlib.util.module_from_spec(spec)
spec.loader.exec_module(baseline)


def gate(kind, inputs, output):
    return {"type": kind, "port_directions": {**{name: "input" for name in inputs}, "Y": "output"},
            "connections": {**{name: [bit] for name, bit in inputs.items()}, "Y": [output]}}


class GenericDepthTests(unittest.TestCase):
    def test_flops_cut_paths_and_controls_are_endpoints(self):
        module = {"ports": {"in": {"direction": "input", "bits": [1]},
                             "clk": {"direction": "input", "bits": [2]},
                             "out": {"direction": "output", "bits": [7]}},
                  "cells": {
                      "a": gate("$_NOT_", {"A": 1}, 3),
                      "b": gate("$_AND_", {"A": 1, "B": 3}, 4),
                      "ff": {"type": "$_DFFE_PP_",
                             "port_directions": {"C": "input", "D": "input", "E": "input", "Q": "output"},
                             "connections": {"C": [2], "D": [4], "E": [4], "Q": [6]}},
                      "c": gate("$_XOR_", {"A": 6, "B": 1}, 7)}}
        result = baseline.generic_depth(module)
        self.assertEqual(result["max_combinational_cell_levels"], 2)
        self.assertEqual(result["max_output_levels"], 1)
        self.assertEqual(result["max_register_input_levels"], 2)
        self.assertEqual(result["register_bits"], 1)
        self.assertEqual(result["endpoint_count"], 3)

    def test_constants_wires_and_reconvergence(self):
        module = {"ports": {"in": {"direction": "input", "bits": [1]},
                             "out": {"direction": "output", "bits": [1, "0", 4]}},
                  "cells": {"a": gate("$_NOT_", {"A": 1}, 2),
                            "b": gate("$_NOT_", {"A": 2}, 3),
                            "c": gate("$_MUX_", {"A": 2, "B": 3, "S": "1"}, 4)}}
        self.assertEqual(baseline.generic_depth(module)["max_output_levels"], 3)

    def test_cycle_is_rejected(self):
        module = {"ports": {"out": {"direction": "output", "bits": [2]}},
                  "cells": {"a": gate("$_NOT_", {"A": 3}, 2),
                            "b": gate("$_NOT_", {"A": 2}, 3)}}
        with self.assertRaisesRegex(ValueError, "Combinational cycle"):
            baseline.generic_depth(module)

    def test_missing_driver_is_rejected(self):
        module = {"ports": {"out": {"direction": "output", "bits": [2]}}, "cells": {}}
        with self.assertRaisesRegex(ValueError, "Undriven"):
            baseline.generic_depth(module)

    def test_unsupported_cells_are_rejected(self):
        module = {"ports": {}, "cells": {"mystery": {"type": "mystery", "connections": {}}}}
        with self.assertRaisesRegex(ValueError, "Unsupported"):
            baseline.generic_depth(module)


if __name__ == "__main__":
    unittest.main()
