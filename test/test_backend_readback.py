"""Fail-closed boundary tests without a CAD installation or retained artifacts."""
import importlib.util
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location("backend_readback", ROOT / "scripts/backend_readback.py")
rb = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = rb
SPEC.loader.exec_module(rb)


def fixture():
    next_bit = 2
    def bits(width):
        nonlocal next_bit
        result = list(range(next_bit, next_bit + width))
        next_bit += width
        return result
    ports = {"clk": {"direction": "input", "bits": bits(1)}}
    for name, (width, _) in rb.INPUTS.items(): ports[name] = {"direction": "input", "bits": bits(width)}
    cells, netnames = {}, {}
    for name, (width, _) in rb.REGISTERS.items():
        wires = bits(width)
        netnames[name] = {"bits": wires, "attributes": {}}
        cells[name] = {"type": "$dff", "parameters": {"WIDTH": f"{width:b}", "CLK_POLARITY": "1"},
            "connections": {"CLK": ports["clk"]["bits"], "D": wires[:], "Q": wires[:]},
            "port_directions": {"CLK": "input", "D": "input", "Q": "output"}}
    for name, (width, _) in rb.OUTPUTS.items():
        ports[name] = {"direction": "output", "bits": netnames.get("r_" + name, {}).get("bits", ["0"] * width)}
    return {"ports": ports, "cells": cells, "netnames": netnames, "attributes": {}}


def combinational(module):
    cell = {"type": "$not", "parameters": {"A_SIGNED": "0", "A_WIDTH": "11", "Y_WIDTH": "11"},
            "connections": {"A": module["ports"]["command"]["bits"], "Y": [10000, 10001, 10002]},
            "port_directions": {"A": "input", "Y": "output"}}
    module["cells"]["logic"] = cell
    module["ports"]["mode"]["bits"] = cell["connections"]["Y"]
    return cell


class BackendReadback(unittest.TestCase):
    def read(self, module):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "import.json"
            path.write_text(json.dumps({"modules": {rb.TOP: module}}))
            return rb.read_rtl(path)

    def test_complete_register_and_output_contract(self):
        graph = self.read(fixture())
        self.assertEqual(len(graph.next), 607)
        self.assertEqual(sum(graph.nodes[n].width for n in graph.next), 6233)
        self.assertEqual(len(graph.outputs), 33)

    def test_register_d_and_q_must_both_match_parameter(self):
        module = fixture()
        register = module["cells"]["r_loader_active"]
        register["connections"]["D"] *= 2
        register["parameters"]["WIDTH"] = "10"
        with self.assertRaisesRegex(ValueError, "Register width mismatch"): self.read(module)

    def test_reject_unsupported_import_shapes(self):
        def clock_constant(m):
            m["ports"]["clk"]["bits"] = ["0"]
        def clock_data(m):
            m["cells"]["r_loader_active"]["connections"]["D"] = m["ports"]["clk"]["bits"]
        def aliased_clock(m):
            m["ports"]["init"]["bits"] = m["ports"]["clk"]["bits"]
        def opposite_edge(m): m["cells"]["r_loader_active"]["parameters"]["CLK_POLARITY"] = "0"
        def initialized(m): m["netnames"]["r_loader_active"]["attributes"]["init"] = "0"
        def unknown(m): m["cells"]["r_loader_active"]["connections"]["D"] = ["x"]
        def high_z(m): m["ports"]["busy"]["bits"] = ["z"]
        def undriven(m): m["ports"]["busy"]["bits"] = [99999]
        def missing_state(m): del m["cells"]["r_cached_word"]
        def aliased_state(m): m["netnames"]["r_loader_valid"]["bits"] = m["netnames"]["r_loader_active"]["bits"]
        def missing_output(m): del m["ports"]["busy"]
        def extra_port(m): m["ports"]["unmodeled"] = {"direction": "input", "bits": [10000]}
        def wrong_direction(m): m["ports"]["busy"]["direction"] = "input"
        def memory(m): m["memories"] = {"unmodeled": {}}
        def blackbox(m): m["attributes"]["blackbox"] = "1"
        def asynchronous(m): m["cells"]["r_loader_active"]["type"] = "$adff"
        def signed(m): combinational(m)["parameters"]["A_SIGNED"] = "1"
        def cycle(m):
            cell = combinational(m)
            cell["connections"]["A"] = cell["connections"]["Y"]
        def multiply_driven(m): combinational(m)["connections"]["Y"] = m["ports"]["command"]["bits"]
        def extension(m):
            cell = combinational(m)
            cell["connections"]["A"] = cell["connections"]["A"][:1]
            cell["parameters"]["A_WIDTH"] = "1"
        def unsupported(m): combinational(m)["type"] = "$unknown"
        def directions(m): combinational(m)["port_directions"]["A"] = "output"
        for mutate in (clock_constant, clock_data, aliased_clock, opposite_edge, initialized,
                       unknown, high_z, undriven, missing_state, aliased_state, missing_output,
                       extra_port, wrong_direction, memory, blackbox, asynchronous, signed,
                       cycle, multiply_driven, extension, unsupported, directions):
            with self.subTest(shape=mutate.__name__):
                module = fixture()
                mutate(module)
                with self.assertRaises(ValueError): self.read(module)

    def test_reduction_comparison_and_wiring_semantics(self):
        # Independent truth tables check the trusted adapter's less obvious cells.
        for kind in ("$logic_not", "$reduce_or", "$reduce_and", "$eq", "$ne", "$lt", "$ge", "$gt"):
            for left in range(8):
                for right in range(8) if kind in ("$eq", "$ne", "$lt", "$ge", "$gt") else (0,):
                    with self.subTest(kind=kind, left=left, right=right):
                        module = fixture()
                        def literal(value): return [str((value >> k) & 1) for k in range(3)]
                        binary = kind in ("$eq", "$ne", "$lt", "$ge", "$gt")
                        module["cells"]["logic"] = {"type": kind,
                            "parameters": {"A_SIGNED": "0", "A_WIDTH": "11", "Y_WIDTH": "1",
                                **({"B_SIGNED": "0", "B_WIDTH": "11"} if binary else {})},
                            "connections": {"A": literal(left), "Y": [10000], **({"B": literal(right)} if binary else {})},
                            "port_directions": {"A": "input", "Y": "output", **({"B": "input"} if binary else {})}}
                        module["ports"]["busy"]["bits"] = [10000]
                        graph = self.read(module)
                        expected = {"$logic_not": left == 0, "$reduce_or": left != 0,
                                    "$reduce_and": left == 7, "$eq": left == right, "$ne": left != right, "$lt": left < right,
                                    "$ge": left >= right, "$gt": left > right}[kind]
                        actual = graph.signatures(1)[graph.outputs["busy"]][1][0]
                        self.assertEqual(actual, int(expected))

    def test_inequality_rejects_signed_or_implicitly_sized_operands(self):
        for mutation in ("signed_a", "signed_b", "narrow_b", "wide_result"):
            with self.subTest(mutation=mutation):
                module = fixture()
                cell = {"type": "$ne",
                    "parameters": {"A_SIGNED": "0", "B_SIGNED": "0", "A_WIDTH": "11", "B_WIDTH": "11", "Y_WIDTH": "1"},
                    "connections": {"A": ["0"] * 3, "B": ["1"] * 3, "Y": [10000]},
                    "port_directions": {"A": "input", "B": "input", "Y": "output"}}
                if mutation.startswith("signed_"):
                    cell["parameters"][mutation[-1].upper() + "_SIGNED"] = "1"
                elif mutation == "narrow_b":
                    cell["connections"]["B"] = ["1"]
                    cell["parameters"]["B_WIDTH"] = "1"
                else:
                    cell["connections"]["Y"] = [10000, 10001]
                    cell["parameters"]["Y_WIDTH"] = "10"
                module["cells"]["logic"] = cell
                with self.assertRaises(ValueError): self.read(module)

    def test_equivalence_receipt_requires_source_proof_and_rtl_identity(self):
        spec = importlib.util.spec_from_file_location("backend_check", ROOT / "scripts/check-backend.py")
        check = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(check)
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            proof, implementation = root / "proof", root / "implementation"
            proof.mkdir()
            implementation.mkdir()
            (root / "Source.lean").write_text("source identity\n")
            for name in ("composed.mlir", "composed.sv"):
                (proof / name).write_text(name)
                (implementation / name).write_text(name)
            (proof / "Proof.lean").write_text("proof identity\n")
            receipt = proof / "report.json"
            evidence = {"standard_axioms_only": True, "register_fields": 607, "register_bits": 6233,
                "outputs": 33, "artifact_sha256": {p.name: check.sha(p) for p in proof.iterdir()},
                "source_sha256": {"Source.lean": check.sha(root / "Source.lean")}}
            receipt.write_text(json.dumps(evidence))
            with patch.object(check, "ROOT", root):
                self.assertEqual(check.readback_identity(receipt, implementation)["sha256"], check.sha(receipt))
                for target in (implementation / "composed.sv", proof / "Proof.lean", root / "Source.lean"):
                    with self.subTest(changed=target.name):
                        original = target.read_bytes()
                        target.write_bytes(original + b"changed")
                        with self.assertRaises(RuntimeError): check.readback_identity(receipt, implementation)
                        target.write_bytes(original)


if __name__ == "__main__":
    unittest.main()
