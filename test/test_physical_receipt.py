"""Portable input identities and stale clock-gate baselines; no CAD execution."""
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

SCRIPTS = Path(__file__).resolve().parents[1] / "scripts"
sys.path.insert(0, str(SCRIPTS))
import physical_receipt as receipt

spec = importlib.util.spec_from_file_location("clock_gates", SCRIPTS / "check-clock-gates.py")
gates = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gates)


class ReceiptPaths(unittest.TestCase):
    def test_logical_pdk_symlink_stays_repository_relative(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory) / "repo"
            root.mkdir()
            outside = Path(directory) / "installed-pdk"
            outside.mkdir()
            (outside / "cells.v").write_text("cells")
            (root / "pdk").symlink_to(outside, target_is_directory=True)
            model = root / "pdk/cells.v"
            self.assertEqual(receipt.path_key(model, root), "pdk/cells.v")
            for hashes in ({"pdk/cells.v": "digest"}, {str(model): "digest"}):
                self.assertEqual(receipt.recorded_digest(hashes, model, root), "digest")
            self.assertEqual(receipt.path_key(outside / "cells.v", root), str(outside / "cells.v"))

    def test_conflicting_old_and_new_labels_are_rejected(self):
        root = Path("/example/repo")
        with self.assertRaisesRegex(RuntimeError, "Conflicting"):
            receipt.recorded_digest({"design.v": "first", str(root / "design.v"): "second"},
                                    root / "design.v", root)


class ClockGateBaseline(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name).resolve()
        self.base = self.root / "build/physical"
        self.check = self.base / "fixture-check"
        self.check.mkdir(parents=True)
        self.netlist = self.base / "gated.v"
        self.netlist.write_text("sg13cmos5l_lgcp_1 gate0 (.CLK(clk), .GATE(enable), .GCLK(gclk));\n")
        self.models = self.base / "pdk/ihp-sg13cmos5l/libs.ref/sg13cmos5l_stdcell/verilog/sg13cmos5l_stdcell.v"
        self.models.parent.mkdir(parents=True)
        self.models.write_text("models")
        self.primitives = self.models.with_name("sg13cmos5l_udp.v")
        self.primitives.write_text("primitives")
        self.vectors = self.root / "vectors.txt"
        self.vectors.write_text("oracle vectors")
        self.bench = self.check / "tb.sv"
        self.bench.write_text(f'file = $fopen({json.dumps(str(self.vectors))}, "r");\n')
        self.reference = self.check / "reference.sv"
        self.reference.write_text("reference")

    def save_receipt(self, legacy=False):
        paths = [self.netlist, self.models, self.primitives, self.vectors]
        if not legacy:
            paths += [self.bench, self.reference]
        key = str if legacy else lambda p: receipt.path_key(p, self.root)
        (self.check / "report.json").write_text(json.dumps({"sha256": {key(p): gates.sha(p) for p in paths}}))

    def invoke(self, baseline_code=0, baseline_text="Passed baseline"):
        self.commands = []

        def simulate(command, **kwargs):
            self.commands.append(command)
            if Path(command[0]).name == "iverilog":
                return subprocess.CompletedProcess(command, 0, "", "")
            if Path(command[-1]).name == "baseline.vvp":
                return subprocess.CompletedProcess(command, baseline_code, baseline_text, "")
            return subprocess.CompletedProcess(command, 1, "LOADER edge 42 mismatch", "")

        with patch.object(gates, "ROOT", self.root), patch.object(gates, "BASE", self.base), \
                patch.object(sys, "argv", ["check-clock-gates.py", str(self.netlist), "--label", "fixture", "--jobs", "1"]), \
                patch.object(gates.subprocess, "run", side_effect=simulate) as run:
            gates.main()
            return run.call_count

    def test_current_and_historical_receipts_recheck_the_baseline(self):
        for legacy in (False, True):
            with self.subTest(legacy=legacy):
                self.save_receipt(legacy)
                self.assertEqual(self.invoke(), 6)
                report = json.loads((self.base / "fixture-gates/report.json").read_text())
                self.assertEqual((report["rejected"], report["mutants"]), (2, 2))
                self.assertEqual(report["baseline_simulation"], "Passed baseline")
                self.assertIn("build/physical/fixture-check/tb.sv", report["sha256"])

    def test_changed_vector_or_model_is_rejected_before_simulation(self):
        for path in (self.vectors, self.models):
            with self.subTest(path=path):
                self.save_receipt(legacy=True)
                path.write_text(path.read_text() + "changed")
                with self.assertRaisesRegex(RuntimeError, "input changed"):
                    self.invoke()
                self.assertEqual(self.commands, [])

    def test_changed_generated_reference_is_rejected(self):
        self.save_receipt()
        self.reference.write_text("different reference")
        with self.assertRaisesRegex(RuntimeError, "artifact changed"):
            self.invoke()

    def test_stale_legacy_testbench_failure_cannot_count_as_a_mutant_rejection(self):
        self.save_receipt(legacy=True)
        self.bench.write_text(self.bench.read_text() + '$fatal(1, "LOADER edge 0 stale expected state");\n')
        with self.assertRaisesRegex(RuntimeError, "Unmodified netlist failed"):
            self.invoke(baseline_code=1, baseline_text="LOADER edge 0 stale expected state")
        self.assertFalse((self.base / "fixture-gates/report.json").exists())
        self.assertFalse((self.base / "fixture-gates/0-0").exists())


if __name__ == "__main__":
    unittest.main()
