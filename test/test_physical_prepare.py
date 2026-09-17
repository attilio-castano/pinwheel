"""Candidate identity gates; isolated temporary directories, no CAD execution."""
import hashlib
import importlib.util
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

spec = importlib.util.spec_from_file_location("prepare", Path(__file__).resolve().parents[1] / "scripts/prepare-physical.py")
prepare = importlib.util.module_from_spec(spec)
spec.loader.exec_module(prepare)


class PrepareTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name).resolve()
        self.out = self.root / "build/physical/core"
        for path in ("physical/experiments", "Pinwheel", "test", "scripts"):
            (self.root / path).mkdir(parents=True)
        for path in ("physical/core.json", "physical/core.sdc", "test/Storage.lean", "scripts/prepare-physical.py"):
            (self.root / path).write_text("fixture")
        self.rtl = self.root / "candidate.sv"
        self.rtl.write_text("module validated; endmodule\n")
        self.digest = hashlib.sha256(self.rtl.read_bytes()).hexdigest()
        (self.root / "physical/experiments/command-split-results.json").write_text(json.dumps({"rtl_sha256": self.digest}))

    def invoke(self):
        with patch.object(prepare, "ROOT", self.root), patch.object(prepare, "OUT", self.out), \
                patch.object(prepare, "__file__", str(self.root / "scripts/prepare-physical.py")), \
                patch.object(sys, "argv", ["prepare", "--validated-command-split", str(self.rtl)]), \
                patch.object(prepare.subprocess, "run") as cad:
            prepare.main()
            cad.assert_not_called()

    def test_exact_artifact_is_frozen_and_identified(self):
        self.invoke()
        report = json.loads((self.out / "inputs.json").read_text())
        self.assertEqual(report["rtl_sha256"], self.digest)
        self.assertEqual(report["variant"], "command-split")
        self.assertEqual((self.out / "design.sv").read_bytes(), self.rtl.read_bytes())
        self.assertIn("Frozen", report["generation"])

    def test_changed_artifact_fails_before_preparation(self):
        self.rtl.write_text("different circuit")
        with self.assertRaisesRegex(RuntimeError, "differs"):
            self.invoke()
        self.assertFalse(self.out.exists())

    def test_existing_preparation_is_preserved(self):
        self.out.mkdir(parents=True)
        (self.out / "inputs.json").write_text("preserve")
        with self.assertRaisesRegex(RuntimeError, "Preserve"):
            self.invoke()
        self.assertEqual((self.out / "inputs.json").read_text(), "preserve")


if __name__ == "__main__":
    unittest.main()
