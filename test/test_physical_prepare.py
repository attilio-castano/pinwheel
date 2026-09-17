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

    def invoke(self, arguments=None):
        arguments = arguments or ["--validated-command-split", str(self.rtl)]
        with patch.object(prepare, "ROOT", self.root), patch.object(prepare, "BASE", self.out.parent), \
                patch.object(prepare, "__file__", str(self.root / "scripts/prepare-physical.py")), \
                patch.object(sys, "argv", ["prepare", *arguments]), \
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

    def test_named_manifest_role_prepares_a_separate_design(self):
        manifest = self.root / "physical/experiments/pin-sampled-results.json"
        manifest.write_text(json.dumps({"candidate": {"rtl_sha256": self.digest, "variant": "pin-sampled"}}))
        self.invoke()
        arguments = ["--validated-rtl", str(self.rtl), "--manifest", str(manifest),
                     "--role", "candidate", "--design", "sampled"]
        self.invoke(arguments)
        report = json.loads((self.out.parent / "sampled/inputs.json").read_text())
        self.assertEqual((report["variant"], report["manifest_role"]), ("pin-sampled", "candidate"))
        self.assertEqual(json.loads((self.out / "inputs.json").read_text())["variant"], "command-split")
        with self.assertRaisesRegex(RuntimeError, "Preserve"):
            self.invoke(arguments)

    def test_untracked_manifest_and_partial_options_are_rejected(self):
        outside = self.root / "manifest.json"
        outside.write_text(json.dumps({"rtl_sha256": self.digest}))
        with self.assertRaisesRegex(RuntimeError, "tracked result"):
            self.invoke(["--validated-rtl", str(self.rtl), "--manifest", str(outside), "--design", "other"])
        with self.assertRaises(SystemExit):
            self.invoke(["--validated-rtl", str(self.rtl), "--design", "other"])
        self.assertFalse((self.out.parent / "other").exists())


if __name__ == "__main__":
    unittest.main()
