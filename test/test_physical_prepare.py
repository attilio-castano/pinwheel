"""Candidate identity gates; isolated temporary directories, no CAD execution."""
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
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
        self.git("init", "-q")
        self.commit_manifest(self.root / "physical/experiments/command-split-results.json")

    def git(self, *args):
        return subprocess.run(["git", *args], cwd=self.root, check=True, capture_output=True)

    def commit_manifest(self, manifest):
        self.git("add", str(manifest.relative_to(self.root)))
        self.git("-c", "user.name=Pinwheel Test", "-c", "user.email=pinwheel-test@example.invalid",
                 "-c", "commit.gpgsign=false", "-c", "core.hooksPath=/dev/null", "commit", "-qm", "fixture")

    def invoke(self, arguments=None):
        if arguments is None:
            arguments = ["--validated-command-split", str(self.rtl)]
        run = subprocess.run

        def git_only(command, **kwargs):
            if command[0] != "git":
                raise AssertionError(f"Unexpected CAD execution: {command}")
            return run(command, **kwargs)

        with patch.object(prepare, "ROOT", self.root), patch.object(prepare, "BASE", self.out.parent), \
                patch.object(prepare, "__file__", str(self.root / "scripts/prepare-physical.py")), \
                patch.object(sys, "argv", ["prepare", *arguments]), \
                patch.object(prepare.subprocess, "run", side_effect=git_only):
            prepare.main()

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
        self.commit_manifest(manifest)
        self.invoke()
        arguments = ["--validated-rtl", str(self.rtl), "--manifest", str(manifest),
                     "--role", "candidate", "--design", "sampled"]
        self.invoke(arguments)
        report = json.loads((self.out.parent / "sampled/inputs.json").read_text())
        self.assertEqual((report["variant"], report["manifest_role"]), ("pin-sampled", "candidate"))
        self.assertEqual(json.loads((self.out / "inputs.json").read_text())["variant"], "command-split")
        with self.assertRaisesRegex(RuntimeError, "Preserve"):
            self.invoke(arguments)

    def test_outside_manifest_is_rejected(self):
        outside = self.root / "manifest.json"
        outside.write_text(json.dumps({"rtl_sha256": self.digest}))
        with self.assertRaisesRegex(RuntimeError, "tracked result"):
            self.invoke(["--validated-rtl", str(self.rtl), "--manifest", str(outside), "--design", "other"])
        self.assertFalse((self.out.parent / "other").exists())

    def test_untracked_or_only_staged_manifest_is_rejected(self):
        manifest = self.root / "physical/experiments/uncommitted.json"
        manifest.write_text(json.dumps({"rtl_sha256": self.digest, "variant": "candidate"}))
        arguments = ["--validated-rtl", str(self.rtl), "--manifest", str(manifest), "--design", "other"]
        for staged in (False, True):
            with self.subTest(staged=staged):
                if staged:
                    self.git("add", str(manifest.relative_to(self.root)))
                with self.assertRaisesRegex(RuntimeError, "tracked and committed"):
                    self.invoke(arguments)
                self.assertFalse((self.out.parent / "other").exists())

    def test_dirty_worktree_or_index_manifest_is_rejected_and_preserves_output(self):
        manifest = self.root / "physical/experiments/command-split-results.json"
        original = manifest.read_bytes()
        changed = json.dumps({"rtl_sha256": self.digest, "variant": "unreviewed"}).encode()
        self.out.mkdir(parents=True)
        (self.out / "inputs.json").write_text("preserve")
        for state in ("worktree", "staged", "index-only"):
            with self.subTest(state=state):
                manifest.write_bytes(changed)
                if state != "worktree":
                    self.git("add", str(manifest.relative_to(self.root)))
                if state == "index-only":
                    manifest.write_bytes(original)
                with self.assertRaisesRegex(RuntimeError, "differs from committed HEAD"):
                    self.invoke()
                self.assertEqual((self.out / "inputs.json").read_text(), "preserve")
                self.assertFalse((self.out / "design.sv").exists())

    def test_invalid_options_fail_before_output_mutation(self):
        manifest = str(self.root / "physical/experiments/command-split-results.json")
        candidates = [
            ["--validated-rtl", str(self.rtl)],
            ["--manifest", manifest],
            ["--validated-command-split", str(self.rtl), "--validated-rtl", str(self.rtl), "--manifest", manifest],
            ["--role", "candidate"],
            ["--validated-command-split", str(self.rtl), "--role", "candidate"],
            ["--validated-rtl", str(self.rtl), "--manifest", manifest, "--role", ""],
        ]
        self.out.mkdir(parents=True)
        (self.out / "inputs.json").write_text("preserve")
        for arguments in candidates:
            with self.subTest(arguments=arguments), self.assertRaises(SystemExit):
                self.invoke(arguments)
            self.assertEqual((self.out / "inputs.json").read_text(), "preserve")
            self.assertFalse((self.out / "design.sv").exists())

    def test_missing_or_malformed_role_never_falls_back_to_emission(self):
        manifest = self.root / "physical/experiments/roles.json"
        manifest.write_text(json.dumps({"empty": {}, "list": [], "bad_hash": {"rtl_sha256": "short"},
                                       "missing_variant": {"rtl_sha256": self.digest},
                                       "bad_variant": {"rtl_sha256": self.digest, "variant": ""}}))
        self.commit_manifest(manifest)
        for role in ("missing", "empty", "list", "bad_hash", "missing_variant", "bad_variant"):
            with self.subTest(role=role), self.assertRaisesRegex(RuntimeError, "Manifest"):
                self.invoke(["--validated-rtl", str(self.rtl), "--manifest", str(manifest),
                             "--role", role, "--design", "other"])
            self.assertFalse((self.out.parent / "other").exists())

    def test_manifest_change_during_copy_does_not_create_a_receipt(self):
        manifest = self.root / "physical/experiments/command-split-results.json"
        copy = prepare.shutil.copyfile

        def change_manifest(source, target):
            result = copy(source, target)
            manifest.write_text(manifest.read_text() + "\n")
            return result

        with patch.object(prepare.shutil, "copyfile", side_effect=change_manifest), \
                self.assertRaisesRegex(RuntimeError, "Manifest changed during preparation"):
            self.invoke()
        self.assertFalse((self.out / "inputs.json").exists())


if __name__ == "__main__":
    unittest.main()
