"""Checkpoint provenance tests using disposable files; no CAD tools required."""
import hashlib
import importlib.util
import json
from pathlib import Path
import shutil
import sys
import tempfile
import unittest
from unittest.mock import patch

SCRIPTS = Path(__file__).resolve().parents[1] / "scripts"
sys.path.insert(0, str(SCRIPTS))
import physical_checkpoint as checkpoint

spec = importlib.util.spec_from_file_location("physical_runner", SCRIPTS / "run-physical.py")
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)


class CheckpointTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.core = self.root / "build/physical/core"
        self.core.mkdir(parents=True)
        self.netlist = self.core / "design.v"
        self.netlist.write_text("module original; endmodule\n")
        self.sdf = self.core / "slow.sdf"
        self.sdf.write_text("delay data\n")
        self.state = self.core / "state_out.json"
        self.state.write_text(json.dumps({
            "nl": "/work/core/design.v", "def": None,
            "sdf": {"slow": ["/work/core/slow.sdf"]},
            "metrics": {"inherited": float("inf"), "label": "not an artifact"},
        }))
        self.manifest = self.core / "checkpoint-manifest.json"
        checkpoint.capture(self.state, self.manifest, self.core)

    def test_nested_artifacts_and_metrics(self):
        value = checkpoint.verify(self.state, self.manifest, self.core)
        self.assertEqual(set(value["artifacts_sha256"]),
                         {"/work/core/design.v", "/work/core/slow.sdf"})
        self.assertIn("no claim about earlier runs", value["provenance"])

    def test_changed_artifact_with_unchanged_state_is_rejected(self):
        before = self.state.read_bytes()
        self.sdf.write_text("different delays")
        with self.assertRaisesRegex(ValueError, "artifacts_sha256"):
            checkpoint.verify(self.state, self.manifest, self.core)
        self.assertEqual(self.state.read_bytes(), before)

    def test_changed_state_is_rejected(self):
        self.state.write_text(self.state.read_text() + "\n")
        with self.assertRaisesRegex(ValueError, "state_sha256"):
            checkpoint.verify(self.state, self.manifest, self.core)

    def test_missing_artifact_is_rejected(self):
        self.sdf.unlink()
        with self.assertRaisesRegex(ValueError, "Missing"):
            checkpoint.verify(self.state, self.manifest, self.core)

    def test_incomplete_manifest_is_rejected(self):
        value = json.loads(self.manifest.read_text())
        value["artifacts_sha256"].pop("/work/core/slow.sdf")
        self.manifest.write_text(json.dumps(value))
        with self.assertRaisesRegex(ValueError, "artifacts_sha256"):
            checkpoint.verify(self.state, self.manifest, self.core)

    def test_capture_does_not_overwrite_identity(self):
        before = self.manifest.read_bytes()
        with self.assertRaises(FileExistsError):
            checkpoint.capture(self.state, self.manifest, self.core)
        self.assertEqual(self.manifest.read_bytes(), before)

    def test_unknown_or_escaping_paths_are_rejected(self):
        for name in ["/other/design.v", "relative.v", "/work/core/../escape.v"]:
            with self.subTest(name=name):
                self.state.write_text(json.dumps({"nl": name}))
                with self.assertRaises(ValueError):
                    checkpoint.inspect(self.state, self.core)

    def test_symlink_outside_core_is_rejected(self):
        outside = self.root / "outside.v"
        outside.write_text("outside")
        self.netlist.unlink()
        self.netlist.symlink_to(outside)
        with self.assertRaisesRegex(ValueError, "out-of-root"):
            checkpoint.inspect(self.state, self.core)

    def test_snapshot_is_independent_and_can_be_resumed_again(self):
        destination = self.core / "experiments/resume/checkpoint"
        receipt = checkpoint.snapshot(self.state, self.manifest, destination, self.core)
        self.netlist.write_text("changed after snapshot")
        state = destination / "state.json"
        copied = json.loads(state.read_text())
        self.assertEqual(checkpoint.artifact_path(copied["nl"], self.core).read_text(),
                         "module original; endmodule\n")
        self.assertEqual(receipt["manifest_sha256"], checkpoint.sha(destination / "manifest.json"))
        # Inherited views in the next output state still resolve under /work/core.
        later_manifest = self.core / "later-manifest.json"
        checkpoint.capture(state, later_manifest, self.core)
        checkpoint.snapshot(state, later_manifest, self.core / "experiments/second/checkpoint", self.core)

    def test_artifact_change_during_copy_is_rejected(self):
        original_copy = shutil.copyfile

        def corrupt_copy(source, target):
            result = original_copy(source, target)
            if Path(source) == self.netlist:
                Path(target).write_text("corrupt copy")
            return result

        with patch.object(checkpoint.shutil, "copyfile", side_effect=corrupt_copy):
            with self.assertRaisesRegex(ValueError, "changed during snapshot"):
                checkpoint.snapshot(self.state, self.manifest, self.core / "snapshot", self.core)

    def test_runner_rejects_changed_checkpoint_before_docker(self):
        self.netlist.write_text("changed")
        with patch.object(runner, "BASE", self.core.parent), \
                patch.object(sys, "argv", ["run-physical.py", "--tag", "resume",
                    "--from-step", "OpenROAD.DetailedRouting", "--state", str(self.state),
                    "--checkpoint-manifest", str(self.manifest)]), \
                patch.object(runner.subprocess, "check_output") as docker, \
                patch.object(runner.subprocess, "run") as launch:
            with self.assertRaisesRegex(ValueError, "artifacts_sha256"):
                runner.main()
            docker.assert_not_called()
            launch.assert_not_called()
        self.assertFalse((self.core / "experiments/resume").exists())

    def test_runner_uses_snapshot_and_records_identity(self):
        (self.root / "tools").mkdir()
        (self.root / "physical").mkdir()
        (self.core.parent / "pdk").mkdir()
        for name, data in {"core.json": "{}", "core.sdc": "clock constraints"}.items():
            (self.root / "physical" / name).write_text(data)
            (self.core / name).write_text(data)
        (self.core / "design.sv").write_text("prepared RTL")
        (self.core / "inputs.json").write_text(json.dumps({
            "rtl_sha256": checkpoint.sha(self.core / "design.sv"), "boundary": "test"}))
        image = {"Id": "test-image", "Architecture": "arm64", "Os": "linux",
                 "RootFS": {"Layers": []}, "Config": {}}
        (self.root / "tools/physical-toolchain.json").write_text(json.dumps({
            "container_tag": "test-image", "container_rootfs_diff_ids": [],
            "container_runtime_config_sha256": hashlib.sha256(b"{}").hexdigest(),
            "pdk_tree_sha256": "test-tree", "pdk_revision": "test-revision"}))
        (self.core.parent / "pdk/installed.json").write_text(json.dumps({
            "tree_sha256": "test-tree", "revision": "test-revision",
            "files_sha256": {}, "symlinks": {}}))
        with patch.object(runner, "ROOT", self.root), \
                patch.object(runner, "BASE", self.core.parent), \
                patch.object(sys, "argv", ["run-physical.py", "--tag", "resume",
                    "--from-step", "OpenROAD.DetailedRouting", "--state", str(self.state),
                    "--checkpoint-manifest", str(self.manifest)]), \
                patch.object(runner.subprocess, "check_output", return_value=json.dumps([image])), \
                patch.object(runner.subprocess, "run") as launch:
            launch.return_value.returncode = 0
            with self.assertRaises(SystemExit) as result:
                runner.main()
            self.assertEqual(result.exception.code, 0)
        receipt = json.loads((self.core.parent / "resume-invocation.json").read_text())
        command = launch.call_args.args[0]
        mount = receipt["checkpoint"]["mount_path"]
        self.assertTrue(any(f"target={mount},readonly" in arg for arg in command))
        self.assertEqual(command[command.index("--with-initial-state") + 1], mount + "/state.json")
        self.assertEqual(receipt["checkpoint"]["artifact_count"], 2)
        self.assertEqual(receipt["checkpoint_sha256"], checkpoint.sha(self.state))


if __name__ == "__main__":
    unittest.main()
