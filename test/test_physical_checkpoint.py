"""Checkpoint provenance tests using disposable files; no CAD tools required."""
import hashlib
import importlib.util
import json
from pathlib import Path
import shutil
import subprocess
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

spec = importlib.util.spec_from_file_location("physical_reporter", SCRIPTS / "report-physical.py")
reporter = importlib.util.module_from_spec(spec)
spec.loader.exec_module(reporter)


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

    def prepare_runner(self):
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
        return image

    def test_runner_uses_snapshot_and_records_identity(self):
        image = self.prepare_runner()
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

    def test_runner_timeout_stops_only_its_named_container(self):
        image = self.prepare_runner()
        with patch.object(runner, "ROOT", self.root), \
                patch.object(runner, "BASE", self.core.parent), \
                patch.object(sys, "argv", ["run-physical.py", "--tag", "bounded", "--timeout-seconds", "7"]), \
                patch.object(runner.subprocess, "check_output", return_value=json.dumps([image])), \
                patch.object(runner.subprocess, "run") as launch:
            launch.side_effect = [subprocess.TimeoutExpired("docker", 7), subprocess.CompletedProcess("stop", 0)]
            with self.assertRaises(SystemExit) as result:
                runner.main()
            self.assertEqual(result.exception.code, 124)
            self.assertEqual(launch.call_args_list[0].kwargs["timeout"], 7)
            self.assertEqual(launch.call_args_list[1].args[0],
                             ["docker", "stop", "--time", "10", "pinwheel-bounded"])
        receipt = json.loads((self.core.parent / "bounded-invocation.json").read_text())
        self.assertEqual(receipt["stop_reason"], "wall_time_limit")
        self.assertEqual(receipt["exit_code"], 124)
        self.assertEqual(receipt["container_termination"]["status"], "stopped")
        self.assertEqual(launch.call_count, 2)

    def run_timeout(self, image, outcomes, tag):
        receipt_path = self.core.parent / (tag + "-invocation.json")
        remaining = iter(outcomes)

        def run(command, **kwargs):
            if command[:2] == ["docker", "run"]:
                raise subprocess.TimeoutExpired(command, 7)
            # The durable timeout must exist before either cleanup operation.
            saved = json.loads(receipt_path.read_text())
            self.assertEqual(saved["exit_code"], 124)
            self.assertEqual(saved["stop_reason"], "wall_time_limit")
            self.assertEqual(saved["container_termination"]["status"], "unconfirmed")
            if command[:2] == ["docker", "stop"]:
                self.assertEqual(command, ["docker", "stop", "--time", "10", "pinwheel-" + tag])
                self.assertEqual(kwargs["timeout"], 30)
            else:
                self.assertEqual(command, ["docker", "container", "ls", "--all", "--filter",
                                           "name=pinwheel-" + tag, "--format", "{{json .}}"])
                self.assertEqual(kwargs["timeout"], 10)
            outcome = next(remaining)
            if isinstance(outcome, BaseException):
                raise outcome
            return outcome

        with patch.object(runner, "ROOT", self.root), \
                patch.object(runner, "BASE", self.core.parent), \
                patch.object(sys, "argv", ["run-physical.py", "--tag", tag, "--timeout-seconds", "7"]), \
                patch.object(runner.subprocess, "check_output", return_value=json.dumps([image])), \
                patch.object(runner.subprocess, "run", side_effect=run):
            with self.assertRaises(SystemExit) as result:
                runner.main()
            self.assertEqual(result.exception.code, 124)
        self.assertIsNone(next(remaining, None), "Expected cleanup operation was skipped")
        self.assertFalse(receipt_path.with_suffix(".json.tmp").exists())
        return json.loads(receipt_path.read_text())

    def test_timeout_preserves_failed_stop_and_confirms_absence(self):
        image = self.prepare_runner()
        receipt = self.run_timeout(image, [subprocess.CompletedProcess("stop", 1),
            subprocess.CompletedProcess("ls", 0, stdout="", stderr="")], "absent")
        self.assertEqual(receipt["container_termination"]["status"], "absent")
        self.assertEqual(receipt["container_termination"]["stop_exit_code"], 1)

    def test_timeout_confirms_exit_after_stop_timeout(self):
        image = self.prepare_runner()
        receipt = self.run_timeout(image, [subprocess.TimeoutExpired("stop", 30),
            subprocess.CompletedProcess("ls", 0, stdout=json.dumps({
                "Names": "pinwheel-exited", "State": "exited"}), stderr="")], "exited")
        self.assertEqual(receipt["container_termination"]["status"], "stopped")
        self.assertIn("TimeoutExpired", receipt["container_termination"]["stop_error"])

    def test_timeout_cannot_infer_absence_from_query_failure(self):
        image = self.prepare_runner()
        cases = [
            (subprocess.CompletedProcess("stop", 1),
             subprocess.CompletedProcess("ls", 1, stdout="", stderr="daemon unavailable")),
            (subprocess.TimeoutExpired("stop", 30), subprocess.TimeoutExpired("ls", 10)),
            (FileNotFoundError("docker unavailable"), FileNotFoundError("docker unavailable")),
        ]
        for i, outcomes in enumerate(cases):
            with self.subTest(case=i):
                receipt = self.run_timeout(image, outcomes, f"failure-{i}")
                termination = receipt["container_termination"]
                self.assertEqual(termination["status"], "unconfirmed")
                self.assertTrue(termination["query_error"])
                self.assertEqual(receipt["exit_code"], 124)

    def test_timeout_does_not_confirm_active_or_ambiguous_state(self):
        image = self.prepare_runner()
        for state in ["running", "paused", "restarting", "created", "removing", "dead"]:
            with self.subTest(state=state):
                receipt = self.run_timeout(image, [subprocess.CompletedProcess("stop", 1),
                    subprocess.CompletedProcess("ls", 0, stdout=json.dumps({
                        "Names": "pinwheel-" + state, "State": state}), stderr="")], state)
                self.assertEqual(receipt["container_termination"]["status"], "unconfirmed")

    def test_timeout_requires_exact_container_name(self):
        image = self.prepare_runner()
        receipt = self.run_timeout(image, [subprocess.CompletedProcess("stop", 1),
            subprocess.CompletedProcess("ls", 0, stdout=json.dumps({
                "Names": "pinwheel-exact-other", "State": "running"}), stderr="")], "exact")
        self.assertEqual(receipt["container_termination"]["status"], "absent")

    def test_timeout_does_not_accept_malformed_listing(self):
        image = self.prepare_runner()
        for i, output in enumerate(["not json", "{}", "[]", '{"Names": null, "State": "exited"}']):
            with self.subTest(output=output):
                receipt = self.run_timeout(image, [subprocess.CompletedProcess("stop", 1),
                    subprocess.CompletedProcess("ls", 0, stdout=output, stderr="")], f"malformed-{i}")
                self.assertEqual(receipt["container_termination"]["status"], "unconfirmed")
                self.assertIn("query_error", receipt["container_termination"])

    def test_interrupted_cleanup_leaves_timeout_and_unconfirmed_termination(self):
        image = self.prepare_runner()
        with patch.object(runner, "ROOT", self.root), \
                patch.object(runner, "BASE", self.core.parent), \
                patch.object(sys, "argv", ["run-physical.py", "--tag", "interrupted"]), \
                patch.object(runner.subprocess, "check_output", return_value=json.dumps([image])), \
                patch.object(runner.subprocess, "run", side_effect=subprocess.TimeoutExpired("run", 3600)), \
                patch.object(runner, "stop_container", side_effect=KeyboardInterrupt):
            with self.assertRaises(KeyboardInterrupt):
                runner.main()
        receipt = json.loads((self.core.parent / "interrupted-invocation.json").read_text())
        self.assertEqual(receipt["exit_code"], 124)
        self.assertEqual(receipt["stop_reason"], "wall_time_limit")
        self.assertEqual(receipt["container_termination"]["status"], "unconfirmed")


class TimeoutReportTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.base = self.root / "build/physical"
        run = self.base / "core/runs/bounded"
        stage = run / "1-finished"
        stage.mkdir(parents=True)
        (stage / "state_out.json").write_text(json.dumps({"metrics": {}}))
        (run / "resolved.json").write_text(json.dumps({
            "CLOCK_PERIOD": 20, "STA_CORNERS": [], "TIMING_VIOLATION_CORNERS": []}))
        self.receipt = {"exit_code": 124, "stop_reason": "wall_time_limit",
                        "stop_step": None, "boundary": "test"}

    def report(self):
        (self.base / "bounded-invocation.json").write_text(json.dumps(self.receipt))
        with patch.object(reporter, "ROOT", self.root), \
                patch.object(reporter, "BASE", self.base), \
                patch.object(sys, "argv", ["report-physical.py", "--tag", "bounded"]):
            reporter.main()

    def test_unconfirmed_or_legacy_timeout_rejected_before_artifact_reads(self):
        for termination in [None, {"status": "unconfirmed"}, {"status": "unexpected"}]:
            with self.subTest(termination=termination):
                if termination is not None:
                    self.receipt["container_termination"] = termination
                with patch.object(Path, "glob", side_effect=AssertionError("Read unsettled run")):
                    with self.assertRaisesRegex(RuntimeError, "termination is unconfirmed"):
                        self.report()
                self.assertFalse((self.base / "bounded-report.json").exists())

    def test_confirmed_timeout_reports_partial_evidence_and_cleanup_status(self):
        for status in ["stopped", "absent"]:
            with self.subTest(status=status):
                self.receipt["container_termination"] = {"status": status, "stop_exit_code": 1}
                self.report()
                report = json.loads((self.base / "bounded-report.json").read_text())
                self.assertEqual(report["flow_exit_code"], 124)
                self.assertEqual(report["container_termination"], self.receipt["container_termination"])
                self.assertFalse(report["detailed_routing_completed"])

    def test_ordinary_completed_receipt_remains_supported(self):
        self.receipt.pop("stop_reason")
        self.receipt["exit_code"] = 0
        self.report()
        report = json.loads((self.base / "bounded-report.json").read_text())
        self.assertEqual(report["flow_exit_code"], 0)
        self.assertIsNone(report["container_termination"])


if __name__ == "__main__":
    unittest.main()
