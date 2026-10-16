from dataclasses import replace
import hashlib
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

TOOLS = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(TOOLS))
from runner import DeadlineExceeded, JobSpec, MAX_JOB_SECONDS, run_owned_job

IMAGE = "sha256:" + "a" * 64
CONTAINER = "b" * 64
CAMPAIGN = "tt-overnight-20261015-000717"


class FakeExecutor:
    def __init__(self, clock, mode="passed", output=None, source=None):
        self.clock, self.mode, self.output, self.source = clock, mode, output, source
        self.calls = []
        self.alive = False

    def __call__(self, argv, **kwargs):
        self.calls.append((argv, kwargs))
        if argv[:2] == ["docker", "run"]:
            self.alive = True
            if self.mode == "timeout":
                self.clock[0] += kwargs["timeout"]
                raise subprocess.TimeoutExpired(argv, kwargs["timeout"])
            if self.mode == "interrupt":
                raise KeyboardInterrupt("test interrupt")
            if self.mode == "late":
                self.clock[0] += 200
            if self.mode == "mutate_source":
                self.source.write_text("changed")
            if self.output:
                (self.output / "checkpoint.def").write_text("actual fake output")
            self.alive = self.mode in ("query_failure", "needs_kill")
            return subprocess.CompletedProcess(argv, 0)
        if argv[:3] == ["docker", "container", "ls"]:
            if self.mode == "query_failure":
                return subprocess.CompletedProcess(argv, 1, "", "query rejected")
            return subprocess.CompletedProcess(argv, 0, CONTAINER + "\n" if self.alive else "", "")
        if argv[:2] == ["docker", "stop"]:
            if self.mode != "needs_kill":
                self.alive = False
            return subprocess.CompletedProcess(argv, 0, "", "")
        if argv[:2] == ["docker", "kill"]:
            self.alive = False
            return subprocess.CompletedProcess(argv, 0, "", "")
        raise AssertionError(argv)


class OwnedRunnerTest(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.source = self.root / "source.odb"
        self.source.write_text("frozen source")
        self.output = self.root / "job"
        self.output.mkdir()
        self.clock = [1000.0]
        self.spec = JobSpec(self.output, self.root / "heavy.lock", IMAGE, ["native-command"], CAMPAIGN,
                            1100, {str(self.source): hashlib.sha256(self.source.read_bytes()).hexdigest()},
                            100, max_job_seconds=100, closeout_reserve_seconds=30)

    def run_fake(self, mode="passed", spec=None):
        fake = FakeExecutor(self.clock, mode, self.output, self.source)
        result = run_owned_job(spec or self.spec, process_run=fake,
                               wall_time=lambda: self.clock[0], monotonic=lambda: self.clock[0],
                               owner_factory=lambda: "test-owner")
        return result, fake

    def test_positive_uses_both_owner_filters_and_clips_native(self):
        result, fake = self.run_fake()
        self.assertEqual(result["status"], "passed")
        self.assertTrue(result["inputs_unchanged"])
        self.assertFalse(result["physical_acceptance_claim"])
        self.assertEqual(result["bounds"]["actual_native_timeout_seconds"], 70)
        command, options = fake.calls[0]
        self.assertIn("org.pinwheel.campaign=" + CAMPAIGN, command)
        self.assertIn("org.pinwheel.baseline_owner=test-owner", command)
        self.assertEqual(options["timeout"], 70)
        self.assertEqual(result["container_termination"]["status"], "absent")
        self.assertIn("checkpoint.def", result["retained_checkpoint_paths"])
        self.assertFalse(self.spec.heavy_lock_path.exists())
        for argv, _ in fake.calls[1:]:
            if argv[:3] == ["docker", "container", "ls"]:
                self.assertIn("label=org.pinwheel.campaign=" + CAMPAIGN, argv)
                self.assertIn("label=org.pinwheel.baseline_owner=test-owner", argv)

    def test_timeout_is_not_success_and_owned_stop_is_confirmed(self):
        result, fake = self.run_fake("timeout")
        self.assertEqual(result["status"], "timed_out")
        self.assertEqual(result["exit_code"], 124)
        self.assertTrue(any(argv[:2] == ["docker", "stop"] for argv, _ in fake.calls))
        self.assertEqual(result["container_termination"]["status"], "absent")

    def test_interrupt_cleans_owner_and_requires_controller_stop(self):
        result, _ = self.run_fake("interrupt")
        self.assertEqual(result["status"], "interrupted")
        self.assertTrue(result["controller_must_stop"])
        self.assertEqual(result["container_termination"]["status"], "absent")

    def test_failed_query_keeps_heavy_lock_and_invalidates(self):
        result, _ = self.run_fake("query_failure")
        self.assertEqual(result["status"], "invalidated")
        self.assertTrue(result["controller_must_stop"])
        self.assertTrue(self.spec.heavy_lock_path.exists())

    def test_kill_fallback_only_targets_exact_owned_id(self):
        result, fake = self.run_fake("needs_kill")
        self.assertEqual(result["status"], "passed")
        self.assertIn(["docker", "kill", CONTAINER], [argv for argv, _ in fake.calls])

    def test_source_mutation_invalidates_even_successful_native_job(self):
        result, _ = self.run_fake("mutate_source")
        self.assertEqual(result["status"], "invalidated")
        self.assertFalse(result["inputs_unchanged"])
        self.assertTrue(result["controller_must_stop"])

    def test_lock_exclusion_and_immutable_receipt(self):
        self.spec.heavy_lock_path.write_text("existing active owner")
        with self.assertRaises(FileExistsError):
            self.run_fake()
        self.spec.heavy_lock_path.unlink()
        self.run_fake()
        with self.assertRaises(FileExistsError):
            self.run_fake()

    def test_absolute_expiry_and_90minute_ceiling(self):
        with self.assertRaises(DeadlineExceeded):
            self.run_fake(spec=replace(self.spec, hard_end_epoch=1020))
        with self.assertRaises(AssertionError):
            self.run_fake(spec=replace(self.spec, max_job_seconds=MAX_JOB_SECONDS + 1))

    def test_no_false_success_if_process_outlives_injected_timeout(self):
        result, _ = self.run_fake("late")
        self.assertEqual(result["status"], "deadline_exceeded")
        self.assertFalse(result["within_absolute_and_job_deadlines"])
        self.assertTrue(result["controller_must_stop"])


if __name__ == "__main__":
    unittest.main()
