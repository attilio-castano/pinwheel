"""No-CAD admission, tamper and host stage-gate regressions."""
import ast
import contextlib
import copy
import hashlib
import io
import json
from pathlib import Path
import shutil
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest import mock

TOOLS = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(TOOLS))
import stage
from campaign_fixtures import native_program_bytes

IMAGE = "sha256:" + "a" * 64
CASES = [("plain", "original", True), ("plain", "patched", True),
         ("same_width", "original", False), ("same_width", "patched", True),
         ("wide", "original", False), ("wide", "patched", True),
         ("fixed", "patched", True), ("distinct_rule", "patched", False),
         ("ndr_rect", "patched", False), ("ambiguous", "patched", False),
         ("unmatched", "patched", False), ("empty", "patched", False)]


def write(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value))


class StageAdmissionTest(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name).resolve()
        # Host tests own their input guide. The production generator still sees
        # the exact tracked native template, without depending on ignored build/.
        original = self.root / "original"
        original.mkdir()
        (original / "input.guide").write_text("synthetic host-test routing guide\n")
        (original / "native.py").write_bytes(native_program_bytes())
        original_patch = mock.patch.object(stage, "ORIGINAL", original)
        original_patch.start()
        self.addCleanup(original_patch.stop)
        self.build_root, self.fixtures_root = self.root / "buildjob", self.root / "fixturejob"
        self.build_root.mkdir(); self.fixtures_root.mkdir()
        self.adapter = self.build_root / "patched.so"
        self.original = self.build_root / "original.so"
        self.adapter.write_bytes(b"patched pinned adapter")
        self.original.write_bytes(b"original pinned importer")
        self.build = self.build_root / "build.json"
        self.build_job = self.build_root / "report.json"
        self.fixtures = self.fixtures_root / "fixtures.json"
        self.fixtures_job = self.fixtures_root / "report.json"
        write(self.build, {"status": "passed", "commands": [
            {"variant": "original", "returncode": 0, "binary_sha256": stage.sha(self.original)},
            {"variant": "patched", "returncode": 0, "binary_sha256": stage.sha(self.adapter)}]})
        write(self.fixtures, {"status": "passed", "fixture_count": len(CASES),
             "before_any_PA_GC_TA_DR": True,
             "binary_sha256": {"original": stage.sha(self.original), "patched": stage.sha(self.adapter)},
             "cases": [{"case": case, "variant": variant, "expected_success": expected,
                        "actual_success": expected, "gate_passed": True} for case, variant, expected in CASES]})
        self.seal(self.build_job, [self.adapter, self.original, self.build])
        self.seal(self.fixtures_job, [self.fixtures])
        self.args = SimpleNamespace(adapter=self.adapter, adapter_build_receipt=self.build,
                                    adapter_build_job_receipt=self.build_job,
                                    adapter_fixture_receipt=self.fixtures,
                                    adapter_fixture_job_receipt=self.fixtures_job, control_root=None)
        self.manifest = {"image_id": IMAGE}
        self.control_guides_hash = stage.sha(stage.ORIGINAL / "input.guide")

    def seal(self, receipt, artifacts):
        write(receipt, {"status": "passed", "exit_code": 0, "image_id": IMAGE,
                        "inputs_unchanged": True, "container_termination": {"status": "absent"},
                        "within_absolute_and_job_deadlines": True,
                        "artifact_sha256": {str(p.relative_to(receipt.parent)): stage.sha(p) for p in artifacts}})

    def edit_fixture_and_reseal(self, mutation):
        value = stage.read(self.fixtures); mutation(value); write(self.fixtures, value)
        self.seal(self.fixtures_job, [self.fixtures])

    def test_positive_adapter_admission(self):
        result = stage.adapter_admission(self.args, self.manifest)
        self.assertEqual(result["status"], "admitted")
        self.assertEqual(result["adapter_sha256"], stage.sha(self.adapter))

    def test_adapter_tamper_rejected_by_actual_build_artifact_binding(self):
        self.adapter.write_bytes(b"changed after successful build")
        with self.assertRaises(AssertionError): stage.adapter_admission(self.args, self.manifest)

    def test_fixture_report_tamper_rejected_without_resealing(self):
        self.fixtures.write_text(self.fixtures.read_text() + " ")
        with self.assertRaises(AssertionError): stage.adapter_admission(self.args, self.manifest)

    def test_failed_or_unconfirmed_or_late_job_not_admitted(self):
        base = stage.read(self.build_job)
        for field, value in [("status", "timed_out"), ("inputs_unchanged", False),
                             ("within_absolute_and_job_deadlines", False),
                             ("container_termination", {"status": "unconfirmed"}),
                             ("image_id", "sha256:" + "f" * 64)]:
            with self.subTest(field=field):
                changed = copy.deepcopy(base); changed[field] = value; write(self.build_job, changed)
                with self.assertRaises(AssertionError): stage.adapter_admission(self.args, self.manifest)
        write(self.build_job, base)

    def test_empty_duplicate_missing_or_failed_fixture_cases_rejected(self):
        base = stage.read(self.fixtures)
        mutations = [lambda x: x.update(cases=[]),
                     lambda x: x["cases"].__setitem__(1, copy.deepcopy(x["cases"][0])),
                     lambda x: x["cases"][0].update(case="unexpected_case"),
                     lambda x: x["cases"][0].update(gate_passed=False)]
        for mutation in mutations:
            with self.subTest(mutation=mutation):
                write(self.fixtures, base); self.edit_fixture_and_reseal(mutation)
                with self.assertRaises(AssertionError): stage.adapter_admission(self.args, self.manifest)

    def test_fixture_binary_mismatch_rejected_even_if_outer_job_succeeded(self):
        self.edit_fixture_and_reseal(lambda x: x["binary_sha256"].update(patched="0" * 64))
        with self.assertRaises(AssertionError): stage.adapter_admission(self.args, self.manifest)

    def control(self):
        control = self.root / "control"; control.mkdir()
        odb = control / "input.odb"; odb.write_bytes(b"exact source checkpoint")
        library = control / "libpinwheel_drt_preservation.so"; shutil.copyfile(self.adapter, library)
        plan = control / "stage-plan.json"
        write(plan, {"control": True, "end_iter": 0, "source_odb_sha256": stage.sha(odb),
                     "adapter_sha256": stage.sha(library), "source_guides_sha256": self.control_guides_hash})
        wire = control / "control-wire-proof.json"; write(wire, {"status": "passed"})
        write(control / "adjudication.json", {"control": True, "stage_execution_and_scope_gate_passed": True})
        self.seal(control / "report.json", [odb, library, plan, wire])
        self.args.control_root = control
        return control, stage.sha(odb)

    def test_candidate_requires_exact_source_control(self):
        with self.assertRaises(AssertionError): stage.control_admission(self.args, stage.sha(self.adapter), "0" * 64, IMAGE)
        control, source = self.control()
        self.assertEqual(stage.control_admission(self.args, stage.sha(self.adapter), source, IMAGE)["root"], str(control))
        with self.assertRaises(AssertionError): stage.control_admission(self.args, stage.sha(self.adapter), "0" * 64, IMAGE)
        with self.assertRaises(AssertionError): stage.control_admission(self.args, "0" * 64, source, IMAGE)

    def test_control_plan_input_library_and_wire_proof_tamper_rejected(self):
        control, source = self.control()
        for filename in ["stage-plan.json", "input.odb", "libpinwheel_drt_preservation.so", "control-wire-proof.json"]:
            with self.subTest(filename=filename):
                path = control / filename; original = path.read_bytes(); path.write_bytes(original + b" ")
                with self.assertRaises(AssertionError): stage.control_admission(self.args, stage.sha(self.adapter), source, IMAGE)
                path.write_bytes(original)

    def test_failed_host_control_adjudication_cannot_admit_candidate(self):
        control, source = self.control()
        write(control / "adjudication.json", {"control": True, "stage_execution_and_scope_gate_passed": False})
        with self.assertRaises(AssertionError): stage.control_admission(self.args, stage.sha(self.adapter), source, IMAGE)

    def test_different_control_guides_rejected_even_if_control_plan_is_hash_bound(self):
        control, source = self.control()
        plan = stage.read(control / "stage-plan.json")
        plan["source_guides_sha256"] = "0" * 64
        write(control / "stage-plan.json", plan)
        self.seal(control / "report.json", [control / name for name in
                  ["stage-plan.json", "input.odb", "libpinwheel_drt_preservation.so", "control-wire-proof.json"]])
        with self.assertRaises(AssertionError):
            stage.control_admission(self.args, stage.sha(self.adapter), source, IMAGE)

    def test_generated_worker_syntax_alias_order_and_strict_control_tokens(self):
        for iteration, control, snapshots in [(0, True, False), (3, False, False), (3, False, True)]:
            with self.subTest(iteration=iteration, control=control, snapshots=snapshots):
                program = stage.native_program(iteration, control, snapshots)
                ast.parse(program)
                self.assertIn(f"detailed_route -droute_end_iter {iteration} ", program)
                self.assertLess(program.index("interp alias {} drt::detailed_route_cmd"), program.index("B,BG,BW=inventory('before')"))
                self.assertEqual("control_wires_exact=" in program, control)
                self.assertEqual("-snapshot_dir /work/diagnostic/checkpoints" in program, snapshots)
                if control:
                    self.assertIn("('NETS','SPECIALNETS')", program)
                    self.assertIn("RULE_TAPER_tokens_exact", program)


class StageHostGateTest(unittest.TestCase):
    """Exercise stage.main with fake Docker and a fake independent scope readback."""
    setUp = StageAdmissionTest.setUp
    seal = StageAdmissionTest.seal
    control = StageAdmissionTest.control

    def run_stage(self, *, control=False, native_log=None, importer_variant="patched",
                  scope_status="scope_verified", producer_status="passed", wire_status="passed",
                  snapshots=False, requested_end=3):
        repo = self.root / "repo"; repo.mkdir()
        original = repo / "original"; original.mkdir()
        actual_original = stage.ORIGINAL
        shutil.copyfile(actual_original / "native.py", original / "native.py")
        for name in ("native_inventory.py", "native-script-hashes.json", "load.tcl", "coordinator.py", "baseline-env.tcl", "corner-env.tcl", "capability-admission.json", "core.sdc", "input.guide"):
            (original / name).write_text("staged fixture input")
        (original / "lib").mkdir(); (original / "lib/lib.lib").write_text("library")
        self.control_guides_hash = stage.sha(original / "input.guide")
        source = repo / "source"; source.mkdir()
        (source / "checkpoint.odb").write_bytes(b"exact source checkpoint")
        for name in ("checkpoint.def", "native-inventory.json", "master-OBS-signature.json", "via-definitions.json"):
            (source / name).write_text("{}")
        audit = repo / "build/physical/tt-p2-drt-postroute-tools-03/audit.py"
        audit.parent.mkdir(parents=True); audit.write_text("# retained mock scope implementation")
        manifest = self.root / "campaign/manifest.json"
        write(manifest, {"image_id": IMAGE, "hard_stop_epoch": 10000,
                         "protected_sources_sha256": {}, "reference_files_sha256": {}})
        if not control: self.control()
        default_log = ("Start 0th optimization iteration.\nNumber of violations = 2.\nViol/Layer Metal2 Via2\nShort 2 0\n"
                       + ("" if control else "Start 3rd optimization iteration.\nNumber of violations = 1.\nViol/Layer Metal2 Via2\nShort 1 0\n")
                       + "Complete detail routing.\n")

        def fake_job(spec):
            (spec.output_dir / "native.log").write_text(default_log if native_log is None else native_log)
            write(spec.output_dir / "import-preservation.json", {"status": "passed", "importer_variant": importer_variant,
                  "before_PA_GC_TA_DR": True, "audit_does_not_modify_imported_state": True,
                  "geometry_and_per_object_path_rule_multisets_exact": True})
            if control: write(spec.output_dir / "control-wire-proof.json", {"status": wire_status})
            receipt = {"status": producer_status}; write(spec.output_dir / "report.json", receipt)
            return receipt

        argv = ["stage.py", "--manifest", str(manifest), "--name", "fixture",
                "--adapter", str(self.adapter), "--adapter-build-receipt", str(self.build),
                "--adapter-build-job-receipt", str(self.build_job),
                "--adapter-fixture-receipt", str(self.fixtures),
                "--adapter-fixture-job-receipt", str(self.fixtures_job),
                "--source-root", str(source), "--end-iter", "0" if control else str(requested_end), "--native-seconds", "300"]
        if control: argv.append("--control")
        else: argv += ["--control-root", str(self.args.control_root)]
        if snapshots: argv.append("--snapshots")
        loader = SimpleNamespace(loader=SimpleNamespace(exec_module=lambda module: None))
        module = SimpleNamespace(audit=lambda report: {"status": scope_status})
        with mock.patch.object(stage, "ROOT", repo), mock.patch.object(stage, "ORIGINAL", original), \
             mock.patch.object(stage, "run_owned_job", side_effect=fake_job), \
             mock.patch.object(stage.time, "time", return_value=1000), \
             mock.patch.object(stage.importlib.util, "spec_from_file_location", return_value=loader), \
             mock.patch.object(stage.importlib.util, "module_from_spec", return_value=module), \
             mock.patch.object(sys, "argv", argv), contextlib.redirect_stdout(io.StringIO()):
            result = stage.main()
        return result, stage.read(manifest.parent / "runs/fixture/adjudication.json")

    def test_completed_candidate_and_exact_control_pass_execution_scope_gate_only(self):
        result, report = self.run_stage()
        self.assertEqual(result, 0)
        self.assertTrue(report["stage_execution_and_scope_gate_passed"])
        self.assertFalse(report["physical_acceptance_claim"])
        self.assertFalse(report["all_terminal_physical_connectivity_proven"])

    def test_nullable_final_table_fails_without_indexing_none(self):
        result, report = self.run_stage(native_log="Start 0th optimization iteration.\nCompleting 10% with 0 violations.\n")
        self.assertEqual(result, 1)
        self.assertIsNone(report["completed_native_final_count"])

    def test_iteration3_start_without_completed_table_does_not_pass(self):
        result, _ = self.run_stage(native_log="Start 3rd optimization iteration.\nCompleting 100% with 1 violations.\n")
        self.assertEqual(result, 1)

    def test_earlier_completed_positive_stage_cannot_satisfy_requested17(self):
        result, report = self.run_stage(requested_end=17)
        self.assertEqual(result, 1)
        self.assertEqual(report["requested_end_iteration"], 17)
        self.assertEqual(report["completed_native_end_iteration"], 3)

    def test_actual_completed17_is_required_for_positive_requested17(self):
        text = "Start 17th optimization iteration.\nNumber of violations = 1.\nViol/Layer Metal4\nShort 1\nComplete detail routing.\n"
        result, report = self.run_stage(native_log=text, requested_end=17)
        self.assertEqual(result, 0)
        self.assertEqual(report["completed_native_end_iteration"], 17)

    def test_actual_completed_early_zero_can_end_requested17(self):
        text = "Start 3rd optimization iteration.\nNumber of violations = 0.\nViol/Layer Metal4\n[INFO DRT-0267] elapsed time = 00:00:01\nComplete detail routing.\n"
        self.assertEqual(self.run_stage(native_log=text, requested_end=17)[0], 0)

    def test_incomplete_early_zero_progress_cannot_end_requested17(self):
        text = "Start 3rd optimization iteration.\nCompleting 100% with 0 violations.\n"
        self.assertEqual(self.run_stage(native_log=text, requested_end=17)[0], 1)

    def test_native_error_does_not_pass_even_if_producer_claims_success(self):
        text = "Start 3rd optimization iteration.\nNumber of violations = 1.\nViol/Layer Metal2\nShort 1\nComplete detail routing.\n[ERROR DRT-0206] failed connectivity\n"
        self.assertEqual(self.run_stage(native_log=text)[0], 1)

    def test_extra_iteration_beyond_declared_bound_rejected(self):
        text = "Start 4th optimization iteration.\nNumber of violations = 1.\nViol/Layer Metal2\nShort 1\nComplete detail routing.\n"
        self.assertEqual(self.run_stage(native_log=text)[0], 1)

    def test_original_importer_never_passes_production_gate(self):
        self.assertEqual(self.run_stage(importer_variant="original")[0], 1)

    def test_rejected_scope_never_passes_execution_gate(self):
        self.assertEqual(self.run_stage(scope_status="scope_rejected")[0], 1)

    def test_failed_producer_never_promoted(self):
        self.assertEqual(self.run_stage(producer_status="timed_out")[0], 1)

    def test_control_requires_exact_wire_proof(self):
        self.assertEqual(self.run_stage(control=True, wire_status="failed")[0], 1)

    def test_positive_nonempty_exact_control(self):
        self.assertEqual(self.run_stage(control=True)[0], 0)

    def test_zero_control_counter_does_not_prove_regenerated_nonempty_markers(self):
        text = "Start 0th optimization iteration.\nNumber of violations = 0.\nViol/Layer Metal2\n[INFO DRT-0267] elapsed time = 00:00:01\nComplete detail routing.\n"
        self.assertEqual(self.run_stage(control=True, native_log=text)[0], 1)

    def test_missing_iteration_identity_is_rejected_without_type_error(self):
        text = "Number of violations = 1.\nViol/Layer Metal2\nShort 1\nComplete detail routing.\n"
        self.assertEqual(self.run_stage(native_log=text)[0], 1)

    def test_unqualified_resident_writer_snapshots_rejected_before_launch(self):
        with self.assertRaises(AssertionError):
            self.run_stage(snapshots=True)


if __name__ == "__main__":
    unittest.main()
