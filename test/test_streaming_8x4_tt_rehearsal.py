import hashlib
import json
from pathlib import Path
import sys
import tempfile
import unittest


sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
import streaming_8x4_tt_rehearsal as rehearsal


class RehearsalTests(unittest.TestCase):
    def setUp(self):
        temp = tempfile.TemporaryDirectory()
        self.addCleanup(temp.cleanup)
        self.root = Path(temp.name).resolve()
        self.bundle = self.root / "build" / "bundle"
        assets = {role: self.file(f"build/input-{role}", f"fixture {role}")
                  for role in rehearsal.REQUIRED_ASSETS}
        self.spec = {
            "schema": rehearsal.INPUT_SCHEMA,
            "source_commit": "a" * 40,
            "target_odb_sha256": assets["odb"]["sha256"],
            "upstream": dict(rehearsal.UPSTREAM),
            "assets": assets,
            "receipts": {},
        }

    def file(self, relative, value):
        path = self.root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(value)
        return {"path": relative, "sha256": hashlib.sha256(value.encode()).hexdigest()}

    def native(self, checks, *, target=None):
        assets = self.spec["assets"]
        value = {"schema": rehearsal.NATIVE_SCHEMA,
                 "target_odb_sha256": target or self.spec["target_odb_sha256"],
                 "gds_sha256": assets["gds"]["sha256"], "checks": checks}
        self.spec["receipts"]["native"] = self.file("build/native.json", json.dumps(value))

    def test_package_copies_assets_and_keeps_unexecuted_gates_open(self):
        result = rehearsal.assemble(self.root, self.spec, self.bundle)
        self.assertTrue(result["verified"])
        self.assertIn("tt_precheck", result["open_gates"])
        self.assertIn("qualified_timing", result["open_gates"])
        self.assertFalse(result["local_checks_passed"])
        self.assertFalse(result["tapeout_ready"])
        target = self.bundle / "package" / f"verilog/{rehearsal.TOP}.v"
        self.assertEqual(target.read_text(), "fixture nl")
        target.write_text("different verilog")
        with self.assertRaisesRegex(ValueError, "SHA-256 differs"):
            rehearsal.verify(self.root, self.bundle, result["manifest_sha256"])

    def test_precheck_cannot_use_the_same_target_with_stale_metadata(self):
        assets = self.spec["assets"]
        old_info = self.file("build/old-info.yaml", "superseded metadata")
        self.native({"tt_precheck": {"status": "pass",
                                     "artifacts": [assets["gds"], assets["lef"], assets["pnl"], old_info],
                                     "support_revision": self.spec["upstream"]["rehearsal_support_revision"]}})
        with self.assertRaisesRegex(ValueError, "TT precheck does not consume"):
            rehearsal.assemble(self.root, self.spec, self.bundle)
        self.assertFalse(self.bundle.exists())

    def test_green_precheck_summary_cannot_override_a_failed_raw_check(self):
        assets = self.spec["assets"]
        cases = [f'<testcase name="{name}" time="1"></testcase>' for name in rehearsal.TT_CHECKS[:-1]]
        cases.append('<testcase name="Analog pin check" time="1"><error message="unexpected pin"/></testcase>')
        results = self.file("build/results.xml", '<testsuites><testsuite name="Tiny Tapeout Prechecks">'
                            + "".join(cases) + "</testsuite></testsuites>")
        records = [assets[role] for role in ("gds", "lef", "pnl", "info_yaml")] + [results]
        self.native({"tt_precheck": {"status": "pass", "artifacts": records, "exit_code": 0,
                                     "support_revision": self.spec["upstream"]["rehearsal_support_revision"]}})
        with self.assertRaisesRegex(ValueError, "Native precheck exit/report disagreement"):
            rehearsal.assemble(self.root, self.spec, self.bundle)

    def test_native_receipt_from_a_different_target_is_rejected(self):
        self.native({}, target="a" * 64)
        with self.assertRaisesRegex(ValueError, "Native receipt target differs"):
            rehearsal.assemble(self.root, self.spec, self.bundle)

    def test_g4_same_odb_with_a_different_netlist_is_rejected(self):
        value = {"schema": rehearsal.G4_SCHEMAS["g4_transport"],
                 "target_odb_sha256": self.spec["target_odb_sha256"],
                 "target_gds_sha256": self.spec["assets"]["gds"]["sha256"],
                 "netlist_sha256": "a" * 64, "passed": True}
        self.spec["receipts"]["g4_transport"] = self.file("build/transport.json", json.dumps(value))
        with self.assertRaisesRegex(ValueError, "Stale digital receipt"):
            rehearsal.assemble(self.root, self.spec, self.bundle)

    def test_symlink_and_traversal_instead_of_local_source_are_rejected(self):
        gds = self.spec["assets"]["gds"]
        link = self.root / "build" / "link"
        link.symlink_to(self.root / gds["path"])
        for relative, message in (("build/link", "Symbolic link"), ("build/../input", "Noncanonical")):
            with self.subTest(relative=relative):
                self.spec["assets"]["gds"] = dict(gds, path=relative)
                with self.assertRaisesRegex(ValueError, message):
                    rehearsal.assemble(self.root, self.spec, self.bundle)

    def test_no_existing_bundle_is_overwritten(self):
        result = rehearsal.assemble(self.root, self.spec, self.bundle)
        with self.assertRaises(FileExistsError):
            rehearsal.assemble(self.root, self.spec, self.bundle)
        self.assertEqual(rehearsal.verify(self.root, self.bundle, result["manifest_sha256"]), result)

    def test_manifest_digest_must_be_pinned_outside_the_bundle(self):
        result = rehearsal.assemble(self.root, self.spec, self.bundle)
        path = self.bundle / "manifest.json"
        value = json.loads(path.read_text())
        value["tapeout_ready"] = True
        path.write_text(json.dumps(value))
        with self.assertRaisesRegex(ValueError, "reviewed SHA-256"):
            rehearsal.verify(self.root, self.bundle, result["manifest_sha256"])

    def test_archive_metadata_must_match_the_workspace_package(self):
        archive = self.root / "clean-archive"
        for role, relative in rehearsal.TRACKED_ASSETS.items():
            self.spec["assets"][role] = self.file(f"build/{role}", f"fixture {role}")
            self.file(f"clean-archive/{relative}", f"fixture {role}")
        result = rehearsal.assemble(self.root, self.spec, self.bundle)
        self.assertEqual(rehearsal.verify(self.root, self.bundle, result["manifest_sha256"],
                                          source_archive=archive), result)
        (archive / "info.yaml").write_text("different archive metadata")
        with self.assertRaisesRegex(ValueError, "SHA-256 differs: info.yaml"):
            rehearsal.verify(self.root, self.bundle, result["manifest_sha256"], source_archive=archive)

    def test_shuttle_revision_is_pinned(self):
        self.spec["upstream"]["action_revision"] = "a" * 40
        with self.assertRaisesRegex(ValueError, "exact support/action revisions differ"):
            rehearsal.assemble(self.root, self.spec, self.bundle)

    def test_manual_go_does_not_turn_pending_local_checks_green(self):
        value = {"schema": "pinwheel.tt-rehearsal-decision.v1",
                 "target_odb_sha256": self.spec["target_odb_sha256"],
                 "gds_sha256": self.spec["assets"]["gds"]["sha256"],
                 "rehearsal_decision": "go", "fabrication_decision": "no-go",
                 "open_gates": {name: {"status": "open", "reason": "Independent evidence pending"}
                                for name in rehearsal.RELEASE_BLOCKERS}}
        self.spec["receipts"]["release_decision"] = self.file("build/decision.json", json.dumps(value))
        with self.assertRaisesRegex(ValueError, "go requires all local evidence"):
            rehearsal.assemble(self.root, self.spec, self.bundle)

    def test_bringup_receipt_must_consume_the_current_g4_model(self):
        model = self.file("build/wire/worker/unchanged.vvp", "new simulator")
        worker = self.file("build/wire/worker/report.json",
                           json.dumps({"artifact_sha256": {"unchanged.vvp": model["sha256"]}}))
        wire = {"worker_report": worker, "worker_artifact_sha256": {"unchanged.vvp": model["sha256"]}}
        fixture = {"schema": "pinwheel.streaming-ready-board-bringup.v1", "top_module": rehearsal.TOP,
                   "queue_depth": 2, "warm_reset_request_hex": "a7270000000000000000000000000000000000009859",
                   **{name: {"words_hex": ["0" * 16]} for name in rehearsal.BRINGUP_CASES}}
        receipts = {"g4_wire": self.file("build/wire/report.json", json.dumps(wire)),
                    "bringup_fixture": self.file("build/fixture.json", json.dumps(fixture)),
                    "bringup_dry_run": self.file("build/dry-run.json", json.dumps({"model_sha256": "a" * 64}))}
        with self.assertRaisesRegex(ValueError, "simulator differs"):
            rehearsal.bringup_checks(self.root, receipts, {"g4_wire": {"status": "passed"}})


if __name__ == "__main__":
    unittest.main()
