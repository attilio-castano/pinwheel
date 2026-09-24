"""Reject cross-run, cross-pass, changed, and incomplete routing evidence."""
import hashlib
import importlib.util
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

SCRIPTS = Path(__file__).resolve().parents[1] / "scripts"
sys.path.insert(0, str(SCRIPTS))
spec = importlib.util.spec_from_file_location("check_routing", SCRIPTS / "check-routing.py")
gate = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gate)


class SelectionTests(unittest.TestCase):
    def setUp(self):
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.root = Path(tmp.name)
        self.design = self.root / "build/physical/design"
        self.step = self.design / "runs/example/05-openroad-detailedrouting"
        self.route = self.step / "drt-run-0"
        self.route.mkdir(parents=True)
        self.db = self.route / "drt_iter1.odb"
        self.db.write_bytes(b"a frozen database identity")
        self.report = self.route / "tt_um_pinwheel.drc-1.rpt"
        self.report.write_text("violation type: Short\n srcs: net:data\n bbox = (1, 1) - (2, 2) on Layer Metal4\n")
        self.invocation = self.root / "build/physical/example-invocation.json"
        self.invocation.write_text(json.dumps(dict(exit_code=124, stop_reason="wall_time_limit", container_termination=dict(status="stopped"))))
        self.context = self.root / "context.json"
        self.ctx = dict(schema=2, database="/work/core/runs/example/05-openroad-detailedrouting/drt-run-0/drt_iter1.odb",
                        database_sha256=gate.sha(self.db), drc_report_sha256=gate.sha(self.report), dbu_per_micron=1,
                        instances={}, nets={"data": dict(type="SIGNAL")}, macro_pins=[], power_shapes=[], signal_segments=[], route_coverage={})
        self.context.write_text(json.dumps(self.ctx))
        (self.step / "openroad-detailedrouting.log").write_text("Start detail routing.\nStart 1st optimization iteration.\nNumber of violations = 1\n")
        self.selection = dict(context="context.json", report=str(self.report.relative_to(self.root)), **{"pass": 0, "iteration": 1})
        self.patcher = patch.object(gate, "ROOT", self.root)
        self.patcher.start()
        self.addCleanup(self.patcher.stop)

    def check(self):
        return gate.check_selection(self.design, self.invocation, self.selection, {})

    def test_matching_selection_is_accepted(self):
        self.assertEqual(self.check()[0]["retained"]["markers"], 1)

    def test_changed_database_is_rejected(self):
        self.db.write_bytes(b"changed")
        with self.assertRaisesRegex(ValueError, "hash changed"):
            self.check()

    def test_same_iteration_from_other_pass_is_rejected(self):
        other = self.step / "drt-run-1/drt_iter1.odb"
        other.parent.mkdir()
        other.write_bytes(self.db.read_bytes())
        self.ctx["database"] = "/work/core/runs/example/05-openroad-detailedrouting/drt-run-1/drt_iter1.odb"
        self.context.write_text(json.dumps(self.ctx))
        with self.assertRaisesRegex(ValueError, "different routing pass"):
            self.check()

    def test_unconfirmed_timeout_and_incomplete_iteration_are_rejected(self):
        self.invocation.write_text(json.dumps(dict(exit_code=124, stop_reason="wall_time_limit", container_termination=dict(status="unconfirmed"))))
        with self.assertRaisesRegex(ValueError, "unconfirmed"):
            self.check()
        self.invocation.write_text(json.dumps(dict(exit_code=0)))
        (self.step / "openroad-detailedrouting.log").write_text("Start detail routing.\nStart 1st optimization iteration.\n")
        with self.assertRaisesRegex(ValueError, "completed logged"):
            self.check()

    def test_conflicting_outer_log_is_rejected(self):
        self.invocation.with_name("example.log").write_text("Start detail routing.\nStart 1st optimization iteration.\nNumber of violations = 2\n")
        with self.assertRaisesRegex(ValueError, "disagree"):
            self.check()

    def test_fresh_check_requires_intact_settled_receipt_and_report(self):
        fresh, script, receipt, raw = (self.root / name for name in ["fresh.rpt", "fresh.tcl", "fresh.json", "raw.json"])
        fresh.write_text(self.report.read_text())
        script.write_text("drt::check_drc -output_file fresh.rpt\n")
        raw.write_text('{"exit_code":0}\n')
        config = self.step / "config.json"
        config.write_text(json.dumps(dict(RT_MIN_LAYER="Metal2", RT_MAX_LAYER="Metal4", RT_CLOCK_MIN_LAYER=None)))
        evidence = dict(exit_code=0, settled=True, source_unchanged=True, seconds=1,
                        source_database_sha256=gate.sha(self.db), report_sha256=gate.sha(fresh),
                        script_sha256=gate.sha(script), raw_receipt_sha256=gate.sha(raw),
                        config_sha256=gate.sha(config), signal_layers="Metal2-Metal4", clock_layers="Metal2-Metal4")
        receipt.write_text(json.dumps(evidence))
        self.selection['fresh_drc'] = dict(receipt="fresh.json", report="fresh.rpt", script="fresh.tcl", raw_receipt="raw.json")
        self.ctx['wire_selection_reports_sha256'] = {"fresh.rpt": gate.sha(fresh)}
        self.context.write_text(json.dumps(self.ctx))
        self.assertEqual(self.check()[0]['fresh_drc']['markers'], 1)
        receipt.write_text(json.dumps(dict(evidence, settled=False)))
        with self.assertRaisesRegex(ValueError, "termination is unconfirmed"):
            self.check()
        receipt.write_text(json.dumps(dict(evidence, signal_layers="Metal1-Metal4")))
        with self.assertRaisesRegex(ValueError, "resolved routing limits"):
            self.check()
        receipt.write_text(json.dumps(evidence))
        raw.write_text('{"exit_code":124}\n')
        with self.assertRaisesRegex(ValueError, "Original fresh DRC receipt changed"):
            self.check()
        raw.write_text('{"exit_code":0}\n')
        fresh.write_text("")
        with self.assertRaisesRegex(ValueError, "script/report changed"):
            self.check()

    def test_existing_diagnosis_cli_binds_pass_and_completes_output(self):
        import contextlib
        import io
        spec = importlib.util.spec_from_file_location("diagnosis_cli", SCRIPTS / "diagnose-routing.py")
        diagnosis = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(diagnosis)
        self.ctx.update(die=[0, 0, 10, 10], ports=[])
        self.context.write_text(json.dumps(self.ctx))
        argv = ["diagnose-routing.py", "--design", str(self.design), "--invocation", str(self.invocation),
                "--report", str(self.report), "--context", str(self.context), "--output", str(self.root / "output")]
        with patch.object(sys, "argv", argv), contextlib.redirect_stdout(io.StringIO()):
            diagnosis.main()
        self.assertTrue((self.root / "output/index.html").is_file())
        other = self.step / "drt-run-1/drt_iter1.odb"
        other.parent.mkdir()
        other.write_bytes(self.db.read_bytes())
        self.ctx['database'] = "/work/core/runs/example/05-openroad-detailedrouting/drt-run-1/drt_iter1.odb"
        self.context.write_text(json.dumps(self.ctx))
        with patch.object(sys, "argv", argv), self.assertRaisesRegex(RuntimeError, "different routing pass"):
            diagnosis.main()


if __name__ == "__main__":
    unittest.main()
