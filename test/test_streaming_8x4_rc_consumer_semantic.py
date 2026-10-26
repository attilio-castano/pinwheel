"""HOST-only new-intake and unchanged six-call body/strict numeric controls."""
import inspect
import json
from pathlib import Path
import shutil
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
import streaming_8x4_rc_consumer_semantic as W
import streaming_8x4_rc_consumer_semantic_readback as R

B = ROOT / 'build/campaigns/8x4-20261022-01'
INPUTS = B / 'rc-consumer-ndr-preparation-01/consumer-inputs'
ACTUAL = B / 'rc-native-outputs/rc-consumer-ndr-01/native/MIN-retained_rules'


class SemanticConsumerControls(unittest.TestCase):
    def test_worker_preserves_original_body_except_new_authority_and_physical_gate(self):
        body = inspect.getsource(W.run_native).replace('def run_native(', 'def run(')
        body = body.replace('verify_consumer(base, plan_hash)', 'verify_plan(base, plan_hash)')
        body = body.replace('pinwheel.streaming-8x4-rc-consumer-route-native-execution.v1', 'pinwheel.streaming-8x4-rc-consumer-execution.v1')
        body = body.replace("                geometry = geometry_gate(base, directory)\n                write(directory / 'semantic-geometry.json', geometry)",
            "                need((directory / 'before.def').read_bytes() == (directory / 'after.def').read_bytes(),\n                     'Extraction changed geometry DEF readback')")
        body = body.replace("'geometry_unchanged': True, 'semantic_geometry_sha256': P.sha(directory / 'semantic-geometry.json'),\n                             'copied_inputs_unchanged': True,", "'geometry_unchanged': True, 'copied_inputs_unchanged': True,")
        self.assertEqual(body, inspect.getsource(W.C.run))

    def test_reader_preserves_original_raw_math_and_components(self):
        body = inspect.getsource(R.native_readback).replace('def native_readback(', 'def readback(')
        body = body.replace('W.verify_consumer(inputs, plan_hash)', 'C.verify_plan(inputs, plan_hash)')
        body = body.replace('pinwheel.streaming-8x4-rc-consumer-route-native-execution.v1', 'pinwheel.streaming-8x4-rc-consumer-execution.v1')
        body = body.replace('pinwheel.streaming-8x4-rc-consumer-route-native-independent-readback.v1', 'pinwheel.streaming-8x4-rc-consumer-independent-readback.v1')
        body = body.replace('        physical(inputs, owner, job)',
            "        C.need(regular(owner / 'before.def').read_bytes() == regular(owner / 'after.def').read_bytes(),\n               'Consumer extraction changed geometry readback')")
        self.assertEqual(body, inspect.getsource(R.OLD.readback))
        self.assertIs(R.component_summary, R.OLD.component_summary)
        self.assertIs(W.parse_spef, W.C.parse_spef); self.assertIs(W.analyze_values, W.C.analyze_values)

    def test_actual_first_SPEF_remains_original_strict_numeric_failure(self):
        plan = json.loads((INPUTS / 'plan.json').read_text())
        values = W.parse_spef((ACTUAL / 'result.spef').read_text(), {r['name'] for r in plan['fixture_rows']})
        result = W.analyze_values(plan, 'MIN', 'retained_rules', values)
        self.assertFalse(result['passed']); self.assertTrue(any(not r['passed'] for r in result['wires']))
        self.assertTrue(all(r['passed'] for r in result['vias']))
        self.assertEqual(len(result['wires']), 12); self.assertEqual(len(result['vias']), 5)

    def test_initial_native_import_is_exact_even_when_pair_headers_match(self):
        plan = json.loads((INPUTS / 'plan.json').read_text())
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary); base = root / 'consumer-inputs'; base.mkdir(); owner = root / 'native'; owner.mkdir()
            for name in ('tech.lef', 'plan.json'): shutil.copyfile(INPUTS / name, base / name)
            baseline = root / 'baseline-ndr-preparation'; baseline.mkdir()
            shutil.copyfile(INPUTS.parent / 'NDR-witness.json', baseline / 'NDR-witness.json')
            for name in ('before.def', 'after.def'): shutil.copyfile(ACTUAL / name, owner / name)
            with patch.object(W, 'verify_consumer', return_value=plan):
                self.assertTrue(W.geometry_gate(base, owner)['passed'])
                for name in ('before.def', 'after.def'):
                    p = owner / name; p.write_text(p.read_text().replace('DESIGN rc_consumer', 'DESIGN foreign'))
                with self.assertRaisesRegex(ValueError, 'initial Native DEF'): W.geometry_gate(base, owner)

    def test_physical_receipt_and_exact_artifact_membership_are_reopened(self):
        with tempfile.TemporaryDirectory() as temporary:
            owner = Path(temporary); wanted = dict(passed=True, all17_routes_checked=True)
            for name in ('tech.lef', 'widths.lef', 'fixture.def', 'run.tcl', 'rules.txt', 'native.log', 'before.def', 'after.def', 'result.spef'):
                (owner / name).write_text('fixture')
            W.write(owner / 'semantic-geometry.json', wanted)
            job = dict(semantic_geometry_sha256=W.P.sha(owner / 'semantic-geometry.json'))
            with patch.object(W, 'geometry_gate', return_value=wanted):
                self.assertEqual(R.physical(owner, owner, job), wanted)
                (owner / 'foreign.report').write_text('foreign')
                with self.assertRaisesRegex(ValueError, 'membership'): R.physical(owner, owner, job)
                (owner / 'foreign.report').unlink(); (owner / 'semantic-geometry.json').write_text('{}')
                with self.assertRaisesRegex(ValueError, 'receipt'): R.physical(owner, owner, job)

    def test_failed_prefix_cannot_enter_complete_raw_reader(self):
        with tempfile.TemporaryDirectory() as temporary:
            owner = Path(temporary)
            W.write(owner / 'report.json', dict(schema='pinwheel.streaming-8x4-rc-consumer-route-execution.v1',
                plan_sha256='seal', qualified=False, model_qualified=False, passed=False, all_six_native_calls_closed=False))
            with patch.object(W, 'verify', return_value={}), patch.object(R, 'native_readback', side_effect=AssertionError('prefix')):
                with self.assertRaises(ValueError): R.readback(owner, 'seal', owner)


if __name__ == '__main__': unittest.main()
