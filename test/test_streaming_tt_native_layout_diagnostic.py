#!/usr/bin/env python3
from pathlib import Path
import sys
from types import SimpleNamespace
import tempfile
import unittest

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'scripts'))
import streaming_tt_native_layout_diagnostic as L


class DiagnosticLayoutTests(unittest.TestCase):
    def test_provider_restored_on_success_and_failure(self):
        original=lambda:'original';replacement=lambda:'adapted';module=SimpleNamespace(actual_inputs=original)
        with L.input_provider(module,replacement):self.assertEqual(module.actual_inputs(),'adapted')
        self.assertIs(module.actual_inputs,original)
        with self.assertRaisesRegex(RuntimeError,'native failure'):
            with L.input_provider(module,replacement):
                self.assertIs(module.actual_inputs,replacement);raise RuntimeError('native failure')
        self.assertIs(module.actual_inputs,original)

    def test_original_module_is_pinned_and_adapter_closure_complete(self):
        self.assertEqual(L.sha(L.P.ROOT/'scripts/streaming_tt_native_layout.py'),L.LAYOUT_SHA256)
        closure=L.dependency_closure(L.P.ROOT,L.ENTRIES)
        for name in ('streaming_tt_native_layout.py','streaming_tt_gds_diagnostic.py','streaming_tt_layout.py'):
            self.assertIn('scripts/'+name,closure['files'])

    def test_measurement_failure_remains_false_and_incomplete_cleanup_is_refused(self):
        with tempfile.TemporaryDirectory() as temporary:
            root=Path(temporary).resolve();data=root/'native.xml';data.write_text('actual measurement')
            expected={'/input/actual.gds':'selected'}
            packet=dict(schema='pinwheel.streaming-tt-native-layout-host.v1',status='completed',measurements_completed=True,
                passed=False,qualified=False,physical_acceptance_claim=False,inputs_unchanged=True,input_sha256=expected,
                commands=[dict(status='completed',exit_code=0,owned_container_absent=True) for _ in range(4)],
                artifacts_sha256={'native.xml':L.sha(data)})
            path=root/'report.json';L.write(path,packet);self.assertFalse(L.validate_measurement(path,expected)['passed'])
            for changed in (dict(packet,commands=packet['commands'][:3]),dict(packet,inputs_unchanged=False),
                    dict(packet,input_sha256={'/input/actual.gds':'different'}),
                    dict(packet,commands=[dict(status='completed',exit_code=False,owned_container_absent=True)]*4)):
                L.write(path,changed)
                with self.assertRaises(ValueError):L.validate_measurement(path,expected)
            L.write(path,packet);data.write_text('changed')
            with self.assertRaises(ValueError):L.validate_measurement(path,expected)


if __name__=='__main__':unittest.main()
