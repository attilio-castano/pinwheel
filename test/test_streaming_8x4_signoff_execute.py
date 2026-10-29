"""Focused reject-before-execution controls for final8x4 coordinators."""
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'scripts'))
import streaming_8x4_signoff_execute as E


class SignoffExecution(unittest.TestCase):
    def test_probe_or_incomplete_views_cannot_be_signoff_input(self):
        with tempfile.TemporaryDirectory() as temporary:
            root=Path(temporary).resolve();report=root/'report.json'
            for value in [dict(schema='pinwheel.streaming-8x4-fixed-export-run.v1',status='export_completed'),
                          dict(schema='pinwheel.streaming-8x4-final-views-run.v1',completed=False),
                          dict(schema='pinwheel.streaming-8x4-final-views-run.v1',completed=True,
                               inputs_pdk_runtime_unchanged=True,physical_acceptance=False,
                               execution=dict(container_termination=dict(status='unconfirmed')))]:
                report.write_text(json.dumps(value))
                with patch.object(E.P,'verify',side_effect=AssertionError('must reject before deeper input use')):
                    with self.assertRaises(ValueError):E.closed_views(report)

    def test_changed_native_target_rejects_before_any_native_tool(self):
        request=dict(schema='pinwheel.streaming-8x4-final-views-native-request.v1',
            source_odb='/input/actual.odb',source_odb_sha256='a'*64)
        with patch.object(E.P,'read',return_value=request),patch.object(E,'sha',return_value='b'*64),\
             patch.object(E.subprocess,'run',side_effect=AssertionError('must not launch')):
            with self.assertRaises(ValueError):E.native_views('/input/request.json')

    def test_layout_decks_and_readers_fit_whole_budget(self):
        for total in (360,600,900,1800):
            each=E.layout_budget(total)
            self.assertGreater(each,0);self.assertLessEqual(each,900)
            self.assertLessEqual(2*each+2*120+60,total)
        for total in (0,359,1801,900.0,True):
            with self.assertRaises(ValueError):E.layout_budget(total)

    def test_owned_native_rejects_unbounded_allowance_before_launch(self):
        with patch.object(E.subprocess,'Popen',side_effect=AssertionError('must not launch')):
            for timeout in (0,3601):
                with self.assertRaises(ValueError):E.owned_native([],Path('/does-not-exist'),'owner',timeout)

    def test_staged_worker_bytes_and_membership_must_remain_exact(self):
        with tempfile.TemporaryDirectory() as temporary:
            root=Path(temporary).resolve();inputs=root/'inputs';source=root/'scripts/worker.py'
            source.parent.mkdir();source.write_text('pass\n')
            worker=inputs/'producer/scripts/worker.py';worker.parent.mkdir(parents=True);worker.write_bytes(source.read_bytes())
            sources={'scripts/worker.py':E.sha(source)};inventory=E.P.inventory(inputs)
            with patch.object(E.P,'ROOT',root):
                E.unchanged_producer(inputs,sources,inventory)
                (inputs/'extra').write_text('unexpected')
                with self.assertRaises(ValueError):E.unchanged_producer(inputs,sources,inventory)
                (inputs/'extra').unlink();source.write_text('changed\n')
                with self.assertRaises(ValueError):E.unchanged_producer(inputs,sources,inventory)


if __name__=='__main__':unittest.main()
