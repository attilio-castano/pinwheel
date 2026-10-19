"""Native layout evidence refuses mismatched GDS/reference and live cleanup."""
import json
from pathlib import Path
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import Mock,patch

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
import streaming_tt_native_layout as L


class NativeLayoutTests(unittest.TestCase):
    def fixture(self,root):
        root=root.resolve();flow=root/'flow';flow.mkdir();inputs=root/'inputs';inputs.mkdir()
        config=flow/'resolved.json';config.write_text(json.dumps({'DESIGN_NAME':'tt_um_pinwheel_streaming_ready_d2'}))
        gds=flow/'actual.gds';gds.write_bytes(b'actual routed gds')
        odb=flow/'actual.odb';odb.write_bytes(b'actual routed odb')
        state=flow/'state_out.json';state.write_text(json.dumps({'gds':'/work/run/actual.gds'}))
        report=root/'report.json';report.write_text('{}')
        exported=root/'export';exported.mkdir();cdl=exported/'implemented.cdl';cdl.write_text('actual powered reference')
        receipt=exported/'report.json';packet=dict(schema='pinwheel.streaming-tt-signoff-export.v1',completed=True,
            exit_code=0,inputs_unchanged=True,inherited_netlist=False,top='tt_um_pinwheel_streaming_ready_d2',
            actual_database_sha256=L.sha(odb),input_sha256_before={'/work/run/resolved.json':L.sha(config)},
            artifacts_sha256={'implemented.cdl':L.sha(cdl)})
        L.write(receipt,packet)
        producer={'artifact_sha256':{'flow/actual.gds':L.sha(gds)}}
        host=SimpleNamespace(checkpoint=lambda *_:(producer,{'/work/run':flow},'actual.odb',odb),
            constraints=lambda *_:{},read_checkpoint=lambda path,**_:L.read(path))
        return report,state,receipt,host,packet,gds,cdl

    def test_actual_gds_and_powered_reference_bind_to_one_closed_odb(self):
        with tempfile.TemporaryDirectory() as tmp:
            report,state,export,host,_,gds,cdl=self.fixture(Path(tmp))
            with patch.object(L,'timing_host',return_value=host):
                _,_,top,actual,reference,frozen=L.actual_inputs(report,state,export)
            self.assertEqual(actual,gds);self.assertEqual(reference,cdl)
            self.assertEqual(top,'tt_um_pinwheel_streaming_ready_d2')
            self.assertIn(str(gds),frozen);self.assertIn(str(cdl),frozen)

    def test_changed_gds_and_stale_or_inherited_cdl_refuse(self):
        with tempfile.TemporaryDirectory() as tmp:
            report,state,export,host,packet,gds,cdl=self.fixture(Path(tmp))
            with patch.object(L,'timing_host',return_value=host):
                before=gds.read_bytes();gds.write_bytes(before+b'changed')
                with self.assertRaisesRegex(ValueError,'GDS differs'):L.actual_inputs(report,state,export)
                gds.write_bytes(before)
                for field,value in [('actual_database_sha256','0'*64),('inherited_netlist',True)]:
                    L.write(export,dict(packet,**{field:value}))
                    with self.subTest(field=field),self.assertRaisesRegex(ValueError,'actual checkpoint ODB'):
                        L.actual_inputs(report,state,export)
                L.write(export,packet);cdl.write_text('collapsed rail reference')
                with self.assertRaisesRegex(ValueError,'CDL changed'):L.actual_inputs(report,state,export)

    def test_native_exit_zero_with_unconfirmed_cleanup_is_not_success(self):
        with tempfile.TemporaryDirectory() as tmp:
            out=Path(tmp);process=Mock();process.wait.return_value=0;process.poll.return_value=0
            with patch.object(L.subprocess,'Popen',return_value=process),\
                    patch.object(L,'cleanup',side_effect=ValueError('Owned layout container remains')):
                with self.assertRaisesRegex(ValueError,'cleanup unconfirmed'):
                    L.run_command(['native'],'owner',1,out,'fault')
            journal=L.read(out/'fault-journal.json')
            self.assertEqual(journal['exit_code'],0);self.assertEqual(journal['status'],'cleanup_unconfirmed')


if __name__=='__main__':unittest.main()
