"""Authenticate fixed-target export seams without CAD or source relocation."""
import copy
import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'scripts'))
import streaming_8x4_export as E


class FixedTarget(unittest.TestCase):
    def fixture(self,root):
        prepared=root/'prepared';prepared.mkdir();(prepared/'preparation.json').write_text('{}')
        run=root/'probe';flow=run/'flow';stage=flow/'21-odb-applydeftemplate';stage.mkdir(parents=True)
        odb=stage/'design.odb';odb.write_bytes(b'exact-odb-bytes')
        state=stage/'state_out.json';E.P.write(state,dict(odb='/work/run/21-odb-applydeftemplate/design.odb',metrics={}))
        resolved=flow/'resolved.json';resolved.write_text('{}')
        row=dict(step_directory=stage.name,state=str(state),state_sha256=E.sha(state),
            views=dict(odb=dict(path=str(odb),sha256=E.sha(odb),container='/work/run/21-odb-applydeftemplate/design.odb')))
        report=dict(schema='pinwheel.streaming-8x4-native-run.v1',mode='probe',status='flow_completed',exit_code=0,
            inputs_pdk_runtime_unchanged=True,container_termination=dict(status='absent'),
            prepared=str(prepared),prepared_input_sha256=E.sha(prepared/'preparation.json'),states=[row],
            artifact_sha256={str(path.relative_to(run)):E.sha(path) for path in (odb,state,resolved)})
        path=run/'report.json';E.P.write(path,report)
        return prepared,path,report,odb

    def test_actual_state_selects_exact_sealed_odb(self):
        with tempfile.TemporaryDirectory() as temp:
            prepared,path,report,odb=self.fixture(Path(temp))
            actual,flow,selected,resolved=E.source_target(path,prepared)
            self.assertEqual(actual,report);self.assertEqual(selected,odb)
            self.assertEqual(resolved,flow/'resolved.json')

    def test_tampered_or_unclosed_parent_rejects(self):
        with tempfile.TemporaryDirectory() as temp:
            prepared,path,report,odb=self.fixture(Path(temp))
            for key,value in [('mode','full'),('status','timed_out'),('exit_code',124),
                              ('inputs_pdk_runtime_unchanged',False),('container_termination',dict(status='unconfirmed'))]:
                broken=copy.deepcopy(report);broken[key]=value;E.P.write(path,broken)
                with self.subTest(key=key),self.assertRaises(ValueError):E.source_target(path,prepared)
            E.P.write(path,report);odb.write_bytes(b'tampered')
            with self.assertRaises(ValueError):E.source_target(path,prepared)

    def test_state_cannot_select_another_odb_or_duplicate_target(self):
        with tempfile.TemporaryDirectory() as temp:
            prepared,path,report,odb=self.fixture(Path(temp))
            broken=copy.deepcopy(report);broken['states'][0]['views']['odb']['container']='/work/run/other.odb'
            E.P.write(path,broken)
            with self.assertRaises(ValueError):E.source_target(path,prepared)
            broken=copy.deepcopy(report);broken['states'].append(broken['states'][0]);E.P.write(path,broken)
            with self.assertRaises(ValueError):E.source_target(path,prepared)


if __name__=='__main__':unittest.main()
