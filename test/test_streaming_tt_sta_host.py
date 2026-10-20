"""Fresh diagnostic timing must consume the producer's actual sealed ODB."""
import importlib.util
import json
from pathlib import Path
import sys
import tempfile
import unittest

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
spec=importlib.util.spec_from_file_location('sta_host',ROOT/'scripts/run-streaming-tt-sta.py')
host=importlib.util.module_from_spec(spec);spec.loader.exec_module(host)


class FreshSTAHostTests(unittest.TestCase):
    def fixture(self,root):
        flow=root/'flow';step=flow/'20-openroad-globalplacement';step.mkdir(parents=True)
        odb=step/'actual.odb';odb.write_bytes(b'actual-database')
        state=step/'state_out.json';state.write_text(json.dumps(dict(
            odb='/work/run/20-openroad-globalplacement/actual.odb',metrics={'stale_setup':999})))
        report=root/'report.json';data=dict(schema='pinwheel.streaming-tt-physical-run.v2',
            inputs_unchanged_after_run=True,container_termination={'status':'absent'},
            path_map={'/work/run':str(flow),'/work/inputs':str(root/'inputs'),'/work/pdk':str(root/'pdk')},
            states=[dict(state=str(state),state_sha256=host.sha(state),views={'odb':{'sha256':host.sha(odb)}})])
        report.write_text(json.dumps(data));return report,state,odb,data

    def test_exact_checkpoint_accepts_with_inherited_metrics_left_unused(self):
        with tempfile.TemporaryDirectory() as tmp:
            report,state,odb,_=self.fixture(Path(tmp))
            _,_,native,actual=host.checkpoint(report,state)
            self.assertEqual(actual,odb.resolve());self.assertEqual(native,'/work/run/20-openroad-globalplacement/actual.odb')

    def test_changed_actual_database_rejects_even_when_state_json_is_unchanged(self):
        with tempfile.TemporaryDirectory() as tmp:
            report,state,odb,_=self.fixture(Path(tmp));odb.write_bytes(b'other-database')
            with self.assertRaisesRegex(ValueError,'ODB changed'):host.checkpoint(report,state)

    def test_changed_or_unrecorded_state_refuses(self):
        with tempfile.TemporaryDirectory() as tmp:
            report,state,_,data=self.fixture(Path(tmp));state.write_text(state.read_text()+'\n')
            with self.assertRaisesRegex(ValueError,'Changed/unrecorded'):host.checkpoint(report,state)
            data['states']=[];report.write_text(json.dumps(data))
            with self.assertRaisesRegex(ValueError,'Changed/unrecorded'):host.checkpoint(report,state)

    def test_unconfirmed_cleanup_or_inputs_refuse(self):
        with tempfile.TemporaryDirectory() as tmp:
            report,state,_,original=self.fixture(Path(tmp))
            for key,value in [('inputs_unchanged_after_run',False),('container_termination',{'status':'unconfirmed'})]:
                data=dict(original);data[key]=value;report.write_text(json.dumps(data))
                with self.subTest(key=key),self.assertRaisesRegex(ValueError,'Unclosed'):host.checkpoint(report,state)

    def test_native_unavailable_inherited_metrics_discarded_but_identity_nonfinite_refuses(self):
        with tempfile.TemporaryDirectory() as tmp:
            path=Path(tmp)/'state.json';path.write_text('{"odb":"actual.odb","metrics":{"unused":Infinity}}')
            self.assertEqual(host.read_checkpoint(path,producer=False),{'odb':'actual.odb'})
            path.write_text('{"odb":Infinity,"metrics":{}}')
            with self.assertRaisesRegex(ValueError,'Nonfinite checkpoint identity'):host.read_checkpoint(path,producer=False)
            path.write_text('{"odb":"actual.odb","odb":"forged.odb"}')
            with self.assertRaisesRegex(ValueError,'Duplicate checkpoint JSON key'):host.read_checkpoint(path,producer=False)

    def closed_constraints(self,root):
        report,state,odb,data=self.fixture(root)
        inputs=root/'inputs';inputs.mkdir();sdc=inputs/'core.sdc';sdc.write_text('create_clock -period 20')
        config=root/'flow/resolved.json';config.write_text('{"CLOCK_PERIOD":20}')
        metadata=root/'inputs.json';metadata.write_text(json.dumps({'input_sha256':{'core.sdc':host.sha(sdc)}}))
        data.update(design=str(root),prepared_input_sha256=host.sha(metadata),
            artifact_sha256={'flow/resolved.json':host.sha(config)})
        report.write_text(json.dumps(data));_,roots,_,_=host.checkpoint(report,state)
        return report,state,odb,data,roots,metadata,config,sdc

    def test_fresh_constraint_freeze_cannot_legitimize_changed_sdc_or_config(self):
        with tempfile.TemporaryDirectory() as tmp:
            report,_,_,data,roots,metadata,config,sdc=self.closed_constraints(Path(tmp))
            self.assertEqual(len(host.constraints(report,data,roots)),3)
            for path,message in [(sdc,'SDC differs'),(config,'configuration differs'),(metadata,'receipt changed')]:
                original=path.read_bytes();path.write_bytes(original+b'\n')
                with self.subTest(path=path.name),self.assertRaisesRegex(ValueError,message):
                    host.constraints(report,data,roots)
                path.write_bytes(original)

    def test_extracted_requires_actual_odb_export_and_closed_checkpoint_spef(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp)
            report,state,odb,data,roots,_,config,_=self.closed_constraints(root)
            data.update(schema='pinwheel.streaming-tt-final-run.v1',status='flow_completed',exit_code=0)
            spef=root/'flow/final.spef';spef.write_text('*SPEF "IEEE 1481-1998"')
            value=json.loads(state.read_text());value['spef']={'nom_*':'/work/run/final.spef'}
            state.write_text(json.dumps(value));data['artifact_sha256']['flow/final.spef']=host.sha(spef)
            exported=root/'export';exported.mkdir();netlist=exported/'implemented.v';netlist.write_text('actual odb netlist')
            receipt=exported/'report.json';packet=dict(schema='pinwheel.streaming-tt-signoff-export.v1',completed=True,
                exit_code=0,inputs_unchanged=True,inherited_netlist=False,actual_database_sha256=host.sha(odb),
                input_sha256_before={'/work/run/resolved.json':host.sha(config)},
                artifacts_sha256={'implemented.v':host.sha(netlist)})
            receipt.write_text(json.dumps(packet))
            views,_,mount=host.extracted_views(report,state,data,roots,'actual.odb',odb,receipt)
            self.assertEqual(views['nl'],'/work/export/implemented.v');self.assertEqual(mount,exported.resolve())
            data.update(status='failed',exit_code=2)
            self.assertEqual(host.extracted_views(report,state,data,roots,'actual.odb',odb,receipt)[0],views)
            for status,code in [('running',0),('failed',0),('flow_completed',2),('invalidated',2),('timed_out',124)]:
                data.update(status=status,exit_code=code)
                with self.subTest(status=status,code=code),self.assertRaisesRegex(ValueError,'closed final producer'):
                    host.extracted_views(report,state,data,roots,'actual.odb',odb,receipt)
            data.update(status='failed',exit_code=2)
            for field,value in [('actual_database_sha256','0'*64),('inherited_netlist',True)]:
                changed=dict(packet);changed[field]=value;receipt.write_text(json.dumps(changed))
                with self.subTest(field=field),self.assertRaisesRegex(ValueError,'actual final ODB'):
                    host.extracted_views(report,state,data,roots,'actual.odb',odb,receipt)
            receipt.write_text(json.dumps(packet));spef.write_text('different extraction')
            with self.assertRaisesRegex(ValueError,'SPEF differs'):
                host.extracted_views(report,state,data,roots,'actual.odb',odb,receipt)


if __name__=='__main__':unittest.main()
