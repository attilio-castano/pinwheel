"""Closed physical/readback, actual FF and native-process handoff refusals."""
from copy import deepcopy
import importlib.util
import json
from pathlib import Path
import sys
import tempfile
from types import SimpleNamespace
import unittest

ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('wire_host',ROOT/'scripts/run-streaming-tt-wire.py')
host=importlib.util.module_from_spec(spec);spec.loader.exec_module(host)


class ActualReadbackTests(unittest.TestCase):
    def fixture(self,root):
        root=root.resolve();report=root/'physical.json';report.write_text('{}')
        state=root/'state_out.json';state.write_text('{}')
        database=root/'actual.odb';database.write_bytes(b'actual database')
        reference=root/'reference.json';reference.write_text('{}')
        export=root/'export-run';directory=export/'native/export';directory.mkdir(parents=True)
        for name in ('connectivity.json','inventory.json'):(directory/name).write_text('{}')
        packet=dict(schema='pinwheel.streaming-tt-odb-export.v1',read_only_database=True,
            top='tt_um_pinwheel_streaming_ready_d2',database_sha256=host.digest(database),
            reference_sha256=host.digest(reference),source_sha256='a'*64,
            artifacts_sha256={name:host.digest(directory/name) for name in ('connectivity.json','inventory.json')})
        host.write(directory/'receipt.json',packet)
        receipt=export/'report.json';outer=dict(schema='pinwheel.streaming-tt-odb-export-run.v1',passed=True,
            status='exported',exit_code=0,native_export_binding=True,inputs_unchanged=True,
            staged_inputs_unchanged=True,runtime_unchanged=True,container_termination={'status':'absent'},
            physical_report=str(report),actual_odb=str(database),actual_odb_sha256=host.digest(database),
            reference=str(reference),input_sha256={str(path):host.digest(path) for path in (report,state)},
            artifact_sha256={str(path.relative_to(export)):host.digest(path) for path in directory.iterdir()})
        host.write(receipt,outer)
        checkpoint=SimpleNamespace(checkpoint=lambda *_:({}, {}, 'actual.odb',database),constraints=lambda *_:{})
        return receipt,report,state,checkpoint,outer,database,directory

    def check(self,receipt,report,state,checkpoint):
        return host.actual_export(receipt,physical_report=report,state=state,checkpoint_host=checkpoint,exporter_sha256='a'*64)

    def test_exact_closed_database_readback_accepts(self):
        with tempfile.TemporaryDirectory() as tmp:
            receipt,report,state,checkpoint,_,database,directory=self.fixture(Path(tmp))
            _,_,actual,_,native,frozen=self.check(receipt,report,state,checkpoint)
            self.assertEqual(actual,database);self.assertEqual(native,directory)
            self.assertIn(str(report),frozen);self.assertIn(str(directory/'receipt.json'),frozen)

    def test_unclosed_or_different_checkpoint_refuses(self):
        with tempfile.TemporaryDirectory() as tmp:
            receipt,report,state,checkpoint,outer,_,_=self.fixture(Path(tmp))
            for field,value in [('passed',False),('inputs_unchanged',False),('runtime_unchanged',False),
                    ('container_termination',{'status':'unconfirmed'}),('actual_odb_sha256','0'*64)]:
                host.write(receipt,dict(outer,**{field:value}))
                with self.subTest(field=field),self.assertRaises(ValueError):self.check(receipt,report,state,checkpoint)
            host.write(receipt,outer);state.write_text('{"other":true}')
            with self.assertRaisesRegex(ValueError,'exact physical checkpoint'):self.check(receipt,report,state,checkpoint)

    def test_actual_connectivity_membership_or_bytes_cannot_change(self):
        with tempfile.TemporaryDirectory() as tmp:
            receipt,report,state,checkpoint,_,_,directory=self.fixture(Path(tmp))
            original=(directory/'connectivity.json').read_bytes();(directory/'connectivity.json').write_bytes(b'other')
            with self.assertRaisesRegex(ValueError,'membership or bytes'):self.check(receipt,report,state,checkpoint)
            (directory/'connectivity.json').write_bytes(original);(directory/'extra.json').write_text('{}')
            with self.assertRaisesRegex(ValueError,'membership or bytes'):self.check(receipt,report,state,checkpoint)


class StateBindingTests(unittest.TestCase):
    def fixture(self,root):
        root=root.resolve();candidate=root/'candidate.json';candidate.write_text('{}')
        database=root/'actual.odb';database.write_bytes(b'actual full FF database')
        cells={};rows=[]
        for index in range(6039):
            name='ff'+str(index);pins=dict(Q=[index*4+2],D=[index*4+3],CLK=[index*4+4],RESET_B=[index*4+5])
            cells[name]=dict(type='sg13cmos5l_dfrbpq_1',connections=pins)
            semantic='core-d2:r_stage'+str(index+1)+':0' if index<2 else 'core-d2:r_state:'+str(index)
            rows.append(dict(semantic=semantic,actual_ff=json.dumps([name],separators=(',',':')),
                actual_cell='sg13cmos5l_dfrbpq_1',actual_q=pins['Q'][0],actual_d=pins['D'][0],
                actual_clock=pins['CLK'][0],actual_reset_b=pins['RESET_B'][0]))
        top='tt_um_pinwheel_streaming_ready_d2';connectivity=root/'connectivity.json'
        host.write(connectivity,{'modules':{top:{'cells':cells}}})
        mapping=dict(rows=rows,database_sha256=host.digest(database),source_candidate_sha256=host.digest(candidate),
            connectivity_sha256=host.digest(connectivity));map_path=root/'state-map.json';host.write(map_path,mapping)
        basis=root/'basis.json';basis.write_text('{}')
        binding=dict(schema='pinwheel.streaming-tt-sampler-binding.v1',top=top,
            connectivity_sha256=host.digest(connectivity),semantic_basis={'basis':{'path':str(basis),'sha256':host.digest(basis)}},
            bindings={})
        for index,stage in enumerate(('stage1','stage2')):
            row=rows[index];binding['bindings'][stage]=dict(component='core-d2',register='r_'+stage,index=0,
                cell=row['actual_ff'],q=row['actual_q'],d=row['actual_d'],clock=row['actual_clock'],reset_b=row['actual_reset_b'])
        binding_path=root/'binding.json';host.write(binding_path,binding)
        return binding_path,map_path,candidate,database,connectivity,binding,mapping

    def check(self,fixture):
        binding,mapping,candidate,database,connectivity,*_=fixture
        return host.sampler_binding(binding,mapping,candidate=candidate,database=database,connectivity=connectivity)

    def test_all_6039_actual_ff_pins_and_semantic_sampler_endpoints_bind(self):
        with tempfile.TemporaryDirectory() as tmp:
            fixture=self.fixture(Path(tmp));result=self.check(fixture)
            self.assertEqual(result['bindings']['stage1']['cell'],'ff0')
            self.assertEqual(result['bindings']['stage2']['cell'],'ff1')
            self.assertIn('actual-state-pairing',result['semantic_basis'])

    def test_missing_full_state_changed_pin_or_wrong_sampler_refuses(self):
        with tempfile.TemporaryDirectory() as tmp:
            fixture=self.fixture(Path(tmp));binding_path,map_path,_,_,_,binding,mapping=fixture
            for change in ('missing','pin','sampler'):
                wrong=deepcopy(mapping);changed=deepcopy(binding)
                if change=='missing':wrong['rows'].pop()
                elif change=='pin':wrong['rows'][200]['actual_d']+=1
                else:changed['bindings']['stage2']['cell']=changed['bindings']['stage1']['cell']
                host.write(map_path,wrong);host.write(binding_path,changed)
                with self.subTest(change=change),self.assertRaises(ValueError):self.check(fixture)


class NativeJournalTests(unittest.TestCase):
    def test_exact_fourteen_closed_calls_and_refuse_incomplete_or_altered_journal(self):
        with tempfile.TemporaryDirectory() as tmp:
            path=Path(tmp)/'native.jsonl';records=[];events=[]
            for index in range(14):
                intent=dict(index=index,scope='uart' if index<2 else 'legacy' if index<4 else 'i2c',
                    argv=['/selected/vvp','actual.vvp'],executable_sha256_before='a'*64)
                result=dict(intent,actual_argv=intent['argv'],native_exit_code=0,client_succeeded=True,
                    executable_sha256_after='a'*64,physical_edges=10)
                records.append(result);events.extend([dict(event='intent',**intent),dict(event='result',**result)])
            original=''.join(json.dumps(event)+'\n' for event in events);path.write_text(original)
            self.assertEqual(host.native_journal(path,records),host.digest(path))
            path.write_text(''.join(json.dumps(event)+'\n' for event in events[:-1]))
            with self.assertRaisesRegex(ValueError,'Missing/extra'):host.native_journal(path,records)
            changed=deepcopy(events);changed[7]['native_exit_code']=-9
            path.write_text(''.join(json.dumps(event)+'\n' for event in changed))
            with self.assertRaisesRegex(ValueError,'disagrees'):host.native_journal(path,records)

    def test_public_wire_overrides_rejected_without_importing_or_spawning_worker(self):
        host.check_environment({'PATH':'/usr/bin'})
        for name in ('PYTHONPATH','LEAN_PATH','LD_PRELOAD','DYLD_INSERT_LIBRARIES','VVP_LOG','IVL_ROOT'):
            with self.subTest(name=name),self.assertRaisesRegex(ValueError,'inherited public-wire'):
                host.check_environment({name:'override'})


if __name__=='__main__':unittest.main()
