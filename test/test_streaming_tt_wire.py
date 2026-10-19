"""Fresh-input/native-journal refusal seams of the physical wire worker."""
from copy import deepcopy
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import struct
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
spec=importlib.util.spec_from_file_location('tt_wire_gate',ROOT/'scripts/check-streaming-tt-wire.py')
gate=importlib.util.module_from_spec(spec);spec.loader.exec_module(gate)


def trace(path,edges=3):
    path.parent.mkdir(parents=True,exist_ok=True)
    data=b''.join(struct.pack('<I16B',index,*([0]*16)) for index in range(1,edges+1))
    path.write_bytes(data)
    return dict(edges=edges,bytes=len(data),format=gate.TRACE_FORMAT,sha256=sha256(data).hexdigest())


def native_fixture(root):
    ordinary=root/'actual.vvp';ordinary.write_bytes(b'actual compiled native program')
    mutant=root/'mutant.vvp';mutant.write_bytes(b'actual one-FF mutant native program')
    result=dict(uart=dict(depth=2,native_runs=[],cases=[dict(mutation={'pin':'D'})],physical_edges=6),
        legacy=dict(depth=2,cases=[],physical_edges=6),i2c=dict(depth=2,cases=[],physical_edges=30),
        executables={'unchanged':str(ordinary),'sampler-ff-pin':str(mutant)},
        sampler_mutation={'pin':'D'},physical_edges=42,native_runs=[])
    rows=[]
    for label,path in [('unchanged',ordinary),('sampler-ff-pin',mutant)]:
        row=dict(physical_edges=3,trace=trace(root/'uart'/(label+'.bin')))
        result['uart']['native_runs'].append(row);rows.append(('uart',row,path))
    for protocol in ('spi','jtag'):
        row=dict(protocol=protocol,physical_edges=3,trace=trace(root/'legacy'/protocol/'wire.bin'))
        result['legacy']['cases'].append(row);rows.append(('legacy',row,ordinary))
    for direction in ('read','write'):
        for profile in ('clean','varying','lastpoll','timeout','address_nack'):
            row=dict(direction=direction,profile=profile,physical_edges=3,
                trace=trace(root/'i2c'/(direction+'-'+profile)/'wire.bin'))
            result['i2c']['cases'].append(row);rows.append(('i2c',row,ordinary))
    for index,(scope,row,executable) in enumerate(rows):
        argv=['/selected/vvp',str(executable)]
        result['native_runs'].append(dict(index=index,scope=scope,argv=argv,actual_argv=argv,
            native_exit_code=0,client_succeeded=True,executable_sha256_before=gate.digest(executable),
            executable_sha256_after=gate.digest(executable),physical_edges=3))
    return result,dict(vvp='/selected/vvp')


class TraceTests(unittest.TestCase):
    def test_exact_real_producer_format_and_complete_trace(self):
        from streaming_wire_cases import EdgeTrace
        self.assertEqual(gate.TRACE_FORMAT,EdgeTrace.FORMAT)
        with tempfile.TemporaryDirectory() as temp:
            path=Path(temp)/'wire.bin';receipt=trace(path)
            self.assertEqual(gate.validate_trace(path,receipt,3)['edges'],3)

    def test_truncated_reordered_wrong_hash_and_format_refused(self):
        with tempfile.TemporaryDirectory() as temp:
            path=Path(temp)/'wire.bin';receipt=trace(path)
            for field,value in [('format','other'),('sha256','0'*64),('bytes',40),('edges',2)]:
                wrong=dict(receipt,**{field:value})
                with self.assertRaises(ValueError):gate.validate_trace(path,wrong,3)
            path.write_bytes(path.read_bytes()[:-1])
            with self.assertRaises(ValueError):gate.validate_trace(path,receipt,3)
            receipt=trace(path);data=bytearray(path.read_bytes());struct.pack_into('<I',data,20,1);path.write_bytes(data)
            receipt['sha256']=gate.digest(path)
            with self.assertRaises(ValueError):gate.validate_trace(path,receipt,3)

    def test_symlink_hardlink_and_bool_edges_refused(self):
        with tempfile.TemporaryDirectory() as temp:
            root=Path(temp);path=root/'wire.bin';receipt=trace(path)
            alias=root/'alias';alias.symlink_to(path)
            with self.assertRaises(ValueError):gate.validate_trace(alias,receipt,3)
            with self.assertRaises(ValueError):gate.validate_trace(path,receipt,True)
            import os
            os.link(path,root/'hardlink')
            with self.assertRaises(ValueError):gate.validate_trace(path,receipt,3)


class NativeBindingTests(unittest.TestCase):
    def validate(self,result,root,tools):
        # Isolate native/process binding; the production function still calls
        # the three independently tested exact public-protocol validators.
        with patch('streaming_mapped_simulation.check_uart_cases'),patch('streaming_uart_legacy_cases.check_legacy_cases'),\
                patch('streaming_ready_wire_cases.check_i2c_cases'):
            return gate.validate_native(result,root,tools)

    def test_actual_fourteen_paths_roundtrip(self):
        with tempfile.TemporaryDirectory() as temp:
            root=Path(temp);result,tools=native_fixture(root)
            self.assertEqual(len(self.validate(result,root,tools)),14)

    def test_actual_process_executable_and_mutation_refusals(self):
        with tempfile.TemporaryDirectory() as temp:
            root=Path(temp);result,tools=native_fixture(root)
            for change in ('argv','exit','hash','count','index','edges','mutant','bool_depth'):
                wrong=deepcopy(result)
                if change=='argv':wrong['native_runs'][0]['actual_argv']=['/unselected/vvp','other']
                elif change=='exit':wrong['native_runs'][0]['native_exit_code']=1
                elif change=='hash':wrong['native_runs'][0]['executable_sha256_after']='0'*64
                elif change=='count':wrong['native_runs'].pop()
                elif change=='index':wrong['native_runs'][0]['index']=2
                elif change=='edges':wrong['physical_edges']+=1
                elif change=='mutant':wrong['sampler_mutation']={'pin':'CLK'}
                else:wrong['uart']['depth']=True
                with self.subTest(change=change),self.assertRaises(ValueError):self.validate(wrong,root,tools)

    def test_real_retained_trace_replacement_refused(self):
        with tempfile.TemporaryDirectory() as temp:
            root=Path(temp);result,tools=native_fixture(root)
            path=root/'i2c/read-lastpoll/wire.bin';path.write_bytes(path.read_bytes().replace(b'\x02\x00\x00\x00',b'\x03\x00\x00\x00',1))
            with self.assertRaises(ValueError):self.validate(result,root,tools)


class InputTests(unittest.TestCase):
    def test_environment_overrides_refused_before_output_or_source_use(self):
        gate.check_environment({});gate.check_environment({'HOME':'/test','PATH':'/usr/bin','VVP_LOG':''})
        for name in ('PYTHONPATH','DYLD_INSERT_LIBRARIES','LD_PRELOAD','LEAN_PATH','LAKE_CACHE_DIR',
                'YOSYS_DATDIR','ABC_SCRIPT','Z3_TRACE','CIRCT_OPTIONS','VVP_LOG','IVERILOG_ICONFIG','IVL_ROOT','VPI_PATH'):
            with self.subTest(name=name),self.assertRaises(ValueError):gate.check_environment({name:'active'})
        with tempfile.TemporaryDirectory() as temp,patch.dict('os.environ',{'VVP_LOG':'override'}),\
                patch.object(gate,'source_snapshot') as source:
            out=Path(temp)/'out'
            with self.assertRaises(ValueError):gate.run_worker({},out)
            source.assert_not_called();self.assertFalse(out.exists())

    def test_configuration_hash_refusal_before_worker_or_output(self):
        with tempfile.TemporaryDirectory() as temp:
            root=Path(temp);config=root/'config.json';config.write_text('{}');out=root/'out'
            with patch.object(gate,'run_worker') as worker,self.assertRaises(ValueError):
                gate.main(['--worker-config',str(config),'--worker-config-sha256','0'*64,'--out',str(out)])
            worker.assert_not_called();self.assertFalse(out.exists())

    def test_duplicate_json_refused(self):
        with tempfile.TemporaryDirectory() as temp:
            path=Path(temp)/'input';path.write_text('{"a":1,"a":2}')
            with self.assertRaises(ValueError):gate.read(path)

    def test_omitted_or_wrong_source_refused_before_output(self):
        with tempfile.TemporaryDirectory() as temp:
            out=Path(temp)/'out'
            config=dict(schema='pinwheel.streaming-tt-wire-request.v1',source_commit='1'*40,producer_commit='1'*40,
                root=str(ROOT),source_sha256={})
            with self.assertRaises(ValueError):gate.run_worker(config,out)
            self.assertFalse(out.exists())


class DurableProtocolTests(unittest.TestCase):
    def test_first_protocol_result_survives_interruption_in_second(self):
        with tempfile.TemporaryDirectory() as temp:
            directory=Path(temp)/'legacy'
            def run_case(_vvp,_executable,out,**options):
                if options['protocol']=='jtag':
                    saved=gate.read(directory/'spi/report.json')
                    self.assertEqual(saved['error'],'actual native SPI exited -9')
                    self.assertFalse(saved['passed'])
                    raise KeyboardInterrupt('stop second simulator')
                out.mkdir();return dict(passed=False,protocol='spi',bits=32768,physical_edges=107111,
                    error='actual native SPI exited -9')
            with patch('streaming_wire_cases.run_stream',side_effect=run_case),self.assertRaises(KeyboardInterrupt):
                gate.run_legacy_durable('/selected/vvp','actual.vvp',directory,depth=2)
            progress=gate.read(directory/'progress.json')
            self.assertFalse(progress['completed']);self.assertFalse(progress['passed'])
            self.assertEqual(progress['status'],'failed_or_interrupted')
            self.assertEqual(progress['cases'][0]['sha256'],gate.digest(directory/'spi/report.json'))
            self.assertFalse((directory/'report.json').exists())

    def test_i2c_case_report_is_closed_before_later_case_interrupts(self):
        import streaming_ready_wire_cases as cases
        with tempfile.TemporaryDirectory() as temp:
            directory=Path(temp)/'i2c'
            def run_case(_vvp,_executable,out,**options):
                if options['profile']!='clean':
                    self.assertEqual(gate.read(directory/'read-clean/report.json')['error'],'actual first I2C failure')
                    raise KeyboardInterrupt('later case interrupted')
                out.mkdir();return dict(passed=False,error='actual first I2C failure')
            with patch.object(cases,'run_i2c_case',side_effect=run_case) as original:
                with self.assertRaises(KeyboardInterrupt):
                    gate.run_i2c_durable('/selected/vvp','actual.vvp',directory,depth=2)
                self.assertIs(cases.run_i2c_case,original)
            self.assertFalse(gate.read(directory/'read-clean/report.json')['passed'])


if __name__=='__main__':unittest.main()
