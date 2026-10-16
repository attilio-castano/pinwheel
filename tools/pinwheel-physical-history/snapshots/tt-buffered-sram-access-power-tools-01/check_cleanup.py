"""Host-only owned cleanup controls; subprocess and Docker are mocked."""
import hashlib
import importlib.util
import json
from pathlib import Path
import signal
import subprocess
import tempfile
from unittest.mock import patch

HERE=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('power_common_controls',HERE/'common.py')
common=importlib.util.module_from_spec(spec);spec.loader.exec_module(common)
owner='controls-owner';identity='a'*64
cp=lambda rc=0,out='',err='':subprocess.CompletedProcess([],rc,out,err)
controls=[]
cases=[('absent',[cp(),cp()],'absent',[3,3]),
       ('sole owned live',[cp(out=identity+'\n'),cp(),cp()],'absent',[3,6,3]),
       ('malformed id',[cp(out='foreign\n')],'unconfirmed',[3]),
       ('multiple ids',[cp(out=identity+'\n'+'b'*64+'\n')],'unconfirmed',[3]),
       ('first query error',[cp(1,err='failed')],'unconfirmed',[3]),
       ('stop timeout',[cp(out=identity+'\n'),subprocess.TimeoutExpired('mocked-stop',6)],'unconfirmed',[3,6]),
       ('remaining live',[cp(),cp(out=identity+'\n')],'unconfirmed',[3,3]),
       ('last query error',[cp(),cp(1,err='failed')],'unconfirmed',[3,3])]
for label,values,status,timeouts in cases:
    with patch.object(common.subprocess,'run',side_effect=values) as mock:
        result=common.cleanup_container(owner)
        assert result['status']==status,(label,result)
        assert [x.kwargs['timeout'] for x in mock.call_args_list]==timeouts
        for call in mock.call_args_list:
            command=call.args[0]
            if command[1]=='container':assert 'label=org.pinwheel.baseline_owner='+owner in command
            else:assert command==['docker','stop','--time','2',identity]
    controls.append({'name':label,'status':'passed'})

for outcome,exception in [('normal',None),('timeout',subprocess.TimeoutExpired('mocked-docker',1)),('interrupt',KeyboardInterrupt('mocked'))]:
    with tempfile.TemporaryDirectory(prefix='pinwheel-power-control-') as name:
        out=Path(name);source=out/'input';source.write_text('immutable');(out/'measurement.json').write_text('{"status":"measured"}')
        previous={s:signal.getsignal(s) for s in (signal.SIGINT,signal.SIGTERM)}
        def cleanup(owner):
            assert signal.getsignal(signal.SIGINT)==signal.SIG_IGN
            assert signal.getsignal(signal.SIGTERM)==signal.SIG_IGN
            return {'status':'absent','ownership_label':owner,'owned_container_ids':[]}
        with patch.object(common.subprocess,'run',side_effect=exception,return_value=cp()) as mock,patch.object(common,'cleanup_container',side_effect=cleanup):
            result=common.execute(out,[source],['mock-native'],seconds=1,cpus=1,memory='1g',schema='host-control',scope='NoCAD; mocked subprocess')
        assert result['inputs_unchanged'] and result['container_termination']['status']=='absent'
        assert result['status']=={'normal':'passed','timeout':'timed_out','interrupt':'interrupted'}[outcome]
        assert all(signal.getsignal(s)==handler for s,handler in previous.items())
        assert mock.call_count==1
    controls.append({'name':'execute cleanup signal masking and restoration '+outcome,'status':'passed'})
report={'schema':'pinwheel-buffered-tt-sram-access-power-cleanup-controls-v1','status':'passed',
        'controls_passed':len(controls),'controls':controls,'CAD_run':False,
        'common_sha256':hashlib.sha256((HERE/'common.py').read_bytes()).hexdigest(),
        'control_source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'boundary':'Actual power-local cleanup and execute tested with subprocess mocks; no Docker or native grid execution.'}
(HERE/'controls.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'status':'passed','controls':len(controls)}))
