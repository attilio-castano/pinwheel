"""Host-only actual failed-producer admission and rejection controls."""
import copy
import hashlib
import importlib.util
import json
from pathlib import Path

HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[2]
spec=importlib.util.spec_from_file_location('power_checkpoint_admission_controls',HERE/'admission.py');module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
manifest=json.loads((HERE/'checkpoint-admission.json').read_text());base=ROOT/manifest['design_path']
record=json.loads((base/'candidate-invocation.json').read_text());state=json.loads((ROOT/manifest['state_path']).read_text());log=(base/'candidate.log').read_text()
validate=module.validate_producer_record
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
for path,digest in manifest['files_sha256'].items():assert sha(ROOT/path)==digest,path
for path,digest in manifest['prior_tools_01_files_sha256'].items():assert sha(ROOT/path)==digest,path
for step in ('05-openroad-generatepdn','06-project-bufferedsrampower'):
    metrics=json.loads((base/'runs/tt-buffered-sram-access-02'/step/'state_out.json').read_text())['metrics']
    assert all(metrics[key]==value for key,value in manifest['inherited_power_metrics'].items())
controls=[];result=validate(record,manifest,state,log)
assert result['overall_native_flow_status']=='failed' and result['fresh_native_PSM_and_metadata_checks_waived'] is False
controls.append({'name':'exact retained failed producer and completed checkpoint admitted only for fresh diagnostic','status':'passed'})
changes=[('passed producer',lambda r,m,s,l:r.update(status='passed')),
         ('different exit code',lambda r,m,s,l:r.update(exit_code=1)),
         ('unconfirmed cleanup',lambda r,m,s,l:r['container_termination'].update(status='unconfirmed')),
         ('changed source custody',lambda r,m,s,l:r.update(inputs_unchanged=False)),
         ('different preparation',lambda r,m,s,l:r.update(preparation_sha256='0'*64)),
         ('different stop stage',lambda r,m,s,l:r.update(stop_after='OpenROAD.CTS')),
         ('completed state hash mismatch',lambda r,m,s,l:r['artifacts_sha256'].update({next(k for k in m['producer_artifacts_sha256'] if k.endswith('state_out.json')):'0'*64})),
         ('missing completed state',lambda r,m,s,l:r['artifacts_sha256'].pop(next(k for k in m['producer_artifacts_sha256'] if k.endswith('state_out.json')))),
         ('different final inherited total',lambda r,m,s,l:s['metrics'].update(design__power_grid_violation__count=30395)),
         ('different declared inherited total',lambda r,m,s,l:m['inherited_power_metrics'].update(design__power_grid_violation__count=30395)),
         ('different ODB view',lambda r,m,s,l:s.update(odb='/work/recovery/other.odb'))]
for label,change in changes:
    r,m,s=copy.deepcopy(record),copy.deepcopy(manifest),copy.deepcopy(state);change(r,m,s,log)
    try:validate(r,m,s,log)
    except (AssertionError,KeyError):controls.append({'name':label+' rejected','status':'passed'})
    else:raise AssertionError(label)
for label,text in [('wrong deferred count',log.replace('30396','30395')),('missing deferred classification',log.replace('One or more deferred errors were','Unclassified failure'))]:
    try:validate(record,manifest,state,text)
    except AssertionError:controls.append({'name':label+' rejected','status':'passed'})
    else:raise AssertionError(label)
controls.append({'name':'all exact checkpoint/source and old01 hashes unchanged','status':'passed'})
report={'schema':'pinwheel-buffered-tt-sram-access-power-checkpoint-controls-v1','status':'passed','controls_passed':len(controls),'controls':controls,'admission_source_sha256':sha(HERE/'admission.py'),'checkpoint_manifest_sha256':sha(HERE/'checkpoint-admission.json'),'control_source_sha256':sha(Path(__file__)),'CAD_run':False,'boundary':'Actual new admission function exercised on the exact retained failed producer/state/log; changed records are rejected. No native PSM, OpenDB metadata or grid assertion is waived or run.'}
(HERE/'admission-controls.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({'status':'passed','controls':len(controls)}))
