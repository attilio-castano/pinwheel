"""Seal one successful scratch producer after root reports settlement. Host-only."""
import argparse
import importlib.util
import json
from pathlib import Path
import sys
import time

ROOT=Path(__file__).resolve().parents[3]
TOOLS=ROOT/'build/physical/tt-buffered-two-buffer-validation-tools-01'
sys.path.insert(0,str(TOOLS))
from common import read,sha,write,source_intakes
from admission import validate,rooted,SOURCE_ODB_SHA

def hashes(values,base=ROOT):
    result={}
    for name,digest in values.items():
        p=rooted(name,base)
        assert sha(p)==digest,('Source/artifact changed',str(p))
        result[str(p)]=digest
    return result

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--producer',type=Path,required=True)
    parser.add_argument('--selection',type=Path,required=True)
    parser.add_argument('--out',type=Path,required=True)
    args=parser.parse_args();started=time.monotonic()
    script=Path(__file__).resolve();prepared=read(script.with_name('prepared.json'))
    assert sha(script)==prepared['creator_sha256']
    hashes(prepared['fixed_source_sha256'])
    selection_path=rooted(args.selection);selection=read(selection_path)
    assert selection['schema']=='pinwheel-buffered-tt-two-buffer-selection-v1'
    assert sha(selection_path)==prepared['selection_sha256']
    for ref in selection['references'].values():assert sha(rooted(ref['path']))==ref['sha256']
    intake_path=rooted(selection['references']['intake']['path']);intake=read(intake_path)
    files={str(selection_path):sha(selection_path),str(intake_path):sha(intake_path),str(script):sha(script),
           str(script.with_name('prepared.json')):sha(script.with_name('prepared.json'))}
    for key in ('protected_sources_sha256','prior_current_source_sha256','references_sha256',
                'original_checkpoint_views_sha256','original_recipe_sha256'):
        files.update(hashes(intake[key]))
    for name,d in intake['prior_manifests'].items():
        p=rooted(name);assert sha(p)==d['sha256'];files[str(p)]=sha(p)
        files.update(hashes(d['evidence_sha256']))
    intakes,intake_hashes=source_intakes();files.update(intake_hashes)
    for label,ref in prepared['fresh_control_receipts'].items():
        p=rooted(ref['path']);assert sha(p)==ref['sha256'];d=read(p)
        assert d['status']=='passed' and d['exit_code']==0 and d['inputs_unchanged']
        assert d['source_database_sha256']==SOURCE_ODB_SHA
        assert d['container_termination']['status']=='absent'
        files[str(p)]=sha(p);files.update(hashes(d['input_sha256']))
        files.update(hashes(d['artifact_sha256'],p.parent))
        assert d['measurement']==read(p.parent/'measurement.json')
        if label=='route':
            assert d['native_extra_iterations']==5 and not d['accepted_route']
            assert d['measurement']['native_overflow']==5840
        else:
            assert d['all_control_corners_reproduce_retained_reference']
            assert d['measurement']['nominal_reference']['same_database'] and d['measurement']['nominal_reference']['reproduced']
    producer_path=rooted(args.producer)
    assert producer_path==(ROOT/'build/physical/tt-buffered-two-buffer-candidate-01/report.json').resolve(),'Only the frozen one candidate producer is admitted'
    producer=read(producer_path);design=producer_path.parent.resolve()
    assert design.is_relative_to(ROOT/'build/physical')
    assert producer['status']=='passed' and producer['exit_code']==0 and producer['inputs_unchanged']
    assert producer['source_database_sha256']==SOURCE_ODB_SHA
    files.update(hashes(producer['input_sha256']))
    files.update(hashes(producer['artifact_sha256'],design))
    files[str(producer_path)]=sha(producer_path)
    descriptor_path=rooted(producer['completed_descriptor'])
    assert descriptor_path.is_relative_to(design) and sha(descriptor_path)==producer['completed_descriptor_sha256']
    descriptor=read(descriptor_path)
    assert descriptor['schema']=='pinwheel-buffered-tt-two-buffer-checkpoint-v1' and 'metrics' not in descriptor
    prefix=descriptor['container_design_root']+'/'
    assert descriptor['container_design_root'] in ('/work/core','/work/recovery')
    assert descriptor['odb'].startswith(prefix) and descriptor['nl'].startswith(prefix)
    database=rooted(descriptor['odb'][len(prefix):],design)
    netlist=rooted(descriptor['nl'][len(prefix):],design)
    movement_path=rooted('movement.json',design)
    assert all(p.is_relative_to(design) for p in (database,netlist,movement_path))
    policy_path=rooted(selection['references']['policy']['path']);files[str(policy_path)]=sha(policy_path)
    out=args.out.resolve();assert out.is_relative_to(ROOT/'build/physical') and not out.exists()
    out.mkdir()
    manifest=dict(schema='pinwheel-buffered-tt-two-buffer-admission-v1',status='admitted',
        design_path=str(design.relative_to(ROOT)),descriptor_path=str(descriptor_path.relative_to(ROOT)),
        database_path=str(database.relative_to(ROOT)),database_sha256=sha(database),
        producer_path=str(producer_path.relative_to(ROOT)),producer_sha256=sha(producer_path),
        movement_path=str(movement_path.relative_to(ROOT)),movement_sha256=sha(movement_path),
        selection_sha256=sha(selection_path),policy_sha256=sha(policy_path),source_database_sha256=SOURCE_ODB_SHA,
        files_sha256=files,core_abi_source_intakes=intakes,fresh_control_receipts=prepared['fresh_control_receipts'],
        candidate_native_producer_status='passed',candidate_native_producer_exit_code=0,
        source_reference_native_flow_status='failed',source_reference_native_flow_exit_code=2,
        source_reference_inherited_power_count=30396,no_candidate_metrics_inherited=True,
        boundary='Successful bounded native scratch producer and whole movement/inventory gate only. Original failed Librelane reference retains its status. Fresh candidate timing/export/power/mapped/paired routing remain required; this admission does not qualify routing or signoff.')
    temporary=out/'admission.pending.json';write(temporary,manifest)
    validate(temporary,selection_path)
    target=out/'admission.json';temporary.rename(target)
    receipt=dict(schema='pinwheel-buffered-tt-two-buffer-admission-creation-v1',status='passed',
        creator_sha256=sha(script),prepared_sha256=sha(script.with_name('prepared.json')),
        admission_sha256=sha(target),producer_sha256=sha(producer_path),descriptor_sha256=sha(descriptor_path),
        database_sha256=sha(database),files_verified=len(files),core_abi_source_intakes=intakes,
        CAD_run=False,elapsed_seconds=round(time.monotonic()-started,3),
        boundary='Host input/source/artifact validation and scratch admission sealing; no CAD, simulation or physical qualification.')
    write(out/'creation.json',receipt)
    print(json.dumps(dict(admission=str(target.relative_to(ROOT)),admission_sha256=sha(target),
        creation_sha256=sha(out/'creation.json'),files_verified=len(files),elapsed_seconds=receipt['elapsed_seconds'])))

if __name__=='__main__':main()
