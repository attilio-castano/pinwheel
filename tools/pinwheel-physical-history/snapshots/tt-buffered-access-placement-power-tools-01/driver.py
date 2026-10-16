"""One offline R0 power/contact/fence diagnostic, at most 80 seconds all-in."""
import argparse
import math
from pathlib import Path
import re
import shutil
import sys
import time
from common import ROOT, execute, read, resolve_view, sha, write
from checkpoint_admission import validate

parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--state',type=Path,required=True)
parser.add_argument('--design',type=Path,required=True)
parser.add_argument('--checkpoint-admission',type=Path,required=True)
parser.add_argument('--selection',type=Path,required=True)
parser.add_argument('--policy',type=Path,required=True)
parser.add_argument('--tag',required=True)
args=parser.parse_args();started=time.monotonic()
assert re.fullmatch('[A-Za-z0-9_-]+',args.tag)
tools=Path(__file__).resolve().parent;prepared=read(tools/'prepared.json')
for name,expected in prepared['tool_sha256'].items():assert sha(tools/name)==expected,name
assert sha(args.selection)==prepared['selection']['sha256']
assert args.selection.resolve()==(ROOT/prepared['selection']['path']).resolve()
assert sha(args.policy)==prepared['policy']['sha256']
selection=read(args.selection);policy=read(args.policy)
for value in selection['references'].values():assert sha(ROOT/value['path'])==value['sha256']
assert len(policy['regions'])==2
for row,selected in zip(policy['regions'],selection['physical_policy']['regions']):
    assert row['macro']==selected['macro']
    assert {m['instance'] for m in row['members']}==set(selected['members'])
    assert row['bbox_dbu']==[round(v*1000) for v in selected['bbox_um']]
admitted_paths,producer_admission=validate(args.design,args.state,args.checkpoint_admission)
design=args.design.resolve();state=read(args.state);database=resolve_view(state,design,'odb');digest=sha(database)
reference=ROOT/'build/physical/tt-buffered-recovery-power-01/input.odb'
assert sha(reference)==prepared['reference_odb_sha256']
plan=design/'power-columns.json';assert sha(plan)==prepared['power_plan_sha256']
intake=ROOT/prepared['intake']['path'];assert sha(intake)==prepared['intake']['sha256']
intake_data=read(intake)
protected={}
for key in ('previous_mirrored_source_sha256','previous_mirrored_evidence_sha256',
            'older_evidence_sha256','protected_sources_sha256','references_sha256'):
    for name,expected in intake_data[key].items():
        source=Path(name) if Path(name).is_absolute() else ROOT/name
        assert sha(source)==expected,name
        protected[str(source.resolve())]=expected
out=ROOT/'build/physical'/args.tag;out.mkdir()
paths=[database,args.state,args.checkpoint_admission,args.selection,args.policy,reference,plan,
       design/'core.json',design/'preparation.json',intake,tools/'prepared.json',
       tools/'checkpoint_admission.py',tools/'common.py',Path(__file__),
       ROOT/'scripts/run-buffered-tt-physical.py',ROOT/'tools/physical-toolchain.json',
       ROOT/'build/physical/pdk/installed.json',*[Path(p)for p in admitted_paths],
       *[Path(p)for p in protected]]
for source,name in [(database,'input.odb'),(reference,'reference.odb'),(plan,'power-columns.json'),
                    (args.state,'source-state.json'),(args.policy,'policy.json')]:
    shutil.copyfile(source,out/name);assert sha(source)==sha(out/name);paths.extend([source,out/name])
for name in ('check_grid.tcl','metadata.py','coordinator.py'):
    shutil.copyfile(tools/name,out/name);paths.extend([tools/name,out/name])
work=min(60,math.floor(80-(time.monotonic()-started)-15));assert work>0
report=execute(out,paths,['python3','-B','/work/diagnostic/coordinator.py'],seconds=work,cpus=1,memory='1g',
    schema='pinwheel-buffered-tt-access-placement-power-fences-v1',
    scope='Fresh both-net whole-grid connectivity, original R0 macro/contact/grid and final twelve address-driver region/group readback. No mutation, routing, extracted timing or signoff.',
    extra={**producer_admission,'source_database':str(database.relative_to(ROOT)),
           'source_database_sha256':digest,'source_state':str(args.state.resolve().relative_to(ROOT)),
           'selection_sha256':sha(args.selection),'policy_sha256':sha(args.policy),
           'overall_bound_seconds':80,'cleanup_bound_seconds':12,
           'reference_database_sha256':prepared['reference_odb_sha256']},
    expected_hashes={database:digest,out/'input.odb':digest,reference:prepared['reference_odb_sha256'],
                     out/'reference.odb':prepared['reference_odb_sha256'],**protected,**admitted_paths})
report['all_in_elapsed_seconds']=round(time.monotonic()-started,3)
report['all_in_scope']='Host staging, native checks, bounded owned cleanup, source recustody and artifact hashes; excludes only final report write/print.'
if report['all_in_elapsed_seconds']>80:report['status']='bound_exceeded'
write(out/'report.json',report);print(out/'report.json',flush=True)
sys.exit(0 if report['status']=='passed' else 1)
