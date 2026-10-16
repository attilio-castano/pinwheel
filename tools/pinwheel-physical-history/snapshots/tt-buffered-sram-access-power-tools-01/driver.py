"""One source-bound offline candidate power check, at most 60 seconds all-in."""
import argparse
from pathlib import Path
import re
import shutil
import sys
import time
from common import ROOT, execute, read, resolve_view, sha, write

parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--state',type=Path,required=True)
parser.add_argument('--design',type=Path,required=True)
parser.add_argument('--tag',required=True)
args=parser.parse_args();started=time.monotonic()
assert re.fullmatch('[A-Za-z0-9_-]+',args.tag)
design=args.design.resolve();state_path=args.state.resolve()
assert design.is_relative_to((ROOT/'build/physical').resolve())
assert state_path.is_relative_to(design) and state_path.name=='state_out.json'
tools=Path(__file__).resolve().parent;prepared=read(tools/'prepared.json')
for name,expected in prepared['tool_sha256'].items():assert sha(tools/name)==expected,name
intake=ROOT/'build/physical/tt-buffered-sram-access-intake-01/report.json';intake_data=read(intake)
for path,expected in prepared['retained_evidence_sha256'].items():assert sha(ROOT/path)==expected,path
for path,expected in intake_data['prior_source_sha256'].items():assert sha(ROOT/path)==expected,path
producer=design/'candidate-invocation.json';produced=read(producer)
assert produced['status']=='passed' and produced['container_termination']['status']=='absent'
assert produced['inputs_unchanged'] and produced['preparation_sha256']==sha(design/'preparation.json')
assert produced['runtime']['image_id']==prepared['image_id']
core=read(design/'core.json');placements=core['MACROS']['RM_IHPSG13_1P_64x64_c2_bm_bist']['instances']
assert placements=={'engine.memory.storage0':{'location':[252,30],'orientation':'FS'},
                    'engine.memory.storage1':{'location':[252,144],'orientation':'FS'}}
state=read(state_path);database=resolve_view(state,design,'odb');database_sha=sha(database)
reference=ROOT/'build/physical/tt-buffered-recovery-power-01/input.odb'
assert sha(reference)==prepared['reference_odb_sha256']
plan=design/'power-columns.json';assert sha(plan)==prepared['power_plan_sha256']
out=ROOT/'build/physical'/args.tag;out.mkdir()
paths=[database,state_path,producer,design/'core.json',design/'preparation.json',plan,
       reference,intake,tools/'prepared.json',ROOT/'tools/physical-toolchain.json',
       ROOT/'scripts/run-buffered-tt-physical.py',ROOT/'build/physical/pdk/installed.json']
for source,target in [(database,'input.odb'),(reference,'reference.odb'),(plan,'power-columns.json'),
                      (state_path,'source-state.json'),(producer,'source-invocation.json')]:
    shutil.copyfile(source,out/target);assert sha(source)==sha(out/target);paths+=[source,out/target]
for name in ('check_grid.tcl','metadata.py','coordinator.py'):
    shutil.copyfile(tools/name,out/name);paths += [tools/name,out/name]
paths += [Path(__file__).resolve(),tools/'common.py']
work_bound=min(42,int(60-(time.monotonic()-started)-15));assert work_bound>0
report=execute(out,paths,['python3','-B','/work/diagnostic/coordinator.py'],
               seconds=work_bound,cpus=1,memory='1g',schema='pinwheel-buffered-tt-sram-access-power-v1',
               scope='Fresh both-net whole-grid connectivity and exact native MX macro/contact/grid readback. No source, netlist or power-grid mutation.',
               extra={'source_database':str(database.relative_to(ROOT)),'source_database_sha256':database_sha,
                      'source_state':str(state_path.relative_to(ROOT)),'overall_bound_seconds':60,
                      'cleanup_bound_seconds':12,'reference_database_sha256':prepared['reference_odb_sha256']},
               expected_hashes={database:database_sha,out/'input.odb':database_sha,
                                reference:prepared['reference_odb_sha256'],out/'reference.odb':prepared['reference_odb_sha256']})
report['all_in_elapsed_seconds']=round(time.monotonic()-started,3)
report['all_in_scope']='Host staging, owned Docker work/cleanup, input recustody, artifact hashes; excludes only final report write and print.'
if report['all_in_elapsed_seconds']>60:report['status']='bound_exceeded'
write(out/'report.json',report);print(out/'report.json',flush=True)
sys.exit(0 if report['status']=='passed' else 1)
