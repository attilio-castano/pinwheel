"""One bounded immutable OpenDB readback; no rerouting or physical mutation."""
import argparse
import math
from pathlib import Path
import re
import shutil
import sys
import time
from common import ROOT,execute,read,sha,write
parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--tag',required=True);args=parser.parse_args();started=time.monotonic()
assert re.fullmatch('[A-Za-z0-9_-]+',args.tag)
tools=Path(__file__).resolve().parent;prepared=read(tools/'prepared.json')
for name,digest in prepared['tool_sha256'].items():assert sha(tools/name)==digest,name
admission=read(tools/'admission.json');assert sha(tools/'admission.json')==prepared['admission_sha256']
source=ROOT/admission['source_directory'];original=read(source/'report.json')
assert original['status']=='failed' and original['exit_code']==1 and original['inputs_unchanged']
assert original['container_termination']['status']=='absent' and original['native_extra_iterations']==5
for path,digest in admission['source_sha256'].items():assert sha(ROOT/path)==digest,path
for relative,digest in original['artifact_sha256'].items():assert sha(source/relative)==digest,relative
for path,digest in original['input_sha256'].items():assert sha(path)==digest,path
assert sha(source/'postcts.odb')==admission['expected_source_postcts_odb_sha256']
assert sha(source/'routed.odb')==admission['expected_source_routed_odb_sha256']
assert sha(source/'before.v')==sha(source/'after.v')
assert 'assert ix+1<len(x) and iy+1<len(y)' in (source/'execution.log').read_text()
out=ROOT/'build/physical'/args.tag;out.mkdir()
paths=[Path(__file__).resolve(),tools/'common.py',tools/'prepared.json',tools/'admission.json',
       ROOT/'scripts/run-buffered-tt-physical.py',ROOT/'tools/physical-toolchain.json',ROOT/'build/physical/pdk/installed.json']
paths += [ROOT/path for path in admission['source_sha256']]
for name,target in [('postcts.odb','postcts.odb'),('routed.odb','routed.odb'),('before.v','before.v'),('after.v','after.v'),('native.log','native-route.log'),('congestion.json','native-markers.json'),('report.json','source-report.json')]:
    shutil.copyfile(source/name,out/target);assert sha(source/name)==sha(out/target);paths+=[source/name,out/target]
shutil.copyfile(tools/'export_geometry.py',out/'export_geometry.py');paths += [tools/'export_geometry.py',out/'export_geometry.py']
work=min(30,math.floor(80-(time.monotonic()-started)-52));assert work>=1
report=execute(out,paths,['openroad','-python','-exit','/work/diagnostic/export_geometry.py'],seconds=work,cpus=1,memory='1g',schema='pinwheel-buffered-tt-sram-access-grid-readback-v1',scope='Native readonly OpenDB readback of existing completedcoarsecandidate route; no reroute, placement, netlist, grid or routingrule mutation. Original failedexport receipt remains failed.',extra={'original_route_receipt_status':'failed','original_native_routing_completed':True,'native_extra_iterations':5,'source_postcts_database_sha256':sha(source/'postcts.odb'),'source_routed_database_sha256':sha(source/'routed.odb'),'source_route_report_sha256':sha(source/'report.json'),'admission_sha256':sha(tools/'admission.json'),'overall_bound_seconds':80,'cleanup_reserve_seconds':50},expected_hashes={source/'postcts.odb':admission['expected_source_postcts_odb_sha256'],out/'postcts.odb':admission['expected_source_postcts_odb_sha256'],source/'routed.odb':admission['expected_source_routed_odb_sha256'],out/'routed.odb':admission['expected_source_routed_odb_sha256']})
report['all_in_elapsed_seconds']=round(time.monotonic()-started,3);report['all_in_scope']='Source validation/staging, bounded native readback, owned cleanup and recustody/artifact hashes; excludes only final receipt write and print.'
if report['all_in_elapsed_seconds']>80:report['status']='bound_exceeded'
write(out/'report.json',report);print(out/'report.json',flush=True);sys.exit(0 if report['status']=='passed' else 1)
