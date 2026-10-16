import shutil,time,json,datetime
from pathlib import Path
from common import ROOT,execute,sha,read,write
T=Path(__file__).resolve().parent;O=ROOT/'build/physical/tt-buffered-pinrc-export-01'; started=time.monotonic();O.mkdir()
P=ROOT/'build/physical/tt-buffered-holdreset-pair-preflight-01/preflight';C=ROOT/'build/physical/tt-buffered-hold30712-route-02/candidate'
I=read(P/'inputs.json');I.update(original_spef_sha256=sha(C/'estimated.spef'))
paths=list(T.glob('*.py'))+[T/'capture.tcl',P/'inputs.json',C/'routed.odb',C/'after_grt.segments',C/'estimated.spef',C/'after.v',ROOT/'build/physical/tt-buffered-hold30712-route-02/report.json']
for name in ['worker.py','capture.tcl','segments.py']:shutil.copyfile(T/name,O/name)
for name in ['baseline-env.tcl','core.sdc']:shutil.copyfile(P/name,O/name);paths.append(P/name)
shutil.copyfile(C/'routed.odb',O/'checkpoint.odb');shutil.copyfile(C/'after_grt.segments',O/'after_grt.segments')
(O/'lib').mkdir()
for p in sorted((P/'lib').glob('*.lib')):shutil.copyfile(p,O/'lib'/p.name);paths.append(p)
write(O/'inputs.json',I);paths.append(O/'inputs.json')
prepared=read(T/'prepared.json'); assert all(sha(p)==d for p,d in prepared['source_sha256'].items());paths.append(T/'prepared.json')
r=execute(O,paths,['python3','-B','/work/diagnostic/worker.py'],seconds=120,cpus=3,memory='3g',schema='pinwheel-buffered-tt-pinrc-native-export-v1',scope='Read-only exact saved ODB/global-segment RC estimation; no routing, placement, masters, connectivity or model changes.',extra={'source_database_sha256':sha(C/'routed.odb'),'source_segments_sha256':sha(C/'after_grt.segments'),'network':'none'},absolute_work_stop=datetime.datetime.fromisoformat('2026-10-13T20:47:07+00:00').timestamp(),all_in_deadline_monotonic=started+180,phase_started_monotonic=started,host_stage_seconds=30)
print(r['status'],r.get('elapsed_seconds')); assert r['status']=='passed'
