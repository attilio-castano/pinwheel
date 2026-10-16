import json,time,shutil
from pathlib import Path
from common import ROOT,execute,sha,write,read
H=Path(__file__).resolve().parent;out=ROOT/'build/physical/tt-buffered-resize-dirty-api-02';assert not out.exists();started=time.monotonic();out.mkdir();P=read(H/'prepared.json')
for n,h in P['tool_sha256'].items():assert sha(ROOT/n)==h,n
paths=[H/'prepared.json']
def copy(p,n):
 q=out/n;q.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,q);paths.extend([p,q])
for n in ['verify.py','coordinator.py','load.tcl','native_inventory.py','native-script-hashes.json']:copy(H/n,n)
prior=ROOT/'build/physical/tt-buffered-stable-pair4-physical-route-06'
for n in ['baseline-env.tcl','corner-env.tcl','core.sdc']:copy(prior/n,n)
for p in (prior/'lib').glob('*.lib'):copy(p,'lib/'+p.name)
source=ROOT/'build/physical/tt-buffered-pair-stabilization-route-01/pass2/routed.odb';assert sha(source)=='1304b736e051f2143b1449e76ad25bc1b9dfd2996afcc4bcf9294416b1ebe078';copy(source,'postcts.odb')
paths.extend([H/'driver.py',H/'common.py',prior/'report.json'])
r=execute(out,paths,['python3','-B','/work/diagnostic/coordinator.py'],seconds=60,cpus=2,memory='2g',schema='pinwheel-buffered-tt-resize-dirty-order-API-verification-v1',scope='Two native-init cache-order fixtures reproduce callback-first filter and verify pre-enrollment-first correction, no route solve or physical edit.',extra={'network':'none','overall_bound_seconds':90,'prepared_sha256':sha(H/'prepared.json'),'source_database_sha256':sha(source)})
r['all_in_elapsed_seconds']=round(time.monotonic()-started,3);write(out/'report.json',r);print(out/'report.json',r['status']);raise SystemExit(0 if r['status']=='passed' else 1)
