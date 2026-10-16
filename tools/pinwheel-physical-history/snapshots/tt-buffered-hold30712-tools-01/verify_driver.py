"""One authorized read-only offline API verification container, <=90s all-in."""
import ast,json,shutil,time,math
from pathlib import Path
from common import ROOT,execute,sha,read,write
H=Path(__file__).resolve().parent
start=time.monotonic();out=ROOT/'build/physical/tt-buffered-incremental-eco-helper-verify-02';assert not out.exists();out.mkdir()
prior=ROOT/'build/physical/tt-buffered-incremental-eco-route-01';retained=ROOT/'build/physical/tt-buffered-timing-eco-control-route-01'
failed=read(prior/'report.json');assert failed['status']=='failed' and failed['inputs_unchanged'] and failed['container_termination']['status']=='absent';assert not(prior/'candidate').exists()
paths=[prior/'report.json'];expected={}
def copy(p,n):
    t=out/n;t.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,t);assert sha(p)==sha(t);paths.extend([p,t]);expected[str(t.resolve())]=sha(p)
for n in ('verify_native.py','verify_coordinator.py','load.tcl','native_inventory.py','native-script-hashes.json'):copy(H/n,n)
copy(prior/'baseline/routed.odb','postcts.odb');copy(prior/'baseline/after_grt.segments','after_grt.segments')
for n in ('baseline-env.tcl','corner-env.tcl','core.sdc'):copy(prior/n,n)
for p in (prior/'lib').glob('*.lib'):copy(p,'lib/'+p.name)
prepared={'schema':'pinwheel-buffered-tt-incremental-eco-verification-prepared-v1','status':'prepared_not_launched','input_sha256':{str(p.resolve()):sha(p) for p in paths},'source_baseline_ODB_sha256':sha(out/'postcts.odb'),'source_exact_segments_sha256':sha(out/'after_grt.segments'),'source_failed_producer_sha256':sha(prior/'report.json'),'overall_cap_seconds':90,'work_seconds_at_most':40,'cleanup_reserve_seconds':50,'cpus':4,'memory':'3g','network':'none','no_GRT_no_ECO':True}
write(out/'prepared.json',prepared);paths.append(out/'prepared.json')
report=execute(out,paths,['python3','-B','/work/diagnostic/verify_coordinator.py'],seconds=max(1,min(40,math.floor(90-(time.monotonic()-start)-50))),cpus=4,memory='3g',schema='pinwheel-buffered-tt-incremental-eco-helper-verification-v1',scope='Exactlyoneauthorizedread-onlypinnedexecutableAPIverification; loadsretainedoriginalR0baselineODB+exactsegments+Lib/SDC, onlyparasitic/reportcommands; no globalroute/incremental/ECOmutation.',expected_hashes=expected,extra={'network':'none','overall_bound_seconds':90,'source_baseline_ODB_sha256':sha(out/'postcts.odb'),'source_exact_segments_sha256':sha(out/'after_grt.segments'),'prior_failed_producer_sha256':sha(prior/'report.json')})
report['all_in_elapsed_seconds']=round(time.monotonic()-start,3)
if report['all_in_elapsed_seconds']>90:report['status']='bound_exceeded'
write(out/'report.json',report);print(out/'report.json',flush=True);raise SystemExit(0 if report['status']=='passed' else 1)
