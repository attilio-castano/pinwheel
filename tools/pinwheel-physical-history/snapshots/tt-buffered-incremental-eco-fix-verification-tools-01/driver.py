import time,shutil,json
from pathlib import Path
from common import ROOT,execute,sha,write
H=Path(__file__).resolve().parent;out=ROOT/"build/physical/tt-buffered-incremental-eco-fix-verification-01";assert not out.exists();out.mkdir();start=time.monotonic();prior=ROOT/"build/physical/tt-buffered-incremental-eco-route-02";paths=[]
def copy(p,n):
 q=out/n;q.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,q);paths.extend([p,q])
for n in ("runtime_guard.py","verify_native.py","verify_coordinator.py","load.tcl","native_inventory.py","native-script-hashes.json"):copy(H/n,n)
copy(prior/"baseline/routed.odb","postcts.odb");copy(prior/"baseline/after_grt.segments","after_grt.segments")
for n in ("baseline-env.tcl","corner-env.tcl","core.sdc"):copy(prior/n,n)
for p in (prior/"lib").glob("*.lib"):copy(p,"lib/"+p.name)
paths.extend([H/"driver.py",H/"common.py",prior/"report.json"]);report=execute(out,paths,["python3","-B","/work/diagnostic/verify_coordinator.py"],seconds=40,cpus=4,memory="3g",schema="pinwheel-buffered-tt-incremental-eco-fix-verification-v1",scope="Authorized bounded exported-function pin-credit suppression/cache invalidation smoke; retained baseline cold import; no GRT or ECO.",extra={"network":"none","overall_bound_seconds":90})
report["all_in_elapsed_seconds"]=round(time.monotonic()-start,3);write(out/"report.json",report);print(out/"report.json");raise SystemExit(0 if report["status"]=="passed" else 1)
