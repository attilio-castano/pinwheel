import time,shutil
from pathlib import Path
from common import ROOT,execute,sha,write
H=Path(__file__).resolve().parent;out=ROOT/"build/physical/tt-buffered-incremental-eco-capability-01";assert not out.exists();out.mkdir();start=time.monotonic();shutil.copyfile(H/"native.py",out/"native.py")
report=execute(out,[H/"driver.py",H/"common.py",H/"native.py",out/"native.py"],["openroad","-python","-exit","-no_splash","/work/diagnostic/native.py"],seconds=40,cpus=4,memory="3g",schema="pinwheel-buffered-tt-incremental-eco-idempotence-capability-v1",scope="One authorized offline capability preflight: native public APIs, compiled symbols/compiler availability only; no loadeddesign/noGRT/noECO.",extra={"network":"none","overall_bound_seconds":90})
report["all_in_elapsed_seconds"]=round(time.monotonic()-start,3);write(out/"report.json",report);print(out/"report.json");raise SystemExit(0 if report["status"]=="passed" else 1)
