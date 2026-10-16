import hashlib,json,os,shutil,subprocess
from pathlib import Path
from librelane.common import get_script_dir
R=Path('/work/diagnostic');scripts=Path(get_script_dir())
for n,h in json.loads((R/'native-script-hashes.json').read_text()).items():assert hashlib.sha256((scripts/n).read_bytes()).hexdigest()==h,n
env=dict(os.environ,SCRIPTS_DIR=str(scripts),_TCL_ENV_IN='/work/diagnostic/corner-env.tcl')
with (R/'native.log').open('w') as log:p=subprocess.run(['openroad','-python','-exit','-threads','4','-no_splash','-metrics','/work/diagnostic/metrics.json','/work/diagnostic/native.py'],cwd=R,env=env,stdout=log,stderr=subprocess.STDOUT)
assert p.returncode==0,('Native no-ECO probe failed',p.returncode)
m=json.loads((R/'measurement.json').read_text());assert m['status']=='measured' and m['full_native_inventory_and_signal_netlist_exact']
