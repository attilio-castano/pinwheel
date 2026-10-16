import os,subprocess,hashlib,json
from pathlib import Path
from librelane.common import get_script_dir
R=Path('/work/diagnostic');scripts=Path(get_script_dir());expected=json.loads((R/'native-script-hashes.json').read_text())
for n,h in expected.items():assert hashlib.sha256((scripts/n).read_bytes()).hexdigest()==h,n
env=dict(os.environ,SCRIPTS_DIR=str(scripts),_TCL_ENV_IN='/work/diagnostic/corner-env.tcl')
with (R/'native.log').open('w') as log:r=subprocess.run(['openroad','-python','-exit','-threads','4','-no_splash','/work/diagnostic/verify_native.py'],cwd=R,env=env,stdout=log,stderr=subprocess.STDOUT)
assert r.returncode==0,r.returncode
