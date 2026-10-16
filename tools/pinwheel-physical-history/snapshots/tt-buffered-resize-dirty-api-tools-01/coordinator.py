import os,subprocess,json,hashlib,shutil
from pathlib import Path
from librelane.common import get_script_dir
R=Path('/work/diagnostic');scripts=Path(get_script_dir())
for name,digest in json.loads((R/'native-script-hashes.json').read_text()).items():
 assert hashlib.sha256((scripts/name).read_bytes()).hexdigest()==digest,name
env=dict(os.environ,SCRIPTS_DIR=str(scripts),_TCL_ENV_IN='/work/diagnostic/corner-env.tcl')
with (R/'native.log').open('w') as log:r=subprocess.run(['openroad','-python','-exit','-threads','2','-no_splash','/work/diagnostic/verify.py'],cwd=R,env=env,stdout=log,stderr=subprocess.STDOUT)
assert r.returncode==0,r.returncode
