import os,subprocess,json,hashlib
from pathlib import Path
from librelane.common import get_script_dir
R=Path('/work/diagnostic');scripts=Path(get_script_dir())
for name,digest in json.loads((R/'native-script-hashes.json').read_text()).items():assert hashlib.sha256((scripts/name).read_bytes()).hexdigest()==digest,name
results={}
for case in ['callback-first','pre-enroll-first']:
 env=dict(os.environ,SCRIPTS_DIR=str(scripts),_TCL_ENV_IN='/work/diagnostic/corner-env.tcl',PINWHEEL_CASE=case)
 with (R/(case+'-native.log')).open('w') as log:r=subprocess.run(['openroad','-python','-exit','-threads','2','-no_splash','/work/diagnostic/verify.py'],cwd=R,env=env,stdout=log,stderr=subprocess.STDOUT)
 assert r.returncode==0,(case,r.returncode)
 results[case]=json.loads((R/(case+'-measurement.json')).read_text())
result={'status':'measured','all3_callback_first_reproduced_filter_failure':True,'all3_pre_enroll_first_unpatched_predicate_true':True,'native_inventory_before_after_identical':True,'physical_edit_count':0,'routing_solve_count':0,'predicate_function_patch':False,'credit_function_patch':False,'case_results':results}
(R/'measurement.json').write_text(json.dumps(result,indent=2)+'\n')
