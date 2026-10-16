import json,os,subprocess
from pathlib import Path
root=Path('/work/diagnostic');plan=json.loads((root/'stage-plan.json').read_text());assert plan['stages']==['preflight']
env=dict(os.environ,PINWHEEL_TIMING_ROOT=str(root/'preflight'));subprocess.run(['python3','-B',str(root/'timing-worker.py')],env=env,cwd=root,check=True)
m=json.loads((root/'preflight/measurement.json').read_text());assert len(m['corners'])==3;m['native_process_count']=3;(root/'measurement.json').write_text(json.dumps(m,indent=2)+'\n')
