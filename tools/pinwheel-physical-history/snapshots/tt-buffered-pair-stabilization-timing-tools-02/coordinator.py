import json,os,subprocess
from pathlib import Path
r=Path('/work/diagnostic');p=json.loads((r/'stage-plan.json').read_text());a=p['arm'];assert a == 'stable';env=dict(os.environ,PINWHEEL_TIMING_ROOT=str(r/a));subprocess.run(['python3','-B',str(r/'timing-worker.py')],env=env,cwd=r,check=True);m=json.loads((r/a/'measurement.json').read_text());assert len(m['corners'])==3;m.update(arm=a,native_process_count=3);(r/'measurement.json').write_text(json.dumps(m,indent=2)+'\n')
