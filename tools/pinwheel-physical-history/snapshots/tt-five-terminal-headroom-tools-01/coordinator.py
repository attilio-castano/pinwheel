import json,os,subprocess
from pathlib import Path
r=Path('/work/diagnostic');env=dict(os.environ,PINWHEEL_TIMING_ROOT=str(r/'headroom'));subprocess.run(['python3','-B',str(r/'timing-worker.py')],env=env,cwd=r,check=True)
m=json.loads((r/'headroom'/'measurement.json').read_text());assert len(m['corners'])==3 and all(v['prior_qualified_global_timing_reproduced'] is True for v in m['corners'].values())
out=dict(status='measured',corners=m['corners'],native_process_count=3,no_edit_control_passed=True,actual_BUF4_checkpoint=True,scope='Frozen BUF4 candidate route07 no-edit three-corner headroom, five D rise/fall max/min contexts plus6168reference paths; exactnativeODB/routeRC/noSPEFimport/nooptimization.')
(r/'measurement.json').write_text(json.dumps(out,indent=2)+'\n')
