"""One arm, three fresh corner processes; never routing or optimization."""
import json, os, subprocess
from pathlib import Path
root = Path('/work/diagnostic')
plan = json.loads((root/'stage-plan.json').read_text())
assert plan['arm'] in ('control', 'candidate')
assert plan['stages'] == [plan['arm']]
environment = dict(os.environ, PINWHEEL_TIMING_ROOT=str(root/plan['arm']))
subprocess.run(['python3','-B',str(root/'timing-worker.py')],env=environment,cwd=root,check=True)
measurement = json.loads((root/plan['arm']/'measurement.json').read_text())
assert len(measurement['corners']) == 3
measurement.update(arm=plan['arm'],native_process_count=3,
    fresh_computational_control=plan['arm']=='control',
    producer_report_sha256=plan['producer_report_sha256'],
    operation='Three fresh saved-global-route RC processes with full global STA/electrical reports and explicit30712 max/min; no routing, placement or optimization.')
(root/'measurement.json').write_text(json.dumps(measurement,indent=2)+'\n')
