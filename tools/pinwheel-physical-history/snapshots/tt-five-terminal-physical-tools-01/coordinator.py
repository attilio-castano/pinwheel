"""Exactly one live native process; no reader/router subprocesses while alive."""
import json,os,subprocess,hashlib,shutil
from pathlib import Path
from librelane.common import get_script_dir
R=Path('/work/diagnostic');scripts=Path(get_script_dir());native=R/'native-scripts';native.mkdir()
expected=json.loads((R/'native-script-hashes.json').read_text())
for name,digest in expected.items():
    p=scripts/name;assert hashlib.sha256(p.read_bytes()).hexdigest()==digest,name
    target=native/name;target.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,target)
env=dict(os.environ,SCRIPTS_DIR=str(scripts),_TCL_ENV_IN='/work/diagnostic/corner-env.tcl')
with (R/'native.log').open('w') as log:
    result=subprocess.run(['openroad','-python','-exit','-threads','4','-no_splash','-metrics','/work/diagnostic/metrics.json','/work/diagnostic/live.py'],cwd=R,env=env,stdout=log,stderr=subprocess.STDOUT)
assert result.returncode==0,('Sole liveOpenROAD failed',result.returncode)
measurement=json.loads((R/'measurement.json').read_text());assert measurement['status']=='measured' and all(measurement[k] for k in ['qualified_stable_P2_reproduction_passed','qualified_buf4_reproduction_passed','matched_noedit_control_passed','candidate_exact_five_additions_passed','native_placement_and_pin_access_legality_passed','native_clock_route_preservation_passed','all_unrelated_route_preservation_passed','native_raw_capacity_preservation_passed','fresh_PSM_both_nets_passed'])
