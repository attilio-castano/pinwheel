"""One exact database edit, legal/PG checks and serialized inventory proof."""
import json,os,subprocess
from pathlib import Path
ROOT=Path('/work/diagnostic')
for phase,command in [('before',['openroad','-python','-exit','/work/diagnostic/gate.py']),('edit',['openroad','-exit','-threads','1','/work/diagnostic/edit.tcl']),('after',['openroad','-python','-exit','/work/diagnostic/gate.py'])]:
    with (ROOT/(phase+'.log')).open('w') as log:
        env=dict(os.environ);env['PINWHEEL_INVENTORY_PHASE']=phase
        r=subprocess.run(command,cwd=ROOT,stdout=log,stderr=subprocess.STDOUT,env=env)
    assert r.returncode==0,(phase,r.returncode)
proof=json.loads((ROOT/'change-proof.json').read_text());assert proof['exact_edit_gate_passed']
log=(ROOT/'edit.log').read_text();pg={n:'All shapes on net '+n+' are connected.' in log for n in ('VPWR','VGND')};assert all(pg.values())
(ROOT/'measurement.json').write_text(json.dumps({'status':'measured','exact_edit_gate_passed':True,'change_proof':proof,'power_grid_all_shapes_connected':pg,'native_check_placement_passed':True,'boundary':'Exactly8identityDdelaystages+2samefunctionresizes; no timing/routing qualification yet.'},indent=2)+'\n')
