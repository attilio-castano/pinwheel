"""Freeze exact ECO tools and source custody without native execution."""
import ast,json
from pathlib import Path
from common import ROOT,sha,read,write
H=Path(__file__).resolve().parent
assert not(H/'prepared.json').exists(),'Immutable preparation'
plan=read(H/'plan.json');controls=read(H/'structural-controls.json');assert controls['status']=='passed' and controls['controls_passed']==10
assert sha(H/'plan.json')=='441228b9b545fd9045f9ef9fa3ae4ec619ac2c656a661d363e0a1d843205f9d5'
intake=ROOT/'build/physical/tt-buffered-timing-eco-review-01/intake.json';body=read(intake);assert body['status']=='passed'
original=dict(body['custody_sha256']);original.update(body['protected_sources_sha256'])
for p in [intake,ROOT/plan['source_database'],ROOT/plan['source_original_state'],ROOT/plan['source_native_inventory']]:original[str(p.relative_to(ROOT))]=sha(p)
for c,v in plan['liberty'].items():original[v['path']]=v['sha256']
for n,d in read(H/'identity-source.json').items():original[n]=d
for n,d in original.items():
    p=Path(n) if Path(n).is_absolute() else ROOT/n;assert p.is_file() and sha(p)==d,n
for p in H.rglob('*.py'):ast.parse(p.read_text())
tools={str(p.relative_to(ROOT)):sha(p) for p in sorted(H.rglob('*')) if p.is_file()}
write(H/'prepared.json',{'schema':'pinwheel-buffered-tt-timing-eco-prepared-v1','status':'prepared_not_launched','source_sha256':original,'tool_sha256':tools,'source_database_sha256':plan['source_database_sha256'],'plan_sha256':sha(H/'plan.json'),'host_controls_sha256':sha(H/'structural-controls.json'),'all_in_cap_seconds':120,'native_work_seconds_at_most':65,'cleanup_reserve_seconds':50,'host_hash_reserve_seconds':5,'cpus':1,'memory':'1g','network':'none','exact_resizes':2,'added_identity_delay_cells':8,'selected_D_rewires':8,'mandatory_neighbors':0,'root_headroom_required':True,'native_optimization_commands':plan['optimization_commands'],'boundary':'Host-only sourcefreeze; actual native exactedit/legality/PG/functionidentity must pass before separate native route and3cornerRCtiming.'})
print(json.dumps({'prepared_sha256':sha(H/'prepared.json'),'driver_sha256':sha(H/'driver.py'),'gate_sha256':sha(H/'gate.py'),'edit_tcl_sha256':sha(H/'edit.tcl'),'tool_files':len(tools),'original_inputs':len(original)},indent=2))
