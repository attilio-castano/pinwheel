"""Freeze host-only sourcebound LIVE route preparation; does not launch CAD."""
import ast,json
from pathlib import Path
from common import ROOT,sha,read,write
H=Path(__file__).resolve().parent;assert not(H/'prepared.json').exists()
intake=ROOT/'build/physical/tt-buffered-incremental-eco-review-01/intake.json';body=read(intake);assert body['status']=='passed'
source=read(H/'plan.json');assert sha(H/'plan.json')=='441228b9b545fd9045f9ef9fa3ae4ec619ac2c656a661d363e0a1d843205f9d5'
inputs=dict(body['custody_sha256']);inputs.update(body['protected_sources_sha256']);inputs[str(intake.relative_to(ROOT))]=sha(intake)
prior=ROOT/'build/physical/tt-buffered-timing-eco-control-route-01'
for p in [ROOT/source['source_database'],*[f for f in prior.iterdir() if f.name in ('baseline-env.tcl','corner-env.tcl','core.sdc','before.v','report.json')],*[f for f in (prior/'lib').glob('*.lib')]]:inputs[str(p.relative_to(ROOT))]=sha(p)
for n,h in inputs.items():assert sha(Path(n) if Path(n).is_absolute() else ROOT/n)==h,n
native={str(f.relative_to(prior/'native-scripts')):sha(f) for f in (prior/'native-scripts').rglob('*.tcl')};native['openroad/common/set_rc.tcl']=read(ROOT/'build/physical/tt-buffered-timing-eco-control-timing-01/inputs.json')['native_script_sha256']['openroad/common/set_rc.tcl'];write(H/'native-script-hashes.json',native)
for p in H.rglob('*.py'):ast.parse(p.read_text())
tools={str(p.relative_to(ROOT)):sha(p) for p in sorted(H.rglob('*')) if p.is_file()}
write(H/'prepared.json',{'schema':'pinwheel-buffered-tt-incremental-eco-prepared-v1','status':'prepared_not_launched','source_sha256':inputs,'tool_sha256':tools,'source_database':source['source_database'],'source_database_sha256':source['source_database_sha256'],'exact_plan_sha256':sha(H/'plan.json'),'same_exact_treatment':True,'native_processes':1,'native_cpus':4,'native_memory':'3g','native_network':'none','native_work_seconds_at_most':300,'all_in_cap_seconds':350,'native_stop_utc':'2026-10-13T17:42:14Z','deadline_utc':'2026-10-13T17:44:14Z','baseline_expected_native_overflow':5226,'original_incident_signal_nets':14,'new_signal_nets':8,'CLOCK_nets_fixed':332,'mandatory_neighbors':0,'boundary':'Hostfreeze only; livebaseline/noopphasegate must pass before sameECO mutation; fixedallCLOCK/unrelatedrouteguard; independentphysical/function/PG/legality gates.'})
print(json.dumps({'prepared_sha256':sha(H/'prepared.json'),'live_sha256':sha(H/'live.py'),'driver_sha256':sha(H/'driver.py'),'tool_files':len(tools),'source_inputs':len(inputs)},indent=2))
