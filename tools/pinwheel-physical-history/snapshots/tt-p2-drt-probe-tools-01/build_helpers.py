import ast,hashlib,json,shutil
from pathlib import Path
R=Path.cwd();H=Path(__file__).resolve().parent;OLD=R/'build/physical/tt-five-net-stabilization-tools-03';P2=R/'build/physical/tt-five-net-stabilization-route-01/pass2-five';REF=R/'build/physical/tt-buffered-stable-pair4-physical-timing-07/candidate'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_text())
def write(p,v):Path(p).write_text(json.dumps(v,indent=2)+'\n')
assert not(H/'prepared.json').exists()
for name in ['common.py','native_inventory.py','native-script-hashes.json']:shutil.copyfile(OLD/name,H/name)
c=(H/'common.py').read_text();assert 'assert seconds==600' in c;c=c.replace('assert seconds==600','assert seconds==1080');(H/'common.py').write_text(c)
(H/'load.tcl').write_text('''source $::env(SCRIPTS_DIR)/openroad/common/io.tcl
read_current_odb
set_propagated_clock [all_clocks]
read_guides /work/diagnostic/input.guide
''')
(H/'native.py').write_text('''"""No-ECO real pin-access/detailed-route probe; detailed wires are measured outputs."""
import datetime,json,hashlib,os,shutil,time
from pathlib import Path
from openroad import Tech,Design
from native_inventory import snapshot,sha
R=Path('/work/diagnostic');STOP=datetime.datetime.fromisoformat('2026-10-14T18:32:29+00:00').timestamp();tech=Tech();design=Design(tech);started=time.monotonic()
def write(p,v):p.write_text(json.dumps(v,indent=2)+'\\n')
def tcl(cmd,allow_error=False):
 assert time.time()<STOP,'Native absolute stop'
 q='if {[catch {\\n'+cmd+'\\n} msg opts]} {set ::pw_error $msg;set ::pw_status ERROR} else {set ::pw_status OK}'
 status=design.evalTclString(q)
 if status!='OK':
  err=design.evalTclString('set ::pw_error')
  if allow_error:return err
  raise RuntimeError(err)
 return None
def inventory(phase):
 p=R/phase;p.mkdir();tcl(f'write_db {p}/checkpoint.odb\\nwrite_def {p}/checkpoint.def\\nwrite_verilog {p}/netlist.v');v=snapshot(design.getDb(),design.getBlock(),phase+'/snapshot');write(p/'native-inventory.json',v)
 guides={n.getName():len(n.getGuides()) for n in design.getBlock().getNets()};write(p/'guide-counts.json',guides)
 wires={n.getName():bool(n.getWire()) for n in design.getBlock().getNets()};write(p/'detailed-wire-presence.json',wires);return v,guides,wires
for n,h in json.loads((R/'phase-inputs.json').read_text()).items():assert sha(Path(n))==h,n
tcl('source /work/diagnostic/load.tcl');B,BG,BW=inventory('before');source=json.loads((R/'source-inventory.json').read_text());assert B==source,'Loaded native P2 inventory differs from frozen source';assert len(B['instances'])==28970
assert all(BG[n]>0 for n,v in B['nets'].items() if v['sig_type'] in ('SIGNAL','CLOCK') and len(v['terminals'])+len(v['ports'])>=2),'Connected net guide missing'
tcl('check_placement -verbose\\ncheck_power_grid -net VPWR -error_file /work/diagnostic/before/VPWR-grid-errors.rpt\\ncheck_power_grid -net VGND -error_file /work/diagnostic/before/VGND-grid-errors.rpt')
write(R/'before-admission.json',{'status':'passed','full_inventory_exact':True,'instance_count':28970,'source_guides_sha256':sha(R/'input.guide'),'connected_signal_and_clock_guides_present':True,'detailed_CLOCK_wires_may_be_new':True,'clock_topology_and_all_masters_locations_frozen':True})
(R/'drt').mkdir();cap=json.loads((R/'capability-admission.json').read_text());assert cap['status']=='passed' and cap['detailed_route_default_pin_access_included'] is True
cmd='detailed_route -droute_end_iter 3 -output_drc /work/diagnostic/drt/violations.rpt -drc_report_iter_step 1 -output_guide_coverage /work/diagnostic/drt/guide-coverage.csv -bottom_routing_layer Metal2 -top_routing_layer Metal4'
write(R/'native-command.json',{'command':cmd,'no_skip_pin_access':True,'no_ECO_or_placement_or_GRT_or_CTS_or_resizer_or_PG_or_OBS_or_capacity_patch':True,'maximum_end_iteration_option':3,'bound_includes_pin_access_and_all_native_phases':True});print('PINWHEEL_NO_ECO_DRT_PINACCESS_BEGIN',flush=True)
error=tcl(cmd,allow_error=True)
A,AG,AW=inventory('after');exact=A==B;write(R/'after/scope-proof.json',{'status':'passed' if exact else 'failed','full_native_inventory_exact':exact,'before_inventory_sha256':sha(R/'before/native-inventory.json'),'after_inventory_sha256':sha(R/'after/native-inventory.json'),'netlist_bytes_exact':sha(R/'before/netlist.v')==sha(R/'after/netlist.v'),'input_guides_sha256':sha(R/'input.guide'),'guide_count_changes':sorted(n for n in BG if BG[n]!=AG[n]),'detailed_wires_new_or_changed_permitted':True,'clock_cell_topology_and_NDR_rules_unchanged':exact,'new_CLOCK_wire_net_count':sum(B['nets'][n]['sig_type']=='CLOCK' and AW[n] and not BW[n] for n in AW)})
assert exact and sha(R/'before/netlist.v')==sha(R/'after/netlist.v'),'DRT changed frozen logical/placement/PG/macro/row/template/NDR scope'
tcl('check_placement -verbose\\ncheck_power_grid -net VPWR -error_file /work/diagnostic/after/VPWR-grid-errors.rpt\\ncheck_power_grid -net VGND -error_file /work/diagnostic/after/VGND-grid-errors.rpt')
write(R/'measurement.json',{'schema':'pinwheel-no-ECO-P2-DRT-probe-measurement-v1','status':'measured','native_detailed_route_error':error,'probe_command_returned_without_Tcl_error':error is None,'full_native_inventory_and_signal_netlist_exact':True,'master_placement_clock_topology_rows_macro_PG_NDR_frozen':True,'source_database_sha256':sha(R/'input.odb'),'source_guides_sha256':sha(R/'input.guide'),'pin_access_included':True,'droute_end_iter_option':3,'detailed_wired_SIGNAL_net_count':sum(B['nets'][n]['sig_type']=='SIGNAL' and AW[n] for n in AW),'detailed_wired_CLOCK_net_count':sum(B['nets'][n]['sig_type']=='CLOCK' and AW[n] for n in AW),'native_elapsed_seconds':round(time.monotonic()-started,3),'DRC_and_pin_failures_must_be_parsed_from_actual_reports':True,'detailed_route_and_signoff_accepted':False,'boundary':'No-ECO bounded physical routing probe. Nonzero DRC/unroutes or native failure are legitimate measurements, not tapeout readiness; CLOCK detailed geometry may be new, clock topology remains exact.'})
print('PINWHEEL_NO_ECO_DRT_PROBE_CAPTURED',flush=True)
if error is not None:raise RuntimeError('Native detailed_route rejected: '+error)
''')
(H/'coordinator.py').write_text('''import hashlib,json,os,shutil,subprocess
from pathlib import Path
from librelane.common import get_script_dir
R=Path('/work/diagnostic');scripts=Path(get_script_dir())
for n,h in json.loads((R/'native-script-hashes.json').read_text()).items():assert hashlib.sha256((scripts/n).read_bytes()).hexdigest()==h,n
env=dict(os.environ,SCRIPTS_DIR=str(scripts),_TCL_ENV_IN='/work/diagnostic/corner-env.tcl')
with (R/'native.log').open('w') as log:p=subprocess.run(['openroad','-python','-exit','-threads','4','-no_splash','-metrics','/work/diagnostic/metrics.json','/work/diagnostic/native.py'],cwd=R,env=env,stdout=log,stderr=subprocess.STDOUT)
assert p.returncode==0,('Native no-ECO probe failed',p.returncode)
m=json.loads((R/'measurement.json').read_text());assert m['status']=='measured' and m['full_native_inventory_and_signal_netlist_exact']
''')
(H/'driver.py').write_text('''import argparse,datetime,json,shutil,time
from pathlib import Path
from common import ROOT,execute,sha,read,write
H=Path(__file__).resolve().parent;STOP=datetime.datetime.fromisoformat('2026-10-14T18:32:29+00:00').timestamp();END=datetime.datetime.fromisoformat('2026-10-14T18:33:29+00:00').timestamp()
def verify(items):
 for n,h in items.items():assert sha(Path(n))==h,n
def main():
 p=argparse.ArgumentParser();p.add_argument('--capability-report',type=Path,required=True);p.add_argument('--capability-sha256',required=True);p.add_argument('--tag',default='tt-p2-drt-probe-01');a=p.parse_args();started=time.monotonic();P=read(H/'prepared.json');verify(P['source_sha256']);verify(P['tool_sha256']);assert sha(a.capability_report)==a.capability_sha256;C=read(a.capability_report);assert C['status']=='passed' and C['image_id']==P['image_id'] and C['detailed_route_default_pin_access_included'] is True
 assert set(P['required_native_detailed_route_options'])<=set(C['detailed_route_supported_options'])
 assert a.tag=='tt-p2-drt-probe-01' and STOP-time.time()>90;O=ROOT/'build/physical'/a.tag;assert not O.exists();O.mkdir()
 for n in ['common.py','native_inventory.py','native-script-hashes.json','load.tcl','native.py','coordinator.py']:shutil.copyfile(H/n,O/n)
 for original,target in P['staged_inputs'].items():shutil.copyfile(original,O/target)
 shutil.copyfile(a.capability_report,O/'capability-admission.json');shutil.copytree(ROOT/P['reference_root']/'lib',O/'lib')
 write(O/'corner-env.tcl','') if False else None
 (O/'corner-env.tcl').write_text('source /work/diagnostic/baseline-env.tcl\\nset ::env(CURRENT_ODB) /work/diagnostic/input.odb\\nset ::env(_SDC_IN) /work/diagnostic/core.sdc\\nforeach key [array names ::env _LIB_CORNER_*] {unset ::env($key)}\\nset ::env(_LIB_CORNER_0) {nom_typ_1p20V_25C /work/diagnostic/lib/sg13cmos5l_stdcell_typ_1p20V_25C.lib /work/diagnostic/lib/sg13cmos5l_io_typ_1p2V_3p3V_25C.lib /work/diagnostic/lib/RM_IHPSG13_1P_64x64_c2_bm_bist_typ_1p20V_25C.lib}\\nset ::env(OPENROAD_THREADS) 4\\n')
 write(O/'phase-inputs.json',{str(Path('/work/diagnostic')/f.relative_to(O)):sha(f) for f in O.rglob('*') if f.is_file()});paths=[H/'prepared.json',a.capability_report,*map(Path,P['source_sha256']),*map(Path,P['tool_sha256']),*[f for f in O.rglob('*') if f.is_file()]]
 r=execute(O,paths,['python3','-B','/work/diagnostic/coordinator.py'],seconds=1080,cpus=4,memory='6g',schema='pinwheel-no-ECO-P2-DRT-probe-v1',scope='Saved P2 native ODB+guides, actual pin access and at most end_iter3 detailed-routing probe, all original inventory/RTL/ABI/SDC/PG/macros/NDR fixed; detailedCLOCK geometry legitimate.',extra={'source_database_sha256':P['source_database_sha256'],'source_guides_sha256':P['source_guides_sha256'],'prepared_sha256':sha(H/'prepared.json'),'native_capability_admission_sha256':a.capability_sha256},expected_hashes={O/'input.odb':P['source_database_sha256'],O/'input.guide':P['source_guides_sha256']},absolute_work_stop=STOP,all_in_deadline_monotonic=min(started+1140,time.monotonic()+END-time.time()))
 r['all_in_elapsed_seconds']=round(time.monotonic()-started,3);verify(P['source_sha256']);verify(P['tool_sha256']);write(O/'report.json',r);print(O/'report.json',r['status']);return 0 if r['status']=='passed' else 1
if __name__=='__main__':raise SystemExit(main())
''')
for f in H.rglob('*.py'):ast.parse(f.read_text(),filename=str(f))
protected=read(R/'build/physical/tt-five-net-stabilization-root-01/plan.json')['protected_sources_sha256'];staged={str(P2/'routed.odb'):'input.odb',str(P2/'after_grt.guide'):'input.guide',str(P2/'native-inventory.json'):'source-inventory.json',str(REF/'baseline-env.tcl'):'baseline-env.tcl',str(REF/'core.sdc'):'core.sdc'}
sources={str(R/n):h for n,h in protected.items()};sources.update({n:sha(n) for n in staged});sources.update({str(f):sha(f) for f in (REF/'lib').iterdir() if f.is_file()});sources[str(P2.parent/'report.json')]=sha(P2.parent/'report.json')
plan=R/'build/physical/tt-p2-drt-probe-root-01/plan.json'
if plan.exists():sources[str(plan)]=sha(plan)
P={'schema':'pinwheel-no-ECO-P2-DRT-probe-prepared-v1','status':'prepared_not_launched','image_id':'sha256:5825633bea1f9cbc705ece2de2bc31de6e4ec83d233739205a0f265ef9d92f92','source_database_sha256':sha(P2/'routed.odb'),'source_guides_sha256':sha(P2/'after_grt.guide'),'source_inventory_sha256':sha(P2/'native-inventory.json'),'source_sha256':sources,'staged_inputs':staged,'reference_root':str(REF.relative_to(R)),'required_native_detailed_route_options':['-droute_end_iter','-output_drc','-drc_report_iter_step','-output_guide_coverage','-bottom_routing_layer','-top_routing_layer'],'clock_topology_frozen_detailed_CLOCK_geometry_permitted':True,'native_stop_utc':'2026-10-14T18:32:29Z','phase_deadline_utc':'2026-10-14T18:33:29Z','hard_deadline_utc':'2026-10-14T18:35:29Z','native_phase_seconds_at_most':1080,'all_in_seconds_at_most':1140,'cpus':4,'memory':'6g','no_GRT_CTS_GPL_resizer_newcells_PG_OBS_or_capacity_patch':True,'pin_access_included':True,'droute_end_iter':3}
P['tool_sha256']={str(f.resolve()):sha(f) for f in H.rglob('*') if f.is_file() and f.name!='prepared.json' and '__pycache__' not in f.parts};write(H/'prepared.json',P);print(sha(H/'prepared.json'),sha(H/'common.py'),len(sources))
