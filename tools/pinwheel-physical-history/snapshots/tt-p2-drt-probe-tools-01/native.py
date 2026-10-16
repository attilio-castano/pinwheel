"""No-ECO real pin-access/detailed-route probe; detailed wires are measured outputs."""
import datetime,json,hashlib,os,shutil,time
from pathlib import Path
from openroad import Tech,Design
from native_inventory import snapshot,sha
R=Path('/work/diagnostic');STOP=datetime.datetime.fromisoformat('2026-10-14T18:32:29+00:00').timestamp();tech=Tech();design=Design(tech);started=time.monotonic()
def write(p,v):p.write_text(json.dumps(v,indent=2)+'\n')
def tcl(cmd,allow_error=False):
 assert time.time()<STOP,'Native absolute stop'
 q='if {[catch {\n'+cmd+'\n} msg opts]} {set ::pw_error $msg;set ::pw_status ERROR} else {set ::pw_status OK}'
 status=design.evalTclString(q)
 if status!='OK':
  err=design.evalTclString('set ::pw_error')
  if allow_error:return err
  raise RuntimeError(err)
 return None
def inventory(phase):
 p=R/phase;p.mkdir();tcl(f'write_db {p}/checkpoint.odb\nwrite_def {p}/checkpoint.def\nwrite_verilog {p}/netlist.v');v=snapshot(design.getDb(),design.getBlock(),phase+'/snapshot');write(p/'native-inventory.json',v)
 guides={n.getName():len(n.getGuides()) for n in design.getBlock().getNets()};write(p/'guide-counts.json',guides)
 wires={n.getName():bool(n.getWire()) for n in design.getBlock().getNets()};write(p/'detailed-wire-presence.json',wires);return v,guides,wires
for n,h in json.loads((R/'phase-inputs.json').read_text()).items():assert sha(Path(n))==h,n
tcl('source /work/diagnostic/load.tcl');B,BG,BW=inventory('before');source=json.loads((R/'source-inventory.json').read_text());assert B==source,'Loaded native P2 inventory differs from frozen source';assert len(B['instances'])==28970
assert all(BG[n]>0 for n,v in B['nets'].items() if v['sig_type'] in ('SIGNAL','CLOCK') and len(v['terminals'])+len(v['ports'])>=2),'Connected net guide missing'
tcl('check_placement -verbose\ncheck_power_grid -net VPWR -error_file /work/diagnostic/before/VPWR-grid-errors.rpt\ncheck_power_grid -net VGND -error_file /work/diagnostic/before/VGND-grid-errors.rpt')
write(R/'before-admission.json',{'status':'passed','full_inventory_exact':True,'instance_count':28970,'source_guides_sha256':sha(R/'input.guide'),'connected_signal_and_clock_guides_present':True,'detailed_CLOCK_wires_may_be_new':True,'clock_topology_and_all_masters_locations_frozen':True})
(R/'drt').mkdir();cap=json.loads((R/'capability-admission.json').read_text());assert cap['status']=='passed' and cap['detailed_route_default_pin_access_included'] is True
cmd='detailed_route -droute_end_iter 3 -output_drc /work/diagnostic/drt/violations.rpt -drc_report_iter_step 1 -output_guide_coverage /work/diagnostic/drt/guide-coverage.csv -bottom_routing_layer Metal2 -top_routing_layer Metal4'
write(R/'native-command.json',{'command':cmd,'no_skip_pin_access':True,'no_ECO_or_placement_or_GRT_or_CTS_or_resizer_or_PG_or_OBS_or_capacity_patch':True,'maximum_end_iteration_option':3,'bound_includes_pin_access_and_all_native_phases':True});print('PINWHEEL_NO_ECO_DRT_PINACCESS_BEGIN',flush=True)
error=tcl(cmd,allow_error=True)
A,AG,AW=inventory('after');exact=A==B;write(R/'after/scope-proof.json',{'status':'passed' if exact else 'failed','full_native_inventory_exact':exact,'before_inventory_sha256':sha(R/'before/native-inventory.json'),'after_inventory_sha256':sha(R/'after/native-inventory.json'),'netlist_bytes_exact':sha(R/'before/netlist.v')==sha(R/'after/netlist.v'),'input_guides_sha256':sha(R/'input.guide'),'guide_count_changes':sorted(n for n in BG if BG[n]!=AG[n]),'detailed_wires_new_or_changed_permitted':True,'clock_cell_topology_and_NDR_rules_unchanged':exact,'new_CLOCK_wire_net_count':sum(B['nets'][n]['sig_type']=='CLOCK' and AW[n] and not BW[n] for n in AW)})
assert exact and sha(R/'before/netlist.v')==sha(R/'after/netlist.v'),'DRT changed frozen logical/placement/PG/macro/row/template/NDR scope'
tcl('check_placement -verbose\ncheck_power_grid -net VPWR -error_file /work/diagnostic/after/VPWR-grid-errors.rpt\ncheck_power_grid -net VGND -error_file /work/diagnostic/after/VGND-grid-errors.rpt')
write(R/'measurement.json',{'schema':'pinwheel-no-ECO-P2-DRT-probe-measurement-v1','status':'measured','native_detailed_route_error':error,'probe_command_returned_without_Tcl_error':error is None,'full_native_inventory_and_signal_netlist_exact':True,'master_placement_clock_topology_rows_macro_PG_NDR_frozen':True,'source_database_sha256':sha(R/'input.odb'),'source_guides_sha256':sha(R/'input.guide'),'pin_access_included':True,'droute_end_iter_option':3,'detailed_wired_SIGNAL_net_count':sum(B['nets'][n]['sig_type']=='SIGNAL' and AW[n] for n in AW),'detailed_wired_CLOCK_net_count':sum(B['nets'][n]['sig_type']=='CLOCK' and AW[n] for n in AW),'native_elapsed_seconds':round(time.monotonic()-started,3),'DRC_and_pin_failures_must_be_parsed_from_actual_reports':True,'detailed_route_and_signoff_accepted':False,'boundary':'No-ECO bounded physical routing probe. Nonzero DRC/unroutes or native failure are legitimate measurements, not tapeout readiness; CLOCK detailed geometry may be new, clock topology remains exact.'})
print('PINWHEEL_NO_ECO_DRT_PROBE_CAPTURED',flush=True)
if error is not None:raise RuntimeError('Native detailed_route rejected: '+error)
