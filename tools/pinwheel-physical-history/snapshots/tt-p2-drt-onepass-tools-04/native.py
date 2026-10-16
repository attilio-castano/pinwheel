"""No-ECO real pin-access/detailed-route probe; detailed wires are measured outputs."""
import datetime,json,hashlib,os,re,shutil,time
from pathlib import Path
from openroad import Tech,Design
from native_inventory import snapshot,sha
R=Path('/work/diagnostic');BOUNDSPATH=Path(os.environ['PW_RUNTIME_BOUNDS_JSON']);BOUNDS=json.loads(BOUNDSPATH.read_text());STOP=BOUNDS['native_stop_epoch'];assert BOUNDS['native_end_iter']==0 and BOUNDS['maximum_actual_search_repair_passes']==1 and time.time()<STOP<=BOUNDS['hard_end_epoch'];tech=Tech();design=Design(tech);started=time.monotonic()
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
def masters_snapshot():
 masters={}
 for inst in design.getBlock().getInsts():
  master=inst.getMaster();name=master.getName()
  if name in masters:continue
  obs=sorted([box.getTechLayer().getName(),[box.xMin(),box.yMin(),box.xMax(),box.yMax()]] for box in master.getObstructions() if box.getTechLayer() is not None)
  terms=[]
  for term in master.getMTerms():
   shapes=sorted([box.getTechLayer().getName(),[box.xMin(),box.yMin(),box.xMax(),box.yMax()]] for p in term.getMPins() for box in p.getGeometry() if box.getTechLayer() is not None)
   terms.append([term.getName(),str(term.getIoType()),str(term.getSigType()),shapes])
  masters[name]={'width':master.getWidth(),'height':master.getHeight(),'type':str(master.getType()),'origin':list(master.getOrigin()),'obstructions':obs,'terminals':sorted(terms)}
 return masters
def via_snapshot():
 db=design.getDb();block=design.getBlock();out={}
 for scope,obj in [('tech',db.getTech()),('block',block)]:
  for via in obj.getVias():
   out[scope+'/'+via.getName()]=sorted([b.getTechLayer().getName(),b.getTechLayer().getRoutingLevel(),[b.xMin(),b.yMin(),b.xMax(),b.yMax()]] for b in via.getBoxes() if b.getTechLayer() is not None)
 return out
def lef_rules_without_vias(phase):
 texts={}
 for f in (R/phase).glob('snapshot-tech-*.lef'):
  text=f.read_text();pat=r'(?ms)^VIA\s+(\S+).*?^END\s+\1\s*$';blocks={v[1]:v[0] for v in re.finditer(pat,text)};remaining=[line for line in re.sub(pat,'',text).splitlines() if line.strip()];assert len(blocks)==len(re.findall(r'^VIA\s',text,re.M));texts[f.name]=(remaining,blocks)
 assert texts;return texts
for n,h in json.loads((R/'phase-inputs.json').read_text()).items():assert sha(Path(n))==h,n
cap=json.loads((R/'capability-admission.json').read_text());assert sha(Path('/proc/self/exe'))==cap['native_binary_sha256'],'Actual loaded native binary differs from fresh capability query'
tcl('source /work/diagnostic/load.tcl');B,BG,BW=inventory('before');BM=masters_snapshot();write(R/'before/master-OBS-signature.json',BM);BV=via_snapshot();BL=lef_rules_without_vias('before');write(R/'before/via-definitions.json',BV);source=json.loads((R/'source-inventory.json').read_text());assert B==source,'Loaded native P2 inventory differs from frozen source';assert len(B['instances'])==28970
assert all(BG[n]>0 for n,v in B['nets'].items() if v['sig_type'] in ('SIGNAL','CLOCK') and len(v['terminals'])+len(v['ports'])>=2),'Connected net guide missing'
tcl('check_placement -verbose\ncheck_power_grid -net VPWR -error_file /work/diagnostic/before/VPWR-grid-errors.rpt\ncheck_power_grid -net VGND -error_file /work/diagnostic/before/VGND-grid-errors.rpt')
write(R/'before-admission.json',{'status':'passed','full_inventory_exact':True,'instance_count':28970,'source_guides_sha256':sha(R/'input.guide'),'connected_signal_and_clock_guides_present':True,'detailed_CLOCK_wires_may_be_new':True,'clock_topology_and_all_masters_locations_frozen':True})
(R/'drt').mkdir();cap=json.loads((R/'capability-admission.json').read_text());assert cap['status']=='passed' and cap['detailed_route_default_pin_access_included'] is True
cmd='detailed_route -droute_end_iter 0 -output_drc /work/diagnostic/drt/violations.rpt -drc_report_iter_step 1 -output_guide_coverage /work/diagnostic/drt/guide-coverage.csv'
write(R/'native-command.json',{'command':cmd,'no_skip_pin_access':True,'no_ECO_or_placement_or_GRT_or_CTS_or_resizer_or_PG_or_OBS_or_capacity_patch':True,'maximum_end_iteration_option':0,'maximum_actual_search_repair_passes':1,'zero_based_iteration_indices':[0],'bound_includes_pin_access_and_all_native_phases':True});print('PINWHEEL_NO_ECO_DRT_PINACCESS_BEGIN',flush=True)
error=tcl(cmd,allow_error=True)
A,AG,AW=inventory('after');AM=masters_snapshot();write(R/'after/master-OBS-signature.json',AM);assert AM==BM,'Original master dimensions/type/origin/OBS/pin geometry changed';AV=via_snapshot();AL=lef_rules_without_vias('after');write(R/'after/via-definitions.json',AV)
assert all(AV.get(n)==v for n,v in BV.items()),'Original technology/block via definition changed'
assert set(AL)==set(BL) and all(AL[n][0]==BL[n][0] and all(AL[n][1].get(v)==d for v,d in BL[n][1].items()) for n in BL),'Original technology rules or via definitions changed'
added_vias={n:v for n,v in AV.items() if n not in BV}
for name,boxes in added_vias.items():
 levels=sorted({v[1] for v in boxes if v[1]>0});assert len(levels)==2 and 1<=levels[0]<levels[1]<=4 and levels[1]-levels[0]==1,(name,'New via outside admitted adjacent M1-M4 layer pair')
 assert len(boxes)>=3 and all(v[2][0]<v[2][2] and v[2][1]<v[2][3] for v in boxes),(name,'Degenerate generated via geometry')
write(R/'after/new-via-audit.json',{'status':'captured','original_via_definitions_exact':True,'all_nonvia_technology_rules_exact':True,'new_generated_vias':added_vias,'new_vias_structurally_adjacent_M1_M4_and_positive_shapes':True,'boundary':'Native generated vias are allowed and recorded; this structural audit does not waive actual detailed-route DRC.'})
exact={k:v for k,v in A.items() if k!='canonical_all_TechLEF_sha256'}=={k:v for k,v in B.items() if k!='canonical_all_TechLEF_sha256'};write(R/'after/scope-proof.json',{'status':'passed' if exact else 'failed','full_native_inventory_exact':exact,'before_inventory_sha256':sha(R/'before/native-inventory.json'),'after_inventory_sha256':sha(R/'after/native-inventory.json'),'netlist_bytes_exact':sha(R/'before/netlist.v')==sha(R/'after/netlist.v'),'input_guides_sha256':sha(R/'input.guide'),'guide_count_changes':sorted(n for n in BG if BG[n]!=AG[n]),'detailed_wires_new_or_changed_permitted':True,'clock_cell_topology_and_NDR_rules_unchanged':exact,'new_generated_via_definition_count':len(added_vias),'original_via_and_technology_rules_preserved':True,'all_used_master_and_OBS_signatures_exact':True,'new_CLOCK_wire_net_count':sum(B['nets'][n]['sig_type']=='CLOCK' and AW[n] and not BW[n] for n in AW)})
assert exact and sha(R/'before/netlist.v')==sha(R/'after/netlist.v'),'DRT changed frozen logical/placement/PG/macro/row/template/NDR scope'
tcl('check_placement -verbose\ncheck_power_grid -net VPWR -error_file /work/diagnostic/after/VPWR-grid-errors.rpt\ncheck_power_grid -net VGND -error_file /work/diagnostic/after/VGND-grid-errors.rpt')
write(R/'measurement.json',{'schema':'pinwheel-no-ECO-P2-DRT-onepass-measurement-v1','status':'measured','native_detailed_route_error':error,'probe_command_returned_without_Tcl_error':error is None,'full_native_inventory_and_signal_netlist_exact':True,'master_placement_clock_topology_rows_macro_PG_NDR_frozen':True,'original_technology_and_via_definitions_exact':True,'all_used_master_and_OBS_signatures_exact':True,'new_generated_via_definition_count':len(added_vias),'source_database_sha256':sha(R/'input.odb'),'source_guides_sha256':sha(R/'input.guide'),'pin_access_included':True,'droute_end_iter_option':0,'maximum_actual_search_repair_passes':1,'detailed_wired_SIGNAL_net_count':sum(B['nets'][n]['sig_type']=='SIGNAL' and AW[n] for n in AW),'detailed_wired_CLOCK_net_count':sum(B['nets'][n]['sig_type']=='CLOCK' and AW[n] for n in AW),'native_elapsed_seconds':round(time.monotonic()-started,3),'DRC_and_pin_failures_must_be_parsed_from_actual_reports':True,'detailed_route_and_signoff_accepted':False,'boundary':'No-ECO bounded physical routing probe. Nonzero DRC/unroutes or native failure are legitimate measurements, not tapeout readiness; CLOCK detailed geometry may be new, clock topology remains exact.'})
print('PINWHEEL_NO_ECO_DRT_PROBE_CAPTURED',flush=True)
if error is not None:raise RuntimeError('Native detailed_route rejected: '+error)
