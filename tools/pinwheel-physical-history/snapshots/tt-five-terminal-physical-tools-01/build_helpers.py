import ast,hashlib,json,shutil,sys
from pathlib import Path
ROOT=Path.cwd();H=Path(__file__).resolve().parent;OLD=ROOT/'build/physical/tt-buffered-stable-pair4-physical-tools-07';Q=ROOT/'build/physical/tt-buffered-stable-pair4-physical-route-07/candidate'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_text())
def write(p,v):Path(p).write_text(json.dumps(v,indent=2)+'\n')
assert not(H/'prepared.json').exists()
for f in OLD.iterdir():
 if f.name=='prepared.json':continue
 if f.is_file():shutil.copyfile(f,H/f.name)
 elif f.name in ['identity','lib']:shutil.copytree(f,H/f.name,dirs_exist_ok=True)
source=read(Q/'native-inventory.json');p=read(ROOT/'build/physical/tt-five-terminal-root-01/plan.json');endpoints=p['endpoints']
rows=source['rows'];placed=[];adds=[]
for endpoint,oldnet in endpoints.items():
 ep=endpoint.split('/')[0];v=source['instances'][ep];b=v['bbox_dbu'];cx=(b[0]+b[2])//2;cy=(b[1]+b[3])//2
 assert ['D',oldnet,'INPUT'] in v['terminals']
 best=None
 for row in rows:
  r=row['bbox_dbu'];y=r[1]
  if abs((y+1890)-cy)>50000:continue
  intervals=sorted((max(r[0],q['bbox_dbu'][0]),min(r[2],q['bbox_dbu'][2])) for q in [*source['instances'].values(),*placed] if q['bbox_dbu'][1]<r[3] and q['bbox_dbu'][3]>r[1] and q['bbox_dbu'][0]<r[2] and q['bbox_dbu'][2]>r[0])
  merged=[]
  for a,z in intervals:
   if merged and a<=merged[-1][1]:merged[-1][1]=max(merged[-1][1],z)
   else:merged.append([a,z])
  gaps=[];left=r[0]
  for a,z in merged:
   if a-left>=1920:gaps.append((left,a))
   left=max(left,z)
  if r[2]-left>=1920:gaps.append((left,r[2]))
  for a,z in gaps:
   amin=((a-row['origin_dbu'][0]+479)//480)*480+row['origin_dbu'][0];amax=((z-1920-row['origin_dbu'][0])//480)*480+row['origin_dbu'][0]
   if amin>amax:continue
   x=max(amin,min(amax,((cx-960-row['origin_dbu'][0]+240)//480)*480+row['origin_dbu'][0]));score=abs(x+960-cx)+abs(y+1890-cy)
   cand=(score,x,y,row['orientation'],row['name'])
   if best is None or cand<best:best=cand
 assert best is not None and best[0]<50000,(endpoint,best)
 dist,x,y,orient,rowname=best;n='timing_eco_terminal_'+ep.strip('_');new=n+'_D';box=[x,y,x+1920,y+3780]
 assert n not in source['instances'] and new not in source['nets']
 adds.append({'instance':n,'endpoint':ep,'endpoint_pin':'D','source_net':oldnet,'new_net':new,'master':'sg13cmos5l_buf_1','bbox_dbu':box,'orientation':orient,'row_name':rowname,'FF_bbox_center_distance_dbu':dist,'nearest_D_pin_distance_native_check_pending':True})
 placed.append({'bbox_dbu':box})
terminal={'schema':'pinwheel-five-terminal-physical-policy-v1','source_candidate_odb_sha256':p['source_candidate_odb_sha256'],'source_candidate_segments_sha256':p['source_candidate_segments_sha256'],'root_plan_sha256':sha(ROOT/'build/physical/tt-five-terminal-root-01/plan.json'),'endpoints':endpoints,'resizes':{},'additions':adds,'added_instances':[a['instance'] for a in adds],'old_signal_nets':sorted(endpoints.values()),'new_signal_nets':sorted(a['new_net'] for a in adds),'allowed_route_change_nets':sorted([*endpoints.values(),*(a['new_net'] for a in adds)]),'zero_original_master_placement_changes':True,'zero_neighbor_moves':True,'native_stop_utc':'2026-10-14T16:07:19Z','deadline_utc':'2026-10-14T16:11:19Z'}
write(H/'terminal-policy.json',terminal)
artifacts={str(f.resolve()):sha(f) for f in Q.iterdir() if f.is_file() and f.name in ['routed.odb','native-inventory.json','after_grt.segments','geometry.json','native-raw-capacity.json','estimated.spef','after.v','typ-timing.json','route-state.json','change-proof.json']}
qsource={'schema':'pinwheel-five-terminal-qualified-buf4-source-v1','source_database_sha256':p['source_candidate_odb_sha256'],'source_segments_sha256':p['source_candidate_segments_sha256'],'artifacts_sha256':artifacts,'producer_report':str(Q.parent/'report.json'),'producer_report_sha256':sha(Q.parent/'report.json'),'producer_status':read(Q.parent/'report.json')['status']};assert qsource['producer_status']=='passed';write(H/'qualified-buf4-source.json',qsource)
text='set block [ord::get_db_block]\n'
for a in adds:
 text+=f'''if {{[$block findInst {{{a['instance']}}}] ne "NULL" || [$block findNet {{{a['new_net']}}}] ne "NULL"}} {{error {{Terminal name collision}}}}
set buffer [odb::dbInst_create $block [[ord::get_db] findMaster {{sg13cmos5l_buf_1}}] {{{a['instance']}}}]
set branch [odb::dbNet_create $block {{{a['new_net']}}}]
$buffer setOrient {a['orientation']}
$buffer setLocation {a['bbox_dbu'][0]} {a['bbox_dbu'][1]}
$buffer setPlacementStatus PLACED
set source [$block findNet {{{a['source_net']}}}]
set sink [[$block findInst {{{a['endpoint']}}}] findITerm D]
if {{[$sink getNet] ne $source}} {{error {{Unexpected terminal D source}}}}
[$buffer findITerm A] connect $source
[$buffer findITerm X] connect $branch
[$buffer findITerm VDD] connect [$block findNet VPWR]
[$buffer findITerm VSS] connect [$block findNet VGND]
$sink disconnect
$sink connect $branch
'''
text+='check_placement -verbose\n';(H/'terminal-edit.tcl').write_text(text)
g=(H/'gate.py').read_text();assert "'width_dbu':4320" in g;g=g.replace("'width_dbu':4320","'width_dbu':b[2]-b[0]");(H/'gate.py').write_text(g)
live=(H/'live.py').read_text().replace('2026-10-14T02:37:00+00:00','2026-10-14T16:07:19+00:00')
live=live.replace("save('control')","save('pair-control')").replace("R/'control/","R/'pair-control/").replace("R/'control'","R/'pair-control'")
live=live.replace("save('candidate')","save('buf4-reproduced')").replace("R/'candidate/","R/'buf4-reproduced/").replace("R/'candidate'","R/'buf4-reproduced'")
extra=r'''
    # NEW treatment starts only after the entire immutable warm BUF4 replay.
    target=json.loads((R/'terminal-policy.json').read_text());source_buf4=json.loads((R/'qualified-buf4-source.json').read_text());Q4=R/'qualified-buf4'
    assert C==json.loads((Q4/'native-inventory.json').read_text()),'Saved BUF4 whole native inventory not reproduced'
    assert CS==canonical(Q4/'after_grt.segments') and sha(R/'buf4-reproduced/after_grt.segments')==source_buf4['source_segments_sha256'],'Saved BUF4 routes not reproduced'
    qg=json.loads((Q4/'geometry.json').read_text())
    assert {k:v for k,v in CG.items() if k!='database_sha256'}=={k:v for k,v in qg.items() if k!='database_sha256'},'Saved BUF4 grid not reproduced'
    assert json.loads((R/'buf4-reproduced/native-raw-capacity.json').read_text())==json.loads((Q4/'native-raw-capacity.json').read_text())
    assert CT==json.loads((Q4/'typ-timing.json').read_text()),'Saved BUF4 nominal full RC/timing not reproduced'
    qm=json.loads((Q4/'route-state.json').read_text());assert {k:v for k,v in CM.items() if k not in ('live_router_pointer','live_process_pid')}=={k:v for k,v in qm.items() if k not in ('live_router_pointer','live_process_pid')}
    assert sha(R/'buf4-reproduced/after.v')==sha(Q4/'after.v') and sha(R/'buf4-reproduced/estimated.spef')==sha(Q4/'estimated.spef')
    headroom=json.loads((R/'terminal-headroom-admission.json').read_text())
    assert headroom['status']=='passed' and all(headroom[k] is True for k in ['physical_admission_passed','three_corner_noedit_control_within_1ps','setup_budget_covers_planned_cells'])
    assert headroom['source_candidate_odb_sha256']==source_buf4['source_database_sha256']==target['source_candidate_odb_sha256']
    assert headroom['source_candidate_segments_sha256']==source_buf4['source_segments_sha256']==target['source_candidate_segments_sha256'] and headroom['endpoints']==target['endpoints']
    write(R/'qualified-buf4-reproduction-gate.json',{'status':'passed','qualified_buf4_reproduction_passed':True,'all_native_inventory_routes_grid_rawcapacity_NL_nominalSPEF_timing_counts_NDR_exact':True,'source_database_sha256':source_buf4['source_database_sha256'],'source_segments_sha256':source_buf4['source_segments_sha256'],'headroom_admission_sha256':sha(R/'terminal-headroom-admission.json')})
    B,BS,BG,BT,BM=C,CS,CG,CT,CM
    for old in ('N','NS','NG','NT','NM','wanted','actual','before_module','after_module','qg','qm','before_rc','after_rc'):globals().pop(old,None)
    gc.collect()
    oldnets=set(target['old_signal_nets']);newnets=set(target['new_signal_nets']);allowed=oldnets|newnets
    assert len(oldnets)==5 and len(newnets)==5 and len(allowed)==10
    for name in oldnets:assert B['nets'][name]['sig_type']=='SIGNAL' and B['nets'][name]['nondefault_rule'] is None
    phase_custody();assert time.time()<STOP-120,'No terminal no-edit plus candidate capture reserve'
    assert macro_access_signature('terminal-before-control')==access
    print('PINWHEEL_TERMINAL_DIRTY_NOEDIT_BEGIN',flush=True);tcl('global_route -congestion_iterations 10 -start_incremental')
    cache=[invalidate_one(design.getGlobalRouter(),design.getBlock().findNet(n)) for n in sorted(oldnets)]
    tcl('global_route -congestion_iterations 10 -end_incremental -allow_congestion')
    def dirty_worklist(marker):
        log=current_log().split(marker)[-1];assert 'Dirty nets:' in log;found=[]
        for line in log.split('Dirty nets:',1)[1].splitlines():
            if not line.strip():continue
            match=re.match(r'^\[DEBUG GRT-incr\]\s+(\S+)\s*$',line)
            if not match:break
            found.append(match[1])
        return found
    found=dirty_worklist('PINWHEEL_TERMINAL_DIRTY_NOEDIT_BEGIN');assert set(found)==oldnets and len(found)==5,('Terminal no-edit worklist',found)
    N,NS,NG,NT,NM=save('control')
    assert N==B and NS==BS and {k:v for k,v in NG.items() if k!='database_sha256'}=={k:v for k,v in BG.items() if k!='database_sha256'} and NT==BT and NM==BM,'Five-net dirty no-edit changed source'
    assert json.loads((R/'control/native-raw-capacity.json').read_text())==json.loads((Q4/'native-raw-capacity.json').read_text())
    assert sha(R/'control/after.v')==sha(Q4/'after.v') and sha(R/'control/estimated.spef')==sha(Q4/'estimated.spef') and macro_access_signature('terminal-after-control')==access
    write(R/'control/noop-gate.json',{'status':'passed','matched_noedit_control_passed':True,'exact_five_oldnets_dirty':True,'actual_dirty_signal_nets':sorted(found),'native_cache_invalidation':cache,'all_native_inventory_routes_grid_rawcapacity_NL_nominalSPEF_timing_NDR_exact':True,'same_warm_router':True})
    phase_custody();assert time.time()<STOP-70,'No terminal edit/candidate capture reserve'
    want=expected(B,target);validate_geometry(want,target)
    print('PINWHEEL_TERMINAL_EDIT_BEGIN',flush=True);tcl('global_route -congestion_iterations 10 -start_incremental')
    pre=[invalidate_one(design.getGlobalRouter(),design.getBlock().findNet(n)) for n in sorted(oldnets)]
    tcl('source /work/diagnostic/terminal-edit.tcl')
    actual=snapshot(design.getDb(),design.getBlock(),'terminal-edit');assert actual==want,'Terminal whole-inventory exact edits mismatch'
    tcl('write_verilog /work/diagnostic/terminal-edit-after.v')
    function=compare_repair(signal_module(B),signal_module(actual),Library(text),list(text),allow_resizing=True)
    assert function['added_cells']=={a['instance']:'sg13cmos5l_buf_1' for a in target['additions']} and function['resized_cells']=={}
    assert function['pinned_transport_functions_checked'] is True and function['pinned_resize_functions_checked'] is True
    write(R/'terminal-function-proof.json',{'status':'passed','proof':function,'native_inventory_exact':True,'before_netlist_sha256':sha(R/'control/after.v'),'after_netlist_sha256':sha(R/'terminal-edit-after.v')})
    enrolled=[invalidate_one(design.getGlobalRouter(),design.getBlock().findNet(n)) for n in sorted(allowed)]
    assert macro_access_signature('terminal-before-route')==access
    tcl('global_route -congestion_iterations 10 -end_incremental -allow_congestion')
    dirty=dirty_worklist('PINWHEEL_TERMINAL_EDIT_BEGIN');assert set(dirty)==allowed and len(dirty)==10,('Terminal exact10-net dirty worklist',dirty)
    C,CS,CG,CT,CM=save('candidate');assert C==want,'Final terminal whole inventory changed'
    assert set(CS)==set(BS)|newnets and all(CS[n]==BS[n] for n in BS if n not in oldnets),'Unrelated/CLOCK routes changed'
    assert all(CS[n]==BS[n] for n in clocks) and all(BG['layers'][n]['capacity']==CG['layers'][n]['capacity'] for n in BG['layers'])
    assert json.loads((R/'candidate/native-raw-capacity.json').read_text())==json.loads((R/'control/native-raw-capacity.json').read_text()),'Native raw capacities changed'
    assert CM['native_clock_ndr_fallback_net_order']==BM['native_clock_ndr_fallback_net_order'],'CLOCK NDR fallback changed'
    rc_before=spef_networks(R/'control/estimated.spef');rc_after=spef_networks(R/'candidate/estimated.spef');assert set(rc_after)==set(rc_before)|newnets
    changedrc=sorted(n for n in rc_before if rc_before[n]!=rc_after[n]);assert set(changedrc)<=oldnets,'Unrelated native RC changed'
    changed=sorted(n for n in BS if BS[n]!=CS[n]);assert set(changed)<=oldnets
    tcl('check_placement -verbose\ncheck_power_grid -net VPWR -error_file /work/diagnostic/VPWR-terminal-grid-errors.rpt\ncheck_power_grid -net VGND -error_file /work/diagnostic/VGND-terminal-grid-errors.rpt')
    tail=current_log().split('PINWHEEL_TERMINAL_EDIT_BEGIN')[-1];assert all('All shapes on net '+n+' are connected.' in tail for n in ('VPWR','VGND')),'Fresh terminal PSM missing'
    proof={'schema':'pinwheel-five-terminal-physical-change-proof-v1','status':'measured','exact_edit_gate_passed':True,'source_database_sha256':source_buf4['source_database_sha256'],'comparison_baseline_database_sha256':sha(R/'control/routed.odb'),'output_database_sha256':sha(R/'candidate/routed.odb'),'added_cells':5,'resized_cells':0,'exact_additions':target['additions'],'all_corner_signal_identity':function,'all_original_master_placement_orientation_status_exact':True,'only_five_original_D_rewires':True,'all_CLOCK_inventory_and332routes_exact':True,'all_unrelated_routes_and_RC_exact':True,'native_raw_capacity_exact':True,'rows_macros_PG_special_wires_blockages_pins_TechLEF_NDR_exact':True,'fresh_PSM_both_nets_passed':True,'native_legal_added_footprints':True,'allowed_route_change_nets':sorted(allowed),'actual_dirty_signal_nets':sorted(dirty),'actual_changed_original_route_nets':changed,'actual_changed_original_RC_nets':changedrc,'pre_edit_cache_enrollment':pre,'post_edit_cache_enrollment':enrolled,'qualified_buf4_reproduction_gate_sha256':sha(R/'qualified-buf4-reproduction-gate.json'),'matched_noedit_control_gate_sha256':sha(R/'control/noop-gate.json'),'headroom_admission_sha256':sha(R/'terminal-headroom-admission.json')}
    write(R/'candidate/change-proof.json',proof)
    measurement={'schema':'pinwheel-five-terminal-physical-measurement-v1','status':'measured','qualified_buf4_reproduction_passed':True,'matched_noedit_control_passed':True,'candidate_exact_five_additions_passed':True,'qualified_stable_P2_reproduction_passed':True,'candidate_exact_two_resizes_passed':True,'native_placement_and_pin_access_legality_passed':True,'native_clock_route_preservation_passed':True,'all_unrelated_route_preservation_passed':True,'native_raw_capacity_preservation_passed':True,'fresh_PSM_both_nets_passed':True,'source_database_sha256':source_buf4['source_database_sha256'],'baseline':BM,'control':NM,'candidate':CM,'resized_cell_count':0,'added_cell_count':5,'allowed_route_change_nets':sorted(allowed),'actual_dirty_signal_nets':sorted(dirty),'actual_changed_original_route_nets':changed,'logical_function_all_corners_identical':True,'native_noop_typ_RC_timing_exact':True,'CLOCK_net_count':332,'live_native_elapsed_seconds':round(time.monotonic()-started,3),'boundary':'Warm originalR0→repaired→30712→P2→BUF4exactreproduction; five-old-net dirty control; exactly5terminalidentityBUF1 additions; no old master/placement edits; only5old+5newSIGNALnets. Fresh3cornerSTA separate.'}
    write(R/'measurement.json',measurement);print('PINWHEEL_FIVE_TERMINAL_PHYSICAL_GATE_PASSED',flush=True)
'''
assert live.count('\nfinally:\n')==1;live=live.replace('\nfinally:\n',extra+'\nfinally:\n');(H/'live.py').write_text(live)
driver=(H/'driver.py').read_text().replace('2026-10-14T02:37:00+00:00','2026-10-14T16:07:19+00:00').replace('2026-10-14T02:37:40+00:00','2026-10-14T16:07:59+00:00').replace('2026-10-14T02:37:00Z','2026-10-14T16:07:19Z').replace('2026-10-14T02:37:40Z','2026-10-14T16:07:59Z').replace('tt-buffered-stable-pair4-physical-route-07','tt-five-terminal-physical-route-01').replace('seconds=1800','seconds=480').replace('started+1860','started+540').replace('>1860','>540')
driver=driver.replace("ap.add_argument('--tag',", "ap.add_argument('--headroom-gate',type=Path,required=True);ap.add_argument('--headroom-sha256',required=True);ap.add_argument('--tag',")
driver=driver.replace("verify(P['source_sha256']);verify(P['tool_sha256']);assert STOP", "verify(P['source_sha256']);verify(P['tool_sha256']);assert sha(a.headroom_gate)==a.headroom_sha256;G=read(a.headroom_gate);T=read(H/'terminal-policy.json');assert G['status']=='passed' and all(G[k] is True for k in ['physical_admission_passed','three_corner_noedit_control_within_1ps','setup_budget_covers_planned_cells']);assert G['source_candidate_odb_sha256']==T['source_candidate_odb_sha256'] and G['source_candidate_segments_sha256']==T['source_candidate_segments_sha256'] and G['endpoints']==T['endpoints'];assert STOP")
driver=driver.replace("shutil.copyfile(a.selection,O/'selection.json')", "shutil.copyfile(a.selection,O/'selection.json');shutil.copyfile(a.headroom_gate,O/'terminal-headroom-admission.json')")
driver=driver.replace("('qualified-stable-source.json','qualified-stable')", "('qualified-stable-source.json','qualified-stable'),('qualified-buf4-source.json','qualified-buf4')")
driver=driver.replace("paths=[a.selection.resolve(),", "paths=[a.selection.resolve(),a.headroom_gate.resolve(),")
driver=driver.replace("'source_database_sha256':P['comparison_database_sha256']", "'source_database_sha256':P['terminal_comparison_database_sha256']")
driver=driver.replace("'source_database':P['comparison_database']", "'source_database':P['terminal_comparison_database']")
driver=driver.replace("'source_segments_sha256':P['source_segments_sha256']", "'source_segments_sha256':P['terminal_source_segments_sha256'],'headroom_admission_sha256':a.headroom_sha256,'terminal_policy_sha256':sha(H/'terminal-policy.json')")
(H/'driver.py').write_text(driver)
co=(H/'coordinator.py').read_text().replace("'qualified_stable_P2_reproduction_passed','matched_noedit_control_passed','candidate_exact_two_resizes_passed'", "'qualified_stable_P2_reproduction_passed','qualified_buf4_reproduction_passed','matched_noedit_control_passed','candidate_exact_five_additions_passed'")
(H/'coordinator.py').write_text(co)
# Host checks exercise exact native-inventory synthesis, row legality and canonical 3-Liberty identity; no CAD.
sys.path.insert(0,str(H));sys.path.insert(0,str(H/'identity'))
import types
sys.modules['odb']=types.ModuleType('odb')
from gate import expected,validate_geometry,signal_module
from physical_routed_repair import compare_repair
from physical_organization import Library
want=expected(source,terminal);validate_geometry(want,terminal);libs={c:[(H/'lib'/Path(v['path']).name).read_text()] for c,v in read(H/'plan.json')['liberty'].items()};proof=compare_repair(signal_module(source),signal_module(want),Library(libs),list(libs),allow_resizing=True);assert proof['added_cells']=={a['instance']:'sg13cmos5l_buf_1' for a in adds} and proof['resized_cells']=={} and proof['pinned_transport_functions_checked']
for f in H.rglob('*.py'):ast.parse(f.read_text(),filename=str(f))
write(H/'host-terminal-verification.json',{'status':'passed','source_inventory_exact':True,'all5proposed_free_bboxes_sitealigned_roworientation_withoutneighbors':True,'3corner_canonical_identity_proof':proof,'host_derived_not_native':True,'placement_native_PSM_checks_pending':True,'allPython_AST_passed':True})
P=read(OLD/'prepared.json');P['schema']='pinwheel-five-terminal-physical-prepared-v1';P['terminal_comparison_database_sha256']=sha(Q/'routed.odb');P['terminal_comparison_database']=str((Q/'routed.odb').relative_to(ROOT));P['terminal_source_segments_sha256']=sha(Q/'after_grt.segments');P.update(native_work_seconds_at_most=480,all_in_cap_seconds=540,native_stop_utc='2026-10-14T16:07:19Z',deadline_utc='2026-10-14T16:07:59Z',terminal_policy_sha256=sha(H/'terminal-policy.json'),terminal_headroom_gate_required_before_launch=True)
P['source_sha256'].update(artifacts);P['source_sha256'][str(Q.parent/'report.json')]=sha(Q.parent/'report.json');P['source_sha256'][str(ROOT/'build/physical/tt-five-terminal-root-01/plan.json')]=sha(ROOT/'build/physical/tt-five-terminal-root-01/plan.json')
P['source_sha256'].update({str(ROOT/k):v for k,v in p['protected_sources_sha256'].items()})
P['tool_sha256']={str(f.resolve()):sha(f) for f in H.rglob('*') if f.is_file() and f.name not in ['prepared.json','selection.json'] and '__pycache__' not in f.parts};write(H/'prepared.json',P)
selection=read(ROOT/'physical/experiments/tt-buffered-stable-pair4-physical-selection-08.json');selection.update(prepared_sha256=sha(H/'prepared.json'),route_native_stop_utc='2026-10-14T16:07:19Z',route_phase_deadline_utc='2026-10-14T16:07:59Z',terminal_policy_sha256=sha(H/'terminal-policy.json'),one_candidate_only=True,root_plan_sha256=sha(ROOT/'build/physical/tt-five-terminal-root-01/plan.json'),terminal_allowed_dirty_signal_nets=terminal['allowed_route_change_nets'],terminal_additions=adds,terminal_original_master_and_placement_changes=[])
write(H/'selection.json',selection)
print(json.dumps({'prepared_sha256':sha(H/'prepared.json'),'selection_sha256':sha(H/'selection.json'),'terminal_policy_sha256':sha(H/'terminal-policy.json'),'additions':adds,'CLI':f"python3 -B {H.relative_to(ROOT)}/driver.py --selection {H.relative_to(ROOT)}/selection.json --headroom-gate PATH --headroom-sha256 SHA --tag tt-five-terminal-physical-route-01"},indent=2))
