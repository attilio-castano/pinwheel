"""ONE live OpenROAD process: fresh route, no-op gate, exact ECO, local GRT."""
import gc,ctypes,datetime,hashlib,json,os,re,shutil,sys,time
from pathlib import Path
from copy import deepcopy
import odb
from openroad import Tech,Design
from native_inventory import snapshot,sha
from route_checks import audit_route
from segments import parse_segments
from gate import expected,signal_module,validate_geometry,protected_def
from physical_routed_repair import compare_repair
from pair_function_gate import validate_pair_function
from physical_organization import Library
from geometry import export
from runtime_guard import Patch,CREDIT,pointer,invalidate_one
R=Path('/work/diagnostic');plan=json.loads((R/'plan.json').read_text());policy=json.loads((R/'policy.json').read_text())
STOP=datetime.datetime.fromisoformat('2026-10-14T02:37:00+00:00').timestamp()
started=time.monotonic();tech=Tech();design=Design(tech)
def write(p,x):
    with p.open('w') as stream:json.dump(x,stream,indent=2);stream.write('\n')
def tcl(s):
    assert time.time()<STOP,'Native absolute stop'
    result=design.evalTclString('if {[catch {\n'+s+'\n} msg opts]} {puts stderr $msg; exit 2}; set ::pinwheel_success PINWHEEL_TCL_OK')
    assert result=='PINWHEEL_TCL_OK',result

def canonical(path):
    raw=parse_segments(path)['nets'];out={}
    for n,rows in raw.items():
        out[n]=sorted(tuple(sorted((tuple(row[:3]),tuple(row[3:])))) for row in rows)
    return out

def router_pointer():
    router=design.getGlobalRouter();return str(int(router.this if hasattr(router,'this') else router))

def current_log():
    sys.stdout.flush();ctypes.CDLL(None).fflush(None);return (R/'native.log').read_text()

def table(log):
    rows=re.findall(r'^(Metal[234]|Total)\s+(\d+)\s+(\d+)\s+([\d.]+)%\s+(\d+)\s*/\s*(\d+)\s*/\s*(\d+)\s*$',log,re.M);assert rows
    return {n:{'resource':int(r),'demand':int(d),'usage_percent':float(u),'max_horizontal_overflow':int(h),'max_vertical_overflow':int(v),'overflow':int(o)} for n,r,d,u,h,v,o in rows}

def macro_access_signature(label):
    router=design.getGlobalRouter();block=design.getBlock();path=R/(label+'-access-pin-grid.txt');router.writePinLocations(str(path))
    frozen=[];prefix=[]
    for inst in block.getInsts():
        master=inst.getMaster()
        if master.isBlock() or str(master.getType()).startswith('PAD'):
            prefix.append(inst.getName()+'/');frozen.append([inst.getName(),master.getName(),str(inst.getOrient()),[inst.getBBox().xMin(),inst.getBBox().yMin(),inst.getBBox().xMax(),inst.getBBox().yMax()],sorted([t.getMTerm().getName(),t.getNet().getName() if t.getNet() else None,sorted([l.getName(),[b.xMin(),b.yMin(),b.xMax(),b.yMax()]] for l,b in t.getGeometries())] for t in inst.getITerms())])
    ports={t.getName() for t in block.getBTerms()};actual=[]
    for line in path.read_text().splitlines():
        fields=line.split()
        if len(fields)==3 and (any(fields[0].startswith(p) for p in prefix) or fields[0] in ports):actual.append(fields)
    assert len(actual)>600,'Missing actualmacro pin-grid records'
    return {'physical_macro_pad_pin_identity':sorted(frozen),'actual_macro_pad_port_grid_positions':sorted(actual),'frozen_ports':sorted(B['pins'])}

def raw_capacity(phase,geom):
    router=design.getGlobalRouter();core=pointer(router.fastroute());fn=getattr(ctypes.CDLL(None),'_ZN3grt13FastRouteCore15getEdgeCapacityEiiiii');fn.argtypes=[ctypes.c_void_p,*([ctypes.c_int]*5)];fn.restype=ctypes.c_int
    nx=len(geom['grid_x']);ny=len(geom['grid_y']);result={}
    for layer in range(1,router.getMaxRoutingLayer()+1):
        result[str(layer)]={'H':[[fn(core,x,y,x+1,y,layer) for y in range(ny)] for x in range(nx-1)],'V':[[fn(core,x,y,x,y+1,layer) for y in range(ny-1)] for x in range(nx)]}
    write(R/phase/'native-raw-capacity.json',{'schema':'pinwheel-incremental-native-raw-capacity-v1','source':'resident FastRouteCore::getEdgeCapacity scalar API; no writes','layers':result});return result

def save(phase):
    p=R/phase;p.mkdir();print('PINWHEEL_PHASE',phase,flush=True)
    tcl(f'write_global_route_segments {p}/after_grt.segments\nwrite_guide {p}/after_grt.guide\nwrite_verilog {p}/after.v\nwrite_def {p}/routed.def\nwrite_db {p}/routed.odb')
    block=design.getBlock();db=design.getDb();snap=snapshot(db,block,phase+'/snapshot');write(p/'native-inventory.json',snap)
    geom=export(db,block,p/'geometry.json')
    spool=Path('/tmp')/('pinwheel-native-reports-'+str(os.getpid()))/phase;spool.mkdir(parents=True,exist_ok=False)
    tcl(f'estimate_parasitics -global_routing -spef_file {p}/estimated.spef\nreport_checks -sort_by_slack -path_delay min -fields {{slew cap input net fanout}} -format full_clock_expanded -group_path_count 1000 -digits 6 > {spool}/min.rpt\nreport_checks -sort_by_slack -path_delay max -fields {{slew cap input net fanout}} -format full_clock_expanded -group_path_count 1000 -digits 6 > {spool}/max.rpt\nset pw_f [open {p}/typ-numbers.txt w]\nputs $pw_f [worst_slack -min]\nputs $pw_f [worst_slack -max]\nclose $pw_f')
    spool_proof={'schema':'pinwheel-buffered-tt-fresh-native-report-spool-v1','status':'passed','phase':phase,'fresh_native_capture':True,'cached_report_substitution':False,'group_path_count':1000,'report_format':'full_clock_expanded','copies':{}}
    for kind in ('min','max'):
        source=spool/(kind+'.rpt');target=p/(kind+'.rpt');assert source.is_file() and source.stat().st_size>0
        source_sha=sha(source);shutil.copyfile(source,target);copied_sha=sha(target);assert source_sha==copied_sha
        spool_proof['copies'][kind]={'source_container_local_path':str(source),'copied_phase_path':str(target),'source_sha256':source_sha,'copied_sha256':copied_sha,'native_command':f'report_checks -sort_by_slack -path_delay {kind} -fields {{slew cap input net fanout}} -format full_clock_expanded -group_path_count 1000 -digits 6 > {source}'}
    write(p/'report-spool-proof.json',spool_proof)
    nums=[float(x) for x in (p/'typ-numbers.txt').read_text().splitlines()];assert len(nums)==2
    timing={'hold_worst_slack_ns':nums[0],'setup_worst_slack_ns':nums[1],'SPEF_sha256':sha(p/'estimated.spef'),'min_report_sha256':sha(p/'min.rpt'),'max_report_sha256':sha(p/'max.rpt'),'parasitic_model':'nativeglobalrouting','clock_and_signal_input_identity':'SPEF retains every estimated net, macro/FFpin geometry and load fixed by nativeinventory/Lib/SDC'};write(p/'typ-timing.json',timing)
    report=getattr(ctypes.CDLL(None),'_ZN3grt12GlobalRouter16reportCongestionEv');report.argtypes=[ctypes.c_void_p];report.restype=None;report(pointer(design.getGlobalRouter()))
    log=current_log();ndr=re.findall(r'Disabled NDR \(to reduce congestion\) for net: (\S+)',log)
    layer=table(log);measure={'native_layers':layer,'native_overflow':layer['Total']['overflow'],'native_clock_ndr_fallback_retries':len(ndr),'native_clock_ndr_fallback_net_order':ndr,'saved_preferred_grid_overflow':sum(v['overflow'] for v in geom['layers'].values()),'native_grid_capacity_usage_sha256':hashlib.sha256(json.dumps({n:{k:v[k] for k in ('capacity','usage')} for n,v in geom['layers'].items()},sort_keys=True).encode()).hexdigest(),'live_router_pointer':router_pointer(),'live_process_pid':os.getpid(),'CLOCK_net_count':sum(n['sig_type']=='CLOCK' for n in snap['nets'].values())};write(p/'route-state.json',measure)
    raw_capacity(phase,geom)
    return snap,canonical(p/'after_grt.segments'),geom,timing,measure

def phase_custody():
    for n,d in json.loads((R/'phase-inputs.json').read_text()).items():assert sha(Path(n))==d,n
    assert sha(R/'postcts.odb')==plan['source_database_sha256']

phase_custody();tcl('source /work/diagnostic/load.tcl')
initial=snapshot(design.getDb(),design.getBlock(),'initial');write(R/'initial-inventory.json',initial)
tcl('global_route -congestion_iterations 10 -verbose -allow_congestion -congestion_report_file /work/diagnostic/current-congestion.json')
tcl('source $::env(SCRIPTS_DIR)/openroad/common/set_rc.tcl')
B,BS,BG,BT,BM=save('original');base_audit=audit_route(initial,B);write(R/'original/source-route-audit.json',base_audit)
E=policy['baseline_expected'];assert BM['native_layers']==E['native_layers'] and BM['native_overflow']==5226
assert BM['native_clock_ndr_fallback_net_order']==E['native_clock_ndr_fallback_net_order'] and BM['native_clock_ndr_fallback_retries']==6
assert BM['saved_preferred_grid_overflow']==E['saved_preferred_grid_overflow']
assert sha(R/'original/after.v')==sha(R/'reference.v'),'Baseline originalnetlist drift'
verification=json.loads((R/'fix-api-verified.json').read_text());assert verification['dirty_mode']=='cache_API' and verification['native_inventory_before_after_identical']
assert sha(Path(os.readlink('/proc/self/exe')))==verification['native_binary_sha256']
assert design.evalTclString('ord::openroad_version')==verification['native_binary_version']
credit=Patch(CREDIT,'return_void',expected=verification['credit']['original_prologue_hex']);assert credit.module_sha256==verification['native_binary_sha256']
access=macro_access_signature('eco-baseline');credit.install();write(R/'runtime-credit-workaround.json',{'status':'armed_after_unpatched_baseline','credit':credit.receipt(),'binary_sha256':verification['native_binary_sha256'],'actual_baseline_credit_once':True,'workaround':'Suppress repeated fixedmacro pin-access credits BEFORE each incremental routing, no resource/output rewriting','no_predicate_function_patch':True})
try:
    phase_custody();assert macro_access_signature('before-dirty-noop')==access
    tcl('set_debug_level GRT incr 2');tcl('global_route -congestion_iterations 10 -start_incremental')
    chosen=design.getBlock().findNet('_03283_');assert str(chosen.getSigType())=='SIGNAL' and chosen.getNonDefaultRule() is None
    print('PINWHEEL_DIRTY_NOOP_BEGIN',flush=True);cache=invalidate_one(design.getGlobalRouter(),chosen)
    # Exactly one explicit native cache invalidation/enrollment and no DB edits.
    # The authoritative native postfilter debug worklist MUST equal this one net.
    tcl('global_route -congestion_iterations 10 -end_incremental -allow_congestion')
    nooplog=current_log().split('PINWHEEL_DIRTY_NOOP_BEGIN')[-1];assert 'Dirty nets:' in nooplog
    found=[]
    for line in nooplog.split('Dirty nets:',1)[1].splitlines():
        if not line.strip():continue
        match=re.match(r'^\[DEBUG GRT-incr\]\s+(\S+)\s*$',line)
        if not match:break
        found.append(match[1])
    assert found==['_03283_'],('Dirtynoop actualsingleton worklist',found)
    N,NS,NG,NT,NM=save('original-noop');assert B==N and BS==NS and {k:v for k,v in BG.items() if k!='database_sha256'}=={k:v for k,v in NG.items() if k!='database_sha256'} and BT==NT and BM==NM,'DIRTY no-op changed inventory/routes/grid/timing/NDR/live state'
    assert json.loads((R/'original/native-raw-capacity.json').read_text())==json.loads((R/'original-noop/native-raw-capacity.json').read_text()),'Rawnativecapacity changedduringDIRTYnoop'
    assert macro_access_signature('after-dirty-noop')==access
    write(R/'original-noop-gate.json',{'schema':'pinwheel-buffered-tt-incremental-eco-noop-gate-v1','status':'passed','noop_pre_edit_gate_passed':True,'dirty_noop_pre_edit_gate_passed':True,'actual_dirty_signal_nets':found,'native_nonempty_initNetlist_exercised':True,'native_cache_invalidation':cache,'all_native_inventory_exact':True,'all_routes_exact':True,'native_grid_capacity_usage_exact':True,'native_raw_capacity_exact':True,'runtime_same_process_router_no_cold_import':True,'NDR_warning_order_counter_exact':True,'typ_RC_SPEF_and_timing_exact':True,'all_corner_RC_inputs_identical_not_separate_baseline_numeric_measurement':True,'inputs_current_before_ECO':True,'source_database_sha256':plan['source_database_sha256']})
    # This admission point is inside the native Python process, before any mutation.
    phase_custody();assert time.time()<STOP-60,'Insufficient native stop reserve before exactECO'
    assert macro_access_signature('before-ECO')==access
    assert json.loads((R/'original/native-raw-capacity.json').read_text())==json.loads((R/'original-noop/native-raw-capacity.json').read_text())
    tcl('global_route -congestion_iterations 10 -start_incremental\nsource /work/diagnostic/exact-edit.tcl')
    post_edit=snapshot(design.getDb(),design.getBlock(),'edit');want=expected(B,plan);assert post_edit==want,'Exact edit inventory mismatch before rerouting';validate_geometry(post_edit,plan)
    text={c:[(R/'lib'/Path(v['path']).name).read_text()] for c,v in plan['liberty'].items()};proof=compare_repair(signal_module(B),signal_module(post_edit),Library(text),list(text),allow_resizing=True);assert len(proof['added_cells'])==8 and len(proof['resized_cells'])==2
    print('PINWHEEL_EXACT_ECO_GATE_PASSED',flush=True)
    print('PINWHEEL_ECO_INCREMENTAL_ROUTE_BEGIN',flush=True)
    assert macro_access_signature('before-ECO-route')==access
    tcl('global_route -congestion_iterations 10 -end_incremental -allow_congestion')
    postlog=current_log().split('PINWHEEL_ECO_INCREMENTAL_ROUTE_BEGIN')[-1]
    assert 'Dirty nets:' in postlog,'Native dirty-net list absent'
    dirtyblock=postlog.split('Dirty nets:',1)[1];dirty=[]
    for line in dirtyblock.splitlines():
        if not line.strip():continue
        m=re.match(r'^\[DEBUG GRT-incr\]\s+(\S+)\s*$',line)
        if not m:break
        dirty.append(m[1])
    assert dirty and set(dirty)<=set(policy['allowed_route_change_nets']),'Native dirty-net whitelist failed'
    write(R/'dirty-route-gate.json',{'status':'passed','actual_dirty_signal_nets':sorted(dirty),'declared_maximum_signal_nets':22,'CLOCK_dirty_nets':[]})
    C,CS,CG,CT,CM=save('eco-baseline');assert C==want,'Native incremental routing changed physical/logical/NDR inventory'
    clocks=set(policy['protected_clock_nets']);allowed=set(policy['allowed_route_change_nets']);assert len(clocks)==332
    assert set(CS)==set(BS)|set(policy['added_signal_nets']),'Route netset changed beyond8newnets'
    changed=[n for n in BS if BS[n]!=CS[n]];assert set(changed)<=allowed,('Unrelatedrouteschanged',set(changed)-allowed)
    assert all(BS[n]==CS[n] for n in clocks),'CLOCK route changed'
    assert json.loads((R/'original/native-raw-capacity.json').read_text())==json.loads((R/'eco-baseline/native-raw-capacity.json').read_text()),'Raw FastRoute capacity changed'
    assert all(BG['layers'][n]['capacity']==CG['layers'][n]['capacity'] for n in BG['layers']),'Routingcapacity changed'
    assert BM['native_clock_ndr_fallback_net_order']==CM['native_clock_ndr_fallback_net_order'],'New clock NDR fallback'
    tcl('check_placement -verbose\ncheck_power_grid -net VPWR -error_file /work/diagnostic/VPWR-grid-errors.rpt\ncheck_power_grid -net VGND -error_file /work/diagnostic/VGND-grid-errors.rpt')
    log=current_log();assert all('All shapes on net '+n+' are connected.' in log for n in ('VPWR','VGND'))
    write(R/'eco-baseline/change-proof.json',{'schema':'pinwheel-buffered-tt-incremental-eco-change-proof-v1','status':'measured','exact_edit_gate_passed':True,'source_database_sha256':plan['source_database_sha256'],'output_database_sha256':sha(R/'eco-baseline/routed.odb'),'all_corner_signal_identity':proof,'exact_added_instances':plan['added_instances'],'exact_rewired_original_pins':plan['allowed_original_sink_rewires'],'exact_resizes':plan['resizes'],'added_cells':8,'resized_cells':2,'original_placement_unchanged_count':28960,'clock_tree_unchanged':True,'PG_special_wire_geometry_unchanged':True,'original_statuses_restored':True,'added_power_bindings_exact':True,'rows_blockages_pins_macros_unchanged':True,'TechLEF_and_NDR_unchanged':True,'all332CLOCKsegments_exact':True,'all_unrelated_routes_exact':True,'allowed_route_change_nets':sorted(allowed),'actual_changed_original_route_nets':sorted(changed),'native_legal_changed_footprints':True})
    # Transfer prior three-corner headroom only across exact rebuilt RC inputs.
    Q=R/'qualified-control';retained=json.loads((Q/'native-inventory.json').read_text());assert C==retained,'Qualifiedcontrol nativeinventory not reproduced'
    assert CS==canonical(Q/'after_grt.segments'),'Qualifiedcontrol canonicalroutes not reproduced'
    refgeom=json.loads((Q/'geometry.json').read_text());assert {k:v for k,v in CG.items() if k!='database_sha256'}=={k:v for k,v in refgeom.items() if k!='database_sha256'},'Qualifiedcontrol fullgrid/geometry not reproduced'
    assert json.loads((R/'eco-baseline/native-raw-capacity.json').read_text())==json.loads((Q/'native-raw-capacity.json').read_text()),'Qualifiedcontrol rawcapacity not reproduced'
    assert sha(R/'eco-baseline/after.v')==sha(Q/'after.v') and sha(R/'eco-baseline/estimated.spef')==sha(Q/'estimated.spef'),'Qualifiedcontrol netlist/nominalSPEF not reproduced'
    assert CT==json.loads((Q/'typ-timing.json').read_text()),'Qualifiedcontrol nominaltiming not reproduced'
    expectednumbers=json.loads((Q/'route-state.json').read_text());assert {k:v for k,v in CM.items() if k not in ('live_router_pointer','live_process_pid')}=={k:v for k,v in expectednumbers.items() if k not in ('live_router_pointer','live_process_pid')},'Qualifiedcontrol nativecounts/NDR not reproduced'
    headroom=json.loads((R/'replay-headroom-gate.json').read_text());assert headroom['schema']=='pinwheel-buffered-tt-hold30712-preflight-gate-v1' and headroom['status']=='passed' and headroom['admitted_to_move'] is True
    assert headroom['qualified_candidate_database_sha256']==json.loads((R/'qualified-control-source.json').read_text())['control_database_sha256']
    assert headroom['qualified_candidate_route_segments_sha256']==sha(Q/'after_grt.segments') and sha(R/'eco-baseline/after_grt.segments')==sha(Q/'after_grt.segments')
    assert headroom['worst_target_setup_ns']>=1.0 and headroom['worst_target_hold_ns']>=.05
    assert headroom['all_03216_sinks']==[['timing_eco_hold_30712','A']]
    write(R/'qualified-control-reproduction-gate.json',{'status':'passed','qualified_control_reproduction_passed':True,'exact_native_inventory':True,'exact_canonical_all_routes':True,'exact_saved_grid_capacity_usage':True,'exact_raw_FastRoute_capacity':True,'exact_netlist_and_nominal_SPEF':True,'exact_nominal_timing':True,'exact_native_counts_NDR_order':True,'three_corner_headroom_transfer_input_identity':True,'prior_candidate_database_sha256':json.loads((R/'qualified-control-source.json').read_text())['control_database_sha256'],'fresh_rebuilt_database_sha256':sha(R/'eco-baseline/routed.odb'),'headroom_gate_sha256':sha(R/'replay-headroom-gate.json')})
    # Current qualified ECO is the actual comparison baseline.
    O,OS,OG,OT,OM=B,BS,BG,BT,BM
    B,BS,BG,BT,BM=C,CS,CG,CT,CM
    phase_custody();assert macro_access_signature('current-before-dirty-noop')==access
    tcl('global_route -congestion_iterations 10 -start_incremental')
    control_names=['_03216_','timing_eco_hold_30712_D'];cache=[]
    print('PINWHEEL_CURRENT_DIRTY_NOOP_BEGIN',flush=True)
    for net_name in control_names:
        chosen=design.getBlock().findNet(net_name);assert str(chosen.getSigType())=='SIGNAL' and chosen.getNonDefaultRule() is None
        cache.append(invalidate_one(design.getGlobalRouter(),chosen))
    tcl('global_route -congestion_iterations 10 -end_incremental -allow_congestion')
    log=current_log().split('PINWHEEL_CURRENT_DIRTY_NOOP_BEGIN')[-1];assert 'Dirty nets:' in log
    found=[]
    for line in log.split('Dirty nets:',1)[1].splitlines():
        if not line.strip():continue
        match=re.match(r'^\[DEBUG GRT-incr\]\s+(\S+)\s*$',line)
        if not match:break
        found.append(match[1])
    assert sorted(found)==sorted(control_names) and len(found)==2,('Currentdirtynoop exactmatchedtwo-netset',found)
    N,NS,NG,NT,NM=save('eco-noop');assert B==N and BS==NS and {k:v for k,v in BG.items() if k!='database_sha256'}=={k:v for k,v in NG.items() if k!='database_sha256'} and BT==NT and BM==NM,'CurrentDIRTYnoop changed inventory/routes/grid/timing/NDR'
    assert json.loads((R/'eco-baseline/native-raw-capacity.json').read_text())==json.loads((R/'eco-noop/native-raw-capacity.json').read_text()),'CurrentDIRTYnoop rawcapacity changed'
    assert macro_access_signature('current-after-dirty-noop')==access
    write(R/'eco-noop-gate.json',{'schema':'pinwheel-buffered-tt-hold30712-noop-gate-v1','status':'passed','noop_pre_edit_gate_passed':True,'dirty_noop_pre_edit_gate_passed':True,'actual_dirty_signal_nets':found,'native_nonempty_initNetlist_exercised':True,'native_cache_invalidation':cache,'all_native_inventory_exact':True,'all_routes_exact':True,'native_grid_capacity_usage_exact':True,'native_raw_capacity_exact':True,'typ_RC_SPEF_and_timing_exact':True,'same_warm_router':True})
    # Exactly one physical cell move; all graph/clock/status/PG metadata frozen.
    phase_custody();assert time.time()<STOP-60,'Insufficient native timebeforemove'
    edit=json.loads((R/'replay-selection.json').read_text())['edit'];assert edit['instance']=='timing_eco_hold_30712' and edit['allowed_signal_routes']==['_03216_','timing_eco_hold_30712_D']
    row=B['instances'][edit['instance']];assert row['bbox_dbu']==edit['before_bbox_DBU'] and row['orientation']==edit['before_orientation'] and row['master']==edit['master']
    assert B['nets']['_03216_']['terminals']==[['_29930_','Y','OUTPUT'],['timing_eco_hold_30712','A','INPUT']],'Unexpectedsharedload on_03216'
    moved=deepcopy(B);moved['instances'][edit['instance']]['bbox_dbu']=edit['target_bbox_DBU'];moved['instances'][edit['instance']]['orientation']=edit['target_orientation']
    validate_geometry(moved,{'resizes':{},'added_instances':[edit['instance']]})
    assert macro_access_signature('before-one-move')==access
    print('PINWHEEL_ONE_MOVE_INCREMENTAL_BEGIN',flush=True);tcl('global_route -congestion_iterations 10 -start_incremental\nsource /work/diagnostic/move.tcl')
    actual=snapshot(design.getDb(),design.getBlock(),'one-move');assert actual==moved,'Unexpectedphysical/logical/status/PG mutationfromone move';assert signal_module(actual)==signal_module(B)
    assert macro_access_signature('before-one-move-route')==access
    tcl('global_route -congestion_iterations 10 -end_incremental -allow_congestion')
    log=current_log().split('PINWHEEL_ONE_MOVE_INCREMENTAL_BEGIN')[-1];assert 'Dirty nets:' in log
    dirty=[]
    for line in log.split('Dirty nets:',1)[1].splitlines():
        if not line.strip():continue
        match=re.match(r'^\[DEBUG GRT-incr\]\s+(\S+)\s*$',line)
        if not match:break
        dirty.append(match[1])
    allowed=set(edit['allowed_signal_routes']);assert set(dirty)==allowed and len(dirty)==2,('Two-netdirtyscope mismatch',dirty)
    C,CS,CG,CT,CM=save('baseline');assert C==moved,'Unexpectedfinalnativeinventorychange'
    assert set(CS)==set(BS),'Placement changedroutenetset'
    changed=[n for n in BS if BS[n]!=CS[n]];assert set(changed)<=allowed and all(BS[n]==CS[n] for n in clocks),'CLOCK/unrelatedroutechange'
    assert all(BG['layers'][n]['capacity']==CG['layers'][n]['capacity'] for n in BG['layers'])
    assert json.loads((R/'eco-baseline/native-raw-capacity.json').read_text())==json.loads((R/'baseline/native-raw-capacity.json').read_text()),'RawFastRoute capacitychanged'
    assert sha(R/'eco-baseline/after.v')==sha(R/'baseline/after.v'),'Placementchangedlogicalnetlistbytes'
    assert BM['native_clock_ndr_fallback_net_order']==CM['native_clock_ndr_fallback_net_order'],'NewCLOCK NDRfallback'
    tcl('check_placement -verbose\ncheck_power_grid -net VPWR -error_file /work/diagnostic/VPWR-move-grid-errors.rpt\ncheck_power_grid -net VGND -error_file /work/diagnostic/VGND-move-grid-errors.rpt')
    log=current_log();assert all('All shapes on net '+n+' are connected.' in log for n in ('VPWR','VGND'))
    write(R/'baseline/change-proof.json',{'schema':'pinwheel-buffered-tt-hold30712-change-proof-v1','status':'measured','exact_edit_gate_passed':True,'native_pure_placement_scope_passed':True,'source_database_sha256':plan['source_database_sha256'],'comparison_baseline_database_sha256':sha(R/'eco-baseline/routed.odb'),'output_database_sha256':sha(R/'baseline/routed.odb'),'moved_instances':[edit['instance']],'moved_instance_count':1,'unmoved_instance_count':len(B['instances'])-1,'masters_topology_statuses_clock_PG_rows_blockages_pins_TechLEF_NDR_exact':True,'logical_netlist_bytes_identical':True,'signal_module_exact':True,'all332CLOCKsegments_exact':True,'all_unrelated_routes_exact':True,'native_raw_capacity_exact':True,'allowed_route_change_nets':sorted(allowed),'actual_changed_original_route_nets':sorted(changed),'native_legal_changed_footprint':True,'fresh_PSM_both_nets_passed':True,'headroom_gate_sha256':sha(R/'replay-headroom-gate.json'),'qualified_control_reproduction_gate_sha256':sha(R/'qualified-control-reproduction-gate.json')})
    # Reproduce the current qualified 30712 candidate before the NEW treatment.
    P=R/'qualified-pair';q=json.loads((R/'qualified-pair-source.json').read_text())
    assert C==json.loads((P/'native-inventory.json').read_text()),'Current8c nativeinventory mismatch'
    assert CS==canonical(P/'after_grt.segments') and sha(R/'baseline/after_grt.segments')==sha(P/'after_grt.segments'),'Current8c routes mismatch'
    pg=json.loads((P/'geometry.json').read_text());assert {k:v for k,v in CG.items() if k!='database_sha256'}=={k:v for k,v in pg.items() if k!='database_sha256'},'Current8c grid/geometry mismatch'
    assert json.loads((R/'baseline/native-raw-capacity.json').read_text())==json.loads((P/'native-raw-capacity.json').read_text()),'Current8c rawcapacity mismatch'
    assert sha(R/'baseline/after.v')==sha(P/'after.v') and sha(R/'baseline/estimated.spef')==sha(P/'estimated.spef'),'Current8c NL/SPEF mismatch'
    assert CT==json.loads((P/'typ-timing.json').read_text()),'Current8c nominal timing mismatch'
    ps=json.loads((P/'route-state.json').read_text());assert {k:v for k,v in CM.items() if k not in ('live_router_pointer','live_process_pid')}=={k:v for k,v in ps.items() if k not in ('live_router_pointer','live_process_pid')},'Current8c counts/NDR mismatch'
    stabilization=json.loads((R/'stabilization-policy.json').read_text())
    assert stabilization['passes']==2 and stabilization['congestion_iterations']==10
    assert stabilization['source_database_sha256']==q['control_database_sha256']=='8c3079c61f73f0f2819d4e0d21d0af2775d4afb76c620494e2841ace4b1dd063'
    assert stabilization['source_segments_sha256']==sha(P/'after_grt.segments')=='20d30f32a303cd2984172d3825fa5ecbe2e663d08509f80932b7bcb72cce9442'
    write(R/'qualified-pair-reproduction-gate.json',{'status':'passed','qualified_control_reproduction_passed':True,'all_native_inventory_routes_grid_rawcapacity_NL_nominalSPEF_timing_counts_NDR_exact':True,'qualified_database_sha256':q['control_database_sha256'],'fresh_rebuilt_database_sha256':sha(R/'baseline/routed.odb')})
    B,BS,BG,BT,BM=C,CS,CG,CT,CM
    allowed=set(stabilization['dirty_signal_nets']);assert allowed=={'_11039_','net913','net914'}
    for n in allowed:assert B['nets'][n]==stabilization['source_net_terminals'][n] and B['nets'][n]['sig_type']=='SIGNAL' and B['nets'][n]['nondefault_rule'] is None
    def spef_networks(path):
        text=path.read_text();blocks={}
        for match in re.finditer(r'(?ms)^\*D_NET (\S+) .*?^\*END\n',text):
            assert match[1] not in blocks;blocks[match[1]]=match[0]
        assert blocks;return blocks
    baseline_spef=spef_networks(R/'baseline/estimated.spef')
    baseline_raw=json.loads((R/'baseline/native-raw-capacity.json').read_text())
    outcomes=[];previous=None
    for pass_number in (1,2):
        phase='pass'+str(pass_number);phase_custody();assert time.time()<STOP-45,'Insufficient native capture reserve'
        assert macro_access_signature(phase+'-before-dirty')==access
        marker='PINWHEEL_STABILIZATION_PASS_'+str(pass_number)+'_BEGIN'
        tcl('global_route -congestion_iterations 10 -start_incremental');print(marker,flush=True);cache=[]
        for name in sorted(allowed):cache.append(invalidate_one(design.getGlobalRouter(),design.getBlock().findNet(name)))
        tcl('global_route -congestion_iterations 10 -end_incremental -allow_congestion')
        log=current_log().split(marker)[-1];assert 'Dirty nets:' in log;found=[]
        for line in log.split('Dirty nets:',1)[1].splitlines():
            if not line.strip():continue
            match=re.match(r'^\[DEBUG GRT-incr\]\s+(\S+)\s*$',line)
            if not match:break
            found.append(match[1])
        assert set(found)==allowed and len(found)==3,('Exact three-net dirty worklist failed',phase,found)
        X,XS,XG,XT,XM=save(phase)
        assert X==B,'Cell/master/placement/orientation/status/graph/PG/NDR/rows/pins changed after baseline'
        assert set(XS)==set(BS),'Route netset changed'
        changed=[n for n in BS if BS[n]!=XS[n]]
        assert set(changed)<=allowed and all(BS[n]==XS[n] for n in clocks),'CLOCK/unrelated route preservation failed'
        assert all(BG['layers'][n]['capacity']==XG['layers'][n]['capacity'] for n in BG['layers']),'Saved grid capacities changed'
        raw=json.loads((R/phase/'native-raw-capacity.json').read_text());assert raw==baseline_raw,'Raw FastRoute capacities changed'
        assert sha(R/phase/'after.v')==sha(R/'baseline/after.v'),'No-sizing logical netlist changed'
        assert BM['native_clock_ndr_fallback_net_order']==XM['native_clock_ndr_fallback_net_order'],'New CLOCK NDR fallback'
        assert macro_access_signature(phase+'-after-dirty')==access
        actual_spef=spef_networks(R/phase/'estimated.spef');assert set(actual_spef)==set(baseline_spef)
        changed_rc=[n for n in baseline_spef if baseline_spef[n]!=actual_spef[n]];assert set(changed_rc)<=allowed,'Unrelated RC network changed'
        outcome={'phase':phase,'scope_preservation_passed':True,'actual_dirty_signal_nets':sorted(found),'actual_changed_routes_from_baseline':sorted(changed),'actual_changed_RC_nets_from_baseline':sorted(changed_rc),'native_cache_invalidation':cache,'native':XM,'typical_timing':XT,'no_cell_changes_after_baseline':True,'CLOCK_routes_exact':True,'all_unrelated_routes_exact':True,'raw_capacities_exact':True,'netlist_bytes_exact':True}
        if previous is not None:
            V,VS,VG,VT,VM,VRAW,VPHASE=previous
            comparisons={'full_native_inventory':X==V,'canonical_all_route_multisets':XS==VS,'logical_netlist_bytes':sha(R/phase/'after.v')==sha(R/VPHASE/'after.v'),'raw_FastRoute_capacities':raw==VRAW,'full_saved_geometry_capacity_usage':{k:v for k,v in XG.items() if k!='database_sha256'}=={k:v for k,v in VG.items() if k!='database_sha256'},'native_route_counts_NDR_state':XM==VM,'nominal_full_SPEF':sha(R/phase/'estimated.spef')==sha(R/VPHASE/'estimated.spef'),'nominal_timing_and_report_bodies':XT==VT}
            outcome['pass1_to_pass2_exact_comparisons']=comparisons;outcome['stable']=all(comparisons.values())
            outcome['actual_route_changes_from_pass1']=sorted(n for n in VS if VS[n]!=XS[n])
        write(R/phase/'preservation-proof.json',outcome);outcomes.append(outcome)
        previous=(X,XS,XG,XT,XM,raw,phase)
    assert len(outcomes)==2 and len(cache)==3
    assert outcomes[-1]['stable'],'Warm P1/P2 did not stabilize: no pair edit admitted'
    stable=json.loads((R/'qualified-stable-source.json').read_text());S=R/'qualified-stable'
    assert X==json.loads((S/'native-inventory.json').read_text()),'P2 native inventory not reproduced'
    assert XS==canonical(S/'after_grt.segments') and sha(R/'pass2/after_grt.segments')==sha(S/'after_grt.segments'),'P2 routes not reproduced'
    SG=json.loads((S/'geometry.json').read_text())
    assert {k:v for k,v in XG.items() if k!='database_sha256'}=={k:v for k,v in SG.items() if k!='database_sha256'},'P2 grid geometry/usage not reproduced'
    assert raw==json.loads((S/'native-raw-capacity.json').read_text()),'P2 raw capacities not reproduced'
    assert XT==json.loads((S/'typ-timing.json').read_text()),'P2 nominal timing/SPEF not reproduced'
    SM=json.loads((S/'route-state.json').read_text())
    assert {k:v for k,v in XM.items() if k not in ('live_router_pointer','live_process_pid')}=={k:v for k,v in SM.items() if k not in ('live_router_pointer','live_process_pid')},'P2 native counters/NDR not reproduced'
    assert sha(R/'pass2/after.v')==sha(S/'after.v') and sha(R/'pass2/estimated.spef')==sha(S/'estimated.spef')
    write(R/'qualified-stable-reproduction-gate.json',{'status':'passed','qualified_stable_P2_reproduction_passed':True,'all_native_inventory_routes_grid_rawcapacity_NL_nominalSPEF_timing_counts_NDR_exact':True,'source_database_sha256':stable['source_database_sha256'],'source_segments_sha256':stable['source_segments_sha256'],'rebuilt_database_sha256':sha(R/'pass2/routed.odb'),'source_failed_OOM_status_preserved':True})
    B,BS,BG,BT,BM=X,XS,XG,XT,XM
    original_route_state=OM
    # Memory-only cleanup of obsolete Python snapshots: native warm router remains live.
    for old_name in ('initial','N','NS','NG','NT','NM','post_edit','want','retained','refgeom','moved','actual','O','OS','OG','OT','OM','C','CS','CG','CT','CM','pg','ps','V','VS','VG','VT','VM','VRAW','previous','SG','SM','baseline_spef','actual_spef'):
        globals().pop(old_name,None)
    gc.collect()
    pair=json.loads((R/'pair-policy.json').read_text());assert pair['qualified_source_database_sha256']==stable['source_database_sha256']
    for name in allowed:assert B['nets'][name]==pair['source_net_terminals'][name]
    phase_custody();assert macro_access_signature('stable-before-dirty-control')==access
    print('PINWHEEL_STABLE_MATCHED_CONTROL_BEGIN',flush=True);tcl('global_route -congestion_iterations 10 -start_incremental');cache=[]
    for name in sorted(allowed):cache.append(invalidate_one(design.getGlobalRouter(),design.getBlock().findNet(name)))
    tcl('global_route -congestion_iterations 10 -end_incremental -allow_congestion')
    log=current_log().split('PINWHEEL_STABLE_MATCHED_CONTROL_BEGIN')[-1];assert 'Dirty nets:' in log;found=[]
    for line in log.split('Dirty nets:',1)[1].splitlines():
        if not line.strip():continue
        match=re.match(r'^\[DEBUG GRT-incr\]\s+(\S+)\s*$',line)
        if not match:break
        found.append(match[1])
    assert set(found)==allowed and len(found)==3,('Matched three-net control worklist',found)
    N,NS,NG,NT,NM=save('control')
    assert B==N and BS==NS and {k:v for k,v in BG.items() if k!='database_sha256'}=={k:v for k,v in NG.items() if k!='database_sha256'} and BT==NT and BM==NM,'Matched P2 no-edit control changed inventory/routes/grid/SPEF/timing/NDR'
    assert raw==json.loads((R/'control/native-raw-capacity.json').read_text())
    assert sha(R/'control/after.v')==sha(S/'after.v') and sha(R/'control/estimated.spef')==sha(S/'estimated.spef')
    assert macro_access_signature('stable-after-dirty-control')==access
    write(R/'control/noop-gate.json',{'status':'passed','matched_noedit_control_passed':True,'actual_dirty_signal_nets':sorted(found),'native_nonempty_initNetlist_exercised':True,'native_cache_invalidation':cache,'all_native_inventory_routes_grid_rawcapacity_NL_nominalSPEF_timing_NDR_exact':True,'same_warm_router':True})
    phase_custody();assert time.time()<STOP-60,'Insufficient native time before pair resize'
    wanted=expected(B,{'resizes':pair['resizes'],'additions':[]})
    validate_geometry(wanted,{'resizes':pair['resizes'],'added_instances':[]})
    assert macro_access_signature('before-pair-resize')==access
    print('PINWHEEL_PAIR_RESIZE_INCREMENTAL_BEGIN',flush=True)
    # updateDirtyNets cleared saved pin history after the matched no-edit pass.
    # Cache invalidation must precede swap/move callbacks: those callbacks save
    # populated old history on first enrollment, and destroyPins alone cannot
    # erase that saved history. Keep the current pins empty during callbacks.
    order=json.loads((R/'cache-order-verified.json').read_text())
    assert order['all3_callback_first_reproduced_filter_failure'] and order['all3_pre_enroll_first_unpatched_predicate_true']
    assert order['native_inventory_before_after_identical'] and not order['predicate_function_patch']
    assert all(v['native_binary_sha256']==verification['native_binary_sha256'] for v in order['case_results'].values())
    tcl('global_route -congestion_iterations 10 -start_incremental')
    pre_enrolled=[]
    for name in sorted(allowed):pre_enrolled.append(invalidate_one(design.getGlobalRouter(),design.getBlock().findNet(name)))
    write(R/'pair-pre-edit-cache-enrollment.json',{'status':'passed','actual_enrolled_signal_nets':sorted(allowed),'native_cache_invalidation':pre_enrolled,'before_any_pair_swap_or_move':True,'callback_order_verification_sha256':sha(R/'cache-order-verified.json'),'predicate_function_unpatched':True,'source_DB_or_route_geometry_edited':False})
    tcl('source /work/diagnostic/pair-edit.tcl')
    actual=snapshot(design.getDb(),design.getBlock(),'pair-edit');assert actual==wanted,'Unexpectedpair edit nativeinventory'
    text={c:[(R/'lib'/Path(v['path']).name).read_text()] for c,v in plan['liberty'].items()}
    before_module=signal_module(B);after_module=signal_module(actual)
    # Capture actual native export before proof consumption, including failed attempts.
    tcl('write_verilog /work/diagnostic/pair-edit-after.v')
    function=compare_repair(before_module,after_module,Library(text),list(text),allow_resizing=True)
    validate_pair_function(function,{n:{'before':v['before'],'after':v['after']} for n,v in pair['resizes'].items()},len(before_module['cells']))
    write(R/'pair-function-proof.json',{'status':'passed','proof':function,'source_signal_module_cells':len(before_module['cells']),'before_native_instance_count':len(B['instances']),'after_native_instance_count':len(actual['instances']),'before_native_netlist_sha256':sha(R/'control/after.v'),'after_native_netlist_sha256':sha(R/'pair-edit-after.v'),'actual_native_inventory_equals_exact_two_resize_expected':True})
    # Re-enroll the exact same nets after edits. Pre-enrollment kept the current
    # pin vector and saved-history cache empty through all swap/move callbacks.
    enrolled=[]
    for name in sorted(allowed):enrolled.append(invalidate_one(design.getGlobalRouter(),design.getBlock().findNet(name)))
    assert macro_access_signature('before-pair-route')==access
    tcl('global_route -congestion_iterations 10 -end_incremental -allow_congestion')
    log=current_log().split('PINWHEEL_PAIR_RESIZE_INCREMENTAL_BEGIN')[-1];assert 'Dirty nets:' in log;dirty=[]
    for line in log.split('Dirty nets:',1)[1].splitlines():
        if not line.strip():continue
        match=re.match(r'^\[DEBUG GRT-incr\]\s+(\S+)\s*$',line)
        if not match:break
        dirty.append(match[1])
    assert set(dirty)==allowed and len(dirty)==3,('Pairresize dirtyscope mismatch',dirty)
    C,CS,CG,CT,CM=save('candidate');assert C==wanted,'Unexpectedfinalpairinventory'
    assert set(CS)==set(BS),'Pairresize changedroutenetset'
    changed=[n for n in BS if BS[n]!=CS[n]];assert set(changed)<=allowed and all(BS[n]==CS[n] for n in clocks),'CLOCK/unrelatedroutechange'
    assert all(BG['layers'][n]['capacity']==CG['layers'][n]['capacity'] for n in BG['layers'])
    assert json.loads((R/'control/native-raw-capacity.json').read_text())==json.loads((R/'candidate/native-raw-capacity.json').read_text()),'RawFastRoutecapacitychanged'
    assert BM['native_clock_ndr_fallback_net_order']==CM['native_clock_ndr_fallback_net_order'],'NewCLOCK NDRfallback'
    before_rc=spef_networks(R/'control/estimated.spef');after_rc=spef_networks(R/'candidate/estimated.spef');assert set(before_rc)==set(after_rc)
    changed_rc=sorted(n for n in before_rc if before_rc[n]!=after_rc[n]);assert set(changed_rc)<=allowed,'Unrelated RC network changed'
    tcl('check_placement -verbose\ncheck_power_grid -net VPWR -error_file /work/diagnostic/VPWR-pair-grid-errors.rpt\ncheck_power_grid -net VGND -error_file /work/diagnostic/VGND-pair-grid-errors.rpt')
    log=current_log().split('PINWHEEL_PAIR_RESIZE_INCREMENTAL_BEGIN')[-1]
    assert all('All shapes on net '+n+' are connected.' in log for n in ('VPWR','VGND')),'FreshpostpairPSM absent'
    change={'schema':'pinwheel-buffered-tt-stable-pair4-physical-change-proof-v1','status':'measured','exact_edit_gate_passed':True,'source_database_sha256':stable['source_database_sha256'],'comparison_baseline_database_sha256':sha(R/'control/routed.odb'),'output_database_sha256':sha(R/'candidate/routed.odb'),'exact_resizes':pair['resizes'],'resized_cells':2,'added_cells':0,'unmodified_instance_count':len(B['instances'])-2,'all_corner_signal_identity':function,'all_other_master_placement_orientation_status_topology_clock_PG_rows_blockages_pins_TechLEF_NDR_exact':True,'all332CLOCKsegments_exact':True,'all_unrelated_routes_exact':True,'native_raw_capacity_exact':True,'allowed_route_change_nets':sorted(allowed),'actual_changed_original_route_nets':sorted(changed),'actual_dirty_signal_nets':sorted(dirty),'explicit_incident_net_cache_enrollment':enrolled,'pre_edit_incident_net_cache_enrollment':pre_enrolled,'cache_order_preflight_sha256':sha(R/'cache-order-verified.json'),'native_legal_changed_footprints':True,'fresh_PSM_both_nets_passed':True,'qualified_stable_reproduction_gate_sha256':sha(R/'qualified-stable-reproduction-gate.json'),'qualified_control_reproduction_gate_sha256':sha(R/'control/noop-gate.json')}
    write(R/'candidate/change-proof.json',change)
    measurement={'schema':'pinwheel-buffered-tt-stable-pair4-physical-measurement-v1','status':'measured','qualified_control_reproduction_passed':True,'dirty_noop_pre_edit_gate_passed':True,'noop_pre_edit_gate_passed':True,'candidate_exact_edit_gate_passed':True,'qualified_stable_P2_reproduction_passed':True,'matched_noedit_control_passed':True,'candidate_exact_two_resizes_passed':True,'native_placement_and_pin_access_legality_passed':True,'exact_two_resizes_only':True,'original':original_route_state,'baseline':BM,'control':NM,'candidate':CM,'native_clock_route_preservation_passed':True,'CLOCK_net_count':332,'all_unrelated_route_preservation_passed':True,'native_raw_capacity_preservation_passed':True,'allowed_route_change_nets':sorted(allowed),'actual_changed_original_route_nets':sorted(changed),'actual_dirty_signal_nets':sorted(dirty),'resized_cell_count':2,'unmodified_instance_count':len(B['instances'])-2,'logical_function_all_corners_identical':True,'live_native_elapsed_seconds':round(time.monotonic()-started,3),'fresh_PSM_both_nets_passed':True,'native_noop_typ_RC_timing_exact':True,'source_database_sha256':stable['source_database_sha256'],'original_R0_database_sha256':plan['source_database_sha256'],'boundary':'Two warm stabilization passes reproduce exact saved P2 before matched3net control and only two BUF4 resizes; one warm originalR0→qualified2+8repair→qualified30712move exactreplay→current8c exactmatch→matched3net dirtynoop→onlytwo buf1-to-buf4 resizes with3netincremental; no coldrouteimport/GPL/DPL/CTS/repair/fullreroutefallback; allCLOCK/unrelatedroutes fixed. Fresh3corner timing separate.'}
    write(R/'measurement.json',measurement);print('PINWHEEL_FANOUT913914_GATE_PASSED',flush=True)

finally:
    credit.restore();write(R/'runtime-credit-restoration.json',{'status':'restored','original_prologue_restored':True,'page_permissions_RX_restored':True,'credit':credit.receipt(),'no_capacity_or_savedgrid_writes':True,'no_predicate_function_patch':True})
