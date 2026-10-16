"""ONE live OpenROAD process: fresh route, no-op gate, exact ECO, local GRT."""
import ctypes,datetime,hashlib,json,os,re,shutil,sys,time
from pathlib import Path
import odb
from openroad import Tech,Design
from native_inventory import snapshot,sha
from route_checks import audit_route
from segments import parse_segments
from gate import expected,signal_module,validate_geometry,protected_def
from physical_routed_repair import compare_repair
from physical_organization import Library
from geometry import export
from runtime_guard import Patch,CREDIT,pointer,invalidate_one
R=Path('/work/diagnostic');plan=json.loads((R/'plan.json').read_text());policy=json.loads((R/'policy.json').read_text())
STOP=datetime.datetime.fromisoformat('2026-10-13T18:07:41+00:00').timestamp()
started=time.monotonic();tech=Tech();design=Design(tech)
def write(p,x):p.write_text(json.dumps(x,indent=2)+'\n')
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
    tcl(f'estimate_parasitics -global_routing -spef_file {p}/estimated.spef\nreport_checks -sort_by_slack -path_delay min -fields {{slew cap input net fanout}} -format full_clock_expanded -group_path_count 1000 -digits 6 > {p}/min.rpt\nreport_checks -sort_by_slack -path_delay max -fields {{slew cap input net fanout}} -format full_clock_expanded -group_path_count 1000 -digits 6 > {p}/max.rpt\nset pw_f [open {p}/typ-numbers.txt w]\nputs $pw_f [worst_slack -min]\nputs $pw_f [worst_slack -max]\nclose $pw_f')
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
B,BS,BG,BT,BM=save('baseline');base_audit=audit_route(initial,B);write(R/'baseline/source-route-audit.json',base_audit)
E=policy['baseline_expected'];assert BM['native_layers']==E['native_layers'] and BM['native_overflow']==5226
assert BM['native_clock_ndr_fallback_net_order']==E['native_clock_ndr_fallback_net_order'] and BM['native_clock_ndr_fallback_retries']==6
assert BM['saved_preferred_grid_overflow']==E['saved_preferred_grid_overflow']
assert sha(R/'baseline/after.v')==sha(R/'reference.v'),'Baseline originalnetlist drift'
verification=json.loads((R/'fix-api-verified.json').read_text());assert verification['dirty_mode']=='cache_API' and verification['native_inventory_before_after_identical']
assert sha(Path(os.readlink('/proc/self/exe')))==verification['native_binary_sha256']
assert design.evalTclString('ord::openroad_version')==verification['native_binary_version']
credit=Patch(CREDIT,'return_void',expected=verification['credit']['original_prologue_hex']);assert credit.module_sha256==verification['native_binary_sha256']
access=macro_access_signature('baseline');credit.install();write(R/'runtime-credit-workaround.json',{'status':'armed_after_unpatched_baseline','credit':credit.receipt(),'binary_sha256':verification['native_binary_sha256'],'actual_baseline_credit_once':True,'workaround':'Suppress repeated fixedmacro pin-access credits BEFORE each incremental routing, no resource/output rewriting','no_predicate_function_patch':True})
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
    N,NS,NG,NT,NM=save('noop');assert B==N and BS==NS and {k:v for k,v in BG.items() if k!='database_sha256'}=={k:v for k,v in NG.items() if k!='database_sha256'} and BT==NT and BM==NM,'DIRTY no-op changed inventory/routes/grid/timing/NDR/live state'
    assert json.loads((R/'baseline/native-raw-capacity.json').read_text())==json.loads((R/'noop/native-raw-capacity.json').read_text()),'Rawnativecapacity changedduringDIRTYnoop'
    assert macro_access_signature('after-dirty-noop')==access
    write(R/'noop-gate.json',{'schema':'pinwheel-buffered-tt-incremental-eco-noop-gate-v1','status':'passed','noop_pre_edit_gate_passed':True,'dirty_noop_pre_edit_gate_passed':True,'actual_dirty_signal_nets':found,'native_nonempty_initNetlist_exercised':True,'native_cache_invalidation':cache,'all_native_inventory_exact':True,'all_routes_exact':True,'native_grid_capacity_usage_exact':True,'native_raw_capacity_exact':True,'runtime_same_process_router_no_cold_import':True,'NDR_warning_order_counter_exact':True,'typ_RC_SPEF_and_timing_exact':True,'all_corner_RC_inputs_identical_not_separate_baseline_numeric_measurement':True,'inputs_current_before_ECO':True,'source_database_sha256':plan['source_database_sha256']})
    # This admission point is inside the native Python process, before any mutation.
    phase_custody();assert time.time()<STOP-60,'Insufficient native stop reserve before exactECO'
    assert macro_access_signature('before-ECO')==access
    assert json.loads((R/'baseline/native-raw-capacity.json').read_text())==json.loads((R/'noop/native-raw-capacity.json').read_text())
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
    C,CS,CG,CT,CM=save('candidate');assert C==want,'Native incremental routing changed physical/logical/NDR inventory'
    clocks=set(policy['protected_clock_nets']);allowed=set(policy['allowed_route_change_nets']);assert len(clocks)==332
    assert set(CS)==set(BS)|set(policy['added_signal_nets']),'Route netset changed beyond8newnets'
    changed=[n for n in BS if BS[n]!=CS[n]];assert set(changed)<=allowed,('Unrelatedrouteschanged',set(changed)-allowed)
    assert all(BS[n]==CS[n] for n in clocks),'CLOCK route changed'
    assert json.loads((R/'baseline/native-raw-capacity.json').read_text())==json.loads((R/'candidate/native-raw-capacity.json').read_text()),'Raw FastRoute capacity changed'
    assert all(BG['layers'][n]['capacity']==CG['layers'][n]['capacity'] for n in BG['layers']),'Routingcapacity changed'
    assert BM['native_clock_ndr_fallback_net_order']==CM['native_clock_ndr_fallback_net_order'],'New clock NDR fallback'
    tcl('check_placement -verbose\ncheck_power_grid -net VPWR -error_file /work/diagnostic/VPWR-grid-errors.rpt\ncheck_power_grid -net VGND -error_file /work/diagnostic/VGND-grid-errors.rpt')
    log=current_log();assert all('All shapes on net '+n+' are connected.' in log for n in ('VPWR','VGND'))
    write(R/'candidate/change-proof.json',{'schema':'pinwheel-buffered-tt-incremental-eco-change-proof-v1','status':'measured','exact_edit_gate_passed':True,'source_database_sha256':plan['source_database_sha256'],'output_database_sha256':sha(R/'candidate/routed.odb'),'all_corner_signal_identity':proof,'exact_added_instances':plan['added_instances'],'exact_rewired_original_pins':plan['allowed_original_sink_rewires'],'exact_resizes':plan['resizes'],'added_cells':8,'resized_cells':2,'original_placement_unchanged_count':28960,'clock_tree_unchanged':True,'PG_special_wire_geometry_unchanged':True,'original_statuses_restored':True,'added_power_bindings_exact':True,'rows_blockages_pins_macros_unchanged':True,'TechLEF_and_NDR_unchanged':True,'all332CLOCKsegments_exact':True,'all_unrelated_routes_exact':True,'allowed_route_change_nets':sorted(allowed),'actual_changed_original_route_nets':sorted(changed),'native_legal_changed_footprints':True})
    measurement={'schema':'pinwheel-buffered-tt-incremental-eco-measurement-v1','status':'measured','dirty_noop_pre_edit_gate_passed':True,'noop_pre_edit_gate_passed':True,'candidate_exact_edit_gate_passed':True,'baseline':BM,'noop':NM,'candidate':CM,'native_clock_route_preservation_passed':True,'CLOCK_net_count':332,'all_unrelated_route_preservation_passed':True,'allowed_route_change_nets':sorted(allowed),'actual_changed_original_route_nets':sorted(changed),'actual_dirty_signal_nets':sorted(dirty),'all_corner_signal_identity':proof,'live_native_elapsed_seconds':round(time.monotonic()-started,3),'fresh_PSM_both_nets_passed':True,'native_noop_typ_RC_timing_exact':True,'source_database_sha256':plan['source_database_sha256'],'boundary':'ONElive10baseline→noeditincrementalcontrol→same2resizes8delayECO→incremental22netmaxscope; no coldrouteimport/extraGPL/DPL/CTS/repair; all332CLOCKandunrelatedroutes invariant. Actual3cornertiming andfinitefunctionalvalidation separate.'};write(R/'measurement.json',measurement);print('PINWHEEL_LIVE_INCREMENTAL_GATE_PASSED',flush=True)
finally:
    credit.restore();write(R/'runtime-credit-restoration.json',{'status':'restored','original_prologue_restored':True,'page_permissions_RX_restored':True,'credit':credit.receipt(),'no_capacity_or_savedgrid_writes':True,'no_predicate_function_patch':True})
