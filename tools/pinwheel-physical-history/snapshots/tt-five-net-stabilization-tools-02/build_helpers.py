import ast,hashlib,json,shutil
from pathlib import Path
ROOT=Path.cwd();H=Path(__file__).resolve().parent;A=ROOT/'build/physical/tt-five-terminal-physical-tools-02'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_text())
def write(p,v):Path(p).write_text(json.dumps(v,indent=2)+'\n')
assert not(H/'prepared.json').exists()
for f in A.iterdir():
 if f.name in ['prepared.json','selection.json','build_helpers.py']:continue
 if f.is_file():shutil.copyfile(f,H/f.name)
 elif f.name in ['identity','lib']:shutil.copytree(f,H/f.name)
oldnets=['_00006_','_03109_','net8042','net8046','net9291'];source=read(H/'qualified-buf4-source.json')
policy={'schema':'pinwheel-five-net-stabilization-policy-v1','source_database_sha256':source['source_database_sha256'],'source_segments_sha256':source['source_segments_sha256'],'passes':2,'congestion_iterations':10,'dirty_signal_nets':oldnets,'no_additions_resizes_or_placement_changes_after_BUF4':True,'native_stop_utc':'2026-10-14T16:55:36Z','phase_deadline_utc':'2026-10-14T16:56:16Z','hard_final_deadline_utc':'2026-10-14T16:57:36Z'};write(H/'five-net-policy.json',policy)
c=(H/'common.py').read_text();assert c.count('assert seconds==480')==1;c=c.replace('assert seconds==480','assert seconds==600');(H/'common.py').write_text(c)
live=(H/'live.py').read_text();prefix=live.split("    # NEW treatment starts only after the entire immutable warm BUF4 replay.")[0]
assert prefix.endswith('\n')
extra=r'''
    # NEW no-edit study, after immutable full warm BUF4 source reproduction.
    source_buf4=json.loads((R/'qualified-buf4-source.json').read_text());Q4=R/'qualified-buf4';five=json.loads((R/'five-net-policy.json').read_text())
    assert C==json.loads((Q4/'native-inventory.json').read_text()),'Saved BUF4 whole native inventory not reproduced'
    assert CS==canonical(Q4/'after_grt.segments') and sha(R/'buf4-reproduced/after_grt.segments')==source_buf4['source_segments_sha256'],'Saved BUF4 routes not reproduced'
    qg=json.loads((Q4/'geometry.json').read_text());assert {k:v for k,v in CG.items() if k!='database_sha256'}=={k:v for k,v in qg.items() if k!='database_sha256'},'Saved BUF4 grid not reproduced'
    assert json.loads((R/'buf4-reproduced/native-raw-capacity.json').read_text())==json.loads((Q4/'native-raw-capacity.json').read_text())
    assert CT==json.loads((Q4/'typ-timing.json').read_text()),'Saved BUF4 nominal full RC/timing not reproduced'
    qm=json.loads((Q4/'route-state.json').read_text());assert {k:v for k,v in CM.items() if k not in ('live_router_pointer','live_process_pid')}=={k:v for k,v in qm.items() if k not in ('live_router_pointer','live_process_pid')}
    assert sha(R/'buf4-reproduced/after.v')==sha(Q4/'after.v') and sha(R/'buf4-reproduced/estimated.spef')==sha(Q4/'estimated.spef')
    assert five['source_database_sha256']==source_buf4['source_database_sha256'] and five['source_segments_sha256']==source_buf4['source_segments_sha256'] and five['passes']==2 and five['congestion_iterations']==10
    write(R/'qualified-buf4-reproduction-gate.json',{'status':'passed','qualified_buf4_reproduction_passed':True,'all_native_inventory_routes_grid_rawcapacity_NL_nominalSPEF_timing_counts_NDR_exact':True,'source_database_sha256':source_buf4['source_database_sha256'],'source_segments_sha256':source_buf4['source_segments_sha256']})
    B,BS,BG,BT,BM=C,CS,CG,CT,CM
    for old in ('N','NS','NG','NT','NM','wanted','actual','before_module','after_module','qg','qm','before_rc','after_rc'):globals().pop(old,None)
    gc.collect()
    allowed=set(five['dirty_signal_nets']);assert allowed=={'_00006_','_03109_','net8042','net8046','net9291'} and len(clocks)==332
    for name in allowed:assert B['nets'][name]['sig_type']=='SIGNAL' and B['nets'][name]['nondefault_rule'] is None
    base_raw=json.loads((Q4/'native-raw-capacity.json').read_text());base_rc=spef_networks(Q4/'estimated.spef');previous=None;outcomes=[]
    for pass_number in (1,2):
        phase='pass'+str(pass_number)+'-five';phase_custody();assert time.time()<STOP-45,'Insufficient pass capture reserve'
        assert macro_access_signature(phase+'-before-dirty')==access
        marker='PINWHEEL_FIVE_NET_STABILIZATION_PASS_'+str(pass_number)+'_BEGIN';print(marker,flush=True)
        tcl('global_route -congestion_iterations 10 -start_incremental')
        cache=[invalidate_one(design.getGlobalRouter(),design.getBlock().findNet(n)) for n in sorted(allowed)]
        tcl('global_route -congestion_iterations 10 -end_incremental -allow_congestion')
        log=current_log().split(marker)[-1];assert 'Dirty nets:' in log;found=[]
        for line in log.split('Dirty nets:',1)[1].splitlines():
            if not line.strip():continue
            match=re.match(r'^\[DEBUG GRT-incr\]\s+(\S+)\s*$',line)
            if not match:break
            found.append(match[1])
        assert set(found)==allowed and len(found)==5,('Exact five-old-net worklist failed',pass_number,found)
        X,XS,XG,XT,XM=save(phase);assert X==B,'No-edit pass changed source inventory/master/placement/connectivity/PG/rows/macros/NDR'
        assert set(XS)==set(BS),'No-edit route netset changed'
        changed=sorted(n for n in BS if XS[n]!=BS[n]);assert set(changed)<=allowed and all(XS[n]==BS[n] for n in clocks),'CLOCK/unrelated route changed'
        assert all(XG['layers'][n]['capacity']==BG['layers'][n]['capacity'] for n in BG['layers']),'Saved routing capacities changed'
        raw=json.loads((R/phase/'native-raw-capacity.json').read_text());assert raw==base_raw,'Raw FastRoute capacities changed'
        assert sha(R/phase/'after.v')==sha(Q4/'after.v'),'No-edit logical netlist changed'
        assert XM['native_clock_ndr_fallback_net_order']==BM['native_clock_ndr_fallback_net_order'],'CLOCK NDR fallback changed'
        assert macro_access_signature(phase+'-after-dirty')==access
        rc=spef_networks(R/phase/'estimated.spef');assert set(rc)==set(base_rc),'Native RC netset changed'
        changed_rc=sorted(n for n in base_rc if rc[n]!=base_rc[n]);assert set(changed_rc)<=allowed and all(rc[n]==base_rc[n] for n in clocks),'CLOCK/unrelated native RC changed'
        tcl(f'check_placement -verbose\ncheck_power_grid -net VPWR -error_file /work/diagnostic/VPWR-{phase}-grid-errors.rpt\ncheck_power_grid -net VGND -error_file /work/diagnostic/VGND-{phase}-grid-errors.rpt')
        log=current_log().split(marker)[-1];assert all('All shapes on net '+n+' are connected.' in log for n in ('VPWR','VGND')),'Fresh pass PSM absent'
        item={'schema':'pinwheel-five-net-stabilization-pass-preservation-v1','phase':phase,'scope_preservation_passed':True,'actual_dirty_signal_nets':sorted(found),'actual_changed_routes_from_BUF4_source':changed,'actual_changed_RC_networks_from_BUF4_source':changed_rc,'no_inventory_changes_after_BUF4':True,'CLOCK332routes_and_native_RC_exact_source':True,'all_unrelated_routes_and_native_RC_exact_source':True,'raw_capacities_exact_source':True,'saved_capacity_exact_source':True,'netlist_bytes_exact_source':True,'macro_pin_access_exact':True,'fresh_PSM_both_nets_passed':True,'native_cache_invalidation':cache,'native':XM,'typical_timing':XT}
        if previous is not None:
            V,VS,VG,VT,VM,VRAW,VPHASE=previous
            comparisons={'full_native_inventory':X==V,'canonical_all_route_multisets':XS==VS,'logical_netlist_bytes':sha(R/phase/'after.v')==sha(R/VPHASE/'after.v'),'raw_FastRoute_capacities':raw==VRAW,'full_saved_geometry_capacity_usage':{k:v for k,v in XG.items() if k!='database_sha256'}=={k:v for k,v in VG.items() if k!='database_sha256'},'native_route_counts_NDR_state':XM==VM,'nominal_full_native_SPEF':sha(R/phase/'estimated.spef')==sha(R/VPHASE/'estimated.spef'),'nominal_all_report_bodies_and_worst_timing':XT==VT}
            item['exact_P1_P2_comparisons']=comparisons;item['stable']=all(comparisons.values());item['actual_route_changes_from_P1']=sorted(n for n in VS if VS[n]!=XS[n]);item['actual_RC_changes_from_P1']=sorted(n for n in rc if rc[n]!=spef_networks(R/VPHASE/'estimated.spef')[n])
        write(R/phase/'preservation-proof.json',item);outcomes.append(item);previous=(X,XS,XG,XT,XM,raw,phase)
    assert len(outcomes)==2 and outcomes[1]['stable'],'Five-old-net dirty no-edit did not stabilize P1/P2; no timing handoff admitted'
    write(R/'five-net-stabilization-gate.json',{'status':'passed','five_old_net_P1_P2_stabilized':True,'source_database_sha256':source_buf4['source_database_sha256'],'source_segments_sha256':source_buf4['source_segments_sha256'],'exact_P1_P2_comparisons':outcomes[1]['exact_P1_P2_comparisons'],'no_inventory_changes_after_BUF4':True,'CLOCK332_and_all_unrelated_routes_and_native_RC_exact_source':True,'native_raw_capacities_exact_source':True,'passes':2,'phase_names':['pass1-five','pass2-five']})
    measurement={'schema':'pinwheel-five-net-stabilization-measurement-v1','status':'measured','qualified_buf4_reproduction_passed':True,'qualified_stable_P2_reproduction_passed':True,'five_old_net_P1_P2_stabilized':True,'no_inventory_changes_after_BUF4':True,'native_clock_route_preservation_passed':True,'all_unrelated_route_preservation_passed':True,'all_unrelated_native_RC_preservation_passed':True,'native_raw_capacity_preservation_passed':True,'fresh_PSM_both_nets_passed':True,'source_database_sha256':source_buf4['source_database_sha256'],'source_segments_sha256':source_buf4['source_segments_sha256'],'baseline':BM,'passes':outcomes,'candidate':outcomes[1]['native'],'CLOCK_net_count':332,'dirty_signal_nets':sorted(allowed),'added_cell_count':0,'resized_cell_count':0,'live_native_elapsed_seconds':round(time.monotonic()-started,3),'boundary':'Warm originalR0 through repaired/30712/P2/BUF4 source exact replay; two five-old-net dirty no-edit passes; P1 may change only those routes/RC and usage; P2 exactly repeats P1 inventory/allroutes/fullnativeRC/grid/rawcap/NDR/nominaltiming. All sourceCLOCK/unrelated routesRC exact; no postBUF4cells/placement/connectivity edits. Fresh threecornerSTA separate.'}
    write(R/'measurement.json',measurement);print('PINWHEEL_FIVE_NET_STABILIZATION_GATE_PASSED',flush=True)
'''
finallypart=live.split('\nfinally:\n')[1];live=prefix+extra+'\nfinally:\n'+finallypart;live=live.replace('2026-10-14T16:07:19+00:00','2026-10-14T16:55:36+00:00');(H/'live.py').write_text(live)
# Actual route driver retains immutable staging and owns its one bounded child.
(H/'driver.py').write_text('''import argparse,datetime,json,shutil,time
from pathlib import Path
from common import ROOT,execute,sha,read,write
H=Path(__file__).resolve().parent
STOP=datetime.datetime.fromisoformat('2026-10-14T16:55:36+00:00').timestamp();DEADLINE=datetime.datetime.fromisoformat('2026-10-14T16:56:16+00:00').timestamp()
def verify(items):
 for n,h in items.items():
  p=Path(n) if Path(n).is_absolute() else ROOT/n;assert p.is_file() and sha(p)==h,n
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--selection',type=Path,required=True);ap.add_argument('--tag',default='tt-five-net-stabilization-route-01');a=ap.parse_args();started=time.monotonic();assert a.tag=='tt-five-net-stabilization-route-01'
 S=read(a.selection);P=read(H/'prepared.json');F=read(H/'five-net-policy.json');W=read(H/'stabilization-policy.json')
 assert S['schema']=='pinwheel-five-net-stabilization-selection-v1' and S['one_candidate_only'] and S['passes']==2 and S['routing_iterations']==10
 assert S['prepared_sha256']==sha(H/'prepared.json') and S['pair_policy_sha256']==sha(H/'pair-policy.json') and S['five_net_policy_sha256']==sha(H/'five-net-policy.json')
 assert S['source_database_sha256']==P['terminal_comparison_database_sha256']==F['source_database_sha256'] and S['source_segments_sha256']==P['terminal_source_segments_sha256']==F['source_segments_sha256']
 assert S['dirty_signal_nets']==F['dirty_signal_nets']==['_00006_','_03109_','net8042','net8046','net9291'] and S['post_BUF4_added_cells']==0 and S['post_BUF4_resizes']==0 and S['post_BUF4_placement_edits']==[]
 assert S['route_native_stop_utc']=='2026-10-14T16:55:36Z' and S['route_phase_deadline_utc']=='2026-10-14T16:56:16Z'
 verify(P['source_sha256']);verify(P['tool_sha256']);assert STOP-time.time()>90 and time.time()+30<DEADLINE
 O=ROOT/'build/physical'/a.tag;assert not O.exists();O.mkdir()
 for f in H.iterdir():
  if f.is_file():shutil.copyfile(f,O/f.name)
  elif f.name in ['identity','lib']:shutil.copytree(f,O/f.name)
 recipe=ROOT/'build/physical/tt-buffered-timing-eco-control-route-01';shutil.copyfile(ROOT/P['source_database'],O/'postcts.odb');shutil.copyfile(recipe/'before.v',O/'reference.v')
 for n in ['baseline-env.tcl','corner-env.tcl','core.sdc']:shutil.copyfile(recipe/n,O/n)
 for f in (recipe/'lib').glob('*.lib'):shutil.copyfile(f,O/'lib'/f.name)
 shutil.copyfile(a.selection,O/'selection.json')
 for n,folder in [('qualified-control-source.json','qualified-control'),('qualified-pair-source.json','qualified-pair'),('qualified-stable-source.json','qualified-stable'),('qualified-buf4-source.json','qualified-buf4')]:
  Q=O/folder;Q.mkdir()
  for name,d in read(H/n)['artifacts_sha256'].items():
   f=Path(name) if Path(name).is_absolute() else ROOT/name;assert sha(f)==d
   if f.name!='report.json':shutil.copyfile(f,Q/f.name)
 write(O/'phase-inputs.json',{str(Path('/work/diagnostic')/f.relative_to(O)):sha(f) for f in O.rglob('*') if f.is_file()})
 paths=[a.selection.resolve(),H/'prepared.json',*[Path(n) if Path(n).is_absolute() else ROOT/n for n in P['source_sha256']],*[Path(n) if Path(n).is_absolute() else ROOT/n for n in P['tool_sha256']],*[f for f in O.rglob('*') if f.is_file()]]
 r=execute(O,paths,['python3','-B','/work/diagnostic/coordinator.py'],seconds=600,cpus=4,memory='5g',schema='pinwheel-five-net-stabilization-route-v1',scope='Warm exact BUF4 replay followed by two five-old-net dirty no-edit passes; P2 exact P1; all sourceCLOCK/unrelatedroutesRC, inventory, PG/macros/rows andrawcapacities fixed.',extra={'network':'none','selection_sha256':sha(a.selection),'prepared_sha256':sha(H/'prepared.json'),'source_database_sha256':P['terminal_comparison_database_sha256'],'source_database':P['terminal_comparison_database'],'source_segments_sha256':P['terminal_source_segments_sha256'],'five_net_policy_sha256':sha(H/'five-net-policy.json')},expected_hashes={O/'postcts.odb':P['source_database_sha256']},absolute_work_stop=STOP,all_in_deadline_monotonic=min(started+660,time.monotonic()+DEADLINE-time.time()))
 r['all_in_elapsed_seconds']=round(time.monotonic()-started,3)
 if r['all_in_elapsed_seconds']>660 or time.time()>DEADLINE:r['status']='bound_exceeded'
 verify(P['source_sha256']);verify(P['tool_sha256']);write(O/'report.json',r);print(O/'report.json',r['status']);return 0 if r['status']=='passed' else 1
if __name__=='__main__':raise SystemExit(main())
''')
co=(H/'coordinator.py').read_text();co=co[:co.index("measurement=json.loads")]+"measurement=json.loads((R/'measurement.json').read_text());assert measurement['status']=='measured' and all(measurement[k] for k in ['qualified_buf4_reproduction_passed','five_old_net_P1_P2_stabilized','no_inventory_changes_after_BUF4','native_clock_route_preservation_passed','all_unrelated_route_preservation_passed','all_unrelated_native_RC_preservation_passed','native_raw_capacity_preservation_passed','fresh_PSM_both_nets_passed'])\n";(H/'coordinator.py').write_text(co)
for f in H.rglob('*.py'):ast.parse(f.read_text(),filename=str(f))
assert 'source /work/diagnostic/terminal-edit.tcl' not in live and "save('candidate')" not in live and 'No terminal edit/candidate capture reserve' not in live
P=read(A/'prepared.json');P.update(schema='pinwheel-five-net-stabilization-prepared-v1',native_work_seconds_at_most=600,all_in_cap_seconds=660,native_stop_utc='2026-10-14T16:55:36Z',deadline_utc='2026-10-14T16:56:16Z',five_net_policy_sha256=sha(H/'five-net-policy.json'),passes=2,dirty_signal_nets=oldnets,no_sizing=True,terminal_headroom_gate_required_before_launch=False,parent_prepared_sha256=sha(A/'prepared.json'))
newroot=ROOT/'build/physical/tt-five-net-stabilization-root-01/plan.json'
if newroot.exists():P['source_sha256'][str(newroot)]=sha(newroot)
P['tool_sha256']={str(f.resolve()):sha(f) for f in H.rglob('*') if f.is_file() and f.name not in ['prepared.json','selection.json'] and '__pycache__' not in f.parts};write(H/'prepared.json',P)
S={'schema':'pinwheel-five-net-stabilization-selection-v1','started_utc':'2026-10-14T16:32:36Z','native_stop_utc':'2026-10-14T16:55:36Z','deadline_utc':'2026-10-14T16:57:36Z','full_bound_seconds':1500,'no_extension':True,'source_database_sha256':P['terminal_comparison_database_sha256'],'source_segments_sha256':P['terminal_source_segments_sha256'],'dirty_signal_nets':oldnets,'passes':2,'routing_iterations':10,'prepared_sha256':sha(H/'prepared.json'),'pair_policy_sha256':P['pair_policy_sha256'],'five_net_policy_sha256':sha(H/'five-net-policy.json'),'one_candidate_only':True,'post_BUF4_added_cells':0,'post_BUF4_resizes':0,'post_BUF4_placement_edits':[],'route_native_stop_utc':'2026-10-14T16:55:36Z','route_phase_deadline_utc':'2026-10-14T16:56:16Z','execution_caps':{'route_native_seconds':600,'route_all_in_seconds':660,'route_cpus':4,'route_memory':'5g','network':'none','sequential_CAD_only':True},'P1_drift_only_five_old_signal_nets':True,'P2_requires_exact_P1_all_native_inventory_routes_RC_grid_rawcapacity_NDR_nominal_timing':True,'RTL_ABI_clocks_unrelated_routes_RC_frozen':True,'no_baseline_promotion':True,'no_auto_repair_or_full_reroute_fallback':True}
if newroot.exists():S['root_plan_sha256']=sha(newroot)
write(H/'selection.json',S)
print(json.dumps({'prepared_sha256':sha(H/'prepared.json'),'selection_sha256':sha(H/'selection.json'),'common_sha256':sha(H/'common.py'),'live_sha256':sha(H/'live.py'),'root_plan_bound':newroot.exists(),'CLI':f"python3 -B {H.relative_to(ROOT)}/driver.py --selection {H.relative_to(ROOT)}/selection.json --tag tt-five-net-stabilization-route-01"},indent=2))
