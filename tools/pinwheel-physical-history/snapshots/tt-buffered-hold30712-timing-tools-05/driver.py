"""Bounded hold30712 exact saved-route preflight/control/candidate timing."""
import argparse,datetime,hashlib,json,math,re,shutil,time
from pathlib import Path
from common import ROOT,IMAGE,execute,read,sha,write
from segments import parse_segments
TOOLS=Path(__file__).resolve().parent;STOP=datetime.datetime.fromisoformat('2026-10-13T18:51:40+00:00').timestamp();DEADLINE=datetime.datetime.fromisoformat('2026-10-13T18:52:46+00:00').timestamp()
SELECTION=ROOT/'physical/experiments/tt-buffered-hold30712-selection-01.json';SELECT_SHA='452d91c56f500c1e5a14f46ce4107dc740e543ad798750107b5c478e780efcad';PRIOR=ROOT/'build/physical/tt-buffered-incremental-eco-route-03';OLDSTA=ROOT/'build/physical/tt-buffered-incremental-eco-candidate-timing-05';NEWPROD=ROOT/'build/physical/tt-buffered-hold30712-route-02'
RETRY=ROOT/'build/physical/tt-buffered-hold30712-root-01/matched-control-retry-admission.json';RETRY_SHA='0a32b76f2e164afe73125094e14077b8096bca94a338f684bac3b9059ce26e0b'
PREFLIGHT=ROOT/'build/physical/tt-buffered-hold30712-preflight-01'
def hashes(v,base=ROOT):
 for n,h in v.items():
  p=Path(n);assert sha(p if p.is_absolute() else base/p)==h,('Changed source',n)
def producer(p,selection_sha):
 d=read(p/'report.json');assert d['status']=='passed' and d['exit_code']==0 and d['inputs_unchanged'] and d['image_id']==IMAGE and d['selection_sha256']==selection_sha
 assert d['container_termination']['status']=='absent' and not d['container_termination']['owned_container_ids']
 assert d['container_termination']['ownership_label']==d['ownership_label'];hashes(d['input_sha256']);hashes(d['artifact_sha256'],p);return d

def main():
 p=argparse.ArgumentParser();p.add_argument('--mode',choices=['candidate'],required=True);a=p.parse_args();started=time.monotonic();prepared=read(TOOLS/'prepared.json');hashes(prepared['tool_sha256'],TOOLS);hashes(prepared['source_sha256']);assert sha(SELECTION)==SELECT_SHA
 sel=read(SELECTION);assert sel['schema']=='pinwheel-buffered-tt-hold30712-selection-v1';hashes(sel['protected_sources_sha256']);assert len(sel['protected_sources_sha256'])==507
 if a.mode=='preflight':
  d=producer(PRIOR,'aa744ff554b4dd62d8dec2aa6be96292e11b0d7876b2cbb915ed88c9ab53c20e');source=PRIOR;stages=['preflight'];source_stage={'preflight':'candidate'}
 else:
  source=NEWPROD;d=producer(source,SELECT_SHA);stages=['baseline','noop'] if a.mode=='control' else ['candidate'];source_stage={x:x for x in stages}
  assert d['schema']=='pinwheel-buffered-tt-hold30712-route-v1' and d['measurement']['status']=='measured' and d['measurement']['dirty_noop_pre_edit_gate_passed'] and d['measurement']['candidate_exact_edit_gate_passed']
  assert d['measurement']['qualified_control_reproduction_passed'] and d['measurement']['native_pure_placement_scope_passed']
 assert sha(RETRY)==RETRY_SHA;retry=read(RETRY);assert retry['selection_sha256']==SELECT_SHA and retry['max_actual_placement_candidates']==1 and retry['one_control_protocol_retry_only'] and retry['new_dirty_current_control_nets']==['_03216_','timing_eco_hold_30712_D']
 amend=ROOT/'build/physical/tt-buffered-hold30712-root-01/candidate-timing-budget-amendment-03.json';assert amend.exists();budget=read(amend);assert budget['native_stop_utc']=='2026-10-13T18:51:40Z' and budget['full_deadline_utc']=='2026-10-13T18:52:46Z';
 pre=read(PREFLIGHT/'report.json');assert pre['status']=='passed' and pre['inputs_unchanged'];hashes(pre['input_sha256']);hashes(pre['artifact_sha256'],PREFLIGHT)
 identity={};old=PRIOR/'candidate';prestage=PREFLIGHT/'preflight'
 assert sha(source/'core.sdc')==sha(prestage/'core.sdc') and sha(source/'baseline-env.tcl')==sha(PRIOR/'baseline-env.tcl')
 producerlibs={q.name:sha(q) for q in (source/'lib').glob('*.lib')};prelibs={q.name:sha(q) for q in (prestage/'lib').glob('*.lib')};assert len(producerlibs)==5 and len(prelibs)==9 and all(prelibs.get(n)==h for n,h in producerlibs.items())
 for name in ['baseline','noop']:
  f=source/name;assert read(f/'native-inventory.json')==read(old/'native-inventory.json')
  assert parse_segments(f/'after_grt.segments')==parse_segments(old/'after_grt.segments')==parse_segments(prestage/'after_grt.segments')
  assert sha(f/'after.v')==sha(old/'after.v') and sha(f/'estimated.spef')==sha(old/'estimated.spef')==sha(prestage/'nom_typ_1p20V_25C/estimated.spef')
  assert read(f/'native-raw-capacity.json')==read(old/'native-raw-capacity.json')
  a,b=read(f/'geometry.json'),read(old/'geometry.json')
  for key in ['dbu_per_micron','die_bbox_dbu','grid_x','grid_y','layers','macros','macro_obstructions','macro_pins','cells','power_boxes']:assert a[key]==b[key],('Currentcontrol geometry differs',name,key)
  identity[name]={'full_native_inventory_exact':True,'canonical_segments_exact':True,'netlist_bytes_exact':True,'nominal_estimated_SPEF_bytes_exact':True,'all_raw_capacity_arrays_exact':True,'all_physical_geometry_and_saved_grid_capacity_usage_exact':True}
 gate=read(PREFLIGHT/'headroom-gate.json');assert gate['admitted_to_move'] and gate['qualified_candidate_database_sha256']=='e0a0059bed3869367dccb72cc4e7d9029d81e5d735447668ae0b420b2889d629'
 reuse=ROOT/'build/physical/tt-buffered-hold30712-control-timing-03';reuse.mkdir()
 reuseinputs={**d['input_sha256'],**{str((source/n).resolve()):h for n,h in d['artifact_sha256'].items()},**pre['input_sha256'],**{str((PREFLIGHT/n).resolve()):h for n,h in pre['artifact_sha256'].items()},str(amend.resolve()):sha(amend),str(RETRY.resolve()):sha(RETRY),str((source/'report.json').resolve()):sha(source/'report.json'),str((PREFLIGHT/'report.json').resolve()):sha(PREFLIGHT/'report.json'),str((PREFLIGHT/'headroom-gate.json').resolve()):sha(PREFLIGHT/'headroom-gate.json'),str((TOOLS/'prepared.json').resolve()):sha(TOOLS/'prepared.json')}
 hashes(reuseinputs)
 write(reuse/'report.json',dict(schema='pinwheel-buffered-tt-hold30712-control-timing-reuse-v1',status='passed',exit_code=0,exit_code_scope='hostRCinputidentityvalidationonly',inputs_unchanged=True,input_sha256=reuseinputs,artifact_sha256={},producer_report_sha256=sha(source/'report.json'),preflight_report_sha256=sha(PREFLIGHT/'report.json'),preflight_report=str((PREFLIGHT/'report.json').relative_to(ROOT)),reused_preflight_three_corner_measurements=True,native_execution_performed=False,native_process_count=0,measurement=pre['measurement'],exact_current_control_RC_input_identity=identity,Lib9_SDC_nativeRCsource_exact=True,dirty_control_nets=retry['new_dirty_current_control_nets'],scope='Allcorner numeric preflightcontrol results transfer solely by exactnative/electrical/RCinput identity andnominalSPEF; no sixadditionalSTAprocesses orfabricatednativepassedreceipt.'))
 inv=read(source/source_stage[stages[0]]/'native-inventory.json');assert inv['nets']['_03216_']['terminals']==[['_29930_','Y','OUTPUT'],['timing_eco_hold_30712','A','INPUT']]
 assert inv['nets']['timing_eco_hold_30712_D']['terminals']==[['_30712_','D','INPUT'],['timing_eco_hold_30712','X','OUTPUT']]
 control_identity={}
 if a.mode=='control':
  b,n=source/'baseline',source/'noop';assert read(b/'native-inventory.json')==read(n/'native-inventory.json');assert sha(b/'after.v')==sha(n/'after.v');assert parse_segments(b/'after_grt.segments')==parse_segments(n/'after_grt.segments')
  for name in ['native-raw-capacity.json','typ-timing.json']:assert read(b/name)==read(n/name)
  gb,gn=read(b/'geometry.json'),read(n/'geometry.json');assert {k:v for k,v in gb.items() if k!='database_sha256'}=={k:v for k,v in gn.items() if k!='database_sha256'}
  control_identity={'all_corner_RC_input_identity':True,'dirty_noop_fresh_numeric_equality_required':True}
 tag='tt-buffered-hold30712-'+('preflight' if a.mode=='preflight' else a.mode+'-timing')+'-03';out=ROOT/'build/physical'/tag;out.mkdir();paths=[SELECTION,TOOLS/'prepared.json',*[TOOLS/n for n in prepared['tool_sha256']],source/'report.json',*[Path(n) for n in d['input_sha256']],*[source/n for n in d['artifact_sha256']],OLDSTA/'report.json',amend,RETRY,PREFLIGHT/'report.json',PREFLIGHT/'headroom-gate.json',reuse/'report.json'];expected={}
 def copy(src,name):
  target=out/name;target.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,target);assert sha(target)==sha(src);paths.extend((src,target));expected[str(target.resolve())]=sha(src)
 for n in ['timing-worker.py','coordinator.py','segments.py']:copy(TOOLS/n,n)
 prior=OLDSTA/'candidate';pi=read(prior/'inputs.json');reference=read(OLDSTA/'report.json')['measurement']['corners']
 for stage in stages:
  folder=source/source_stage[stage];si=read(folder/'native-inventory.json');copy(folder/'routed.odb',stage+'/checkpoint.odb');copy(folder/'after_grt.segments',stage+'/after_grt.segments');copy(TOOLS/'route-corner.tcl',stage+'/route-corner.tcl')
  for name in ['baseline-env.tcl','core.sdc']:copy(prior/name,stage+'/'+name)
  for lib in (prior/'lib').glob('*.lib'):copy(lib,stage+'/lib/'+lib.name)
  assert len(list((out/stage/'lib').glob('*.lib')))==9
  defs=re.findall(r'(?ms)^NONDEFAULTRULES\s+\d+\s*;.*?^END NONDEFAULTRULES',(folder/'routed.def').read_text());assert len(defs)==1 and not re.search(r'\+\s+(?:VIA|USEVIA|USEVIARULE)\b',defs[0])
  write(out/stage/'inputs.json',dict(corners=pi['corners'],native_script_sha256=pi['native_script_sha256'],route_source_report_sha256=sha(source/'report.json'),routed_database_sha256=sha(folder/'routed.odb'),route_segments_sha256=sha(folder/'after_grt.segments'),netlist_sha256=sha(folder/'after.v'),post_route_ndr_map={k:v['nondefault_rule'] for k,v in si['nets'].items()},canonical_block_NDR_DEF_sha256=hashlib.sha256(defs[0].encode()).hexdigest(),endpoints=['_30712_/D'],reproduction_required=a.mode!='candidate',retained_reference_corners=reference,scope='Exactsavedglobalroutes/9Lib/SDC; fullglobalSTA+targeted30712max/min; _03216_singleloads→delayA→30712D. Conditionalfast−40logic/−55SRAM; no optimization/routing/placementestimate orsignoff.'));paths.append(out/stage/'inputs.json')
 write(out/'stage-plan.json',dict(stages=stages,arm=a.mode,producer_report_sha256=sha(source/'report.json'),baseline_noop_native_input_identity=control_identity));paths.append(out/'stage-plan.json')
 assert time.time()<STOP,'Absolute nativeSTOP already elapsed';assert time.monotonic()-started<=40,'Hoststage40 exceeded'
 report=execute(out,paths,['python3','-B','/work/diagnostic/coordinator.py'],seconds=90,cpus=3,memory='3g',schema='pinwheel-buffered-tt-hold30712-timing-v1',scope='Fresh3corners+exact30712max/min; preflight/control reproducequalifiedreference, controlbaseline/noop6numericprocesses mustequal; candidateindependent3. No movement/routing/optimization.',expected_hashes=expected,absolute_work_stop=STOP,all_in_deadline_monotonic=started+min(170,DEADLINE-time.time()),phase_started_monotonic=started,extra=dict(mode=a.mode,control_timing_reused=True,control_reuse_report_sha256=sha(reuse/'report.json'),budget_amendment_sha256=sha(amend),retry_admission_sha256=RETRY_SHA,selection_sha256=SELECT_SHA,producer_report_sha256=sha(source/'report.json'),producer_report=str((source/'report.json').relative_to(ROOT)),absolute_native_work_stop_utc='2026-10-13T18:51:40Z',route_based_only=True,parasitic_model='estimate_parasitics -global_routing',affected_endpoint='_30712_/D',affected_input_load='timing_eco_hold_30712/A'))
 report['all_in_elapsed_seconds']=round(time.monotonic()-started,3);report['overall_bound_seconds']=170
 if report['all_in_elapsed_seconds']>170 or time.time()>DEADLINE:report['status']='bound_exceeded'
 write(out/'report.json',report)
 if a.mode=='preflight' and report['status']=='passed':
  values=[c['endpoint_headroom']['_30712_/D'] for c in report['measurement']['corners'].values()];passed=all(v['setup_slack_ns']>=1 and v['hold_slack_ns']>=.05 for v in values)
  write(out/'headroom-gate.json',dict(schema='pinwheel-buffered-tt-hold30712-preflight-gate-v1',status='passed' if passed else 'failed',admitted_to_move=passed,report=str((out/'report.json').relative_to(ROOT)),report_sha256=sha(out/'report.json'),qualified_candidate_database_sha256=report['measurement']['routed_database_sha256'],qualified_candidate_route_segments_sha256=report['measurement']['route_segments_sha256'],worst_target_setup_ns=min(v['setup_slack_ns'] for v in values),worst_target_hold_ns=min(v['hold_slack_ns'] for v in values),endpoint='_30712_/D',all_03216_sinks=[['timing_eco_hold_30712','A']],transfer_only_if_rebuilt_control_exact_identity=True))
 print(out/'report.json',report['status'],flush=True);return 0 if report['status']=='passed' else 1
if __name__=='__main__':raise SystemExit(main())
