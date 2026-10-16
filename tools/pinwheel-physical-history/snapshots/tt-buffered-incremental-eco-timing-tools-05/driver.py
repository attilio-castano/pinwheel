"""Fresh six-process baseline/noop control or three-process candidate route RC."""
import argparse,datetime,json,math,re,shutil,sys,time
from pathlib import Path
from common import ROOT,IMAGE,execute,read,sha,write
from segments import parse_segments
TOOLS=Path(__file__).resolve().parent;SOURCE='95f0fdb260de137d5b4f77669c9aaa5eb3bf56e7dc55f4c9b7d51b2b8a16556e';STOP=datetime.datetime.fromisoformat('2026-10-13T17:42:14+00:00').timestamp();DEADLINE=STOP+120

def hashes(values,base=ROOT):
 for n,h in values.items():
  p=Path(n);assert sha(p if p.is_absolute() else base/p)==h,('Changed source',n)
def physical_noop(base,no):
 assert read(base/'native-inventory.json')==read(no/'native-inventory.json'),'No-op physical/electrical native signature changed'
 assert sha(base/'after.v')==sha(no/'after.v'),'No-op netlist changed'
 a,b=parse_segments(base/'after_grt.segments'),parse_segments(no/'after_grt.segments');assert a==b,'No-op segment netset/multiset changed'
 x,y=read(base/'geometry.json'),read(no/'geometry.json')
 assert set(x)==set(y),'No-op geometry schema changed'
 assert {k:v for k,v in x.items() if k!='database_sha256'}=={k:v for k,v in y.items() if k!='database_sha256'},'No-op entire geometry changed beyond database bytehash'
 assert x['database_sha256']==sha(base/'routed.odb') and y['database_sha256']==sha(no/'routed.odb')
 t,u=read(base/'typ-timing.json'),read(no/'typ-timing.json')
 ignored={'stage','database_sha256','routed_database_sha256','source_database_sha256','scope'}
 assert {k:v for k,v in t.items() if k not in ignored}=={k:v for k,v in u.items() if k not in ignored},'No-op live typRC/clock timing changed'
 return dict(native_inventory_exact=True,netlist_byte_equal=True,segment_netset_multiset_equal=True,native_grid_capacity_usage_and_all_geometry_equal=True,live_typ_RC_clock_equality=True,raw_ODB_byte_equal=sha(base/'routed.odb')==sha(no/'routed.odb'),all_corner_RC_input_identity=True)
def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--selection',type=Path,required=True);p.add_argument('--producer-report',type=Path,required=True);p.add_argument('--rejected-audit',type=Path,required=True);p.add_argument('--arm',choices=['control','candidate'],required=True);p.add_argument('--tag',required=True);a=p.parse_args();started=time.monotonic()
 assert a.tag=='tt-buffered-incremental-eco-'+a.arm+'-timing-03'
 pr=read(TOOLS/'prepared.json');hashes(pr['tool_sha256'],TOOLS);hashes(pr['derivation_sha256'])
 sel=read(a.selection);assert sel['schema']=='pinwheel-buffered-tt-incremental-eco-diagnostic-selection-v1'
 if 'references' in sel and 'timing_tools' in sel['references']:
  r=sel['references']['timing_tools'];assert (ROOT/r['path']).resolve()==(TOOLS/'prepared.json').resolve() and r['sha256']==sha(TOOLS/'prepared.json')
 else:assert sel['tool_sha256'][str((TOOLS/'prepared.json').relative_to(ROOT))]==sha(TOOLS/'prepared.json')
 for key in ['source_custody_sha256','tool_sha256']:
  if key in sel:hashes(sel[key])
 source=a.producer_report.resolve();assert source==(ROOT/'build/physical/tt-buffered-incremental-eco-route-02/report.json').resolve()
 prod=read(source);assert prod['schema']=='pinwheel-buffered-tt-incremental-eco-route-v1' and prod['status']=='failed' and prod['exit_code']==1 and prod['inputs_unchanged']
 assert prod['source_database_sha256']==SOURCE and prod['selection_sha256']==sel['references']['original_selection']['sha256'] and prod['image_id']==IMAGE
 assert prod['container_termination']['status']=='absent' and not prod['container_termination']['owned_container_ids'] and prod['container_termination']['ownership_label']==prod['ownership_label']
 hashes(prod['input_sha256']);hashes(prod['artifact_sha256'],source.parent)
 original_ref=sel['references']['original_selection'];original_path=ROOT/original_ref['path'];assert sha(original_path)==original_ref['sha256'] and original_path.resolve()==(ROOT/'physical/experiments/tt-buffered-incremental-eco-selection-02.json').resolve()
 assert prod['exact_plan_sha256']=='441228b9b545fd9045f9ef9fa3ae4ec619ac2c656a661d363e0a1d843205f9d5'
 assert sel['diagnostic_only'] and sel['candidate_physical_status']=='rejected_due_to_capacity_drift'
 assert sel['references']['producer']['sha256']==sha(source) and (ROOT/sel['references']['producer']['path']).resolve()==source
 audit_path=a.rejected_audit.resolve();audit=read(audit_path);ar=sel['references']['rejected_audit'];assert (ROOT/ar['path']).resolve()==audit_path and ar['sha256']==sha(audit_path)
 assert audit['status']=='rejected_due_to_capacity_drift' and audit['producer_report_sha256']==sha(source) and audit['source_database_sha256']==SOURCE and audit['exact_plan_sha256']==prod['exact_plan_sha256']
 hashes(audit['source_sha256']);g=audit['diagnostic_admission_gates'];assert g['all332CLOCKsegments_exact'] and g['all_unrelated_route_segments_exact'] and g['complete_exact_2resize_8addition_inventory_verified'] and g['all_artifact_and_input_custody_current'] and g['capacity_drift_measured']
 log=(source.parent/'execution.log').read_text();assert 'AssertionError: Routingcapacity changed' in log
 assert read(source.parent/'noop-gate.json')['status']=='passed' and read(source.parent/'noop-gate.json')['noop_pre_edit_gate_passed']
 no_op=physical_noop(source.parent/'baseline',source.parent/'noop')
 stages=['baseline','noop'] if a.arm=='control' else ['candidate'];prior=ROOT/'build/physical/tt-buffered-route-effort-probe-timing-01';pi=read(prior/'inputs.json')
 out=ROOT/'build/physical'/a.tag;out.mkdir();paths=[source,a.selection,audit_path,original_path,TOOLS/'prepared.json',*[TOOLS/n for n in pr['tool_sha256']],*[Path(n) for n in prod['input_sha256']],*[source.parent/n for n in prod['artifact_sha256']],prior/'inputs.json'];expected={}
 def copy(src,name):
  target=out/name;target.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,target);assert sha(src)==sha(target);paths.extend((src,target));expected[str(target.resolve())]=sha(src)
 for n in ['timing-worker.py','segments.py','coordinator.py']:copy(TOOLS/n,n)
 for stage in stages:
  folder=source.parent/stage;inv=read(folder/'native-inventory.json');copy(folder/'routed.odb',stage+'/checkpoint.odb');copy(folder/'after_grt.segments',stage+'/after_grt.segments')
  for n in ['baseline-env.tcl','core.sdc']:copy(prior/n,stage+'/'+n)
  copy(TOOLS/'route-corner.tcl',stage+'/route-corner.tcl')
  for lib in (prior/'lib').glob('*.lib'):copy(lib,stage+'/lib/'+lib.name)
  assert len(list((out/stage/'lib').glob('*.lib')))==9
  defs=re.findall(r'(?ms)^NONDEFAULTRULES\s+\d+\s*;.*?^END NONDEFAULTRULES',(folder/'routed.def').read_text());assert len(defs)==1 and not re.search(r'\+\s+(?:VIA|USEVIA|USEVIARULE)\b',defs[0])
  inputs=dict(corners=pi['corners'],native_script_sha256=pi['native_script_sha256'],route_source_report_sha256=sha(source),routed_database_sha256=sha(folder/'routed.odb'),route_segments_sha256=sha(folder/'after_grt.segments'),netlist_sha256=sha(folder/'after.v'),post_route_ndr_map={n:v['nondefault_rule'] for n,v in inv['nets'].items()},canonical_block_NDR_DEF_sha256=__import__('hashlib').sha256(defs[0].encode()).hexdigest(),scope='FreshrouteRC nooptimization/placementfallback; matched9libs/SDC, conditionalfast-40logic/-55SRAM. No-op electricalinputidentity plusindependentnumericcorners; notextracted/signoff.')
  write(out/stage/'inputs.json',inputs);paths.append(out/stage/'inputs.json')
 write(out/'stage-plan.json',dict(stages=stages,arm=a.arm,producer_report_sha256=sha(source),baseline_noop_native_input_identity=no_op));paths.append(out/'stage-plan.json')
 now=time.time();assert now<=STOP-140 and now+200<=DEADLINE,'Insufficient nativework/cleanup deadline reserve'
 stage_time=time.monotonic()-started;assert stage_time<=10,'Hoststage reserve exceeded';work=min(140,math.floor(STOP-now),math.floor(200-stage_time-60));assert work>0
 report=execute(out,paths,['python3','-B','/work/diagnostic/coordinator.py'],seconds=work,cpus=3,memory='3g',schema='pinwheel-buffered-tt-incremental-eco-diagnostic-timing-v1',scope='Matched freshrouteRC: controlbaseline+noop6processes mustequalnumericmetrics/SPEF/DBNDR/segments foreach3corner; candidate3processes. No routing, optimization orplacement estimates.',expected_hashes=expected,extra=dict(arm=a.arm,diagnostic_only=True,candidate_physical_status='rejected_due_to_capacity_drift',original_producer_status='failed',original_producer_exit_code=1,rejected_audit_sha256=sha(audit_path),rejected_audit=str(audit_path.relative_to(ROOT)),producer_report=str(source.relative_to(ROOT)),producer_report_sha256=sha(source),selection_sha256=sha(a.selection),baseline_noop_native_input_identity=no_op,route_based_only=True,parasitic_model='estimate_parasitics -global_routing',reference_database_sha256=SOURCE,absolute_native_work_stop_utc='2026-10-13T17:42:14Z'))
 report['all_in_elapsed_seconds']=round(time.monotonic()-started,3);report['overall_bound_seconds']=200
 if report['all_in_elapsed_seconds']>200 or time.time()>DEADLINE:report['status']='bound_exceeded'
 write(out/'report.json',report);print(out/'report.json',flush=True);return 0 if report['status']=='passed' else 1
if __name__=='__main__':raise SystemExit(main())
