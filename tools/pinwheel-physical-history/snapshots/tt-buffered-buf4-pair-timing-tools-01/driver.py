"""Three fresh native route-RC corners, immutable arm and producer binding."""
import argparse,datetime,hashlib,json,re,shutil,time
from pathlib import Path
from common import ROOT,IMAGE,read,sha,write,execute
from segments import parse_segments
T=Path(__file__).resolve().parent
G=ROOT/'build/physical/tt-buffered-hold30712-route-02/candidate'
R=ROOT/'build/physical/tt-buffered-holdreset-pair-preflight-01'
L=R/'preflight'
CORNERS={'nom_typ_1p20V_25C','nom_slow_1p08V_125C','nom_fast_1p32V_m40C'}
def main():
 p=argparse.ArgumentParser();p.add_argument('--arm',choices=['control','candidate'],required=True);p.add_argument('--producer-report',type=Path,required=True);p.add_argument('--producer-sha256',required=True);p.add_argument('--selection',type=Path,required=True);p.add_argument('--selection-sha256',required=True);p.add_argument('--control-report',type=Path);p.add_argument('--tag',required=True);a=p.parse_args();started=time.monotonic()
 assert re.fullmatch(r'tt-buffered-buf4-pair-(control|candidate)-timing-[0-9]+',a.tag)
 selection=a.selection.resolve();producer_path=a.producer_report.resolve();assert selection.is_relative_to(ROOT) and producer_path.is_relative_to(ROOT);assert sha(selection)==a.selection_sha256 and sha(producer_path)==a.producer_sha256
 s=read(selection);producer=read(producer_path);prepared=read(T/'prepared.json');assert producer['schema']=='pinwheel-buffered-tt-buf4-pair-route-v1';assert producer['status']=='passed' and producer['exit_code']==0 and producer['inputs_unchanged'];assert producer['image_id']==IMAGE and producer['container_termination']['status']=='absent' and not producer['container_termination']['owned_container_ids']
 gates=['qualified_control_reproduction_passed','dirty_noop_pre_edit_gate_passed','noop_pre_edit_gate_passed','candidate_exact_edit_gate_passed','native_clock_route_preservation_passed','all_unrelated_route_preservation_passed','native_raw_capacity_preservation_passed','fresh_PSM_both_nets_passed']
 assert all(producer['measurement'][k] is True for k in gates)
 expected={}
 def bind(path,digest=None):
  path=Path(path).resolve();digest=digest or sha(path);assert expected.get(str(path),digest)==digest;expected[str(path)]=digest
 for k,v in producer['input_sha256'].items():bind(ROOT/k,v)
 for k,v in producer['artifact_sha256'].items():bind(producer_path.parent/k,v)
 for k,v in prepared['source_sha256'].items():bind(k,v)
 for k,v in prepared['tool_sha256'].items():bind(T/k,v)
 for k,v in s['source_bindings_sha256'].items():bind(ROOT/k,v)
 assert len(s['protected_sources_sha256'])==507
 for k,v in s['protected_sources_sha256'].items():bind(ROOT/k,v)
 bind(producer_path,a.producer_sha256);bind(selection,a.selection_sha256);bind(T/'prepared.json')
 baseline=producer_path.parent/'baseline';noop=producer_path.parent/'noop';folder=noop if a.arm=='control' else producer_path.parent/'candidate'
 assert read(baseline/'native-inventory.json')==read(noop/'native-inventory.json')==read(G/'native-inventory.json')
 assert parse_segments(baseline/'after_grt.segments')==parse_segments(noop/'after_grt.segments')==parse_segments(G/'after_grt.segments')
 for name in ['after.v','estimated.spef','native-raw-capacity.json']:assert sha(baseline/name)==sha(noop/name)==sha(G/name),(name,'Control/noop/gold mismatch')
 assert sha(baseline/'routed.odb')==sha(noop/'routed.odb')==sha(G/'routed.odb'),'Required hardbyte8c control mismatch'
 if a.arm=='candidate':
  assert a.control_report is not None;control_path=a.control_report.resolve();control=read(control_path);assert control['status']=='passed' and control['exit_code']==0 and control['inputs_unchanged'] and control['container_termination']['status']=='absent' and not control['container_termination']['owned_container_ids'];assert control['selection_sha256']==a.selection_sha256 and control['producer_report_sha256']==a.producer_sha256 and control['arm']=='control';assert set(control['measurement']['corners'])==CORNERS and all(v['prior_qualified_global_timing_reproduced'] is True for v in control['measurement']['corners'].values())
  for k,v in control['input_sha256'].items():bind(ROOT/k,v)
  for k,v in control['artifact_sha256'].items():bind(control_path.parent/k,v)
  bind(control_path)
 for k,v in expected.items():assert sha(k)==v,('Changed source',k)
 stop=datetime.datetime.fromisoformat(s['native_stop_utc'].replace('Z','+00:00')).timestamp();deadline=datetime.datetime.fromisoformat(s['deadline_utc'].replace('Z','+00:00')).timestamp();assert time.time()<stop and deadline>stop
 out=ROOT/'build/physical'/a.tag;assert not out.exists();out.mkdir()
 def copy(source,name):
  target=out/name;target.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(source,target);assert sha(source)==sha(target);bind(source);bind(target)
 for name in ['coordinator.py','timing-worker.py','segments.py']:copy(T/name,name)
 stage=a.arm
 for old,new in [('routed.odb','checkpoint.odb'),('after_grt.segments','after_grt.segments')]:copy(folder/old,stage+'/'+new)
 copy(T/'route-corner.tcl',stage+'/route-corner.tcl')
 for name in ['baseline-env.tcl','core.sdc']:copy(L/name,stage+'/'+name)
 for lib in sorted((L/'lib').glob('*.lib')):copy(lib,stage+'/lib/'+lib.name)
 assert len(list((out/stage/'lib').glob('*.lib')))==9
 old_inputs=read(L/'inputs.json');ref=read(R/'report.json');native=read(folder/'native-inventory.json');ndr=re.findall(r'(?ms)^NONDEFAULTRULES\s+\d+\s*;.*?^END NONDEFAULTRULES',(folder/'routed.def').read_text());assert len(ndr)==1 and not re.search(r'\+\s+(VIA|USEVIA|USEVIARULE)\b',ndr[0])
 refs={};norm={}
 for c in CORNERS:
  refs[c]={}
  for driver in ['fanout914','fanout913']:
   for edge in ['rise','fall']:
    for kind in ['max','min']:
     text=(L/c/('resetpair-'+driver+'-'+edge+'-'+kind+'.rpt')).read_text();rows={}
     for b in re.findall(r'(?ms)^Startpoint: .*?(?=^Startpoint:|\Z)',text):
      pins=re.findall(r'[\^v]\s+(\S+)\s+\(',b.split('data arrival time')[0]);rows[pins[-1]]=float(re.findall(r'(-?\d+\.\d+)\s+slack',b)[0])
     assert len(rows)==257;refs[c][driver+'/'+edge+'/'+kind]=rows
  norm[c]=hashlib.sha256(''.join(line for line in (L/c/'estimated.spef').read_text().splitlines(keepends=True) if not line.startswith('*DATE ')).encode()).hexdigest()
 inputs=dict(corners=old_inputs['corners'],native_script_sha256=old_inputs['native_script_sha256'],route_source_report_sha256=a.producer_sha256,routed_database_sha256=sha(folder/'routed.odb'),route_segments_sha256=sha(folder/'after_grt.segments'),netlist_sha256=sha(folder/'after.v'),post_route_ndr_map={name:n['nondefault_rule'] for name,n in native['nets'].items()},canonical_block_NDR_DEF_sha256=hashlib.sha256(ndr[0].encode()).hexdigest(),endpoints=['_30712_/D'],reproduction_required=a.arm=='control',retained_reference_corners=ref['measurement']['corners'],retained_control_normalized_spef_sha256=norm,affected_reference=refs,scope='Fresh physical exact-ODB/segments native global-route RC: no lossySPEFimport or optimization. Three declared corners,257affected endpoints×8contexts; conditionalFAST logic-40/SRAM-55.')
 write(out/stage/'inputs.json',inputs);write(out/'stage-plan.json',dict(arm=a.arm));bind(out/stage/'inputs.json');bind(out/'stage-plan.json')
 report=execute(out,list(expected),['python3','-B','/work/diagnostic/coordinator.py'],seconds=300,cpus=3,memory='3g',schema='pinwheel-buffered-tt-buf4-pair-native-timing-v1',scope=inputs['scope'],expected_hashes=expected,absolute_work_stop=stop,all_in_deadline_monotonic=started+min(420,deadline-time.time()+time.monotonic()-started),phase_started_monotonic=started,host_stage_seconds=60,extra=dict(arm=a.arm,selection_sha256=a.selection_sha256,producer_report_sha256=a.producer_sha256,prepared_sha256=sha(T/'prepared.json'),fresh_control_report_sha256=sha(a.control_report) if a.control_report else None))
 report['all_in_elapsed_seconds']=round(time.monotonic()-started,3);write(out/'report.json',report);print(out/'report.json',report['status']);return 0 if report['status']=='passed' else 1
if __name__=='__main__':raise SystemExit(main())
