"""One bounded six-native-process physical route-RC timing measurement."""
import argparse,datetime,hashlib,json,re,shutil,time
from pathlib import Path
from common import ROOT,IMAGE,read,sha,write,execute
from segments import parse_segments
T=Path(__file__).resolve().parent
G=ROOT/'build/physical/tt-buffered-pair-stabilization-route-01/pass2'
R=ROOT/'build/physical/tt-buffered-pair-stabilization-headroom-01'
L=R/'stable'
CORNERS={'nom_typ_1p20V_25C','nom_slow_1p08V_125C','nom_fast_1p32V_m40C'}
def main():
 p=argparse.ArgumentParser();p.add_argument('--producer-report',type=Path,required=True);p.add_argument('--producer-sha256',required=True);p.add_argument('--selection',type=Path,required=True);p.add_argument('--selection-sha256',required=True);p.add_argument('--tag',required=True);opts=p.parse_args();started=time.monotonic()
 assert re.fullmatch(r'tt-buffered-stable-pair4-physical-timing-[0-9]+',opts.tag)
 selection=opts.selection.resolve();producer_path=opts.producer_report.resolve();assert selection.is_relative_to(ROOT) and producer_path.is_relative_to(ROOT);assert sha(selection)==opts.selection_sha256 and sha(producer_path)==opts.producer_sha256
 selected=read(selection);producer=read(producer_path);prepared=read(T/'prepared.json')
 assert producer['schema']=='pinwheel-buffered-tt-stable-pair4-physical-route-v1' and producer['status']=='passed' and producer['exit_code']==0 and producer['inputs_unchanged']
 assert producer['image_id']==IMAGE and producer['container_termination']['status']=='absent' and not producer['container_termination']['owned_container_ids']
 assert producer['selection_sha256']==opts.selection_sha256 and producer['source_database_sha256']==sha(G/'routed.odb')
 gates=['qualified_stable_P2_reproduction_passed','matched_noedit_control_passed','candidate_exact_two_resizes_passed','native_clock_route_preservation_passed','all_unrelated_route_preservation_passed','native_raw_capacity_preservation_passed','fresh_PSM_both_nets_passed']
 assert producer['measurement']['status']=='measured' and all(producer['measurement'][k] is True for k in gates)
 expected={}
 def bind(path,digest=None):
  path=Path(path).resolve();digest=digest or sha(path);assert expected.get(str(path),digest)==digest;expected[str(path)]=digest
 for k,v in producer['input_sha256'].items():bind(ROOT/k,v)
 for k,v in producer['artifact_sha256'].items():bind(producer_path.parent/k,v)
 for k,v in prepared['source_sha256'].items():bind(k,v)
 for k,v in prepared['tool_sha256'].items():bind(T/k,v)
 for k,v in selected['source_bindings_sha256'].items():bind(ROOT/k,v)
 assert len(selected['protected_sources_sha256'])==507
 for k,v in selected['protected_sources_sha256'].items():bind(ROOT/k,v)
 bind(producer_path,opts.producer_sha256);bind(selection,opts.selection_sha256);bind(T/'prepared.json')
 reference=read(R/'report.json');assert reference['status']=='passed' and reference['exit_code']==0 and reference['inputs_unchanged'] and reference['stable_database_sha256']==sha(G/'routed.odb')
 for k,v in reference['input_sha256'].items():bind(ROOT/k,v)
 for k,v in reference['artifact_sha256'].items():bind(R/k,v)
 bind(R/'report.json')
 control=producer_path.parent/'control';candidate=producer_path.parent/'candidate'
 assert read(control/'native-inventory.json')==read(G/'native-inventory.json')
 assert parse_segments(control/'after_grt.segments')==parse_segments(G/'after_grt.segments')
 for name in ['after.v','estimated.spef','native-raw-capacity.json']:assert sha(control/name)==sha(G/name),(name,'Noedit stablecontrol mismatch')
 gc=read(control/'geometry.json');gg=read(G/'geometry.json');gc.pop('database_sha256',None);gg.pop('database_sha256',None);assert gc==gg
 for k,v in expected.items():assert sha(k)==v,('Changed source',k)
 stop=datetime.datetime.fromisoformat(selected['native_stop_utc'].replace('Z','+00:00')).timestamp();deadline=datetime.datetime.fromisoformat(selected['deadline_utc'].replace('Z','+00:00')).timestamp();assert time.time()<stop and deadline>stop
 out=ROOT/'build/physical'/opts.tag;assert not out.exists();out.mkdir()
 def copy(source,name):
  target=out/name;target.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(source,target);assert sha(source)==sha(target);bind(source);bind(target)
 for name in ['coordinator.py','timing-worker.py','segments.py']:copy(T/name,name)
 original_inputs=read(L/'inputs.json');refs={};norm={}
 for corner in CORNERS:
  refs[corner]={}
  for driver in ['fanout914','fanout913']:
   for edge in ['rise','fall']:
    for kind in ['max','min']:
     text=(L/corner/('resetpair-'+driver+'-'+edge+'-'+kind+'.rpt')).read_text();rows={}
     for body in re.findall(r'(?ms)^Startpoint: .*?(?=^Startpoint:|\Z)',text):
      pins=re.findall(r'[\^v]\s+(\S+)\s+\(',body.split('data arrival time')[0]);assert pins[-1] not in rows;rows[pins[-1]]=float(re.findall(r'(-?\d+\.\d+)\s+slack',body)[0])
     assert len(rows)==257;refs[corner][driver+'/'+edge+'/'+kind]=rows
  norm[corner]=hashlib.sha256(''.join(line for line in (L/corner/'estimated.spef').read_text().splitlines(keepends=True) if not line.startswith('*DATE ')).encode()).hexdigest()
 for arm,folder in [('control',control),('candidate',candidate)]:
  for old,new in [('routed.odb','checkpoint.odb'),('after_grt.segments','after_grt.segments')]:copy(folder/old,arm+'/'+new)
  copy(T/'route-corner.tcl',arm+'/route-corner.tcl')
  for name in ['baseline-env.tcl','core.sdc']:copy(L/name,arm+'/'+name)
  for lib in sorted((L/'lib').glob('*.lib')):copy(lib,arm+'/lib/'+lib.name)
  assert len(list((out/arm/'lib').glob('*.lib')))==9
  native=read(folder/'native-inventory.json');ndr=re.findall(r'(?ms)^NONDEFAULTRULES\s+\d+\s*;.*?^END NONDEFAULTRULES',(folder/'routed.def').read_text());assert len(ndr)==1 and not re.search(r'\+\s+(VIA|USEVIA|USEVIARULE)\b',ndr[0])
  inputs=dict(corners=original_inputs['corners'],native_script_sha256=original_inputs['native_script_sha256'],route_source_report_sha256=opts.producer_sha256,routed_database_sha256=sha(folder/'routed.odb'),route_segments_sha256=sha(folder/'after_grt.segments'),netlist_sha256=sha(folder/'after.v'),post_route_ndr_map={name:n['nondefault_rule'] for name,n in native['nets'].items()},canonical_block_NDR_DEF_sha256=hashlib.sha256(ndr[0].encode()).hexdigest(),endpoints=['_30712_/D'],reproduction_required=arm=='control',retained_reference_corners=reference['measurement']['corners'],retained_control_normalized_spef_sha256=norm,affected_reference=refs,scope='ActualphysicalBUF4pair native exactODB/segments globalrouteRC; fresh stablecontrol3corners<=1ps thenphysicalcandidate3corners/6168affectedcontexts; no lossySPEF import/optimization; FASTlogic-40/SRAM-55 conditional.')
  write(out/arm/'inputs.json',inputs);bind(out/arm/'inputs.json')
 write(out/'stage-plan.json',dict(arms=['control','candidate']));bind(out/'stage-plan.json')
 report=execute(out,list(expected),['python3','-B','/work/diagnostic/coordinator.py'],seconds=600,cpus=3,memory='3g',schema='pinwheel-buffered-tt-stable-pair4-physical-timing-v1',scope=inputs['scope'],expected_hashes=expected,absolute_work_stop=stop,all_in_deadline_monotonic=started+min(720,deadline-time.time()+time.monotonic()-started),phase_started_monotonic=started,host_stage_seconds=60,extra=dict(selection_sha256=opts.selection_sha256,producer_report_sha256=opts.producer_sha256,prepared_sha256=sha(T/'prepared.json'),reference_report_sha256=sha(R/'report.json'),actual_physical_candidate=True,source_physical_producer_status='passed',native_stage_order=['control','candidate']))
 report['all_in_elapsed_seconds']=round(time.monotonic()-started,3);write(out/'report.json',report);print(out/'report.json',report['status']);return 0 if report['status']=='passed' else 1
if __name__=='__main__':raise SystemExit(main())
