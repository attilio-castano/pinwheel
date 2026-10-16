"""Fresh native three-corner P1/P2 routing-only five-net stability comparison."""
import argparse,datetime,hashlib,json,re,shutil,time
from pathlib import Path
from common import ROOT,IMAGE,read,sha,write,execute
from segments import parse_segments
T=Path(__file__).resolve().parent
REF=ROOT/'build/physical/tt-five-terminal-headroom-01'
SOURCE=ROOT/'build/physical/tt-buffered-stable-pair4-physical-route-07/candidate'
ENDPOINTS=['_30759_/D','_30606_/D','_30747_/D','_30602_/D','_34083_/D']
ALLOWED={'net8042','net8046','net9291','_00006_','_03109_'}
def main():
 p=argparse.ArgumentParser();p.add_argument('--producer-report',type=Path,required=True);p.add_argument('--producer-sha256',required=True);p.add_argument('--selection',type=Path,required=True);p.add_argument('--selection-sha256',required=True);p.add_argument('--native-stop-utc',required=True);p.add_argument('--deadline-utc',required=True);p.add_argument('--tag',default='tt-five-net-stabilization-timing-01');o=p.parse_args();started=time.monotonic()
 assert o.tag=='tt-five-net-stabilization-timing-01';producer_path=o.producer_report.resolve();selection=o.selection.resolve();assert producer_path.is_relative_to(ROOT) and selection.is_relative_to(ROOT)
 assert sha(producer_path)==o.producer_sha256 and sha(selection)==o.selection_sha256
 r=read(producer_path);sel=read(selection);prepared=read(T/'prepared.json');assert r['schema']=='pinwheel-five-net-stabilization-route-v1' and r['status']=='passed' and r['exit_code']==0 and r['inputs_unchanged'] and r['image_id']==IMAGE
 assert r['selection_sha256']==o.selection_sha256 and r['container_termination']['status']=='absent' and not r['container_termination']['owned_container_ids']
 m=r['measurement'];assert m['schema']=='pinwheel-five-net-stabilization-measurement-v1' and m['status']=='measured'
 gates=['qualified_buf4_reproduction_passed','five_old_net_P1_P2_stabilized','no_inventory_changes_after_BUF4','native_clock_route_preservation_passed','all_unrelated_route_preservation_passed','all_unrelated_native_RC_preservation_passed','native_raw_capacity_preservation_passed','fresh_PSM_both_nets_passed'];assert all(m[k] is True for k in gates)
 p1=producer_path.parent/'pass1-five';p2=producer_path.parent/'pass2-five';b=read(p1/'native-inventory.json');c=read(p2/'native-inventory.json');assert b==c==read(SOURCE/'native-inventory.json')
 assert parse_segments(p1/'after_grt.segments')==parse_segments(p2/'after_grt.segments')
 for name in ['after.v','estimated.spef','native-raw-capacity.json']:assert sha(p1/name)==sha(p2/name)
 comparisons=read(p2/'preservation-proof.json')['exact_P1_P2_comparisons'];assert comparisons and all(v is True for v in comparisons.values())
 reference=read(REF/'report.json');assert reference['status']=='passed' and reference['exit_code']==0 and reference['inputs_unchanged'] and reference['measurement']['no_edit_control_passed'];refs=reference['measurement']['corners'];prior=REF/'headroom'
 expected={}
 def bind(path,digest=None):
  path=Path(path).resolve();digest=digest or sha(path);assert expected.get(str(path),digest)==digest;expected[str(path)]=digest
 for path in [producer_path,REF/'report.json']:
  x=read(path)
  for k,v in x['input_sha256'].items():bind(ROOT/k,v)
  for k,v in x['artifact_sha256'].items():bind(path.parent/k,v)
  bind(path)
 bind(selection,o.selection_sha256)
 for k,v in prepared['source_sha256'].items():bind(k,v)
 for k,v in prepared['tool_sha256'].items():bind(T/k,v)
 bind(T/'prepared.json')
 stop=datetime.datetime.fromisoformat(o.native_stop_utc.replace('Z','+00:00')).timestamp();deadline=datetime.datetime.fromisoformat(o.deadline_utc.replace('Z','+00:00')).timestamp();assert time.time()<stop<deadline
 assert o.native_stop_utc=='2026-10-14T16:55:36Z' and o.deadline_utc=='2026-10-14T16:57:36Z'
 out=ROOT/'build/physical'/o.tag;assert not out.exists();out.mkdir()
 def copy(source,name):
  target=out/name;target.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(source,target);assert sha(source)==sha(target);bind(source);bind(target)
 for n in ['coordinator.py','timing-worker.py','segments.py']:copy(T/n,n)
 original=read(prior/'inputs.json');norm={corner:hashlib.sha256(''.join(line for line in (prior/corner/'estimated.spef').read_text().splitlines(keepends=True) if not line.startswith('*DATE ')).encode()).hexdigest() for corner in refs}
 for arm,folder in [('pass1',p1),('pass2',p2)]:
  for old,new in [('routed.odb','checkpoint.odb'),('after_grt.segments','after_grt.segments')]:copy(folder/old,arm+'/'+new)
  copy(T/'route-corner.tcl',arm+'/route-corner.tcl')
  for n in ['baseline-env.tcl','core.sdc']:copy(prior/n,arm+'/'+n)
  for lib in sorted((prior/'lib').glob('*.lib')):copy(lib,arm+'/lib/'+lib.name)
  assert len(list((out/arm/'lib').glob('*.lib')))==9
  native=read(folder/'native-inventory.json');ndr=re.findall(r'(?ms)^NONDEFAULTRULES\s+\d+\s*;.*?^END NONDEFAULTRULES',(folder/'routed.def').read_text());assert len(ndr)==1 and not re.search(r'\+\s+(VIA|USEVIA|USEVIARULE)\b',ndr[0])
  inputs=dict(corners=original['corners'],native_script_sha256=original['native_script_sha256'],route_source_report_sha256=o.producer_sha256,routed_database_sha256=sha(folder/'routed.odb'),route_segments_sha256=sha(folder/'after_grt.segments'),netlist_sha256=sha(folder/'after.v'),post_route_ndr_map={name:n['nondefault_rule'] for name,n in native['nets'].items()},canonical_block_NDR_DEF_sha256=hashlib.sha256(ndr[0].encode()).hexdigest(),endpoints=['_30712_/D'],terminal_endpoints=ENDPOINTS,reproduction_required=False,retained_reference_corners=refs,retained_control_normalized_spef_sha256=norm,affected_reference={corner:v['pair_headroom']['contexts'] for corner,v in refs.items()},scope='Fresh P1/P2 five-old-net routing-only STA: originalBUF4sourcecomparisonDIAGNOSTIC; nativeP1sourcecontrolmeasuredfirst, nativeP2mustreproducefreshP1 within1ps/global/20terminal/30712/6168 andexactnormalizedfullSPEF/electricalcounts. NoSPEFimport/optimization; FASTconditional.')
  filename='inputs.json' if arm=='pass1' else 'inputs-template.json';write(out/arm/filename,inputs);bind(out/arm/filename)
 report=execute(out,list(expected),['python3','-B','/work/diagnostic/coordinator.py'],seconds=360,cpus=3,memory='3g',schema='pinwheel-five-net-stabilization-native-timing-v1',scope=inputs['scope'],expected_hashes=expected,absolute_work_stop=stop,all_in_deadline_monotonic=started+min(420,deadline-time.time()+time.monotonic()-started),phase_started_monotonic=started,host_stage_seconds=60,extra=dict(producer_report_sha256=o.producer_sha256,selection_sha256=o.selection_sha256,prepared_sha256=sha(T/'prepared.json'),reference_report_sha256=sha(REF/'report.json'),prior_source_reference_diagnostic_only=True,native_process_count_expected=6,native_stop_utc=o.native_stop_utc,deadline_utc=o.deadline_utc))
 report['all_in_elapsed_seconds']=round(time.monotonic()-started,3);write(out/'report.json',report);print(out/'report.json',report['status']);return 0 if report['status']=='passed' else 1
if __name__=='__main__':raise SystemExit(main())
