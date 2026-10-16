"""Bounded no-edit three-corner native BUF4 candidate terminal headroom."""
import argparse,datetime,hashlib,json,re,shutil,time
from pathlib import Path
from common import ROOT,IMAGE,read,sha,write,execute
from segments import parse_segments
T=Path(__file__).resolve().parent
ENDPOINTS=['_30759_/D','_30606_/D','_30747_/D','_30602_/D','_34083_/D']
def main():
 p=argparse.ArgumentParser();p.add_argument('--producer-report',type=Path,required=True);p.add_argument('--producer-sha256',required=True);p.add_argument('--reference-report',type=Path,required=True);p.add_argument('--reference-sha256',required=True);p.add_argument('--native-stop-utc',required=True);p.add_argument('--deadline-utc',required=True);p.add_argument('--tag',default='tt-five-terminal-headroom-01');opts=p.parse_args();started=time.monotonic()
 assert opts.tag=='tt-five-terminal-headroom-01'
 producer_path=opts.producer_report.resolve();reference_path=opts.reference_report.resolve();assert producer_path.is_relative_to(ROOT) and reference_path.is_relative_to(ROOT)
 assert sha(producer_path)==opts.producer_sha256 and sha(reference_path)==opts.reference_sha256
 producer=read(producer_path);reference=read(reference_path);prepared=read(T/'prepared.json')
 assert producer['status']==reference['status']=='passed' and producer['exit_code']==reference['exit_code']==0 and producer['inputs_unchanged'] and reference['inputs_unchanged']
 assert producer['image_id']==reference['image_id']==IMAGE
 assert all(r['container_termination']['status']=='absent' and not r['container_termination']['owned_container_ids'] for r in [producer,reference])
 assert reference['producer_report_sha256']==opts.producer_sha256 and reference['actual_physical_candidate'] is True
 gates=['qualified_stable_P2_reproduction_passed','matched_noedit_control_passed','candidate_exact_two_resizes_passed','native_clock_route_preservation_passed','all_unrelated_route_preservation_passed','native_raw_capacity_preservation_passed','fresh_PSM_both_nets_passed']
 assert producer['measurement']['status']=='measured' and all(producer['measurement'][k] is True for k in gates)
 expected={}
 def bind(path,digest=None):
  path=Path(path).resolve();digest=digest or sha(path);assert expected.get(str(path),digest)==digest;expected[str(path)]=digest
 for source in [producer_path,reference_path]:
  r=read(source)
  for k,v in r['input_sha256'].items():bind(ROOT/k,v)
  for k,v in r['artifact_sha256'].items():bind(source.parent/k,v)
  bind(source)
 for k,v in prepared['source_sha256'].items():bind(k,v)
 for k,v in prepared['tool_sha256'].items():bind(T/k,v)
 bind(T/'prepared.json')
 folder=producer_path.parent/'candidate';prior=reference_path.parent/'candidate';refs=reference['measurement']['results']['candidate']
 assert set(refs)=={'nom_typ_1p20V_25C','nom_slow_1p08V_125C','nom_fast_1p32V_m40C'}
 assert sha(folder/'routed.odb')==sha(prior/'checkpoint.odb') and parse_segments(folder/'after_grt.segments')==parse_segments(prior/'after_grt.segments')
 assert all(v['global_failure_counts']=={'max':0,'min':0} for v in refs.values())
 for k,v in expected.items():assert sha(k)==v,('Changed source',k)
 stop=datetime.datetime.fromisoformat(opts.native_stop_utc.replace('Z','+00:00')).timestamp();deadline=datetime.datetime.fromisoformat(opts.deadline_utc.replace('Z','+00:00')).timestamp();assert time.time()<stop<deadline
 out=ROOT/'build/physical'/opts.tag;assert not out.exists();out.mkdir()
 def copy(source,name):
  target=out/name;target.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(source,target);assert sha(source)==sha(target);bind(source);bind(target)
 for name in ['coordinator.py','timing-worker.py','segments.py']:copy(T/name,name)
 for old,new in [('routed.odb','checkpoint.odb'),('after_grt.segments','after_grt.segments')]:copy(folder/old,'headroom/'+new)
 copy(T/'route-corner.tcl','headroom/route-corner.tcl')
 for name in ['baseline-env.tcl','core.sdc']:copy(prior/name,'headroom/'+name)
 for lib in sorted((prior/'lib').glob('*.lib')):copy(lib,'headroom/lib/'+lib.name)
 assert len(list((out/'headroom/lib').glob('*.lib')))==9
 original=read(prior/'inputs.json');norm={}
 for corner in refs:
  norm[corner]=hashlib.sha256(''.join(line for line in (prior/corner/'estimated.spef').read_text().splitlines(keepends=True) if not line.startswith('*DATE ')).encode()).hexdigest()
 native=read(folder/'native-inventory.json');ndr=re.findall(r'(?ms)^NONDEFAULTRULES\s+\d+\s*;.*?^END NONDEFAULTRULES',(folder/'routed.def').read_text());assert len(ndr)==1 and not re.search(r'\+\s+(VIA|USEVIA|USEVIARULE)\b',ndr[0])
 inputs=dict(corners=original['corners'],native_script_sha256=original['native_script_sha256'],route_source_report_sha256=opts.producer_sha256,routed_database_sha256=sha(folder/'routed.odb'),route_segments_sha256=sha(folder/'after_grt.segments'),netlist_sha256=sha(folder/'after.v'),post_route_ndr_map={name:n['nondefault_rule'] for name,n in native['nets'].items()},canonical_block_NDR_DEF_sha256=hashlib.sha256(ndr[0].encode()).hexdigest(),endpoints=['_30712_/D'],terminal_endpoints=ENDPOINTS,reproduction_required=True,retained_reference_corners=refs,retained_control_normalized_spef_sha256=norm,affected_reference={corner:r['pair_headroom']['contexts'] for corner,r in refs.items()},scope='ActualphysicalBUF4 candidate07 native exactODB/segments three-corner no-edit <=1ps/global/fullSPEF/electrical/6168affectedcontext reproduction plus5terminalD rise/fallmax/min; nooptimization, noSPEFimport; FASTlogic-40/SRAM-55conditional.')
 write(out/'headroom/inputs.json',inputs);bind(out/'headroom/inputs.json')
 report=execute(out,list(expected),['python3','-B','/work/diagnostic/coordinator.py'],seconds=240,cpus=3,memory='3g',schema='pinwheel-five-terminal-buf4-headroom-v1',scope=inputs['scope'],expected_hashes=expected,absolute_work_stop=stop,all_in_deadline_monotonic=started+min(300,deadline-time.time()+time.monotonic()-started),phase_started_monotonic=started,host_stage_seconds=60,extra=dict(producer_report_sha256=opts.producer_sha256,reference_report_sha256=opts.reference_sha256,prepared_sha256=sha(T/'prepared.json'),terminal_endpoints=ENDPOINTS,read_only_design_analysis=True,native_stop_utc=opts.native_stop_utc,deadline_utc=opts.deadline_utc))
 report['all_in_elapsed_seconds']=round(time.monotonic()-started,3);write(out/'report.json',report);print(out/'report.json',report['status']);return 0 if report['status']=='passed' else 1
if __name__=='__main__':raise SystemExit(main())
