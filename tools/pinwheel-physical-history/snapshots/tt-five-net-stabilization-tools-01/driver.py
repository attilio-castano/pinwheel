import argparse,datetime,json,shutil,time
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
