import argparse,datetime,json,shutil,time
from pathlib import Path
from common import ROOT,execute,sha,read,write
H=Path(__file__).resolve().parent
STOP=datetime.datetime.fromisoformat('2026-10-14T00:52:32+00:00').timestamp();DEADLINE=datetime.datetime.fromisoformat('2026-10-14T00:53:12+00:00').timestamp()
def verify(items):
 for n,h in items.items():
  p=Path(n) if Path(n).is_absolute() else ROOT/n;assert p.is_file() and sha(p)==h,n
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--selection',type=Path,required=True);ap.add_argument('--tag',default='tt-buffered-stable-pair4-physical-route-01');a=ap.parse_args();started=time.monotonic();assert a.tag=='tt-buffered-stable-pair4-physical-route-01'
 S=read(a.selection);P=read(H/'prepared.json');policy=read(H/'stabilization-policy.json')
 assert S['schema']=='pinwheel-buffered-tt-stable-pair4-physical-selection-v1' and S['routing_iterations']==10 and S['one_candidate_only']
 assert S['prepared_sha256']==sha(H/'prepared.json') and S['pair_policy_sha256']==sha(H/'pair-policy.json')
 assert S['source_database_sha256']==P['comparison_database_sha256']
 assert S['route_native_stop_utc']=='2026-10-14T00:52:32Z' and S['route_phase_deadline_utc']=='2026-10-14T00:53:12Z'
 assert set(S['allowed_dirty_signal_nets'])==set(policy['dirty_signal_nets']) and S['allowed_master_substitutions']=={'fanout914':['sg13cmos5l_buf_1','sg13cmos5l_buf_4'],'fanout913':['sg13cmos5l_buf_1','sg13cmos5l_buf_4']}
 verify(P['source_sha256']);verify(P['tool_sha256']);assert STOP-time.time()>90 and time.time()+30<DEADLINE
 O=ROOT/'build/physical'/a.tag;assert not O.exists();O.mkdir()
 for f in H.iterdir():
  if f.is_file():shutil.copyfile(f,O/f.name)
  elif f.name in ['identity','lib']:shutil.copytree(f,O/f.name)
 recipe=ROOT/'build/physical/tt-buffered-timing-eco-control-route-01';shutil.copyfile(ROOT/P['source_database'],O/'postcts.odb');shutil.copyfile(recipe/'before.v',O/'reference.v')
 for n in ['baseline-env.tcl','corner-env.tcl','core.sdc']:shutil.copyfile(recipe/n,O/n)
 for f in (recipe/'lib').glob('*.lib'):shutil.copyfile(f,O/'lib'/f.name)
 shutil.copyfile(a.selection,O/'selection.json')
 for n,folder in [('qualified-control-source.json','qualified-control'),('qualified-pair-source.json','qualified-pair'),('qualified-stable-source.json','qualified-stable')]:
  Q=O/folder;Q.mkdir()
  for name,d in read(H/n)['artifacts_sha256'].items():
   f=Path(name) if Path(name).is_absolute() else ROOT/name;assert sha(f)==d
   if f.name!='report.json':shutil.copyfile(f,Q/f.name)
 write(O/'phase-inputs.json',{str(Path('/work/diagnostic')/f.relative_to(O)):sha(f) for f in O.rglob('*') if f.is_file()})
 paths=[a.selection.resolve(),H/'prepared.json',*[Path(n) if Path(n).is_absolute() else ROOT/n for n in P['source_sha256']],*[Path(n) if Path(n).is_absolute() else ROOT/n for n in P['tool_sha256']],*[f for f in O.rglob('*') if f.is_file()]]
 r=execute(O,paths,['python3','-B','/work/diagnostic/coordinator.py'],seconds=540,cpus=4,memory='5g',schema='pinwheel-buffered-tt-stable-pair4-physical-route-v1',scope='Warm originalR0/8c replay and two passes reproduce stabilized P2; matched three-net noedit control then only fanout913/914 BUF4 master/footprint changes; CLOCK/unrelated/PG/capacities fixed.',extra={'network':'none','selection_sha256':sha(a.selection),'prepared_sha256':sha(H/'prepared.json'),'source_database_sha256':P['comparison_database_sha256'],'original_R0_database_sha256':P['source_database_sha256'],'pair_policy_sha256':P['pair_policy_sha256'],'source_database':P['comparison_database'], 'source_segments_sha256':P['source_segments_sha256']},expected_hashes={O/'postcts.odb':P['source_database_sha256']},absolute_work_stop=STOP,all_in_deadline_monotonic=min(started+600,time.monotonic()+DEADLINE-time.time()))
 r['all_in_elapsed_seconds']=round(time.monotonic()-started,3)
 if r['all_in_elapsed_seconds']>600 or time.time()>DEADLINE:r['status']='bound_exceeded'
 verify(P['source_sha256']);verify(P['tool_sha256']);write(O/'report.json',r);print(O/'report.json',r['status']);return 0 if r['status']=='passed' else 1
if __name__=='__main__':raise SystemExit(main())
