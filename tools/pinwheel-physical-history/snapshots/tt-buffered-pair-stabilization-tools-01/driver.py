import argparse,datetime,json,shutil,time
from pathlib import Path
from common import ROOT,execute,sha,read,write
H=Path(__file__).resolve().parent
STOP=datetime.datetime.fromisoformat('2026-10-13T23:59:11+00:00').timestamp();DEADLINE=datetime.datetime.fromisoformat('2026-10-14T00:03:11+00:00').timestamp()
def verify(items):
 for n,h in items.items():
  p=Path(n) if Path(n).is_absolute() else ROOT/n;assert p.is_file() and sha(p)==h,n
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--selection',type=Path,required=True);ap.add_argument('--tag',default='tt-buffered-pair-stabilization-route-01');a=ap.parse_args();started=time.monotonic();assert a.tag=='tt-buffered-pair-stabilization-route-01'
 S=read(a.selection);P=read(H/'prepared.json');policy=read(H/'stabilization-policy.json')
 assert S['schema']=='pinwheel-buffered-tt-pair-stabilization-selection-v1' and S['routing_iterations']==10 and S['one_candidate_only']
 assert S['prepared_sha256']==sha(H/'prepared.json') and S['stabilization_policy_sha256']==sha(H/'stabilization-policy.json')
 assert S['base_database_sha256']==P['comparison_database_sha256'] and S['source_database_sha256']==P['source_database_sha256']
 assert S['native_stop_utc']=='2026-10-13T23:59:11Z' and S['deadline_utc']=='2026-10-14T00:03:11Z'
 assert set(S['allowed_signal_route_nets'])==set(policy['dirty_signal_nets']) and S['passes']==2 and S['no_sizing'] is True
 verify(P['source_sha256']);verify(P['tool_sha256']);assert STOP-time.time()>420 and time.time()+480<=DEADLINE
 O=ROOT/'build/physical'/a.tag;assert not O.exists();O.mkdir()
 for f in H.iterdir():
  if f.is_file():shutil.copyfile(f,O/f.name)
  elif f.name in ['identity','lib']:shutil.copytree(f,O/f.name)
 recipe=ROOT/'build/physical/tt-buffered-timing-eco-control-route-01';shutil.copyfile(ROOT/P['source_database'],O/'postcts.odb');shutil.copyfile(recipe/'before.v',O/'reference.v')
 for n in ['baseline-env.tcl','corner-env.tcl','core.sdc']:shutil.copyfile(recipe/n,O/n)
 for f in (recipe/'lib').glob('*.lib'):shutil.copyfile(f,O/'lib'/f.name)
 shutil.copyfile(a.selection,O/'selection.json')
 for n,folder in [('qualified-control-source.json','qualified-control'),('qualified-pair-source.json','qualified-pair')]:
  Q=O/folder;Q.mkdir()
  for name,d in read(H/n)['artifacts_sha256'].items():
   f=Path(name) if Path(name).is_absolute() else ROOT/name;assert sha(f)==d
   if f.name!='report.json':shutil.copyfile(f,Q/f.name)
 write(O/'phase-inputs.json',{str(Path('/work/diagnostic')/f.relative_to(O)):sha(f) for f in O.rglob('*') if f.is_file()})
 paths=[a.selection.resolve(),H/'prepared.json',*[Path(n) if Path(n).is_absolute() else ROOT/n for n in P['source_sha256']],*[Path(n) if Path(n).is_absolute() else ROOT/n for n in P['tool_sha256']],*[f for f in O.rglob('*') if f.is_file()]]
 r=execute(O,paths,['python3','-B','/work/diagnostic/coordinator.py'],seconds=420,cpus=4,memory='3g',schema='pinwheel-buffered-tt-pair-stabilization-route-v1',scope='Warmrebuildtoexactqualified8c then exactlytwo3net dirty passes; no sizing/cell edits; clock/unrelatedroutes/power/capacities frozen.',extra={'network':'none','selection_sha256':sha(a.selection),'prepared_sha256':sha(H/'prepared.json'),'source_database_sha256':P['comparison_database_sha256'],'original_R0_database_sha256':P['source_database_sha256'],'stabilization_policy_sha256':P['stabilization_policy_sha256']},expected_hashes={O/'postcts.odb':P['source_database_sha256']},absolute_work_stop=STOP,all_in_deadline_monotonic=started+480)
 r['all_in_elapsed_seconds']=round(time.monotonic()-started,3)
 if r['all_in_elapsed_seconds']>480 or time.time()>DEADLINE:r['status']='bound_exceeded'
 verify(P['source_sha256']);verify(P['tool_sha256']);write(O/'report.json',r);print(O/'report.json',r['status']);return 0 if r['status']=='passed' else 1
if __name__=='__main__':raise SystemExit(main())
