"""Fresh numeric baseline/noop (six processes) or candidate (three), no routing."""
import os,sys,subprocess,json,hashlib
from pathlib import Path
ROOT=Path('/work/diagnostic')
read=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
plan=read(ROOT/'stage-plan.json');stages=plan['stages'];assert stages in (['baseline','noop'],['candidate'],['preflight'])
measurements={}
for stage in stages:
 env=dict(os.environ,PINWHEEL_TIMING_ROOT=str(ROOT/stage))
 subprocess.run(['python3','-B',str(ROOT/'timing-worker.py')],env=env,cwd=ROOT,check=True)
 measurements[stage]=read(ROOT/stage/'measurement.json')
proof={}
def spef_without_date(path):
 text=path.read_text();lines=text.splitlines(keepends=True);dates=[line for line in lines if line.startswith('*DATE ')]
 assert len(dates)==1,('Missing/ambiguous SPEF date header',str(path))
 remaining=''.join(line for line in lines if not line.startswith('*DATE '))
 assert remaining.startswith('*SPEF '),('Malformed SPEF header',str(path))
 return hashlib.sha256(remaining.encode()).hexdigest(),dates[0].rstrip('\n')
if stages==['baseline','noop']:
 baseline,noop=measurements['baseline'],measurements['noop'];assert set(baseline['corners'])==set(noop['corners'])
 for corner in baseline['corners']:
  a,b=baseline['corners'][corner],noop['corners'][corner]
  assert a['fresh_metrics']==b['fresh_metrics'],('No-op changed fresh numeric electrical metrics',corner)
  assert a['route_import']['segment_roundtrip']==b['route_import']['segment_roundtrip']
  spef_a,spef_b=ROOT/'baseline'/corner/'estimated.spef',ROOT/'noop'/corner/'estimated.spef'
  normalized_a,date_a=spef_without_date(spef_a);normalized_b,date_b=spef_without_date(spef_b)
  assert normalized_a==normalized_b,('No-op changed full SPEF except DATE',corner)
  assert a['route_import']['annotation']==b['route_import']['annotation']
  for n in ['ndr-before-import.txt','ndr-after-import.txt','ndr-after-timing.txt']:
   assert sha(ROOT/'baseline'/corner/n)==sha(ROOT/'noop'/corner/n),('No-op changed DBNDR map',corner)
  proof[corner]={'fresh_metric_equality':True,'estimated_SPEF_equal_except_DATE':True,'normalized_SPEF_sha256':normalized_a,'baseline_actual_SPEF_sha256':sha(spef_a),'noop_actual_SPEF_sha256':sha(spef_b),'baseline_DATE_header':date_a,'noop_DATE_header':date_b,'SPEF_normalization_only_DATE':True,'DBNDR_map_equality':True,'exact_segment_roundtrip_equality':True,'annotation_equality':True,'baseline_setup_ns':a['setup_worst_slack_ns'],'noop_setup_ns':b['setup_worst_slack_ns'],'baseline_hold_ns':a['hold_worst_slack_ns'],'noop_hold_ns':b['hold_worst_slack_ns']}
 selected=json.loads(json.dumps(noop))
else:selected=json.loads(json.dumps(measurements[stages[0]]))
selected.update(operation='Freshhold30712 fullglobalandtargetedrouteRC; sixbaseline/noop processes or3candidate/preflight; no optimizer/reroute',producer_report_sha256=plan['producer_report_sha256'],baseline_noop_native_input_identity=plan['baseline_noop_native_input_identity'],all_corner_noop_numeric_equality_proof=proof,stage_measurements=measurements,arm=plan['arm'])
(ROOT/'measurement.json').write_text(json.dumps(selected,indent=2)+'\n')
