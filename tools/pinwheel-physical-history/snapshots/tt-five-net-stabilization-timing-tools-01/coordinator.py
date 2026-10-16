import hashlib,json,os,subprocess
from pathlib import Path
r=Path('/work/diagnostic');results={}
for arm in ['pass1','pass2']:
 if arm=='pass2':
  p=r/'pass2'/'inputs.json';inputs=json.loads((r/'pass2'/'inputs-template.json').read_text());assert not p.exists();inputs['retained_reference_corners']=results['pass1'];inputs['affected_reference']={corner:v['pair_headroom']['contexts'] for corner,v in results['pass1'].items()};inputs['reproduction_required']=True
  inputs['retained_control_normalized_spef_sha256']={corner:hashlib.sha256(''.join(line for line in (r/'pass1'/corner/'estimated.spef').read_text().splitlines(keepends=True) if not line.startswith('*DATE ')).encode()).hexdigest() for corner in results['pass1']}
  p.write_text(json.dumps(inputs,indent=2)+'\n')
 env=dict(os.environ,PINWHEEL_TIMING_ROOT=str(r/arm));subprocess.run(['python3','-B',str(r/'timing-worker.py')],env=env,cwd=r,check=True)
 m=json.loads((r/arm/'measurement.json').read_text());assert len(m['corners'])==3
 if arm=='pass2':assert all(v['prior_qualified_global_timing_reproduced'] is True for v in m['corners'].values())
 results[arm]=m['corners']
comparisons={}
for corner,p1 in results['pass1'].items():
 p2=results['pass2'][corner];rows={}
 for key in ['setup_worst_slack_ns','hold_worst_slack_ns']:
  rows[key]=dict(pass1=p1[key],pass2=p2[key],delta_ns=p2[key]-p1[key]);assert abs(rows[key]['delta_ns'])<=.001
 for ep,row in p1['terminal_headroom'].items():
  for ctx,c in row['contexts'].items():assert abs(c['slack_ns']-p2['terminal_headroom'][ep]['contexts'][ctx]['slack_ns'])<=.001
 assert all(v==p2['fresh_metrics'][key] for key,v in p1['fresh_metrics'].items() if 'violation__count__corner:' in key or 'vio__count__corner:' in key)
 comparisons[corner]=rows
out=dict(status='measured',results=results,native_process_count=6,fresh_P1_three_corners_before_P2=True,P2_three_corner_agreement_within1ps=True,all_candidate_global_setup_hold_met=all(v['setup_met'] and v['hold_met'] for v in results['pass2'].values()),global_comparisons=comparisons,source_BUF4_comparison_diagnostic_only=True,scope='Routing-only five-old-net warmP1/P2 stability;3freshP1then3freshP2 nativeODB/globalrouteRC; fullSPEF/counts/global/30712/20terminal/6168contextreproduction. OriginalBUF4referencecomparisondiagnostic, notfixed1psrequirement; noplacement/cell/signal/clockchanges.')
(r/'measurement.json').write_text(json.dumps(out,indent=2)+'\n')
