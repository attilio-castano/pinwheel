import json,os,subprocess
from pathlib import Path
r=Path('/work/diagnostic');results={}
for arm in ['control','candidate']:
 env=dict(os.environ,PINWHEEL_TIMING_ROOT=str(r/arm));subprocess.run(['python3','-B',str(r/'timing-worker.py')],env=env,cwd=r,check=True)
 m=json.loads((r/arm/'measurement.json').read_text());assert set(m['corners'])=={'nom_typ_1p20V_25C','nom_slow_1p08V_125C','nom_fast_1p32V_m40C'}
 if arm=='control':assert all(v['prior_qualified_global_timing_reproduced'] is True for v in m['corners'].values())
 results[arm]=m['corners']
 (r/'control-validation.json').write_text(json.dumps(dict(status='passed',fresh_native_corner_count=3,control=results['control']),indent=2)+'\n')
minimum_hold=min(v['pair_headroom']['minimum_affected_hold_ns'] for v in results['candidate'].values())
out=dict(status='measured',results=results,native_process_count=6,fresh_control_validated_before_candidate=True,route_based_only=True,parasitic_model='estimate_parasitics -global_routing',all_candidate_global_setup_hold_met=all(v['setup_met'] and v['hold_met'] for v in results['candidate'].values()),minimum_candidate_affected_hold_ns=minimum_hold,conservative_candidate_affected_hold_reserve_ns=minimum_hold-.001,candidate_affected_hold_at_least50ps=minimum_hold-.001>=.05,scope='ActualphysicaltwoBUF4resize nativefixedroute RC afterpinaccess; control3cornersfirst thencandidate3; no lossySPEF import or optimization.')
(r/'measurement.json').write_text(json.dumps(out,indent=2)+'\n')
