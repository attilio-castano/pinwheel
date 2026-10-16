import json,os,subprocess
from pathlib import Path
r=Path('/work/diagnostic');results={}
for arm in ['control','candidate']:
 env=dict(os.environ,PINWHEEL_TIMING_ROOT=str(r/arm));subprocess.run(['python3','-B',str(r/'timing-worker.py')],env=env,cwd=r,check=True)
 m=json.loads((r/arm/'measurement.json').read_text());assert len(m['corners'])==3
 if arm=='control':assert all(v['prior_qualified_global_timing_reproduced'] is True for v in m['corners'].values())
 results[arm]=m['corners']
import importlib.util
spec=importlib.util.spec_from_file_location('branchgates',r/'branch-gates.py');g=importlib.util.module_from_spec(spec);spec.loader.exec_module(g);gates=g.assess(r,results)
(r/'branch-RC-domain-gates.json').write_text(json.dumps(gates,indent=2)+'\n')
out=dict(branch_RC_and_domain_gates=gates,status='measured',results=results,native_process_count=6,fresh_control_validated_before_candidate=True,all_candidate_global_setup_hold_met=all(v['setup_met'] and v['hold_met'] for v in results['candidate'].values()),minimum_candidate_global_hold_after1ps_ns=min(v['hold_worst_slack_ns'] for v in results['candidate'].values())-.001,scope='Actualfive-terminalphysicalcandidate nativefixedglobalrouteRC; fresh3cornercontrol first, fresh3cornercandidate next; numericperformanceanddomain/RCgates separate.')
(r/'measurement.json').write_text(json.dumps(out,indent=2)+'\n')
