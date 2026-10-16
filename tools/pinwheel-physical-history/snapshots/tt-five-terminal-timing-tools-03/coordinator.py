import json,os,subprocess,importlib.util
from pathlib import Path
r=Path('/work/diagnostic');control=json.loads((r/'retained-control.json').read_text());assert len(control)==3 and all(v['prior_qualified_global_timing_reproduced'] is True for v in control.values());results={'control':control}
env=dict(os.environ,PINWHEEL_TIMING_ROOT=str(r/'candidate'));subprocess.run(['python3','-B',str(r/'timing-worker.py')],env=env,cwd=r,check=True)
m=json.loads((r/'candidate'/'measurement.json').read_text());assert len(m['corners'])==3;results['candidate']=m['corners']
spec=importlib.util.spec_from_file_location('branchgates',r/'branch-gates.py');g=importlib.util.module_from_spec(spec);spec.loader.exec_module(g);gates=g.assess(r,results)
(r/'branch-RC-domain-gates.json').write_text(json.dumps(gates,indent=2)+'\n')
out=dict(status='measured',results=results,native_process_count=3,prior_fresh_control_native_process_count=3,controls_renewed_in_current_container=False,control_mode='Todayfreshheadroom3corners transferredbycurrentexactfive-netdirtycontrolsourceinventory/routes/NL/NDR/fullnominalSPEF identity',branch_RC_and_domain_gates=gates,all_candidate_global_setup_hold_met=all(v['setup_met'] and v['hold_met'] for v in results['candidate'].values()),minimum_candidate_global_hold_after1ps_ns=min(v['hold_worst_slack_ns'] for v in results['candidate'].values())-.001,scope='Actualfive-terminalphysicalcandidate3NEWnativeSTAprocesses; todayspriorfreshthreecornerheadroomcontrols remain provenance-bound; unconditionaltimingwithmodelqualificationseparate.')
(r/'measurement.json').write_text(json.dumps(out,indent=2)+'\n')
