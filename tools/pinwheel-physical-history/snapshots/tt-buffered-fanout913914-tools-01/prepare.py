"""Freeze one conditional pair-resize producer. Host-only; no CAD."""
import argparse, ast, json
from pathlib import Path
from common import ROOT,sha,read,write
H=Path(__file__).resolve().parent
def main():
    parser=argparse.ArgumentParser();parser.add_argument('--headroom-gate',type=Path,required=True);parser.add_argument('--intake',type=Path,required=True);cli=parser.parse_args()
    assert not (H/'prepared.json').exists()
    gate_path=cli.headroom_gate.resolve();gate=read(gate_path)
    assert gate['schema']=='pinwheel-buffered-tt-holdreset-pair-headroom-gate-v1' and gate['status']=='passed' and gate['admitted_to_resize'] is True
    assert gate['source_database_sha256']=='8c3079c61f73f0f2819d4e0d21d0af2775d4afb76c620494e2841ace4b1dd063'
    assert gate['all_corner_coverage_complete'] is True and gate['minimum_through_hold_ns']>=1.05 and gate['minimum_through_setup_ns']>=0
    assert gate['hold_loss_allowance_ns']==1 and gate['minimum_conservative_residual_hold_ns']>=.05 and gate['estimated_slow_drive_gain_ns']>0 and gate['NLDM_loss_bound_within_allowance'] is True
    assert gate['exact_target_pins']==['fanout914/X','fanout913/X']
    report_path=gate_path.parent/'report.json';report=read(report_path)
    assert sha(report_path)==gate['preflight_report_sha256'] and report['status']=='passed' and report['exit_code']==0 and report['inputs_unchanged'] and report['container_termination']['status']=='absent'
    intake=read(cli.intake);assert intake['status']=='passed'
    paths={str(cli.intake.resolve()):sha(cli.intake),**intake['source_sha256'],str(gate_path):sha(gate_path),str(report_path):sha(report_path),**report['input_sha256']}
    paths.update({str(report_path.parent/n):h for n,h in report['artifact_sha256'].items()})
    prior=ROOT/'build/physical/tt-buffered-hold30712-tools-02/prepared.json';previous=read(prior);paths[str(prior)]=sha(prior);paths.update(previous['source_sha256']);paths.update(previous['tool_sha256'])
    for name in ['qualified-control-source.json','qualified-pair-source.json']:
        q=read(H/name);paths.update(q['artifacts_sha256'])
    for name in ['plan.json','pair-policy.json','replay-selection.json','replay-headroom-gate.json']:paths[str(H/name)]=sha(H/name)
    for n,h in paths.items():assert sha(Path(n) if Path(n).is_absolute() else ROOT/n)==h,n
    for p in H.rglob('*.py'):ast.parse(p.read_text())
    tools={str(p.relative_to(ROOT)):sha(p) for p in sorted(H.rglob('*')) if p.is_file()}
    plan=read(H/'plan.json');pair=read(H/'qualified-pair-source.json')
    receipt={'schema':'pinwheel-buffered-tt-fanout913914-prepared-v1','status':'prepared_not_launched','source_sha256':paths,'tool_sha256':tools,'source_database':plan['source_database'],'source_database_sha256':plan['source_database_sha256'],'comparison_database_sha256':pair['control_database_sha256'],'pair_policy_sha256':sha(H/'pair-policy.json'),'headroom_gate':{'path':str(gate_path.relative_to(ROOT)),'sha256':sha(gate_path)},'preflight_selection_sha256':report['selection_sha256'],'executable_verification':previous['executable_verification'],'native_work_seconds_at_most':360,'all_in_cap_seconds':420,'cpus':4,'memory':'3g','network':'none','native_stop_utc':'2026-10-13T19:50:58Z','deadline_utc':'2026-10-13T19:54:58Z','only_resized_instances':['fanout913','fanout914'],'allowed_signal_routes':['_11039_','net913','net914'],'no_optimizer_or_placement_calls':True,'all_CLOCK_and_unrelated_routes_frozen':True,'historical_replay_plan_sha256':sha(H/'plan.json')}
    write(H/'prepared.json',receipt)
    print(json.dumps({'prepared_sha256':sha(H/'prepared.json'),'tool_files':len(tools),'source_bindings':len(paths),'live_sha256':sha(H/'live.py'),'driver_sha256':sha(H/'driver.py')}))
if __name__=='__main__':main()
