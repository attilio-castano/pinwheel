"""Launch one immutable warm-router pair-resize experiment after safety admission."""
import argparse,datetime,json,math,shutil,time
from pathlib import Path
from common import ROOT,execute,sha,read,write
H=Path(__file__).resolve().parent
STOP=datetime.datetime.fromisoformat('2026-10-13T19:50:58+00:00').timestamp()
DEADLINE=datetime.datetime.fromisoformat('2026-10-13T19:54:58+00:00').timestamp()
def verify(items):
    for n,h in items.items():
        p=Path(n) if Path(n).is_absolute() else ROOT/n
        assert p.is_file() and sha(p)==h,n
def main():
    parser=argparse.ArgumentParser();parser.add_argument('--selection',type=Path,required=True);parser.add_argument('--tag',default='tt-buffered-fanout913914-route-01');cli=parser.parse_args();started=time.monotonic()
    assert cli.tag=='tt-buffered-fanout913914-route-01'
    selection=read(cli.selection);prepared=read(H/'prepared.json')
    assert selection['schema']=='pinwheel-buffered-tt-fanout913914-selection-v1' and selection['routing_iterations']==10
    assert selection['prepared_sha256']==sha(H/'prepared.json') and selection['pair_policy_sha256']==sha(H/'pair-policy.json')
    assert selection['headroom_gate']==prepared['headroom_gate']
    preflight_selection=selection['preflight_selection']
    assert sha(ROOT/preflight_selection['path'])==preflight_selection['sha256']==prepared['preflight_selection_sha256']
    assert selection['one_candidate_only'] is True and selection['base_database_sha256']==prepared['comparison_database_sha256']
    pair=read(H/'pair-policy.json')
    assert set(selection['allowed_signal_route_nets'])==set(pair['allowed_signal_routes'])
    assert set(selection['edits'])==set(pair['resizes'])
    for name,edit in selection['edits'].items():
        policy=pair['resizes'][name]
        assert edit=={'before_master':policy['before'],'after_master':policy['after'],'before_bbox_DBU':policy['before_bbox_dbu'],'target_bbox_DBU':policy['bbox_dbu'],'orientation':policy['orientation']}
    assert selection['native_stop_utc']=='2026-10-13T19:50:58Z' and selection['deadline_utc']=='2026-10-13T19:54:58Z'
    verify(prepared['source_sha256']);verify(prepared['tool_sha256'])
    verify(selection['source_bindings_sha256']);verify(selection['protected_sources_sha256'])
    assert sha(ROOT/prepared['source_database'])==prepared['source_database_sha256']=='95f0fdb260de137d5b4f77669c9aaa5eb3bf56e7dc55f4c9b7d51b2b8a16556e'
    gate_path=ROOT/prepared['headroom_gate']['path'];gate=read(gate_path)
    assert sha(gate_path)==prepared['headroom_gate']['sha256'] and gate['status']=='passed' and gate['admitted_to_resize'] is True
    out=ROOT/'build/physical'/cli.tag;assert not out.exists(),'Single-use immutable experiment';assert STOP-time.time()>360,'Insufficient full native window'
    assert time.time()+420<=DEADLINE,'Full host wall bound would exceed full deadline'
    out.mkdir()
    for file in H.iterdir():
        if file.is_file():shutil.copyfile(file,out/file.name)
        elif file.name in ('identity','lib'):shutil.copytree(file,out/file.name)
    recipe=ROOT/'build/physical/tt-buffered-timing-eco-control-route-01'
    shutil.copyfile(ROOT/prepared['source_database'],out/'postcts.odb');shutil.copyfile(recipe/'before.v',out/'reference.v')
    for name in ['baseline-env.tcl','corner-env.tcl','core.sdc']:shutil.copyfile(recipe/name,out/name)
    for file in (recipe/'lib').glob('*.lib'):shutil.copyfile(file,out/'lib'/file.name)
    shutil.copyfile(cli.selection,out/'selection.json');shutil.copyfile(gate_path,out/'headroom-gate.json')
    for source_name,folder_name in [('qualified-control-source.json','qualified-control'),('qualified-pair-source.json','qualified-pair')]:
        directory=out/folder_name;directory.mkdir()
        for name,digest in read(H/source_name)['artifacts_sha256'].items():
            file=Path(name) if Path(name).is_absolute() else ROOT/name
            assert sha(file)==digest
            if file.name!='report.json':shutil.copyfile(file,directory/file.name)
    write(out/'phase-inputs.json',{str(Path('/work/diagnostic')/file.relative_to(out)):sha(file) for file in out.rglob('*') if file.is_file()})
    paths=[cli.selection.resolve(),H/'prepared.json',*[Path(n) if Path(n).is_absolute() else ROOT/n for n in prepared['source_sha256']],*[Path(n) if Path(n).is_absolute() else ROOT/n for n in prepared['tool_sha256']],*[file for file in out.rglob('*') if file.is_file()]]
    work=360
    report=execute(out,paths,['python3','-B','/work/diagnostic/coordinator.py'],seconds=work,cpus=4,memory='3g',schema='pinwheel-buffered-tt-fanout913914-route-v1',scope='Warm originalR0 replay of qualified2+8ECO+30712move; exact8c controlmatch, matched3net dirtynoop, onlyfanout913/914buf1-to-buf4,3netincremental. Allothercells/clock/routes/PG/RTL/ABI/constraints unchanged.',extra={'network':'none','selection_sha256':sha(cli.selection),'prepared_sha256':sha(H/'prepared.json'),'headroom_gate_sha256':prepared['headroom_gate']['sha256'],'source_database':prepared['source_database'],'source_database_sha256':prepared['source_database_sha256'],'qualified_control_database_sha256':prepared['comparison_database_sha256'],'pair_policy_sha256':prepared['pair_policy_sha256'],'overall_bound_seconds':420,'native_stop_utc':'2026-10-13T19:50:58Z','deadline_utc':'2026-10-13T19:54:58Z','reference_native_flow_status':'failed','reference_native_flow_exit_code':2,'reference_inherited_power_count':30396},expected_hashes={out/'postcts.odb':prepared['source_database_sha256']},absolute_work_stop=STOP,all_in_deadline_monotonic=started+420)
    report['artifact_sha256'].update({str(file.relative_to(out)):sha(file) for file in sorted(out.rglob('*')) if file.is_file() and str(file.resolve()) not in report['input_sha256'] and file.name!='report.json'})
    verify(prepared['source_sha256']);verify(prepared['tool_sha256']);report['all_in_elapsed_seconds']=round(time.monotonic()-started,3)
    if report['all_in_elapsed_seconds']>420 or time.time()>DEADLINE:report['status']='bound_exceeded'
    write(out/'report.json',report);print(out/'report.json');return 0 if report['status']=='passed' else 1
if __name__=='__main__':raise SystemExit(main())
