"""Independently close frozen Lean replay before detailed-route admission.

Immutable earlier receipts stay unchanged. This companion binds their exact
source/compiler/module/native journals and the later physical continuation.
It permits a bounded routing/signoff attempt; it does not accept its result.
"""
import argparse
from pathlib import Path
import re
import subprocess

from streaming_tt_signoff import read,regular,require,sha,unchanged,write
from streaming_tt_opt_intake import ROOT,artifacts
from streaming_mapped_campaign import audit_source
from validation_run import fresh_directory


def bound(value):
    path=regular(value['path']);require(sha(path)==value['sha256'],'Changed bound replay artifact')
    return path


def journal_matches(path,commands):
    rows=[read_line(line) for line in regular(path).read_text().splitlines()]
    require(len(rows)==2*len(commands),'Incomplete/extra native replay operations')
    for index,command in enumerate(commands):
        intent,result=rows[index*2:index*2+2]
        require(intent.get('event')=='intent' and result.get('event')=='result',
            'Reordered or unclosed native replay journal')
        require({key:value for key,value in result.items() if key!='event'}==command,
            'Native replay result differs from child receipt')
        require(all(key!='event' and command.get(key)==value for key,value in intent.items() if key!='event'),
            'Native replay intent/result mismatch')
        require(type(command.get('exit_code')) is int and command['compiler_sha256_before']==
            command['compiler_sha256_after']==sha(regular(command['argv'][0])) and
            command['source_sha256_before']==command['source_sha256_after']==sha(regular(command['argv'][-1])) and
            command['log_sha256']==sha(regular(command['log'])),'Native replay source/compiler/log changed')
    return rows


def read_line(text):
    from streaming_tt_signoff import decode
    return decode(text)


def close_replay(parent_path,replay_path,private_path,tag):
    parent_path,replay_path,private_path=map(regular,(parent_path,replay_path,private_path))
    parent,replay,private=map(read,(parent_path,replay_path,private_path))
    commit=parent['source_commit']
    require(parent.get('schema')=='pinwheel.streaming-tt-optimized-intake.v1' and parent.get('passed') is True and
        parent.get('qualified') is False and len(parent['checked'])==9 and all(parent['checked'].values()),
        'Source candidate lacks independent parent admission')
    require(replay.get('schema')=='pinwheel.streaming-tt-optimization-frozen-replay.v1' and
        replay.get('passed') is True and replay.get('qualified') is False and replay.get('stage')=='closed' and
        replay.get('source_commit')==replay.get('producer_commit')==commit,'Frozen Lean replay not closed')
    for key in ('all_regenerated_sources_identical','generated_sources_unchanged','library_objects_unchanged',
        'original_artifacts_unchanged','private_unused_axiom_rejected','sources_unchanged'):
        require(replay.get(key) is True,'Missing frozen replay closeout: '+key)
    require(private.get('schema')=='pinwheel.streaming-tt-private-control.v1' and private.get('passed') is True and
        private.get('qualified') is False and private.get('source_commit')==commit and
        private.get('inputs_unchanged') is True and private.get('unused_private_axiom_rejected') is True,
        'Exact-environment unused-private-axiom control missing')
    require(replay['closed_worker_report']==parent['worker_report']['path'] and
        replay['closed_worker_report_sha256']==parent['worker_report']['sha256'],'Replay belongs to another candidate')
    worker=read(bound(parent['worker_report']));cfg=read(bound(parent['worker_config']))
    fresh=any('fresh_foundation' in value for value in (cfg,replay,private))
    if fresh:
        require(cfg.get('fresh_foundation')==replay.get('fresh_foundation')==private.get('fresh_foundation') and
            type(cfg.get('fresh_foundation')) is dict,'Fresh replay/private foundation marker differs')
    unchanged(replay['closed_input_sha256_before']);unchanged(replay['library_artifacts_before'])
    require(replay['source_sha256_before']==replay['source_sha256_after'],'Selected replay source snapshot changed')
    unchanged({str(Path(cfg['root'])/name):value for name,value in replay['source_sha256_before'].items()})
    library=Path(cfg['root'])/'.lake/build/lib/lean'
    require({str(library/name):value for name,value in artifacts(library).items()}==replay['library_artifacts_before'],
        'Replay source library membership changed')
    require(replay['tool_identity_before']==replay['tool_identity_after'],'Replay tool/runtime identity changed')
    from streaming_tt_opt_intake import load
    gate=load('_streaming_tt_replay_gate',ROOT/'scripts/check-streaming-uart.py');helper=gate.helpers()
    require(gate.tool_identity(helper,cfg['tools'],read(Path(cfg['root'])/'tools/hardware-toolchain.json'))==
        replay['tool_identity_before'],'Actual replay tool/runtime differs')
    regeneration=read(bound(replay['regeneration_manifest']));modules=regeneration['modules']
    parent_plan=read(parent_path.parent/'native-replay-plan.json')['modules']
    count=392
    if replay.get('replay_inventory_profile') is not None:
        require(fresh,'Exact-inventory replay requires fresh source/library binding')
        from streaming_tt_replay_inventory import validate
        count=validate(replay,parent_path,modules)
    else:require('exact_parent_inventory' not in replay,'Unmarked exact replay inventory')
    require(len(modules)==replay['module_count']==replay['positive_native_checks']==count and
        replay['regenerated_modules']==count and len({entry['module'] for entry in modules})==count,
        'Incomplete regenerated/replayed module closure')
    require([(entry['module'],entry['sha256']) for entry in modules]==
        [(entry['module'],entry['sha256']) for entry in parent_plan],
        'Frozen replay module sources differ from independently regenerated parent sources')
    require({entry['source']:entry['sha256'] for entry in modules}==replay['generated_source_sha256_before'],
        'Whole generated source set was not frozen')
    unchanged(replay['generated_source_sha256_before'])
    commands=replay['commands'];replay_events=journal_matches(bound(replay['native_journal']),commands)
    positive=[row for row in commands if row['negative_control'] is False]
    require(len(commands)==count+2 and len(positive)==count,'Missing positive native module operations')
    lean_path=':'.join(str(replay_path.parent/stage) for stage in ('frontend','core-d2','device'))+':'+str(library)
    for entry,row in zip(modules,positive):
        source=regular(entry['source']);object_path=source.with_suffix('.olean')
        require(row['module']==entry['module'] and row['source']==str(source) and row['exit_code']==0 and
            row['source_sha256_before']==entry['sha256'] and
            (fresh or row['lean_path']==lean_path and row['argv']==[cfg['tools']['lean'],
                '--root='+str(source.parent),'-DwarningAsError=true','-o',str(object_path),str(source)]) and
            row['object_sha256']==sha(regular(object_path)),
            'Positive module did not compile from exact frozen source/new output path')
    expected_outputs={str(Path(entry['source']).with_suffix(suffix)) for entry in modules for suffix in ('.lean','.olean','.log')}
    actual_outputs={str(path) for stage in ('frontend','core-d2','device')
        for path in (replay_path.parent/stage).rglob('*') if path.is_file()}
    if fresh:
        from streaming_tt_fresh_replay import validate_positive_stages,events
        binding,original_positive_events=validate_positive_stages(replay,cfg,modules,replay_path,parent_path=parent_path)
    else:require(actual_outputs==expected_outputs,'Unexpected generated replay import/output membership')
    audit=regular(bound(replay['final_audit']))
    require(re.fullmatch(r'Mapped audit: [1-9][0-9]* declarations, [1-9][0-9]* theorems; standard axioms only\.\s*',
        audit.read_text()) is not None,'Missing strict complete private-declaration audit')
    private_manifest=read(bound(private['input_manifest']))
    require(private_manifest['source_commit']==commit and private_manifest['selected_source_sha256']==
        replay['source_sha256_before'],'Private control uses another source snapshot')
    unchanged(private_manifest['input_sha256'])
    for path,identity in private_manifest['runtime_files'].items():
        require(str(Path(path).resolve())==identity['resolved'] and sha(regular(identity['resolved']))==identity['sha256'],
            'Private-control native runtime changed')
    private_commands=private['commands'];journal_matches(bound(private['native_journal']),private_commands)
    require(len(private_commands)==2 and [row['exit_code'] for row in private_commands]==[0,1],
        'Unused-private-axiom native control did not compile then reject')
    for row in private_commands:
        require(row['environment']==private_manifest['environment'] and row['cwd']==cfg['root'] and
            row['input_manifest_sha256']==private['input_manifest']['sha256'] and
            row['compiler_sha256_before']==private_manifest['compiler_sha256'],
            'Private control exact native environment/manifest mismatch')
    if fresh:
        from streaming_tt_fresh_replay import validate_private_commands
        validate_private_commands(private,private_manifest,cfg,replay_path,binding,worker)
        require(commands==positive+private_commands and replay_events==original_positive_events+
            events(bound(private['native_journal'])),'Replay aggregate differs from complete original positive+2 pre-use native journals')
    private_dir=private_path.parent;axiom_name=private_commands[0]['module'];audit_name=private_commands[1]['module']
    require((private_dir/(axiom_name+'.lean')).read_text()==
        'import StreamingOptimizedRequired\nnamespace Pinwheel.Artifact.OptimizationReplayExactControl\n'
        'private axiom forbiddenUnused : False\nend Pinwheel.Artifact.OptimizationReplayExactControl\n',
        'Private negative control source differs')
    require((private_dir/(audit_name+'.lean')).read_text()==audit_source([*worker['audit_owner_modules'],axiom_name]),
        'Private negative control does not execute the strict owner audit')
    message=Path(private_commands[1]['log']).read_text()
    require('Unapproved axioms in _private.'+axiom_name in message and '.forbiddenUnused' in message,
        'Private axiom was not the native rejection reason')
    out=fresh_directory(ROOT/'build/streaming-tt-optimization','replay-intake-'+tag).resolve()
    report=dict(schema='pinwheel.streaming-tt-replay-intake.v1',passed=True,qualified=False,physical_acceptance_claim=False,
        source_commit=commit,producer_commit=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),
        parent_intake=dict(path=str(parent_path),sha256=sha(parent_path)),
        frozen_replay=dict(path=str(replay_path),sha256=sha(replay_path)),
        private_axiom_control=dict(path=str(private_path),sha256=sha(private_path)),
        generated_modules=count,positive_native_checks=count,
        checked={name:True for name in ('regenerated_frozen_replay','actual_native_journal',
            'strict_private_axiom_control','input_closeout')},candidate_json=parent['artifacts']['candidate_json'],
        candidate_sv=parent['artifacts']['candidate_sv'],
        excluded_control_note='Earlier replay negative-journal environment presentation is superseded by the separately frozen exact-environment control.',
        boundary='Frozen source correspondence/replay closed. Actual closed physical checkpoint admission, post-PNR proof and every physical signoff result remain separate.')
    if replay.get('replay_inventory_profile') is not None:
        report.update(replay_inventory_profile=replay['replay_inventory_profile'],exact_parent_inventory=replay['exact_parent_inventory'])
    write(out/'report.json',report);print(out/'report.json',flush=True);return report


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    for name in ('parent-intake','replay','private-control','tag'):parser.add_argument('--'+name,required=True)
    args=parser.parse_args()
    require(regular(__file__).read_bytes()==subprocess.check_output(['git','show','HEAD:scripts/streaming_tt_replay_intake.py'],cwd=ROOT),
        'Commit parent replay intake before use')
    close_replay(args.parent_intake,args.replay,args.private_control,args.tag)


if __name__=='__main__':main()
