"""Bind fresh649 replay to original bounded native stages and exact controls."""
import argparse
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import time

import streaming_tt_fresh_foundation as F
from streaming_mapped_campaign import audit_source

STAGE_CHECKS = {'lean_binary_unchanged','toolchain_seal_unchanged','foundation_library_unchanged',
    'foundation_receipt_unchanged','runner_unchanged','source_seal_unchanged','schedule_unchanged',
    'sources_unchanged','generated_namespace_and_order_unchanged','command_intents_durable_and_exact',
    'selected_imports_unchanged','import_resolution_unchanged','import_plan_and_sources_reverified',
    'successful_outputs_intact','all_process_groups_closed'}
POSITIVE_INTENT_KEYS={'index','module','argv','source','source_sha256','source_sha256_before',
    'compiler_sha256_before','lean_path','negative_control','started_at'}
PRIVATE_INTENT_KEYS={'index','module','source','argv','cwd','environment','lean_path',
    'input_manifest_sha256','source_sha256_before','compiler_sha256_before','negative_control'}


def dump(path, value):
    Path(path).write_text(json.dumps(value, indent=2, allow_nan=False) + '\n')


def events(path):
    return [json.loads(line, object_pairs_hook=F.pairs) for line in Path(path).read_text().splitlines()]


def validate_positive_stages(replay, config, modules, replay_path, *, parent_path=None):
    """Native stage receipts are authoritative; rows and intents are not invented."""
    marker = config['fresh_foundation']; binding = F.read(F.verify_bound(marker))
    F.require(replay.get('fresh_foundation') == marker and binding['candidate_commit'] == config['source_commit'] ==
        config['producer_commit'] == replay['source_commit'] == replay['producer_commit'], 'Fresh replay source/foundation selection differs')
    F.verify_binding(binding); F.verify_staged(binding); F.check_native_environment()
    from streaming_tt_replay_inventory import validate
    count=validate(replay,parent_path,modules)
    base = Path(replay_path).resolve().parent
    roots = [base / stage for stage in ('frontend', 'core-d2', 'device')]
    library = Path(binding['candidate_root']) / '.lake/build/lib/lean'
    stdlib = Path(binding['lean']).parent.parent / 'lib/lean'
    F.generated_paths_owned(roots, base)
    stages = replay.get('positive_native_stages', [])
    F.require(len(stages) == 3, 'All three fresh native replay stages are mandatory')
    regeneration=F.read(F.verify_bound(replay['regeneration_manifest']))
    frozen=regeneration['input_sha256']
    F.require(frozen and all(F.sha(F.regular(name))==value for name,value in frozen.items()),
        'Frozen replay regeneration/producer inputs changed')
    commands = []; native_events = []; allowed = set()
    for stage, root in zip(stages, roots):
        paths = {key: F.verify_bound(stage[key]) for key in
            ('report', 'source_seal', 'import_resolution', 'post_import_resolution', 'native_journal', 'runner', 'schedule')}
        native = F.read(paths['report']); seal = F.read(paths['source_seal'])
        selected = [row for row in modules if Path(row['source']).parent == root]
        F.require(selected and native.get('status') == 'completed' and native.get('qualified') is False and
            native.get('required_modules') == [row['module'] for row in selected] and
            type(native.get('required_count')) is int and native['required_count'] == len(selected) and
            native.get('completed_count') == len(selected) and native.get('attempted_count') == len(selected) and
            native.get('exact_membership_and_order') is True and native.get('all_final_checks_passed') is True and
            set(native.get('final_checks',{})) == STAGE_CHECKS and all(value is True for value in native['final_checks'].values()),
            'Fresh native stage is partial, failed or lacks exact source membership')
        F.require(native['source_seal_sha256'] == stage['source_seal']['sha256'] and
            native['post_import_resolution_sha256'] == stage['post_import_resolution']['sha256'] and
            native['native_journal'] == stage['native_journal'] and
            seal['native_journal_path'] == str(paths['native_journal']) and
            seal['import_resolution_sha256'] == stage['import_resolution']['sha256'] and
            seal['runner_sha256'] == stage['runner']['sha256'] and
            seal['schedule_sha256'] == stage['schedule']['sha256'] and
            seal['foundation_binding_sha256'] == marker['sha256'] and
            seal['positive_foundation_artifacts'] == 1298 and seal['foundation_library_verified_before_native'] is True and
            seal['sources'] == {row['module']: row['sha256'] for row in selected} and
            seal['lean_binary_sha256'] == F.sha(binding['lean']), 'Fresh native stage producer/source/import seal differs')
        schedule=F.read(paths['schedule'])
        F.require((schedule[native['phase']] if type(schedule) is dict else schedule)==native['required_modules'],
            'Fresh native stage selected schedule differs')
        for key in ('import_resolution', 'post_import_resolution'):
            resolution = F.read(paths[key])
            F.require(resolution.get('foundation_binding_sha256') == marker['sha256'] and
                all(row.get('foundation_binding_sha256') == marker['sha256'] for row in resolution['rows']
                    if row['status'] == 'resolved_exactly_once'), 'Fresh native import resolution borrowed another source wave')
        origin_receipt=F.read(paths['import_resolution'])
        origin_path=F.verify_bound(dict(path=origin_receipt['plan_path'],sha256=origin_receipt['plan_sha256']))
        origin=F.read(origin_path);checker=F.regular(origin_path.parent/'verify.py');checker_sha=F.sha(checker)
        F.require(checker_sha==origin_receipt['checker_sha256'] and
            any(value==checker_sha and F.sha(F.regular(name))==checker_sha for name,value in frozen.items()) and
            origin['foundation_binding']==marker and origin['foundation_binding_sha256']==marker['sha256'] and
            Path(origin['proof_root'])==base and origin['required_count']==len(modules)==count and
            [(row['module'],row['source'],row['source_sha256'],row['target_olean']) for row in origin['rows']]==
            [(row['module'],row['source'],row['sha256'],str(Path(row['source']).with_suffix('.olean'))) for row in modules],
            'Native import checker/plan is outside the complete frozen regenerated producer closure')
        spec=importlib.util.spec_from_file_location('_frozen_fresh_replay_import_checker',checker)
        verifier=importlib.util.module_from_spec(spec);spec.loader.exec_module(verifier)
        verifier.complete_group(paths['report'],{row['module']:row for row in origin['rows']},binding,
            marker['sha256'],Path(__file__).resolve().parents[1],paths['runner'],origin['stages'])
        search = seal['lean_path'].split(os.pathsep)
        F.require(search[:2] == [str(library), str(stdlib)] and search[2:] and
            len(search) == len(set(search)) and set(search[2:]) <= set(map(str, roots)) and str(root) in search,
            'Fresh replay import roots/precedence differ')
        rows = native['commands']; F.require(len(rows) == len(selected), 'Fresh stage native command count differs')
        journal = events(paths['native_journal'])
        F.require(len(journal) == 2 * len(rows), 'Fresh stage lacks original pre-use native intents')
        for index, (source, row) in enumerate(zip(selected, rows)):
            path = F.regular(source['source']); obj = path.with_suffix('.olean'); log = F.regular(row['log'])
            expected = [binding['lean'], '-M4096', '-j1', '-DElab.async=false', '--root=' + str(root),
                '-DwarningAsError=true', '-DmaxErrors=1', '-o', str(obj), str(path)]
            F.require(row.get('module') == source['module'] and row.get('source') == str(path) and row.get('argv') == expected and
                type(row.get('index')) is int and row['index']==index and
                row.get('lean_path') == seal['lean_path'] and type(row.get('exit_code')) is int and row['exit_code'] == 0 and
                row.get('timed_out') is False and row.get('native_process_group_closed') is True and
                row.get('source_unchanged') is True and row.get('olean_exists_nonempty') is True and
                row.get('negative_control') is False and row['compiler_sha256_before'] == row['compiler_sha256_after'] == F.sha(binding['lean']) and
                row['source_sha256_before'] == row['source_sha256_after'] == source['sha256'] == F.sha(path) and
                obj.is_file() and not obj.is_symlink() and obj.stat().st_size > 0 and
                row['object_sha256'] == row['olean_sha256'] == F.sha(obj) and log.parent == root and row['log_sha256'] == F.sha(log),
                'Fresh replay command/object/source/log differs from bounded native execution')
            intent, result = journal[2*index:2*index+2]
            F.require(intent.get('event') == 'intent' and result.get('event') == 'result' and
                set(intent)==POSITIVE_INTENT_KEYS|{'event'} and type(intent.get('index')) is int and
                intent['index']==index and type(intent.get('started_at')) is str and bool(intent['started_at']) and
                intent['source_sha256']==source['sha256'] and
                {k:v for k,v in result.items() if k != 'event'} == row and
                all(row.get(k) == v for k,v in intent.items() if k != 'event'), 'Fresh original intent/result mapping differs')
            allowed.update((path, obj, log))
        commands.extend(rows); native_events.extend(journal)
        allowed.update(path for key, path in paths.items() if key != 'runner' and path.parent == root)
    F.require([row['module'] for row in commands] == [row['module'] for row in modules] and len(commands) == count,
        'Complete fresh native replay order/membership differs')
    positive = [row for row in replay['commands'] if row.get('negative_control') is False]
    F.require(positive == commands, 'Replay positive rows differ from authoritative original native stages')
    actual = set()
    for root in roots:
        for path in root.rglob('*'):
            F.require(not path.is_symlink(), 'Aliased fresh replay output')
            if path.is_file(): actual.add(path)
    F.require(actual == allowed, 'Unexpected/missing fresh replay import or output membership')
    return binding, native_events


def run_private_control(parent_path, positive_path, out):
    """Exactly two Native commands in the frozen complete positive environment."""
    parent_path = F.regular(Path(parent_path).resolve()); positive_path = F.regular(Path(positive_path).resolve())
    parent = F.read(parent_path); positive = F.read(positive_path)
    F.require(parent.get('passed') is True and parent.get('schema') == 'pinwheel.streaming-tt-optimized-intake.v1' and
        positive.get('schema') == 'pinwheel.streaming-tt-fresh-replay-positive.v1' and positive.get('passed') is True and
        type(positive.get('positive_native_checks')) is int, 'Complete source-bound positive replay required')
    cfg = F.read(F.verify_bound(parent['worker_config'])); worker = F.read(F.verify_bound(parent['worker_report']))
    regeneration = F.read(F.verify_bound(positive['regeneration_manifest']))
    binding, _ = validate_positive_stages(positive, cfg, regeneration['modules'], positive_path,parent_path=parent_path)
    out = Path(out).resolve(); F.require(not out.exists(), 'Preserve previous private-control attempt'); out.mkdir(parents=True)
    bad = 'StreamingOptimizedReplayExactPrivateAxiom'; audit = 'StreamingOptimizedReplayExactPrivateAudit'
    texts = {bad: 'import StreamingOptimizedRequired\nnamespace Pinwheel.Artifact.OptimizationReplayExactControl\n'
        'private axiom forbiddenUnused : False\nend Pinwheel.Artifact.OptimizationReplayExactControl\n',
        audit: audit_source([*worker['audit_owner_modules'], bad])}
    for name, text in texts.items(): (out / (name + '.lean')).write_text(text)
    source = Path(cfg['root']); library = source / '.lake/build/lib/lean'; stdlib = Path(binding['lean']).parent.parent / 'lib/lean'
    roots = [positive_path.parent / stage for stage in ('frontend', 'core-d2', 'device')]
    environment = {key:os.environ[key] for key in ('HOME','PATH','TMPDIR','LANG','LC_ALL') if key in os.environ}
    environment.update(LEAN_PATH=os.pathsep.join(map(str,[library,stdlib,out,*roots])), LEAN_SYSROOT=str(stdlib.parent.parent))
    selected = F.read(F.verify_bound(parent['raw_gate_report']))['source_sha256']
    F.require(all(F.sha(source/name)==value for name,value in selected.items()),'Selected source changed before private control')
    inputs = {str(parent_path):F.sha(parent_path),str(positive_path):F.sha(positive_path),str(Path(__file__).resolve()):F.sha(__file__)}
    for directory in [*roots,library,out]:
        for path in directory.rglob('*'):
            F.require(not path.is_symlink(), 'Aliased private-control input')
            if path.is_file(): inputs[str(path)] = F.sha(path)
    runtime = F.read(F.verify_bound(binding['runtime_report']))
    runtime_files = F.read(F.verify_bound(runtime['runtime_before']))
    manifest = out/'input-manifest.json'; dump(manifest,dict(schema='pinwheel.streaming-tt-private-control-inputs.v1',
        source_commit=cfg['source_commit'],fresh_foundation=cfg['fresh_foundation'],input_sha256=inputs,
        compiler_sha256=F.sha(binding['lean']),selected_source_sha256=selected,environment=environment,runtime_files=runtime_files,
        audit_owner_modules=worker['audit_owner_modules']))
    receipt = dict(schema='pinwheel.streaming-tt-private-control.v1',passed=False,qualified=False,source_commit=cfg['source_commit'],
        fresh_foundation=cfg['fresh_foundation'],input_manifest=F.bound(manifest),commands=[])
    journal=out/'journal.jsonl'; report=out/'report.json'
    def event(row):
        with journal.open('a') as stream:
            stream.write(json.dumps(row)+'\n');stream.flush();os.fsync(stream.fileno())
    dump(report,receipt)
    try:
        for name, expected in ((bad,0),(audit,1)):
            F.check_native_environment(); path=out/(name+'.lean');obj=path.with_suffix('.olean');log=path.with_suffix('.log')
            argv=[binding['lean'],'-M4096','-j1','-DElab.async=false','--root='+str(out),'-DwarningAsError=true',
                '-DmaxErrors=1','-o',str(obj),str(path)]
            row=dict(index=expected,module=name,source=str(path),argv=argv,cwd=str(source),environment=environment,lean_path=environment['LEAN_PATH'],
                input_manifest_sha256=F.sha(manifest),source_sha256_before=F.sha(path),compiler_sha256_before=F.sha(binding['lean']),negative_control=True)
            event(dict(event='intent',**row));start=time.monotonic();timed_out=False
            with log.open('wb') as stream:
                child=subprocess.Popen(argv,cwd=source,env=environment,stdout=stream,stderr=subprocess.STDOUT,start_new_session=True)
                try: code=child.wait(timeout=180)
                except subprocess.TimeoutExpired: timed_out=True;F.terminate_group(child.pid);child.wait(timeout=3);code=124
            closed=F.closed_group(child.pid)
            if not closed: closed=F.terminate_group(child.pid)
            row.update(exit_code=code,timed_out=timed_out,native_process_group_closed=closed,source_sha256_after=F.sha(path),
                compiler_sha256_after=F.sha(binding['lean']),log=str(log),log_sha256=F.sha(log),elapsed_seconds=time.monotonic()-start,
                object_sha256=F.sha(obj) if obj.is_file() else None)
            event(dict(event='result',**row));receipt['commands'].append(row);dump(report,receipt)
            F.require(type(code) is int and code==expected and not timed_out and closed and
                row['source_sha256_before']==row['source_sha256_after'] and row['compiler_sha256_before']==row['compiler_sha256_after'],
                'Private-control native outcome/source/ownership failed')
            if expected==0:F.require(obj.is_file() and not obj.is_symlink() and obj.stat().st_size>0,'No fresh private-control object')
        text=(out/(audit+'.log')).read_text()
        F.require('Unapproved axioms in _private.'+bad in text and '.forbiddenUnused' in text,'Unrelated private audit rejection')
        F.require(all(F.sha(name)==value for name,value in inputs.items()) and
            all(F.sha(source/name)==value for name,value in selected.items()) and F.sha(manifest)==receipt['input_manifest']['sha256'],
            'Private-control frozen input changed')
        F.verify_binding(binding);F.verify_staged(binding)
        receipt.update(passed=True,unused_private_axiom_rejected=True,inputs_unchanged=True,native_journal=F.bound(journal))
    except BaseException as error:
        receipt['error']=type(error).__name__+': '+str(error);dump(report,receipt);raise
    dump(report,receipt);return receipt


def validate_private_commands(private, manifest, config, replay_path, binding, worker):
    F.require(private.get('schema')=='pinwheel.streaming-tt-private-control.v1' and private.get('qualified') is False,
        'Wrong exact private-control receipt')
    marker=config['fresh_foundation'];out=Path(private['input_manifest']['path']).resolve().parent
    library=Path(config['root'])/'.lake/build/lib/lean';stdlib=Path(binding['lean']).parent.parent/'lib/lean'
    roots=[Path(replay_path).resolve().parent/stage for stage in ('frontend','core-d2','device')]
    environment=manifest['environment']
    F.require(manifest.get('fresh_foundation')==private.get('fresh_foundation')==marker and
        environment.get('LEAN_PATH')==os.pathsep.join(map(str,[library,stdlib,out,*roots])) and
        environment.get('LEAN_SYSROOT')==str(stdlib.parent.parent) and
        set(environment)<= {'HOME','PATH','TMPDIR','LANG','LC_ALL','LEAN_PATH','LEAN_SYSROOT'},
        'Private control import environment/binding differs')
    runtime=F.read(F.verify_bound(binding['runtime_report']))
    F.require(manifest['runtime_files']==F.read(F.verify_bound(runtime['runtime_before'])),
        'Private control full runtime membership differs')
    commands=private['commands'];F.require(len(commands)==2,'Exactly two private-control operations required')
    bad='StreamingOptimizedReplayExactPrivateAxiom';audit='StreamingOptimizedReplayExactPrivateAudit'
    F.require([row['module'] for row in commands]==[bad,audit] and
        manifest['audit_owner_modules']==worker['audit_owner_modules'] and
        (out/(bad+'.lean')).read_text()=='import StreamingOptimizedRequired\nnamespace Pinwheel.Artifact.OptimizationReplayExactControl\n'
        'private axiom forbiddenUnused : False\nend Pinwheel.Artifact.OptimizationReplayExactControl\n' and
        (out/(audit+'.lean')).read_text()==audit_source([*worker['audit_owner_modules'],bad]),
        'Exact private-control module names/source/owner audit differ')
    original=events(F.verify_bound(private['native_journal']))
    F.require(len(original)==4,'Private original pre-use journal incomplete')
    for index,row in enumerate(commands):
        path=out/(row['module']+'.lean');obj=path.with_suffix('.olean');log=path.with_suffix('.log')
        F.require(row.get('argv')==[binding['lean'],'-M4096','-j1','-DElab.async=false','--root='+str(out),
            '-DwarningAsError=true','-DmaxErrors=1','-o',str(obj),str(path)] and row.get('source')==str(path) and
            row.get('cwd')==config['root'] and row.get('environment')==environment and row.get('lean_path')==environment['LEAN_PATH'] and
            type(row.get('index')) is int and row['index']==index and
            row.get('negative_control') is True and row.get('timed_out') is False and row.get('native_process_group_closed') is True and
            type(row.get('exit_code')) is int and row['exit_code']==index and row['source_sha256_before']==row['source_sha256_after']==F.sha(path) and
            row['compiler_sha256_before']==row['compiler_sha256_after']==F.sha(binding['lean']) and row['log']==str(log) and
            row['log_sha256']==F.sha(log) and row['input_manifest_sha256']==private['input_manifest']['sha256'],
            'Private control actual bounded command/source/log/ownership differs')
        if index==0:F.require(obj.is_file() and not obj.is_symlink() and obj.stat().st_size>0 and
            F.sha(obj)==row.get('object_sha256'),'Private axiom object was not freshly compiled')
        intent,result=original[2*index:2*index+2]
        F.require(intent.get('event')=='intent' and result.get('event')=='result' and
            set(intent)==PRIVATE_INTENT_KEYS|{'event'} and type(intent.get('index')) is int and intent['index']==index and
            {k:v for k,v in result.items() if k!='event'}==row and
            all(row.get(k)==v for k,v in intent.items() if k!='event'),'Private original intent/result differs')
    text=(out/(audit+'.log')).read_text()
    F.require('Unapproved axioms in _private.'+bad in text and '.forbiddenUnused' in text,
        'Private-control audit failed for an unrelated reason')
    return True


def assemble(parent_path, positive_path, private_path):
    """Close one replay by joining all original positive+2 events without replaying Lean."""
    parent=F.read(F.regular(Path(parent_path).resolve()));positive_path=F.regular(Path(positive_path).resolve())
    positive=F.read(positive_path);private_path=F.regular(Path(private_path).resolve());private=F.read(private_path)
    config=F.read(F.verify_bound(parent['worker_config']));modules=F.read(F.verify_bound(positive['regeneration_manifest']))['modules']
    binding,original_events=validate_positive_stages(positive,config,modules,positive_path,parent_path=parent_path)
    F.require(private.get('passed') is True and private.get('inputs_unchanged') is True and
        private.get('unused_private_axiom_rejected') is True,'Exact private control has not closed')
    validate_private_commands(private,F.read(F.verify_bound(private['input_manifest'])),config,positive_path,binding,
        F.read(F.verify_bound(parent['worker_report'])))
    required=('all_regenerated_sources_identical','generated_sources_unchanged','library_objects_unchanged',
        'original_artifacts_unchanged','sources_unchanged')
    F.require(all(positive.get(key) is True for key in required),'Positive replay immutable closeout missing')
    report=positive_path.parent/'report.json';journal=positive_path.parent/'native-journal.jsonl'
    F.require(not report.exists() and not journal.exists(),'Preserve prior assembled replay')
    combined=original_events+events(F.verify_bound(private['native_journal']))
    journal.write_text(''.join(json.dumps(row)+'\n' for row in combined))
    receipt=dict(positive,schema='pinwheel.streaming-tt-optimization-frozen-replay.v1',passed=True,qualified=False,
        stage='closed',module_count=len(modules),regenerated_modules=len(modules),positive_native_checks=len(modules),negative_native_checks=2,
        commands=positive['commands']+private['commands'],private_unused_axiom_rejected=True,native_journal=F.bound(journal),
        exact_private_control=F.bound(private_path),positive_native_manifest=F.bound(positive_path))
    dump(report,receipt);return receipt


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    for name in ('parent-intake','positive-manifest','out'):parser.add_argument('--'+name,required=True)
    args=parser.parse_args()
    F.require(Path(__file__).read_bytes()==subprocess.check_output(['git','show','HEAD:scripts/streaming_tt_fresh_replay.py']),
        'Commit the exact fresh replay/control producer before Native execution')
    run_private_control(args.parent_intake,args.positive_manifest,args.out)
    assemble(args.parent_intake,args.positive_manifest,Path(args.out)/'report.json')


if __name__=='__main__':main()
