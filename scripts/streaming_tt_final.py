"""Frozen continuation from an admitted post-global-route checkpoint.

Detailed routing and native signoff execution are diagnostic permission, not
acceptance. The latest ODB remains authoritative over a carried netlist view.
"""
import hashlib
import importlib.util
import json
import os
from pathlib import Path
from datetime import datetime, timezone
import shutil
import signal
import subprocess
import time
import uuid

import streaming_tt_physical as P
from streaming_tt_intake import dependency_closure, stage_sources

CHECKS = frozenset(('regenerated_frozen_replay','actual_native_journal','strict_private_axiom_control','input_closeout'))
TAIL = tuple('''OpenROAD.DetailedRouting
Odb.RemoveRoutingObstructions
OpenROAD.CheckAntennas-1
Checker.TrDRC
Odb.ReportDisconnectedPins
Checker.DisconnectedPins
Odb.ReportWireLength
Checker.WireLength
OpenROAD.FillInsertion
Odb.CellFrequencyTables
OpenROAD.RCX
OpenROAD.STAPostPNR
OpenROAD.IRDropReport
Magic.StreamOut
KLayout.StreamOut
KLayout.Render
Magic.WriteLEF
Odb.CheckDesignAntennaProperties
KLayout.XOR
Checker.XOR
Magic.DRC
KLayout.DRC
Checker.MagicDRC
Checker.KLayoutDRC
Magic.SpiceExtraction
Checker.IllegalOverlap
Netgen.LVS
Checker.LVS
Yosys.EQY
Checker.SetupViolations
Checker.HoldViolations
Checker.MaxSlewViolations
Checker.MaxCapViolations
Misc.ReportManufacturability'''.splitlines())
BOUNDARY = ('Source/replay-bound diagnostic continuation from an exact closed postGRT state. '
    'No check, recipe, SDC, routing-layer or PDK change is authorized. Native completion does not '
    'establish post-PNR correspondence, extracted timing acceptance, DRC/LVS/antenna/power closure '
    'or official TT precheck. Unsupported/skipped Classic checks are not successful signoff. '
    'A separately re-exported latest ODB must supply final logical/physical acceptance inputs.')


def common_runner():
    spec = importlib.util.spec_from_file_location('_streaming_tt_coarse_runner',
        Path(__file__).with_name('run-streaming-tt-physical.py'))
    module = importlib.util.module_from_spec(spec); spec.loader.exec_module(module)
    return module


def bound(entry):
    P.require(type(entry) is dict and {'path','sha256'} <= entry.keys(), 'Missing final-admission binding')
    path = P.regular(Path(entry['path']).absolute()).resolve()
    P.require(P.sha(path) == entry['sha256'], 'Final-admission input changed: '+str(path))
    return path


def validate_order(ids):
    P.require(type(ids) is list and len(ids) == len(set(ids)) and all(type(x) is str for x in ids),
        'Malformed native flow ordering')
    P.require('OpenROAD.STAMidPNR-3' in ids and 'OpenROAD.DetailedRouting' in ids,
        'Missing actual checkpoint or detailed-route native step')
    cut = ids.index('OpenROAD.DetailedRouting')
    P.require(ids.index('OpenROAD.STAMidPNR-3') + 1 == cut and tuple(ids[cut:]) == TAIL,
        'Native continuation would skip or alter a required scheduled step')
    return ids


def replay_count(parent_path,parent,replay,sealed,parent_binding,source):
    """Use the strict sealed intake's complete regenerated parent source manifest."""
    count=392
    if replay.get('replay_inventory_profile') is not None:
        # The closed intake already regenerated these complete sources. Keep
        # physical execution's import closure separate from its host coordinator.
        profile='pinwheel.streaming-tt-exact-parent-replay.v1'
        P.require(parent_binding==dict(path=str(parent_path),sha256=P.sha(P.regular(parent_path))) and
            P.read(parent_path)==parent,'Exact inventory parent receipt identity differs')
        inventory=replay.get('exact_parent_inventory',{})
        plan_path=P.regular(parent_path.parent/'native-replay-plan.json')
        plan=P.read(plan_path);rows=plan.get('modules',[])
        P.require(replay['replay_inventory_profile']==profile and rows and
            all(set(row)=={'module','path','sha256'} for row in rows) and
            len({row['module'] for row in rows})==len(rows) and
            plan==dict(source_commit=source,modules=rows),'Exact complete parent replay plan required')
        source_map={row['path']:row['sha256'] for row in rows};count=len(rows)
        stages=('frontend-proof','core-d2-proof','device-proof')
        selected_stages=[Path(row['path']).parent.name for row in rows]
        worker_root=bound(parent['worker_report']).parent
        P.require(set(selected_stages)==set(stages) and selected_stages==sorted(selected_stages,key=stages.index) and
            all(Path(row['path']).parent.parent==worker_root and Path(row['path']).name==row['module']+'.lean' for row in rows),
            'Detailed-route exact inventory omits or reorders a complete source stage')
        P.require(len(source_map)==count and type(parent.get('generated_module_count')) is int and
            parent['generated_module_count']==count and parent.get('generated_sources_sha256')==source_map and
            set(inventory)=={'schema','parent_intake','source_commit','native_replay_plan','module_count',
                'modules','generated_sources_sha256','input_sha256','validator_producer','regeneration_execution'} and
            inventory['schema']==profile and inventory['parent_intake']==parent_binding and
            inventory['source_commit']==source and inventory['native_replay_plan']==
                dict(path=str(plan_path),sha256=P.sha(plan_path)) and
            type(inventory['module_count']) is int and inventory['module_count']==count and
            inventory['modules']==rows and inventory['generated_sources_sha256']==source_map,
            'Exact inventory differs from independently regenerated complete parent sources')
        P.require(inventory['input_sha256'],'Missing exact inventory input closeout')
        P.require(all(P.sha(P.regular(path))==value for path,value in
            {**source_map,**inventory['input_sha256']}.items()),'Exact replay sources/validator inputs changed')
        regenerated=P.read(bound(replay['regeneration_manifest']))['modules']
        P.require([(row['module'],row['sha256']) for row in regenerated]==
            [(row['module'],row['sha256']) for row in rows] and replay.get('regenerated_modules')==count,
            'Frozen replay source membership/order differs from complete parent')
        P.require(sealed.get('replay_inventory_profile')==replay['replay_inventory_profile'] and
            sealed.get('exact_parent_inventory')==replay['exact_parent_inventory'] and
            sealed.get('generated_modules')==sealed.get('positive_native_checks')==count,
            'Detailed-route replay intake inventory profile/count differs')
        # This validator runs only bounded host Python from the immutable,
        # completely inventoried selected archive; it launches no CAD or Lean.
        from streaming_tt_replay_inventory import validate
        P.require(validate(replay,parent_path,validator_workspace=P.ROOT)==count,
            'Independent exact parent regeneration differs')
    else:P.require('exact_parent_inventory' not in replay and 'replay_inventory_profile' not in sealed and
        'exact_parent_inventory' not in sealed,'Unmarked detailed-route replay inventory')
    return count


def admission(path, expected):
    path = P.regular(Path(path).absolute()).resolve()
    P.require(P.sha(path) == expected, 'Final admission changed before use')
    report = P.read(path)
    P.require(report.get('schema') == 'pinwheel.streaming-tt-detailed-route-admission.v1' and
        report.get('passed') is True and report.get('qualified') is False and
        report.get('physical_acceptance_claim') is False and type(report.get('checked')) is dict and
        CHECKS <= report['checked'].keys() and all(report['checked'][name] is True for name in CHECKS),
        'Parent has not admitted diagnostic detailed routing')
    entries = {name:bound(report[name]) for name in ('parent_intake','replay_intake','frozen_replay',
        'private_axiom_control','candidate_json','candidate_sv','coarse_report','state','prepared_input')}
    parent, replay, private, sealed = (P.read(entries[name]) for name in
        ('parent_intake','frozen_replay','private_axiom_control','replay_intake'))
    source = report['source_commit']
    P.require(parent.get('schema') == 'pinwheel.streaming-tt-optimized-intake.v1' and parent.get('passed') is True and
        parent.get('source_commit') == source and sealed.get('schema') == 'pinwheel.streaming-tt-replay-intake.v1' and
        sealed.get('passed') is True and sealed.get('source_commit') == source and sealed.get('qualified') is False and
        all(sealed.get('checked',{}).get(name) is True for name in CHECKS), 'Source/replay parent intake is not closed')
    for name in ('parent_intake','frozen_replay','private_axiom_control','candidate_json','candidate_sv'):
        P.require(sealed[name] == report[name], 'Detailed-route admission changes the sealed replay identity')
    count=replay_count(entries['parent_intake'],parent,replay,sealed,report['parent_intake'],source)
    P.require(replay.get('schema') == 'pinwheel.streaming-tt-optimization-frozen-replay.v1' and
        replay.get('passed') is True and replay.get('source_commit') == source and replay.get('stage') == 'closed' and
        replay.get('module_count') == replay.get('positive_native_checks') == count and
        all(replay.get(name) is True for name in ('all_regenerated_sources_identical','generated_sources_unchanged',
            'original_artifacts_unchanged','library_objects_unchanged','sources_unchanged')) and
        private.get('schema') == 'pinwheel.streaming-tt-private-control.v1' and private.get('passed') is True and
        private.get('source_commit') == source and private.get('unused_private_axiom_rejected') is True and
        private.get('inputs_unchanged') is True, 'Frozen positive/private replay evidence is incomplete')
    coarse = P.read(entries['coarse_report']); prepared = P.read(entries['prepared_input'])
    P.require(coarse.get('schema') == 'pinwheel.streaming-tt-physical-run.v2' and coarse.get('status') == 'flow_completed' and
        coarse.get('exit_code') == 0 and coarse.get('stop_step') == 'OpenROAD.STAMidPNR-3' and
        coarse.get('inputs_unchanged_after_run') is True and coarse.get('container_termination',{}).get('status') == 'absent' and
        coarse.get('prepared_input_sha256') == P.sha(entries['prepared_input']) and
        coarse.get('candidate_source_commit') == source, 'Coarse physical checkpoint is not closed')
    design = Path(coarse['design']).resolve()
    P.require(entries['prepared_input'] == design/'inputs.json' and
        entries['coarse_report'].parent.resolve() == (P.BASE/coarse['tag']).resolve(), 'Physical receipt location mismatch')
    from streaming_tt_candidate import verify_optimized
    P.require(verify_optimized(design) == prepared, 'Prepared physical inputs do not reproduce')
    verify_cts_trial(coarse,prepared,entries['coarse_report'].parent)
    P.require(prepared['candidate']['admission_sha256'] == report['parent_intake']['sha256'] and
        prepared['candidate']['netlist_sha256'] == report['candidate_json']['sha256'] and
        prepared['candidate']['verilog_sha256'] == report['candidate_sv']['sha256'], 'Wrong physical candidate identity')
    relative = str(entries['state'].relative_to(entries['coarse_report'].parent))
    P.require(coarse['artifact_sha256'].get(relative) == P.sha(entries['state']) and
        entries['state'].name == 'state_out.json' and entries['state'].parent.name.endswith('openroad-stamidpnr-3'),
        'Checkpoint state is not the actual closed postGRT artifact')
    P.require(P.sha(path) == expected, 'Detailed-route admission changed during validation')
    return report, entries, design


def verify_cts_trial(coarse, prepared, coarse_root):
    """Before DRT, bind a declared CTS trial to its actual closed native log."""
    trial = prepared.get('physical_recipe_experiment',{}).get('cts_trial')
    if trial is None:
        return None  # Historical recipes do not make an explicit CTS8 claim.
    from streaming_tt_candidate import validate_cts_trial
    root = Path(coarse_root).resolve()
    resolved = P.regular(root/'flow/resolved.json')
    logs = list((root/'flow').glob('*-openroad-cts/openroad-cts.log'))
    P.require(len(logs) == 1, 'Missing/ambiguous closed native CTS log')
    log = P.regular(logs[0])
    for path in (resolved,log):
        relative = str(path.relative_to(root))
        P.require(coarse.get('artifact_sha256',{}).get(relative) == P.sha(path), 'Closed native CTS trial artifact changed')
    return validate_cts_trial(P.read(resolved),log.read_text())


def snapshot_state(state, coarse_root, design, destination):
    """Copy every referenced native view; reject unresolved/escaping paths."""
    roots = {'/work/run':Path(coarse_root).resolve(),
        '/work/inputs':(Path(design)/'inputs').resolve(),'/work/pdk':(Path(design)/'pdk').resolve()}
    files = {}; copied = {}
    def view(value):
        if value is None: return None
        if type(value) is list: return [view(child) for child in value]
        if type(value) is dict: return {name:view(child) for name,child in value.items()}
        P.require(type(value) is str, 'Unsupported native checkpoint view')
        path = None
        for prefix,root in roots.items():
            if value == prefix or value.startswith(prefix+'/'):
                path = root/value[len(prefix):].lstrip('/'); path = P.regular(path).resolve()
                P.require(path.is_relative_to(root), 'Checkpoint view escapes its native mount'); break
        P.require(path is not None, 'Unresolved native checkpoint view: '+value)
        if str(path) not in copied:
            name = str(len(copied)).zfill(3)+'-'+path.name
            target = destination/name; shutil.copyfile(path,target)
            files[str(path)] = P.sha(path); copied[str(path)] = '/work/inputs/checkpoint/'+name
        return copied[str(path)]
    result = {name:(value if name == 'metrics' else view(value)) for name,value in state.items()}
    P.require(type(result.get('odb')) is str, 'Checkpoint has no authoritative ODB')
    return result, files


def verify_view_inventory(files, coarse, coarse_root, prepared, design):
    """A live file hash must match the earlier closed input/artifact record."""
    roots = [(Path(coarse_root).resolve(),coarse['artifact_sha256']),
        ((Path(design)/'inputs').resolve(),prepared['input_sha256']),
        ((Path(design)/'pdk').resolve(),prepared['pdk']['complete_files_sha256'])]
    for name,value in files.items():
        path = Path(name).resolve(); matches = [(root,mapping) for root,mapping in roots if path.is_relative_to(root)]
        P.require(len(matches) == 1,'Checkpoint view has no unique closed source inventory')
        root,mapping = matches[0]
        P.require(mapping.get(str(path.relative_to(root))) == value,
            'Checkpoint view differs from closed source inventory: '+name)


def prepare(path, expected, tag, timeout_seconds):
    P.safe_name(tag); P.require(1 <= timeout_seconds <= 14400, 'Final continuation timeout must be1..14400 seconds')
    report, entries, design = admission(path,expected)
    sources = dict(P.producer_hashes(optimized=True))
    for name in ('scripts/streaming_tt_final.py','scripts/run-streaming-tt-final.py','test/test_streaming_tt_final.py'):
        sources[name] = hashlib.sha256(P.committed(P.ROOT/name)).hexdigest()
    closure = dependency_closure(P.ROOT,list(sources))
    for name in closure['files']:
        if name not in sources:sources[name]=hashlib.sha256(P.committed(P.ROOT/name)).hexdigest()
    P.require(set(closure['files']) == set(sources), 'Final producer imports are not completely staged')
    out = P.BASE/tag; out.mkdir(parents=True,exist_ok=False); inputs = out/'inputs'; inputs.mkdir()
    prepared = P.read(entries['prepared_input'])
    for name,value in prepared['input_sha256'].items():
        if name.startswith('producer/'): continue
        source = P.regular(design/'inputs'/P.relative_path(name)); P.require(P.sha(source) == value,'Prepared input changed')
        target = inputs/name; target.parent.mkdir(parents=True,exist_ok=True); shutil.copyfile(source,target)
    checkpoint = inputs/'checkpoint'; checkpoint.mkdir()
    state, views = snapshot_state(P.read(entries['state']),entries['coarse_report'].parent/'flow',design,checkpoint)
    verify_view_inventory(views,P.read(entries['coarse_report']),entries['coarse_report'].parent,prepared,design)
    P.write(inputs/'seed.json',state)
    stage_sources(P.ROOT,inputs/'producer',closure['files'],P.committed)
    for staged_path in inputs.rglob('*'):
        if staged_path.is_file(): staged_path.chmod(0o444)
    external = {str(bound(value)):value['sha256'] for value in report.values()
        if type(value) is dict and {'path','sha256'} <= value.keys()}
    external[str(Path(path).resolve())] = expected; external.update(views)
    metadata = dict(schema='pinwheel.streaming-tt-final-input.v1',qualified=False,physical_acceptance_claim=False,
        workspace_root=str(P.ROOT),producer_commit=subprocess.check_output(['git','rev-parse','HEAD'],cwd=P.ROOT,text=True).strip(),
        producer_sha256=sources,producer_dependency_closure=closure,tag=tag,timeout_seconds=timeout_seconds,
        admission=str(Path(path).resolve()),admission_sha256=expected,source_commit=report['source_commit'],
        design=str(design),pdk=str(design/'pdk'),external_input_sha256=external,
        input_sha256={str(p.relative_to(inputs)):P.sha(p) for p in sorted(inputs.rglob('*')) if p.is_file()},
        authoritative_odb=state['odb'],carried_netlist=state.get('nl'),boundary=BOUNDARY)
    P.write(out/'inputs.json',metadata); verify(out/'inputs.json')
    return out/'inputs.json'


def verify(path):
    metadata = P.read(P.regular(path)); P.require(metadata.get('schema') == 'pinwheel.streaming-tt-final-input.v1',
        'Unknown final continuation input schema')
    out = Path(path).parent; P.verify_files(out/'inputs',metadata['input_sha256'])
    P.verify_files(P.ROOT,metadata['producer_sha256']); P.verify_files(out/'inputs/producer',metadata['producer_sha256'])
    P.require(dependency_closure(out/'inputs/producer',list(metadata['producer_sha256'])) == metadata['producer_dependency_closure'],
        'Frozen final producer import closure differs')
    for name,value in metadata['external_input_sha256'].items():
        P.require(P.sha(P.regular(name)) == value, 'Final continuation external input changed: '+name)
    admission(metadata['admission'],metadata['admission_sha256'])
    return metadata


def collect_states(output, inputs, pdk):
    roots = {'/work/run':Path(output),'/work/inputs':Path(inputs),'/work/pdk':Path(pdk)}
    def resolve(value):
        if type(value) is dict: return {key:resolve(child) for key,child in value.items()}
        if type(value) is list: return [resolve(child) for child in value]
        if type(value) is not str: return value
        for prefix,root in roots.items():
            if value.startswith(prefix+'/'):
                path = root/value[len(prefix)+1:]
                P.require(path.resolve().is_relative_to(root.resolve()), 'Final native view escapes its mount')
                if path.is_file():return dict(container=value,path=str(path),sha256=P.sha(path))
        return value
    return [dict(state=str(path),state_sha256=P.sha(path),step_directory=path.parent.name,
        metrics=P.read(path).get('metrics',{}),views=resolve({key:value for key,value in P.read(path).items() if key!='metrics'}),
        authoritative_physical_view='odb',carried_netlist_requires_ODB_reexport=True)
        for path in sorted(Path(output).rglob('state_out.json'))]


def run(path):
    path = P.regular(path).resolve(); metadata_sha256 = P.sha(path); metadata = verify(path); out = path.parent
    P.require(P.sha(path) == metadata_sha256, 'Final prepared receipt changed before use')
    P.require(out.resolve() == (P.BASE/metadata['tag']).resolve(), 'Wrong final continuation output')
    for name,value in metadata['producer_sha256'].items():
        content = subprocess.check_output(['git','show',metadata['producer_commit']+':'+name],cwd=P.ROOT,timeout=30)
        P.require(hashlib.sha256(content).hexdigest() == value,'Uncommitted final producer source')
    output = out/'flow'; output.mkdir(exist_ok=False)
    owner = str(uuid.uuid4()); lock = P.BASE/'streaming-tt-active.json'
    fd = os.open(lock,os.O_WRONLY|os.O_CREAT|os.O_EXCL,0o600)
    with os.fdopen(fd,'w') as stream:json.dump(dict(owner=owner,pid=os.getpid(),tag=metadata['tag']),stream)
    receipt_path = out/'report.json'
    report = dict(schema='pinwheel.streaming-tt-final-run.v1',qualified=False,physical_acceptance_claim=False,
        post_pnr_equivalence_proved=False,status='preflight',tag=metadata['tag'],source_commit=metadata['source_commit'],
        producer_commit=metadata['producer_commit'],prepared_input_sha256=metadata_sha256,
        started_utc=datetime.now(timezone.utc).isoformat(),
        executed_staged_producer=str(Path(__file__).resolve()),ownership_label=owner,
        cpus=4,memory='6g',memory_swap='6g',network='none',input_mount_readonly=True,pdk_mount_readonly=True,
        from_step=TAIL[0],stop_step=TAIL[-1],timeout_seconds=metadata['timeout_seconds'],boundary=BOUNDARY)
    start = time.monotonic(); process = None; coarse = common_runner()
    old_handler = signal.getsignal(signal.SIGTERM)
    def interrupt(signum,frame):raise KeyboardInterrupt('signal '+str(signum))
    signal.signal(signal.SIGTERM,interrupt)
    P.write(receipt_path,report)
    with (out/'native.log').open('w') as log:
        try:
            runtime = P.inspect_runtime(P.read(P.ROOT/'tools/physical-toolchain.json'));report['runtime']=runtime
            code = 'import json; from librelane_plugin_streaming_tt import StreamingTTCertified; print(json.dumps([x.id for x in StreamingTTCertified.Steps]))'
            order = ['docker','run','--rm','--pull','never','--network','none','--cpus','1','--memory','512m',
                '--memory-swap','512m',
                '--label','org.pinwheel.streaming_tt_owner='+owner,'--env','PYTHONDONTWRITEBYTECODE=1',
                '--env','PYTHONPATH=/probe','--mount','type=bind,source='+str(out/'inputs')+',target=/probe,readonly',
                runtime['image_id'],'python3','-B','-c',code]
            report['ordering_preflight']=dict(argv=order,status='intent',timeout_seconds=30)
            P.write(receipt_path,report)
            inspected = subprocess.run(order,capture_output=True,text=True,timeout=30)
            (out/'ordering.stdout').write_text(inspected.stdout);(out/'ordering.stderr').write_text(inspected.stderr)
            report['ordering_preflight'].update(status='completed',exit_code=inspected.returncode,
                stdout_sha256=P.sha(out/'ordering.stdout'),stderr_sha256=P.sha(out/'ordering.stderr'))
            P.require(inspected.returncode == 0,'Native continuation ordering preflight failed')
            report['native_step_ids']=validate_order(json.loads(inspected.stdout))
            command = ['docker','run','--rm','--pull','never','--name','pinwheel-'+metadata['tag'],
                '--label','org.pinwheel.streaming_tt_owner='+owner,'--network','none','--cpus','4','--memory','6g',
                '--memory-swap','6g',
                '--env','PYTHONPATH=/work/inputs','--env','PYTHONDONTWRITEBYTECODE=1',
                '--mount','type=bind,source='+str(out/'inputs')+',target=/work/inputs,readonly',
                '--mount','type=bind,source='+metadata['pdk']+',target=/work/pdk,readonly',
                '--mount','type=bind,source='+str(output)+',target=/work/run','--workdir','/work/inputs',
                runtime['image_id'],'python3','-B','-m','librelane','--manual-pdk','--pdk-root','/work/pdk',
                '--pdk','ihp-sg13cmos5l','--jobs','4','--run-tag',metadata['tag'],'--force-run-dir','/work/run',
                '--with-initial-state','/work/inputs/seed.json','--from',TAIL[0],'--to',TAIL[-1],'/work/inputs/core.json']
            report.update(status='running',command=command);P.write(receipt_path,report)
            process = subprocess.Popen(command,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
            code = process.wait(timeout=metadata['timeout_seconds'])
            report.update(exit_code=code,status='flow_completed' if code==0 else 'failed')
        except subprocess.TimeoutExpired:
            report.update(exit_code=124,status='timed_out',stop_reason='wall_time_limit')
        except KeyboardInterrupt as error:
            report.update(exit_code=130,status='interrupted',error=str(error))
        except (OSError,ValueError,subprocess.CalledProcessError) as error:
            report.update(exit_code=127,status='blocked',error=type(error).__name__+': '+str(error))
        finally:
            P.write(receipt_path,report);report['container_termination']=coarse.cleanup(owner,log)
            if process is not None and process.poll() is None:
                try:process.wait(timeout=5)
                except subprocess.TimeoutExpired:os.killpg(process.pid,signal.SIGTERM)
            try:
                P.require(P.sha(path) == metadata_sha256, 'Final prepared receipt changed during native execution')
                verify(path);report['inputs_unchanged_after_run']=True
            except (OSError,ValueError) as error:
                report.update(inputs_unchanged_after_run=False,status='invalidated',closeout_error=str(error))
            report['elapsed_seconds']=round(time.monotonic()-start,3)
            try:report['states']=collect_states(output,out/'inputs',metadata['pdk'])
            except (OSError,ValueError) as error:
                report.update(status='invalidated',state_closeout_error=str(error))
            if report['container_termination'].get('status') != 'absent':
                report['status'] = 'cleanup_unconfirmed'
            report['artifact_sha256']={str(p.relative_to(out)):P.sha(p) for p in sorted(out.rglob('*'))
                if p.is_file() and p!=receipt_path}
            P.write(receipt_path,report)
            if report['container_termination']['status']=='absent' and P.read(lock)['owner']==owner:lock.unlink()
            signal.signal(signal.SIGTERM,old_handler)
    print(receipt_path)
    return report.get('exit_code',127) or (3 if report['status']!='flow_completed' else 0)
