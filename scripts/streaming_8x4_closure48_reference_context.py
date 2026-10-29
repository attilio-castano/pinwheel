"""Exact completion bodies in new globals; campaign48 HOST custody only."""
import hashlib
import inspect
import json
from pathlib import Path
import streaming_8x4_closure48_policy as CLOCK

OLD_PREFIX='pinwheel.streaming-8x4-rc-reference-completion-'
PREFIX='pinwheel.streaming-8x4-closure48-reference-completion-'
OLD_PLAN='7bd27dc9a7f6e9b7f8e44189886f271a2ae8e20c5321ed662c49d26deb70abd9'
PINS={
 'streaming_8x4_rc_reference_completion.py':'299860062bb94ed3b3a12049e85108b6896c5fa3a441a41efd7eed81eba5ab65',
 'streaming_8x4_rc_reference_completion_readback.py':'a993910525b994378739c5b7f3cdf77271b4136b6eb9d0026d20a4613b4f52f0',
 'streaming_8x4_rc_reference_expanded_kernel.py':'ee35496c64f33577e148b8b7d59d2d28f5f68a3bec9b574578260aee45bea265'}


def body(module,name):
    path=Path(module.__file__)
    CLOCK.require(PINS.get(path.name)==CLOCK.sha(path),'Frozen completion body source changed')
    return inspect.getsource(getattr(module,name))


def install(module,names,namespace):
    """Only schema strings change; functions resolve globals of the NEW owner."""
    for name in names:
        source=body(module,name).replace(OLD_PREFIX,PREFIX)
        exec(compile(source,namespace['__file__'],'exec'),namespace)


def derivation(base,reader):
    root=Path(base.__file__).parent
    CLOCK.require(all(CLOCK.sha(root/n)==pin for n,pin in PINS.items()),'Original completion/kernel source differs')
    return dict(original_sources=PINS,original_completion_plan_sha256=OLD_PLAN,
        native_body_sha256={n:hashlib.sha256(body(base,n).encode()).hexdigest()
            for n in ('dispatch_argv','one','dispatch','run')},
        reader_body_sha256={n:hashlib.sha256(body(reader,n).encode()).hexdigest()
            for n in ('numeric_leaf','dispatch','analysis','work_state','readback')},
        native_changes=['typed schema prefix only; NEW policy/plan/output globals'],
        direct_original_kernel=True,all_equations_and_numeric_gates_unchanged=True,
        old_module_globals_unchanged=True,complete32_requires_original27_and_all_fresh5=True,
        scope='nominal TYP finite2D empirical component; never G2/corner/full-model qualification')


def bound(path):
    path=Path(path)
    CLOCK.require(path.is_file() and not path.is_symlink(),'Regular nonaliased custody input required')
    return dict(path=str(path.resolve()),sha256=CLOCK.sha(path))


def resource_join(worker,path,proposal_path,proposal,inputs,plan,report,root_go):
    root=worker.ROOT;row=json.loads(Path(path).read_text());b=row['campaign_boundary']
    code,status=row['exit_code'],row['status']
    terminal=(status=='stopped' and type(code) is int and code==124) or (
        type(code) is int and code==(0 if report['passed'] else 2)
        and status==('completed' if report['passed'] else 'failed'))
    CLOCK.require(terminal and row['schema']=='pinwheel.streaming-tt-resource-job.v1'
        and row['argv']==proposal['argv'] and row['timeout_seconds']==1110
        and row['cleanup_confirmed'] is True and row['inputs_unchanged'] is True
        and row['containers_remaining']==row['owned_processes_remaining']==row['cleanup_errors']==[],
        'Completion48 exact command/terminal/budget/cleanup differs')
    wrapper=root/'scripts/streaming_8x4_closure48_resources.py'
    policy=root/'scripts/streaming_8x4_closure48_policy.py';guard=root/'scripts/streaming_tt_resources.py'
    CLOCK.require(b['schema']=='pinwheel.streaming-8x4-closure48-resource-boundary.v1'
        and b['campaign_id']==CLOCK.CAMPAIGN and b['campaign_directory']==str(root/'build/campaigns'/CLOCK.CAMPAIGN)
        and b['campaign_root']==str(root) and b['schedule']==CLOCK.SCHEDULE
        and b['shared_lease']==CLOCK.shared_lease_paths(root) and b['campaign_kind']=='rc_reference_probe'
        and b['wrapper_path']==str(wrapper) and b['wrapper_sha256']==CLOCK.sha(wrapper)
        and b['policy_path']==str(policy) and b['policy_sha256']==CLOCK.sha(policy)
        and b['inherited_supervisor_path']==str(guard)
        and b['inherited_supervisor_sha256']==row['supervisor_sha256']==CLOCK.sha(guard)
        and b['historical_producer_sha256']==CLOCK.historical_sources(root)
        and b['resource_limits']==CLOCK.resource_limits('reference-probe')
        and all(b[n] is None for n in ('frozen_parent','reference_admission_evidence','model_qualification_evidence','timing_failure_evidence'))
        and all(b[n] is False for n in ('reference_admission_verified','engineering_evidence_verified','acceptance_claim'))
        and row['acceptance_claim'] is False,'Completion48 campaign/source/scope differs')
    window=b['initial_window']
    CLOCK.require(window['kind']=='rc_reference_probe' and window['requested_timeout_seconds']==1110
        and window['timeout_seconds']==1110 and window['cleanup_reserve_seconds']==20
        and CLOCK.timestamp(window['execution_cutoff'])==CLOCK.timestamp(CLOCK.SCHEDULE['reference_decision'])
        and window['acceptance_claim'] is False,'Completion48 reference-decision clock differs')
    CLOCK.require(not Path(b['shared_lease']['cleanup_sentinel']).exists(),'Shared cleanup sentinel remains present')
    seals=row['input_sha256'];required={str(Path(proposal_path).resolve()):CLOCK.sha(proposal_path),
        proposal['plan_path']:proposal['plan_sha256'],str(Path(root_go).resolve()):CLOCK.sha(root_go),
        **{str(root/'scripts'/n):pin for n,pin in plan['producer_sha256'].items()}}
    for name,item in plan['files'].items():
        CLOCK.require(item['kind']=='file','Completion inputs must not contain aliases')
        required[str((inputs/name).resolve())]=item['sha256']
    CLOCK.require(all(seals.get(n)==pin and CLOCK.sha(n)==pin for n,pin in required.items()),
        'Completion48 source/input/proposal/RootGO current seals differ')
    go=json.loads(Path(root_go).read_text())
    CLOCK.require(go['schema']=='pinwheel.extraction48-Root-GO.v1'
        and go['decision']=='GO for this exact fixed job only' and go['acceptance_claim'] is False
        and go['numerical_tuning_forbidden'] is True,'Completion48 RootGO scope differs')
    launch_pin,proposal_pin=go['launch'],go['proposal']
    CLOCK.require(bound(launch_pin['path'])==launch_pin and bound(proposal_pin['path'])==proposal_pin,'Root launch/proposal changed')
    launch=json.loads(Path(launch_pin['path']).read_text());admitted=json.loads(Path(proposal_pin['path']).read_text())
    CLOCK.require(launch['schema']=='pinwheel.extraction48-root-job-launch.v1'
        and launch['proposal']==proposal_pin and launch['acceptance_claim'] is False
        and admitted['schema']=='pinwheel.extraction48-root-job-proposal.v2'
        and admitted['worker_argv']==proposal['argv'] and admitted['kind']=='reference-probe'
        and admitted['timeout_seconds']==1110 and admitted['container_name']==proposal['container_name']
        and all(admitted[n] is None for n in ('parent','reference_admission','model_qualification','timing_failure'))
        and admitted['acceptance_claim'] is False
        and b['actual_wrapper_argv'][1:]==launch['resource_supervisor_argv'][1:]
        and seals.get(proposal_pin['path'])==proposal_pin['sha256']
        and all(bound(item['path'])==item and seals.get(item['path'])==item['sha256'] for item in admitted['inputs']),
        'Completion48 actual Root command/input/interpreter-argument joins differ')
    CLOCK.require(CLOCK.timestamp(row['started_utc'])>=CLOCK.timestamp(CLOCK.SCHEDULE['start'])
        and CLOCK.timestamp(row['finished_utc'])<=CLOCK.timestamp(CLOCK.SCHEDULE['reference_decision']),
        'Completion48 actual execution crosses reference-decision boundary')
    return dict(resource_report=bound(path),root_go=bound(root_go),root_launch=launch_pin,
        root_proposal=proposal_pin,cleanup_confirmed=True,inputs_unchanged=True,
        owned_processes_remaining=[],containers_remaining=[],exit_code=code,status=status,
        observed_wrapper_interpreter=b['actual_wrapper_argv'][0],declared_wrapper_interpreter=launch['resource_supervisor_argv'][0],
        interpreter_payload_identity_claim=False)
