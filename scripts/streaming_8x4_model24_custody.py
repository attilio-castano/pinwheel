"""Shared exact closure24 experiment receipt join; no execution or promotion."""
import json
from pathlib import Path
import streaming_8x4_closure24_policy as P

ROOT=Path(__file__).resolve().parents[1]


def regular(path):
    P.require(path.is_file() and not path.is_symlink(),'Missing/aliased model24 custody evidence');return path


def resource_join(path,proposal_path,proposal,plan,report,root_go):
    r=json.loads(regular(path).read_text());b=r['campaign_boundary']
    wrapper=ROOT/'scripts/streaming_8x4_closure24_resources.py';policy=ROOT/'scripts/streaming_8x4_closure24_policy.py';guard=ROOT/'scripts/streaming_tt_resources.py'
    P.require(r['schema']=='pinwheel.streaming-tt-resource-job.v1' and r['argv']==proposal['argv']
        and r['timeout_seconds']==proposal['timeout_seconds']
        and type(r['exit_code']) is int and r['exit_code']==(0 if report['passed'] else 2)
        and r['status']==('completed' if report['passed'] else 'failed')
        and r['cleanup_confirmed'] is True and r['inputs_unchanged'] is True
        and r['containers_remaining']==r['owned_processes_remaining']==r['cleanup_errors']==[],
        'Model24 exact resource/command/terminal/cleanup differs')
    P.require(b['schema']=='pinwheel.streaming-8x4-closure24-resource-boundary.v1'
        and b['campaign_id']==P.CAMPAIGN and b['campaign_directory']==str(ROOT/'build/campaigns'/P.CAMPAIGN)
        and b['schedule']==P.SCHEDULE and b['campaign_root']==str(ROOT) and b['shared_lease']==P.shared_lease_paths(ROOT)
        and b['campaign_kind']=='rc_experiment' and b['wrapper_path']==str(wrapper) and b['wrapper_sha256']==P.sha(wrapper)
        and b['policy_path']==str(policy) and b['policy_sha256']==P.sha(policy)
        and b['inherited_supervisor_path']==str(guard) and b['inherited_supervisor_sha256']==r['supervisor_sha256']==P.sha(guard)
        and b['historical_producer_sha256']==P.historical_sources(ROOT)
        and b['acceptance_claim'] is False and b['engineering_evidence_verified'] is False,
        'Model24 exact campaign/cutoff/shared-lease/wrapper/source differs')
    seals=r['input_sha256'];required={str(proposal_path.resolve()):P.sha(proposal_path),
        proposal['plan_path']:proposal['plan_sha256'],str(root_go.resolve()):P.sha(regular(root_go)),
        **{str(ROOT/'scripts'/n):h for n,h in plan['producer_sha256'].items()}}
    P.require(all(seals.get(n)==h for n,h in required.items()),'Model24 proposal/plan/GO/source input seals differ')
    go=json.loads(root_go.read_text())
    P.require(go['proposal_sha256']==P.sha(proposal_path) and go['model_qualified'] is False,
        'Model24 exact experiment Root GO identity/scope differs')
    return dict(resource_report=dict(path=str(path.resolve()),sha256=P.sha(path)),root_go_sha256=P.sha(root_go),
        campaign_boundary=b,cleanup_confirmed=True,inputs_unchanged=True,containers_remaining=[],owned_processes_remaining=[])
