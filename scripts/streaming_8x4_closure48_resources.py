"""Thin 48h resource adapter; only Root launches and typed producers admit work."""
import argparse
from datetime import datetime,timezone
import importlib.util
import json
from pathlib import Path
import sys

import streaming_8x4_closure48_policy as P

SCHEDULE, KINDS, timestamp = P.SCHEDULE, P.KINDS, P.timestamp


def parser():
    result=argparse.ArgumentParser(description=__doc__)
    result.add_argument('--campaign-root',type=Path,required=True)
    result.add_argument('--kind',choices=tuple(KINDS),required=True)
    result.add_argument('--tag',required=True)
    result.add_argument('--timeout-seconds',type=int,required=True)
    result.add_argument('--rss-mib',type=int,default=4096)
    result.add_argument('--container-name')
    result.add_argument('--input',type=Path,action='append',default=[])
    result.add_argument('--validation-parent',type=Path)
    result.add_argument('--reference-admission',type=Path)
    result.add_argument('--model-qualification',type=Path)
    result.add_argument('--timing-failure',type=Path)
    result.add_argument('--deadline',help='Optional exact approved supervisor cutoff; cannot extend a slice')
    result.add_argument('argv',nargs=argparse.REMAINDER)
    return result


def load_guard(root):
    P.historical_sources(root)
    path=root/'scripts/streaming_tt_resources.py'
    spec=importlib.util.spec_from_file_location('streaming_closure48_inherited_resources',path)
    result=importlib.util.module_from_spec(spec);spec.loader.exec_module(result)
    return result


def frozen(path):
    P.require(path is not None and path.is_file() and not path.is_symlink(),'Evidence must be a regular frozen file')
    return dict(path=str(path.resolve()),sha256=P.sha(path))


def validate_container(info,limits):
    config=info['HostConfig']
    P.require(type(config['Memory']) is int and 0<config['Memory']<=limits['container_memory_bytes'],
        'Container exceeds closure48 kind memory cap')
    P.require(type(config['MemorySwap']) is int and config['MemorySwap']==config['Memory'],'Additional container swap forbidden')
    P.require(type(config['NanoCpus']) is int and 0<config['NanoCpus']<=limits['container_cpus']*10**9,
        'Container exceeds closure48 kind CPU cap')
    P.require(config['NetworkMode']=='none','Container must remain offline')


def run(args,*,guard=None,now=None):
    root=args.campaign_root.resolve(strict=True);leases=P.shared_lease_paths(root)
    historical=P.historical_sources(root)
    family,inherited_kind,_=KINDS[args.kind];limits=P.resource_limits(args.kind)
    P.require(args.kind not in P.UNAVAILABLE,
        'Timing/ECO blocked until separately reviewed actual G2 reopener: '+P.QUALIFICATION_ENDPOINT)
    P.require(args.model_qualification is None and args.timing_failure is None,
        'Only a future typed G2 admission adapter may consume model/timing evidence; file presence is insufficient')
    P.require(family not in P.NUMERICAL or args.container_name,
        'Numerical jobs require an exact observed bounded container name')
    P.require(type(args.rss_mib) is int and 128<=args.rss_mib<=limits['maximum_host_rss_mib'],'Host RSS exceeds reviewed kind cap')
    P.require((family in P.FIXED)==(args.validation_parent is not None),'Fixed jobs require an explicit frozen parent')
    parent=frozen(args.validation_parent) if args.validation_parent is not None else None
    P.require(args.reference_admission is None or family in {'rc_experiment','rc_validation'},
        'Reference admission is a separate model-producer input, not a reference-probe or design PASS')
    reference=frozen(args.reference_admission) if args.reference_admission is not None else None
    deadline=SCHEDULE['hard_deadline' if family=='host_closeout' else 'heavy_cutoff']
    P.require(args.deadline is None or timestamp(args.deadline)==timestamp(deadline),'Cannot override approved supervisor cutoff')
    window=P.job_window(args.kind,SCHEDULE,now or datetime.now(timezone.utc).isoformat(),args.timeout_seconds,
        frozen_parent_sha256=parent['sha256'] if parent else None)
    guard=guard or load_guard(root);guard.ROOT=root;guard.BASE=Path(leases['heavy_lock']).parent
    inherited_write,inherited_command=guard.write,guard.command
    wrapper=Path(__file__).resolve();policy=Path(P.__file__).resolve();guard_path=root/'scripts/streaming_tt_resources.py'
    metadata=dict(schema='pinwheel.streaming-8x4-closure48-resource-boundary.v1',campaign_id=P.CAMPAIGN,
        campaign_directory=str(root/'build/campaigns'/P.CAMPAIGN),schedule=SCHEDULE,campaign_root=str(root),
        shared_lease=leases,campaign_kind=family,root_go_required=True,root_go_is_external_authority=True,
        actual_wrapper_argv=list(getattr(sys,'orig_argv',sys.argv)),wrapper_path=str(wrapper),wrapper_sha256=P.sha(wrapper),
        policy_path=str(policy),policy_sha256=P.sha(policy),inherited_supervisor_path=str(guard_path),
        inherited_supervisor_sha256=P.sha(guard_path),historical_producer_sha256=historical,
        frozen_parent=parent,reference_admission_evidence=reference,reference_admission_verified=False,
        model_qualification_evidence=None,timing_failure_evidence=None,
        initial_window=window,resource_limits=limits,acceptance_claim=False,engineering_evidence_verified=False,
        model_generation_admission_owner='Root and typed producer: separately verify references/corners/envelope/workload; clock is not admission',
        qualified_timing_admission='blocked until separately reviewed actual G2 reopener',
        physical_variant_ledger_owner='Root and typed producer; maximum two new variants total, no clock-derived acceptance')
    expected_seals={**historical,str(wrapper):metadata['wrapper_sha256'],str(policy):metadata['policy_sha256']}
    for evidence in (parent,reference):
        if evidence is not None:expected_seals[evidence['path']]=evidence['sha256']

    def enriched_write(path,value):
        if value.get('schema')=='pinwheel.streaming-tt-resource-job.v1':
            P.require(all(value.get('input_sha256',{}).get(name)==pin for name,pin in expected_seals.items()),
                'Actual inherited input seals differ from admitted wrapper/evidence identities')
            value['campaign_boundary']=metadata
        inherited_write(path,value)

    def admission(kind,actual_deadline,current):
        P.require(kind==inherited_kind and actual_deadline==timestamp(deadline),'Inherited kind/deadline changed')
        P.require(all(P.sha(name)==pin for name,pin in expected_seals.items()),'Frozen admission evidence/source changed')
        fresh=P.job_window(args.kind,SCHEDULE,now or current.isoformat(),args.timeout_seconds,
            frozen_parent_sha256=parent['sha256'] if parent else None)
        return fresh['timeout_seconds']+fresh['cleanup_reserve_seconds']

    def checked_command(argv):
        result=inherited_command(argv)
        if argv[:2]==['docker','inspect']:
            records=json.loads(result);P.require(type(records) is list and bool(records),'Missing actual container config')
            for info in records:validate_container(info,limits)
        return result

    guard.write=enriched_write;guard.admission_window=admission;guard.command=checked_command
    forwarded=['resource','--tag',args.tag,'--kind',inherited_kind,'--timeout-seconds',str(args.timeout_seconds),
        '--rss-mib',str(args.rss_mib),'--deadline',deadline]
    if args.container_name:forwarded+=['--container-name',args.container_name]
    inputs=[*args.input,wrapper,policy,*map(Path,historical)]
    for evidence in (parent,reference):
        if evidence is not None:inputs.append(Path(evidence['path']))
    if inherited_kind=='cad-validation':forwarded+=['--validation-parent',parent['path']]
    for path in inputs:forwarded+=['--input',str(path)]
    worker=args.argv[1:] if args.argv[:1]==['--'] else args.argv
    P.require(worker,'Missing worker command');forwarded+=['--',*worker]
    original=sys.argv
    try:
        sys.argv=forwarded
        return guard.main()
    finally:sys.argv=original


def main():return run(parser().parse_args())


if __name__=='__main__':raise SystemExit(main())
