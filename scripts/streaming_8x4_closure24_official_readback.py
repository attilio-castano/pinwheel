"""HOST-only strict full9/3call official6g/resource-context reopener."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import streaming_8x4_closure24_official_budget as B
import streaming_8x4_closure24_policy as P


def resource_join(path,proposal_path,proposal,plan,root_go,report):
    resource=B.ORIGINAL.read(B.ORIGINAL.regular(path));boundary=resource['campaign_boundary'];root=B.ROOT
    wrapper=root/'scripts/streaming_8x4_closure24_resources.py';guard=root/'scripts/streaming_tt_resources.py';policy=root/'scripts/streaming_8x4_closure24_policy.py'
    B.need(resource['schema']=='pinwheel.streaming-tt-resource-job.v1' and resource['argv']==proposal['argv'] and resource['kind']=='cad-validation'
        and resource['timeout_seconds']==3660 and resource['rss_mib']==2048 and resource['cleanup_confirmed'] is True and resource['inputs_unchanged'] is True
        and resource['validation_parent']==plan['views_report']
        and resource['containers_remaining']==resource['owned_processes_remaining']==resource['cleanup_errors']==[], 'Official resource command/clock/cleanup differs')
    B.need(boundary['schema']=='pinwheel.streaming-8x4-closure24-resource-boundary.v1' and boundary['campaign_id']==P.CAMPAIGN and boundary['schedule']==P.SCHEDULE
        and boundary['campaign_root']==str(root) and boundary['campaign_kind']=='fixed_cad' and boundary['shared_lease']==P.shared_lease_paths(root)
        and boundary['campaign_directory']==str(root/'build/campaigns'/P.CAMPAIGN) and boundary['frozen_parent']==plan['views_report']
        and boundary['wrapper_path']==str(wrapper) and boundary['wrapper_sha256']==B.sha(wrapper)
        and boundary['policy_path']==str(policy) and boundary['policy_sha256']==B.sha(policy)
        and boundary['inherited_supervisor_path']==str(guard) and boundary['inherited_supervisor_sha256']==resource['supervisor_sha256']==B.sha(guard)
        and boundary['historical_producer_sha256']==P.historical_sources(root) and boundary['acceptance_claim'] is False and boundary['engineering_evidence_verified'] is False,
        'Official fixed-parent/shared-lease/wrapper context differs')
    required={proposal['plan']['path']:proposal['plan']['sha256'],str(proposal_path.resolve()):B.sha(proposal_path),str(root_go.resolve()):B.sha(root_go),
        plan['views_report']['path']:plan['views_report']['sha256'],plan['prior_report']['path']:plan['prior_report']['sha256'],plan['prior_guard']['path']:plan['prior_guard']['sha256'],
        str(wrapper):B.sha(wrapper),str(policy):B.sha(policy),**P.historical_sources(root),
        **{str(root/name):pin for name,pin in plan['producer_sha256'].items()}}
    B.need(all(resource['input_sha256'].get(name)==pin for name,pin in required.items()),'Official plan/GO/views/failure/source resource seals differ')
    go=B.ORIGINAL.read(B.ORIGINAL.regular(root_go));B.need(go['proposal_sha256']==B.sha(proposal_path) and go['physical_acceptance'] is False,'Official exact RootGO identity/scope differs')
    if report['passed']:B.need(resource['status']=='completed' and resource['exit_code']==0,'Passing full official result has failed/stopped supervisor')
    else:B.need(resource['status'] in ('failed','stopped') and resource['exit_code'] in (2,124),'Incomplete/failed official result has inconsistent supervisor')
    return dict(resource=B.bound(path),Root_GO=B.bound(root_go),actual_status=resource['status'],exit_code=resource['exit_code'],stop_reason=resource.get('stop_reason'),cleanup_confirmed=True)


def readback(plan_path,resource_path,proposal_path,root_go):
    plan=B.verify(plan_path);proposal=B.ORIGINAL.read(B.ORIGINAL.regular(proposal_path));B.need(proposal==B.proposal(plan_path),'Official resource proposal differs')
    output=Path(plan['output']);report=B.ORIGINAL.read(B.ORIGINAL.regular(output/'report.json'));config=B.ORIGINAL.read(output/'native-config.json')
    B.need(report['schema']=='pinwheel.closure24-official-budget-precheck-run.v1' and report['resource_policy']==B.policy() and report['qualified'] is False
        and report['physical_acceptance'] is False and report['physical_candidate']==plan['physical_candidate'] and report['target']==plan['target']
        and report['views_report']==plan['views_report'] and report['resource_replay_plan']==B.bound(plan_path)
        and report['prior_memory_stop']==dict(report=plan['prior_report'],resource=plan['prior_guard']) and report['inputs_pdk_runtime_unchanged'] is True
        and report['cleanup']['status']=='absent' and report['selected_checks']==list(B.BASE.Q.OFFICIAL_CHECKS), 'Official exact final-target/resource/full-check context differs')
    B.need(config['schema']=='pinwheel.closure24-official-budget-native-config.v1' and config['resource_policy']==B.policy()
        and config['out']==str(output) and config['container_name']==B.ORIGINAL.container_name(output) and config['image_id']==report['runtime']['image_id'], 'Official explicit6g Native configuration differs')
    B.need(report['drc_scope']['deck']['sha256']==B.DECK and report['drc_scope']['disabled_rule_switches']==[], 'Official main deck/switch scope changed')
    old,_,views,prepared=B.previous(Path(plan['prior_report']['path']),Path(plan['prior_guard']['path']))
    B.need(report['runtime']==old['runtime'] and report['python']==old['python'] and report['official_support_commit']==old['official_support_commit']
        and report['official_omissions']==old['official_omissions'] and config['pdk']==prepared['pdk_root'], 'Official runtime/support/omission/PDK context differs')
    suffix=[str(Path(plan['python']).absolute()),'-B','precheck.py','--gds',str(output/'design'/(B.BASE.Q.TOP+'.gds')),'--tech','ihp-sg13cmos5l']
    B.need(report['argv'][0]=='env' and report['argv'][-len(suffix):]==suffix,'Official actual host caller flags differ')
    parent=Path(plan['views_report']['path']).parent
    for source,extension in ((parent/'design.gds','gds'),(parent/'official-format.lef','lef'),(parent/'signoff-views/implemented.power.v','v')):
        B.need(B.sha(source)==B.sha(output/'design'/(B.BASE.Q.TOP+'.'+extension)),'Official replay is not the exact same-target copied design')
    B.ORIGINAL.unchanged(report['input_sha256']);B.ORIGINAL.unchanged_aliases(report['runtime_aliases'])
    B.need(report['producer_sha256']==plan['producer_sha256'] and report['producer_dependency_closure']==plan['producer_dependency_closure'],'Official complete staged producer closure differs')
    for name,pin in report['producer_sha256'].items():
        B.need(B.sha(output/'inputs/producer'/name)==pin and hashlib.sha256(subprocess.check_output(['git','show',report['source_commit']+':'+name],cwd=B.ROOT)).hexdigest()==pin,'Official staged producer/commit differs')
    complete=False;failure=None;result=None;native=None
    try:
        result=B.ORIGINAL.precheck_result(output/'tt/precheck/reports/results.xml',list(B.BASE.Q.OFFICIAL_CHECKS),report['exit_code'])
        native=B.native_journal(output/'native-klayout.jsonl',out=output,pdk=Path(config['pdk']),owner=config['owner'],image_id=config['image_id'],gds=output/'design'/ (B.BASE.Q.TOP+'.gds'))
        B.need(report.get('executed') is True and report.get('result')==result and report.get('native')==native,'Official complete actual full9/3call verdict differs');complete=True
    except (ValueError,OSError,KeyError) as error:failure=type(error).__name__+': '+str(error)
    passed=complete and result['passed'] and native['passed'];B.need(report['passed'] is passed,'Official partial/failing checks cannot pass')
    joined=resource_join(resource_path,proposal_path,proposal,plan,root_go,report)
    return dict(schema='pinwheel.closure24-official-budget-independent-readback.v1',plan=B.bound(plan_path),report=B.bound(output/'report.json'),
        prior_memory_stop=dict(report=plan['prior_report'],resource=plan['prior_guard']),resource_policy=B.policy(),same_final_views=plan['views_report'],physical_candidate=plan['physical_candidate'],
        all_nine_checks_and_three_Native_calls_completed=complete,official_precheck_passed=passed,result=result,native=native,error=failure,
        native_journal=B.bound(output/'native-klayout.jsonl'),resource_cleanup_join=joined,old_memory_stop_remains_incomplete=True,
        no_Native_by_reader=True,qualified_timing=False,model_qualified=False,physical_acceptance=False)


def main():
    q=argparse.ArgumentParser(description=__doc__)
    for name in ('plan','resource-report','command-proposal','root-go','output'):q.add_argument('--'+name,type=Path,required=True)
    a=q.parse_args();B.need(not a.output.exists(),'Preserve earlier official independent readback')
    row=readback(a.plan,a.resource_report,a.command_proposal,a.root_go);B.ORIGINAL.write(a.output,row)
    print(json.dumps(dict(completed=row['all_nine_checks_and_three_Native_calls_completed'],passed=row['official_precheck_passed'])));return 0 if row['official_precheck_passed'] else 2

if __name__=='__main__':raise SystemExit(main())
