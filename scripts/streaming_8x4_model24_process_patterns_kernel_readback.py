"""New HOST-only kernel-key reopener; immutable old reader failure preserved."""
import argparse
import json
import math
from pathlib import Path
import sys
sys.path.insert(0,str(Path(__file__).resolve().parent))
import streaming_8x4_model24_process_patterns as W
import streaming_8x4_model24_custody as C
import streaming_8x4_model24_process_patterns_readback as OLD


def work(row):
    s=row['actual_work_seconds'];W.P.need(type(s) in (int,float) and math.isfinite(s) and s>=0 and row['work_budget_passed'] is (s<=90),'Owned-ITF observed work clock differs');return s<=90


def cgroup_contract(cg):
    W.P.need(type(cg) is dict and set(cg)=={'cpu.max','memory.max','memory.swap.max','pids.max'},'Exact actual producer dotted kernel-key schema required')
    cpu=cg['cpu.max'].split();W.P.need(len(cpu)==2 and all(v.isdigit() for v in cpu) and 0<int(cpu[0])<=int(cpu[1])
        and cg['memory.max']=='2147483648' and cg['memory.swap.max']=='0' and cg['pids.max']=='128','Owned-ITF actual cgroup bounds differ')
    return True


def preserve_old_failure(inputs,digest,directory,resource,proposal_path,root_go):
    failure=None
    try:OLD.readback(inputs,digest,directory,resource,proposal_path,root_go)
    except KeyError as e:
        W.P.need(e.args==('cpu_max',),'Different old-reader failure cannot be relabeled');failure=dict(type='KeyError',args=list(e.args))
    W.P.need(failure is not None,'Original frozen reader schema failure must remain reproducible')
    return failure


def readback(inputs,digest,directory,resource,proposal_path,root_go):
    plan=W.verify(inputs,digest);proposal=json.loads(C.regular(proposal_path).read_text());W.P.need(directory.name==W.OUTPUT and proposal==W.proposal(inputs,digest,directory.parent,False),'Exact owned-ITF command/output differs')
    row=json.loads(C.regular(directory/'report.json').read_text());W.P.need(row['schema']=='pinwheel.model24-owned-itf-pattern-execution.v1' and row['plan_sha256']==digest and row['policy']==W.policy()
        and row['argv'][1:]==['-no_init','-exit','run.tcl'] and Path(row['argv'][0]).name=='openroad' and row['openroad_sha256']==W.OPENROAD_SHA
        and row['inputs_sources_unchanged'] is True and row['openroad_unchanged'] is True and row['copied_tcl_unchanged'] is True
        and row['native_executed'] is True and row['numeric_solver_executed'] is False and row['model_qualified'] is False and row['qualified_timing'] is False
        and (directory/'run.tcl').read_bytes()==(inputs/'run.tcl').read_bytes() and W.E.sha(C.regular(directory/'native.log'))==row['native_log_sha256'],
        'Owned-ITF exact native/source/command/claim/raw binding differs')
    env=row['environment'];W.P.need(set(env)=={'PATH','HOME','LANG','LC_ALL','TZ','OMP_NUM_THREADS','OMP_DYNAMIC'} and env['PATH'] and all(env[k]==v for k,v in dict(HOME='/tmp',LANG='C',LC_ALL='C',TZ='UTC',OMP_NUM_THREADS='1',OMP_DYNAMIC='FALSE').items()),'Owned-ITF actual environment differs')
    cgroup_contract(row['cgroups'])
    old_failure=preserve_old_failure(inputs,digest,directory,resource,proposal_path,root_go)
    terminal=inventory=None;failure=None
    try:
        terminal=W.parse_terminal((directory/'native.log').read_text(),row['exit_code'],row['timed_out']);inventory=W.inventory(inputs,directory)
    except (ValueError,OSError) as e:failure=type(e).__name__+': '+str(e)
    feasible=W.S.N.resource_observation(row);passed=failure is None and feasible and work(row)
    W.P.need(row['terminal']==terminal and row['inventory']==inventory and row['resource_feasible'] is feasible and row['passed'] is passed
        and (failure is None or row['error']==failure),'Owned-ITF independent raw/material/case/resource/failure differs')
    _,parent,h=W.S.parent_pattern(inputs/'pattern-launcher.json');W.P.need(h==plan['pattern_authority_sha256'] and parent==json.loads((inputs/'pattern-authority.json').read_text()),'Historical first native source/census changed')
    joined=C.resource_join(resource,proposal_path,proposal,plan,row,root_go)
    return dict(schema='pinwheel.model24-owned-itf-pattern-kernel-schema-readback.v1',plan_sha256=digest,execution_report_sha256=W.E.sha(directory/'report.json'),
        legacy_frozen_reader_failure=old_failure,legacy_reader_source_sha256=plan['producer_sha256']['streaming_8x4_model24_process_patterns_readback.py'],
        HOST_kernel_schema_reopener_source_sha256=W.E.sha(__file__),native_bytes_and_old_producers_unchanged=True,
        native_process_grammar_and_expected_cases_passed=passed,terminal=terminal,inventory=inventory,error=failure,actual_work_seconds=row['actual_work_seconds'],
        source_defined_process_policy=W.U.policy(),raw_owned_tree=W.E.tree(directory),resource_cleanup_join=joined,
        numeric_solver_executed=False,native_executed_by_readback=False,physical_model_accuracy='unmeasured',model_qualified=False,qualified_timing=False)


def main():
    q=argparse.ArgumentParser(description=__doc__)
    for n in ('inputs','directory','resource-report','command-proposal','root-go','output'):q.add_argument('--'+n,type=Path,required=True)
    q.add_argument('--plan-sha256',required=True);a=q.parse_args();r=readback(a.inputs,a.plan_sha256,a.directory,a.resource_report,a.command_proposal,a.root_go);W.write(a.output,r)
    print(json.dumps(dict(native_process_grammar_and_expected_cases_passed=r['native_process_grammar_and_expected_cases_passed'],model_qualified=False)))
    return 0 if r['native_process_grammar_and_expected_cases_passed'] else 2
if __name__=='__main__':raise SystemExit(main())
