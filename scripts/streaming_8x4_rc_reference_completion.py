"""Exact five-grid resource-clock completion; old failed packet stays failed.

Root alone admits numerical execution. A distinct HOST composite must reopen
all27 historical strict rows and all5 fresh rows before complete32 authority.
"""
import argparse
import ast
import copy
import json
import os
import signal
import subprocess
import time
from pathlib import Path
import shutil
import sys

sys.path.insert(0,str(Path(__file__).resolve().parent))
import streaming_8x4_rc_reference_expanded as X
import streaming_8x4_rc_reference_expanded_readback as R
P,E,W,H,F,M=X.P,X.E,X.W,X.H,X.F,X.M
ROOT,PYTHON=X.ROOT,X.PYTHON
PARENT='e4694822f0ce6dc22a0f9cbdb2dc167b30259d7ce1b6132fee3b4429650006ec'
FAILED='f7061991c8aea61b5de02867bd7f5bee1b2dd26cfc0184fed0e4ce94f5490ae2'
INDICES=list(range(27,32))
OUTPUT='rc-reference-completion-5-01'
CONTAINER='pinwheel-8x4-'+OUTPUT
NEW=('streaming_8x4_rc_reference_completion.py','streaming_8x4_rc_reference_completion_readback.py')
snapshot,validate_snapshot,deltas,resource_feasible=X.snapshot,X.validate_snapshot,X.deltas,X.resource_feasible
jobs,validate_row=X.jobs,X.validate_row


def policy():
    row=copy.deepcopy(X.policy());row.update(schema='pinwheel.streaming-8x4-rc-reference-completion-policy.v1',
        maximum_calls=5,seconds_per_leaf=180,work_seconds=1050,outer_seconds=1110,
        selected_global_indices=INDICES,
        scope='exact expanded-grid indices27to31 completion; resource-clock change only; composite32 requires independently reopened original27 and all5 fresh observations')
    return row


def sources():
    pending=list(NEW)+list(X.NEW)+list(X.O.NEW)+['streaming_8x4_acceptance_resources.py','streaming_8x4_acceptance.py','streaming_tt_resources.py'];done={}
    while pending:
        n=pending.pop()
        if n in done:continue
        p=Path(__file__).with_name(n);done[n]=E.sha(p)
        for node in ast.walk(ast.parse(p.read_text())):
            names=[x.name for x in node.names] if isinstance(node,ast.Import) else ([node.module] if isinstance(node,ast.ImportFrom) and node.module else [])
            pending += [v+'.py' for v in names if v.startswith('streaming_') and '.' not in v]
    return dict(sorted(done.items()))


def parent_failure(path):
    P.need(E.sha(path)==FAILED,'Exact failed expanded packet identity differs')
    row=json.loads(path.read_text());leaves=row['leaves']
    P.need(row['new_expanded_reference_plan']['sha256']==PARENT and row['expanded_reference_complete_passed'] is False
        and row['measurement_packet_completed'] is False and row['resource_feasible'] is False
        and row['work_budget_passed'] is True and len(leaves)==28
        and [r['index'] for r in leaves]==list(range(28))
        and all(r['numeric_passed'] is True and r['resource_feasible'] is True for r in leaves[:27])
        and leaves[27]['numeric_passed'] is False and leaves[27]['resource_feasible'] is False
        and leaves[27]['actual_dispatch']['timed_out'] is True and leaves[27]['leaf_sha256'] is None
        and row['resource_cleanup_join']['cleanup_confirmed'] is True
        and row['resource_cleanup_join']['inputs_unchanged'] is True,
        'Original27 strict observations/failed027/closed resource history differs')
    return row


def reopen_parent(path):
    stored=parent_failure(path)
    for item in (stored['new_expanded_reference_plan'],stored['execution_report'],stored['command_proposal'],stored['resource_cleanup_join']['resource_report']):
        P.need(E.sha(Path(item['path']))==item['sha256'],'Historical expanded dependency changed')
    actual=R.readback(Path(stored['new_expanded_reference_plan']['path']).parent,PARENT,
        Path(stored['execution_report']['path']).parent,
        Path(stored['resource_cleanup_join']['resource_report']['path']),Path(stored['command_proposal']['path']))
    P.need(actual==stored,'Historical expanded raw/resource readback differs')
    return actual


def prepare(parent,failed_authority,output):
    old=X.verify(parent,PARENT);closed=reopen_parent(failed_authority)
    P.need(not output.exists() and output.parent.is_dir(),'Fresh completion owner required')
    output.mkdir();shutil.copytree(parent,output/'parent-expanded');shutil.copyfile(failed_authority,output/'failed-expanded-authority.json')
    row=dict(schema='pinwheel.streaming-8x4-rc-reference-completion-plan.v1',qualified=False,model_qualified=False,
        qualified_timing=False,finite_BEM_passed=False,native_executed=False,root_go_required=True,
        parent_plan_sha256=PARENT,failed_parent_authority_sha256=FAILED,old_expanded_packet_remains_failed=True,
        policy=policy(),selected_indices=INDICES,selected_jobs=[dict(index=i,**jobs(old)[i]) for i in INDICES],
        cases=old['cases'],grid_inventory=old['grid_inventory'],protocol=old['protocol'],
        kernel_admission_derivation=old['kernel_admission_derivation'],storage_admission=old['storage_admission'],
        original_M1_FVM_control_authority=old['original_M1_FVM_control_authority'],
        historical_successful_dispatch_sha256=[r['dispatch_sha256'] for r in closed['leaves'][:27]],
        failed027_dispatch_sha256=closed['leaves'][27]['dispatch_sha256'],producer_sha256=sources(),files=W.input_files(output))
    W.write(output/'plan.json',row);verify(output,E.sha(output/'plan.json'));return row


def verify(inputs,digest):
    P.need(E.sha(inputs/'plan.json')==digest,'Completion plan hash differs');row=json.loads((inputs/'plan.json').read_text())
    old=X.verify(inputs/'parent-expanded',PARENT);closed=parent_failure(inputs/'failed-expanded-authority.json')
    expected=dict(schema='pinwheel.streaming-8x4-rc-reference-completion-plan.v1',qualified=False,model_qualified=False,
        qualified_timing=False,finite_BEM_passed=False,native_executed=False,root_go_required=True,
        parent_plan_sha256=PARENT,failed_parent_authority_sha256=FAILED,old_expanded_packet_remains_failed=True,
        policy=policy(),selected_indices=INDICES,selected_jobs=[dict(index=i,**jobs(old)[i]) for i in INDICES],
        cases=old['cases'],grid_inventory=old['grid_inventory'],protocol=old['protocol'],
        kernel_admission_derivation=old['kernel_admission_derivation'],storage_admission=old['storage_admission'],
        original_M1_FVM_control_authority=old['original_M1_FVM_control_authority'],
        historical_successful_dispatch_sha256=[r['dispatch_sha256'] for r in closed['leaves'][:27]],
        failed027_dispatch_sha256=closed['leaves'][27]['dispatch_sha256'],producer_sha256=sources(),files=W.input_files(inputs))
    P.need(row==expected,'Exact completion scope/indices/kernel/source/history differs');return row


def dispatch_argv(inputs,digest,index,output):
    return [PYTHON,'-I','-B','/rc-source/'+NEW[0],'one','--inputs',str(inputs),'--plan-sha256',digest,'--index',str(index),'--output',str(output)]


def proposal(inputs,digest,parent,require_fresh=True):
    plan=verify(inputs,digest);old=X.proposal(inputs/'parent-expanded',PARENT,parent,require_fresh=False);argv=list(old['argv'])
    P.need(not require_fresh or not(parent/OUTPUT).exists(),'Fresh completion output required')
    for before,after in [(X.CONTAINER,CONTAINER),
        ('type=bind,src='+str((inputs/'parent-expanded').resolve())+',dst=/rc-inputs,readonly','type=bind,src='+str(inputs.resolve())+',dst=/rc-inputs,readonly'),
        ('/rc-source/'+X.NEW[0],'/rc-source/'+NEW[0]),(PARENT,digest),('/rc-output-parent/'+X.OUTPUT,'/rc-output-parent/'+OUTPUT)]:
        P.need(argv.count(before)==1,'Exact completion argv adaptation differs');argv[argv.index(before)]=after
    return dict(schema='pinwheel.streaming-8x4-rc-reference-completion-command-proposal.v1',root_go_required=True,
        admitted=False,native_executed=False,qualified=False,model_qualified=False,qualified_timing=False,finite_BEM_passed=False,
        plan_path=str((inputs/'plan.json').resolve()),plan_sha256=digest,output_name=OUTPUT,container_name=CONTAINER,
        timeout_seconds=1110,policy=policy(),producer_sha256=plan['producer_sha256'],argv=argv)


def one(inputs, digest, index, output):
    plan = verify(inputs, digest); snapshot(); calls = jobs(plan)
    P.need(type(index) is int and index in INDICES and not output.exists() and output.parent.is_dir(), 'Undeclared FVM leaf/fresh output')
    job = calls[index]; case = next(c for c in plan['cases'] if c['name'] == job['case'])
    result = {'schema': 'pinwheel.streaming-8x4-rc-reference-completion-leaf.v1', 'plan_sha256': digest,
        'index': index, 'job': job, 'qualified': False, 'model_qualified': False, 'qualified_timing': False,
        'finite_BEM_passed': False, 'numeric_passed': False, 'kernel_row': None}
    try:
        result['kernel_row'] = F.solve([{'name': r['name'], 'bounds_um': list(map(float, r['bounds_um']))} for r in case['rectangles']],
            [list(map(float, slab)) for slab in case['epsilon_layers']], float(job['extent']), float(job['step']),
            tolerance=1e-9, maximum_iterations=6000, maximum_nodes=70000)
        validate_row(plan, job, result['kernel_row']); result['numeric_passed'] = True
    except (ValueError, KeyError, TypeError, ArithmeticError, MemoryError) as error:
        result['error'] = type(error).__name__ + ': ' + str(error)
    verify(inputs, digest); snapshot(); W.write(output, result); return result


def dispatch(inputs, digest, index, owner):
    owner.mkdir(); target = owner / 'leaf.json'; before = snapshot(); child = None; started = time.monotonic()
    row = {'schema': 'pinwheel.streaming-8x4-rc-reference-completion-dispatch.v1', 'index': index,
        'plan_sha256': digest, 'argv': dispatch_argv(inputs, digest, index, target), 'timeout_seconds': 180,
        'cgroup_before': before, 'maximum_polled_memory_current': before['memory_current'],
        'timed_out': False, 'memory_guard_triggered': False, 'process_tree_reaped': False, 'exit_code': None,
        'numeric_passed': False, 'resource_feasible': False, 'leaf_sha256': None, 'native_log_empty': False}
    try:
        with (owner / 'native.log').open('xb') as stream:
            child = subprocess.Popen(row['argv'], stdout=stream, stderr=subprocess.STDOUT, start_new_session=True)
            while child.poll() is None:
                current = snapshot()['memory_current']; row['maximum_polled_memory_current'] = max(current, row['maximum_polled_memory_current'])
                if current >= before['memory_max'] * 95 // 100:
                    row['memory_guard_triggered'] = True; break
                if time.monotonic() - started >= 180:
                    row['timed_out'] = True; break
                time.sleep(.25)
            if child.poll() is None: os.killpg(child.pid, signal.SIGKILL)
            row['exit_code'] = child.wait(timeout=2)
        try: os.killpg(child.pid, 0)
        except ProcessLookupError: row['process_tree_reaped'] = True
        else: os.killpg(child.pid, signal.SIGKILL); raise ValueError('FVM child process group remained live')
        if target.exists():
            leaf = json.loads(target.read_text()); row['leaf_sha256'] = E.sha(target)
            row['numeric_passed'] = leaf['numeric_passed'] is True and row['exit_code'] == 0
    except BaseException as error:
        row['error'] = type(error).__name__ + ': ' + str(error)
    finally:
        if child is not None and child.poll() is None:
            os.killpg(child.pid, signal.SIGKILL); child.wait(timeout=2)
        row['cgroup_after'] = snapshot(); row['counter_deltas'] = deltas(before, row['cgroup_after'])
        row['resource_feasible'] = resource_feasible(row) and row['leaf_sha256'] is not None
        row['log_sha256'] = E.sha(owner / 'native.log') if (owner / 'native.log').exists() else None
        row['native_log_empty'] = (owner / 'native.log').is_file() and (owner / 'native.log').stat().st_size == 0
        row['numeric_passed'] = row['numeric_passed'] and row['native_log_empty']
        row['wall_seconds'] = time.monotonic() - started; W.write(owner / 'dispatch.json', row)
    return row


def run(inputs, digest, output):
    started = time.monotonic(); plan = verify(inputs, digest); snapshot()
    P.need(not output.exists() and output.parent.is_dir(), 'Reference-only run output must be fresh'); output.mkdir()
    row = {'schema': 'pinwheel.streaming-8x4-rc-reference-completion-execution.v1', 'plan_sha256': digest,
        'policy': policy(), 'qualified': False, 'model_qualified': False, 'qualified_timing': False,
        'finite_BEM_passed': False, 'reference_stability_passed': False, 'measurement_packet_completed': False,
        'all_numeric_leaves_passed': False, 'resource_feasible': False, 'passed': False, 'jobs': []}
    try:
        for index in INDICES:
            job = jobs(plan)[index]
            P.need(time.monotonic() - started < 860, 'Reference-only lacks full next-leaf budget')
            dispatch_row = dispatch(inputs, digest, index, output / ('job-' + str(index).zfill(3)))
            row['jobs'].append(dict(job, index=index, dispatch_sha256=E.sha(output / ('job-' + str(index).zfill(3)) / 'dispatch.json'),
                numeric_passed=dispatch_row['numeric_passed'], resource_feasible=dispatch_row['resource_feasible']))
            verify(inputs, digest)
            P.need(dispatch_row['resource_feasible'], 'Reference-only resource/custody failure stops suffix')
    except BaseException as error: row['error'] = type(error).__name__ + ': ' + str(error)
    finally:
        verify(inputs, digest); row['inputs_sources_unchanged'] = True
        row['measurement_packet_completed'] = len(row['jobs']) == 5
        row['all_numeric_leaves_passed'] = row['measurement_packet_completed'] and all(j['numeric_passed'] for j in row['jobs'])
        row['actual_work_seconds'] = time.monotonic() - started
        row['wall_seconds'] = row['actual_work_seconds']
        row['work_budget_passed'] = row['actual_work_seconds'] <= policy()['work_seconds']
        row['resource_feasible'] = (row['measurement_packet_completed'] and row['work_budget_passed']
            and all(j['resource_feasible'] for j in row['jobs']))
        row['passed'] = row['all_numeric_leaves_passed'] and row['resource_feasible']
        W.write(output / 'report.json', row)
    return row


def main():
    p=argparse.ArgumentParser(description=__doc__);sub=p.add_subparsers(dest='action',required=True)
    q=sub.add_parser('prepare')
    for n in ('parent','failed-authority','output'):q.add_argument('--'+n,type=Path,required=True)
    for action in ('verify','proposal','one','run'):
        q=sub.add_parser(action);q.add_argument('--inputs',type=Path,required=True);q.add_argument('--plan-sha256',required=True)
        if action!='verify':q.add_argument('--output',type=Path,required=True)
        if action=='one':q.add_argument('--index',type=int,required=True)
    a=p.parse_args()
    if a.action=='prepare':prepare(a.parent,a.failed_authority,a.output);print(E.sha(a.output/'plan.json'));return 0
    if a.action=='verify':verify(a.inputs,a.plan_sha256);print('verified');return 0
    if a.action=='proposal':W.write(a.output,proposal(a.inputs,a.plan_sha256,a.output.parent/'rc-native-outputs'));return 0
    result=one(a.inputs,a.plan_sha256,a.index,a.output) if a.action=='one' else run(a.inputs,a.plan_sha256,a.output)
    return 0 if result['numeric_passed' if a.action=='one' else 'passed'] else 2


if __name__=='__main__':raise SystemExit(main())
