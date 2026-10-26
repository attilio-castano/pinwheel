"""Fresh E32/64 complete32 FVM authority; Root alone admits field execution.

Only physical domain and node admission change. Old failed reference authority
and every frozen producer remain intact; no finite-BEM/model/timing claim.
"""
import argparse
import ast
import copy
import hashlib
import json
import math
import os
from pathlib import Path
import shutil
import signal
import subprocess
import sys
import time

sys.path.insert(0,str(Path(__file__).resolve().parent))
import streaming_8x4_rc_reference_only as O
import streaming_8x4_rc_reference_expanded_kernel as F
P,E,M,W,H=O.P,O.E,O.M,O.W,O.H
ROOT=O.ROOT
BASELINE='bd24cf673c33be53a2a83a1d4c27d3c14ea989208cfb8689a09d861baec69e32'
PROPOSAL='d8187683ba62fd48ac61e0c1bf92ef2c72a38e52c7a82c122a3736dc02e8e884'
FAILED_PARENT='59911dcdb99b3b16b0153455cf70ed92377f5b9683867ba2260c306db2636e5b'
OUTPUT='rc-reference-expanded-32-01'
CONTAINER='pinwheel-8x4-'+OUTPUT
NEW=('streaming_8x4_rc_reference_expanded.py','streaming_8x4_rc_reference_expanded_kernel.py','streaming_8x4_rc_reference_expanded_readback.py')
PYTHON=O.PYTHON
snapshot,validate_snapshot,deltas,resource_feasible=O.snapshot,O.validate_snapshot,O.deltas,O.resource_feasible


def policy():
    row=O.policy();row.update(schema='pinwheel.streaming-8x4-rc-reference-expanded-policy.v1',
        domain_extents_um=['32','64'],maximum_nodes=70000,
        actual_terminal_work_seconds_required=True,
        scope='complete eight nominal TYP self/centered-adjacent cases; fresh E32/64 empirical FVM only, old failed reference unchanged; no finite-BEM/full-model/timing authority')
    return row


def sources():
    pending=list(NEW)+list(O.NEW)+['streaming_8x4_acceptance_resources.py','streaming_8x4_acceptance.py','streaming_tt_resources.py'];done={}
    while pending:
        name=pending.pop()
        if name in done:continue
        path=Path(__file__).with_name(name);done[name]=E.sha(path)
        for node in ast.walk(ast.parse(path.read_text())):
            names=[x.name for x in node.names] if isinstance(node,ast.Import) else ([node.module] if isinstance(node,ast.ImportFrom) and node.module else [])
            pending += [n+'.py' for n in names if n.startswith('streaming_') and '.' not in n]
    return dict(sorted(done.items()))


def function_body(path,name):
    text=path.read_text();nodes=[n for n in ast.parse(text).body if isinstance(n,ast.FunctionDef) and n.name==name]
    P.need(len(nodes)==1,'Exact kernel function membership differs');node=nodes[0]
    return '\n'.join(text.splitlines()[node.body[0].lineno-1:node.end_lineno])


def kernel_derivation():
    old=Path(O.F.__file__);new=Path(F.__file__);left,right=old.read_text(),new.read_text()
    P.need(E.sha(old)=='5a21e1a89b942e770557850319b48592ec04f5bfa420be81fd42fe8843138e03',
        'Exact original65k kernel source differs')
    P.need(right.count('extent in (32.0, 64.0)')==1 and right.count('maximum_nodes=70000')==1,
        'New expanded admission constants differ')
    normalized='\n'.join(right.splitlines()[2:])+'\n'
    normalized=normalized.replace('extent in (32.0, 64.0)','extent in (16.0, 32.0)').replace('maximum_nodes=70000','maximum_nodes=65000')
    P.need(normalized=='\n'.join(left.splitlines()[2:])+'\n','Expanded kernel changed bytes outside declared admission/header')
    oldbody=function_body(old,'solve');newbody=function_body(new,'solve')
    normalized_body=newbody.replace('extent in (32.0, 64.0)','extent in (16.0, 32.0)')
    P.need(normalized_body==oldbody and function_body(new,'_axis')==function_body(old,'_axis'),
        'Expanded solve/axis equation body differs after exact admission normalization')
    return dict(original_source_sha256=E.sha(old),expanded_source_sha256=E.sha(new),
        normalized_solve_body_sha256=hashlib.sha256(oldbody.encode()).hexdigest(),
        axis_body_sha256=hashlib.sha256(function_body(old,'_axis').encode()).hexdigest(),
        remaining_module_bytes_identical_after_two_admission_constants_and_header=True,
        solve_body_identical_after_domain_guard_normalization=True,axis_body_byte_identical=True,
        only_changes=['declared extent tuple(16.0,32.0)to(32.0,64.0)','default node admission65000to70000','provenance comment header'],
        no_frozen_module_monkeypatch=True)


def grid_inventory(cases):
    rows=[]
    for case in cases:
        for h in policy()['mesh_steps_um']:
            for e in policy()['domain_extents_um']:
                extent=float(e);xa,ya={-extent,extent},{0.,extent}
                for rect in case['rectangles']:
                    x0,x1,y0,y1=map(float,rect['bounds_um']);xa.update((x0,x1));ya.update((y0,y1))
                for slab in case['epsilon_layers']:
                    ya.update(y for y in map(float,slab[:2]) if 0<y<extent)
                xs,ys=F._axis(sorted(xa),float(h)),F._axis(sorted(ya),float(h))
                nodes=len(xs)*len(ys)
                P.need(set(xa)<=set(xs) and set(ya)<=set(ys) and nodes<=70000,'Expanded dry-grid anchors/node admission differs')
                rows.append(dict(case=case['name'],step_um=h,extent_um=e,nodes=nodes,nx=len(xs),ny=len(ys),
                    minimum_dx_um=min(b-a for a,b in zip(xs,xs[1:])),minimum_dy_um=min(b-a for a,b in zip(ys,ys[1:])),
                    exact_material_and_conductor_anchors_present=True,within_proposed70000_nodes=True))
    P.need(len(rows)==32 and max(r['nodes'] for r in rows)==68817 and sum(r['nodes'] for r in rows)==1045176,
        'Expanded full32 fixed dry-grid inventory differs')
    return rows


def storage_admission(parent):
    row=copy.deepcopy(parent['storage_admission']);nodes=70000;total=nodes*row['object_storage_budget_bytes_per_node']*row['allocator_and_transient_factor']
    total += row['interpreter_and_worker_reserve_bytes']+row['scratch_bytes']
    P.need(total==1549533184 and total<2147483648*95//100,'Expanded structural storage lacks95percent guard headroom')
    row.update(maximum_nodes=nodes,conservative_total_bytes=total,headroom_bytes=2147483648-total,
        headroom_below95percent_guard_bytes=2147483648*95//100-total,operator_source_sha256=E.sha(F.__file__))
    return row


def jobs(plan):
    return [dict(case=c['name'],step=h,extent=e) for c in plan['cases'] for h in policy()['mesh_steps_um'] for e in policy()['domain_extents_um']]


def protocol(parent):
    value=copy.deepcopy(parent['protocol']);value.update(reference_domain_extents_um=['32','64'],maximum_reference_nodes=70000)
    return value


def failed_parent(path):
    P.need(E.sha(path)==FAILED_PARENT,'Exact failed original32 closeout differs')
    row=json.loads(path.read_text())
    P.need(row['new_reference_only_plan']['sha256']==BASELINE
        and row['reference_only_complete_passed'] is False and row['measurement_packet_completed'] is True
        and row['all_numeric_leaves_passed'] is True and row['analysis']['passed'] is False
        and [c['case'] for c in row['analysis']['cases'] if not c['passed']]==[
            'TYP-TopMetal1-self','TYP-Metal3-Metal4-centered','TYP-Metal4-TopMetal1-centered'],
        'Original32 three empirical domain failures must remain failed')
    return dict(authority_sha256=FAILED_PARENT,reference_only_complete_passed=False,
        failed_cases=[c for c in row['analysis']['cases'] if not c['passed']],
        scope='immutable previously independently closed failure provenance; no numerical prefix reused')


def prepare(parent,approved_proposal,failed_parent_authority,output):
    old=O.verify(parent,BASELINE);P.need(E.sha(approved_proposal)==PROPOSAL and not output.exists() and output.parent.is_dir(),
        'Exact corrected scope/fresh expanded owner required')
    failed_parent(failed_parent_authority)
    output.mkdir();shutil.copytree(parent,output/'parent-reference-only');shutil.copyfile(approved_proposal,output/'approved-proposal.json')
    shutil.copyfile(failed_parent_authority,output/'failed-parent-authority.json')
    grids=grid_inventory(old['cases']);proposal=json.loads(approved_proposal.read_text())
    P.need(proposal['cases']==old['cases'] and proposal['grid_inventory']==grids,'Expanded approved physical/grid universe differs')
    row=dict(schema='pinwheel.streaming-8x4-rc-reference-expanded-plan.v1',qualified=False,model_qualified=False,
        qualified_timing=False,finite_BEM_passed=False,native_executed=False,root_go_required=True,
        parent_reference_only_plan_sha256=BASELINE,corrected_proposal_sha256=PROPOSAL,
        historical_plan_sha256=old['historical_plan_sha256'],historical_plan_executed_or_admitted=False,
        old_failed_reference_not_promoted=True,policy=policy(),protocol=protocol(old),cases=old['cases'],grid_inventory=grids,
        original_failed_reference_authority=failed_parent(output/'failed-parent-authority.json'),
        kernel_admission_derivation=kernel_derivation(),storage_admission=storage_admission(old),
        original_M1_FVM_control_authority=old['original_M1_FVM_control_authority'],
        producer_sha256=sources(),files=W.input_files(output))
    W.write(output/'plan.json',row);verify(output,E.sha(output/'plan.json'));return row


def verify(inputs,digest):
    P.need(E.sha(inputs/'plan.json')==digest,'Expanded plan hash differs');row=json.loads((inputs/'plan.json').read_text())
    old=O.verify(inputs/'parent-reference-only',BASELINE)
    P.need(E.sha(inputs/'approved-proposal.json')==PROPOSAL,'Corrected expanded proposal changed')
    proposal=json.loads((inputs/'approved-proposal.json').read_text());grids=grid_inventory(old['cases'])
    P.need(row['schema']=='pinwheel.streaming-8x4-rc-reference-expanded-plan.v1'
        and all(row[k] is False for k in ('qualified','model_qualified','qualified_timing','finite_BEM_passed','native_executed','historical_plan_executed_or_admitted'))
        and row['root_go_required'] is True and row['old_failed_reference_not_promoted'] is True
        and row['parent_reference_only_plan_sha256']==BASELINE and row['corrected_proposal_sha256']==PROPOSAL
        and row['historical_plan_sha256']==old['historical_plan_sha256']
        and row['policy']==policy() and row['protocol']==protocol(old)
        and row['cases']==proposal['cases']==old['cases'] and row['grid_inventory']==proposal['grid_inventory']==grids
        and row['kernel_admission_derivation']==kernel_derivation() and row['storage_admission']==storage_admission(old)
        and row['original_failed_reference_authority']==failed_parent(inputs/'failed-parent-authority.json')
        and row['original_M1_FVM_control_authority']==old['original_M1_FVM_control_authority']
        and row['producer_sha256']==sources() and row['files']==W.input_files(inputs),
        'Expanded scope/physical/operator/source/storage/reference authority differs')
    return row


def validate_row(plan,job,row):
    case=next(c for c in plan['cases'] if c['name']==job['case']);p=plan['protocol'];names=[r['name'] for r in case['rectangles']]
    grid=next(g for g in plan['grid_inventory'] if (g['case'],g['step_um'],g['extent_um'])==(job['case'],job['step'],job['extent']))
    P.need(row['schema']=='pinwheel.streaming-8x4-rc-layered-reference.v1' and row['names']==names
        and row['rectangles']==[dict(name=r['name'],bounds_um=list(map(float,r['bounds_um']))) for r in case['rectangles']]
        and row['epsilon_layers']==[list(map(float,s)) for s in case['epsilon_layers']]
        and row['mesh_step_um']==float(job['step']) and row['extent_um']==float(job['extent'])
        and row['qualified'] is False and row['continuum_error_enclosure'] is False,
        'Expanded actual geometry/material/mesh/domain/scope differs')
    M.validate_excitation_membership(names,row['excitations'])
    P.need(type(row['nodes']) is int and row['nodes']==grid['nodes']<=70000
        and type(row['unknown_nodes']) is int and 0<row['unknown_nodes']<row['nodes']
        and all(0<e['cg_iterations']<=p['maximum_cg_iterations'] and math.isfinite(e['true_residual_relative'])
            and 0<=e['true_residual_relative']<=float(p['true_residual_relative_tolerance'])
            and math.isfinite(e['energy_flux_relative_error']) and 0<=e['energy_flux_relative_error']<=float(p['energy_flux_relative_tolerance']) for e in row['excitations']),
        'Expanded actual nodes/excitation/residual/energy contract differs')
    matrix=row['matrix_F_per_m'];P.matrix_physics(names,[[str(x) for x in r] for r in matrix],asymmetry_limit=P.number(p['reciprocity_relative_tolerance']))
    P.need(len(row['ground_C_F_per_m'])==len(names)
        and all(abs(sum(r)-g)<=1e-12*abs(g) for r,g in zip(matrix,row['ground_C_F_per_m']))
        and (row['coupling_C_F_per_m'] is None if len(names)==1 else abs(row['coupling_C_F_per_m']+matrix[0][1])<=1e-12*abs(matrix[0][1]))
        and math.isfinite(row['wall_seconds']) and row['wall_seconds']>=0
        and math.isfinite(row['reciprocity_relative_error']) and 0<=row['reciprocity_relative_error']<=1e-7,
        'Expanded full matrix/ground/coupling/runtime semantics differ')


def dispatch_argv(inputs,digest,index,output):
    return [PYTHON,'-I','-B','/rc-source/'+NEW[0],'one','--inputs',str(inputs),'--plan-sha256',digest,'--index',str(index),'--output',str(output)]


def proposal(inputs,digest,parent,require_fresh=True):
    inputs,parent=inputs.resolve(),parent.resolve();plan=verify(inputs,digest)
    P.need(parent.is_dir() and (not require_fresh or not(parent/OUTPUT).exists()),'Fresh expanded output required')
    command=['docker','run','--name',CONTAINER,'--rm','--pull','never','--network','none','--read-only','--cpus','1',
        '--memory','2g','--memory-swap','2g','--pids-limit','128','--tmpfs','/tmp:rw,nosuid,noexec,size=134217728',
        '--mount',f'type=bind,src={Path(__file__).resolve().parent},dst=/rc-source,readonly',
        '--mount',f'type=bind,src={inputs},dst=/rc-inputs,readonly','--mount',f'type=bind,src={parent},dst=/rc-output-parent',
        '--entrypoint',PYTHON,W.C.D.IMAGE,'-I','-B','/rc-source/'+NEW[0],'run','--inputs','/rc-inputs',
        '--plan-sha256',digest,'--output','/rc-output-parent/'+OUTPUT]
    return dict(schema='pinwheel.streaming-8x4-rc-reference-expanded-command-proposal.v1',root_go_required=True,
        admitted=False,native_executed=False,qualified=False,model_qualified=False,qualified_timing=False,finite_BEM_passed=False,
        plan_path=str(inputs/'plan.json'),plan_sha256=digest,output_name=OUTPUT,container_name=CONTAINER,
        timeout_seconds=1860,policy=policy(),producer_sha256=plan['producer_sha256'],argv=command)


def one(inputs, digest, index, output):
    plan = verify(inputs, digest); snapshot(); calls = jobs(plan)
    P.need(type(index) is int and 0 <= index < 32 and not output.exists() and output.parent.is_dir(), 'Undeclared FVM leaf/fresh output')
    job = calls[index]; case = next(c for c in plan['cases'] if c['name'] == job['case'])
    result = {'schema': 'pinwheel.streaming-8x4-rc-reference-expanded-leaf.v1', 'plan_sha256': digest,
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
    row = {'schema': 'pinwheel.streaming-8x4-rc-reference-expanded-dispatch.v1', 'index': index,
        'plan_sha256': digest, 'argv': dispatch_argv(inputs, digest, index, target), 'timeout_seconds': 120,
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
                if time.monotonic() - started >= 120:
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
    row = {'schema': 'pinwheel.streaming-8x4-rc-reference-expanded-execution.v1', 'plan_sha256': digest,
        'policy': policy(), 'qualified': False, 'model_qualified': False, 'qualified_timing': False,
        'finite_BEM_passed': False, 'reference_stability_passed': False, 'measurement_packet_completed': False,
        'all_numeric_leaves_passed': False, 'resource_feasible': False, 'passed': False, 'jobs': []}
    try:
        for index, job in enumerate(jobs(plan)):
            P.need(time.monotonic() - started < 1670, 'Reference-only lacks full next-leaf budget')
            dispatch_row = dispatch(inputs, digest, index, output / ('job-' + str(index).zfill(3)))
            row['jobs'].append(dict(job, index=index, dispatch_sha256=E.sha(output / ('job-' + str(index).zfill(3)) / 'dispatch.json'),
                numeric_passed=dispatch_row['numeric_passed'], resource_feasible=dispatch_row['resource_feasible']))
            verify(inputs, digest)
            P.need(dispatch_row['resource_feasible'], 'Reference-only resource/custody failure stops suffix')
    except BaseException as error: row['error'] = type(error).__name__ + ': ' + str(error)
    finally:
        verify(inputs, digest); row['inputs_sources_unchanged'] = True
        row['measurement_packet_completed'] = len(row['jobs']) == 32
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
    for n in ('parent','approved-proposal','failed-parent-authority','output'):q.add_argument('--'+n,type=Path,required=True)
    for action in ('verify','proposal','one','run'):
        q=sub.add_parser(action);q.add_argument('--inputs',type=Path,required=True);q.add_argument('--plan-sha256',required=True)
        if action in ('proposal','one','run'):q.add_argument('--output',type=Path,required=True)
        if action=='one':q.add_argument('--index',type=int,required=True)
    a=p.parse_args()
    if a.action=='prepare':prepare(a.parent,a.approved_proposal,a.failed_parent_authority,a.output);print(E.sha(a.output/'plan.json'));return 0
    if a.action=='verify':verify(a.inputs,a.plan_sha256);print('verified');return 0
    if a.action=='proposal':W.write(a.output,proposal(a.inputs,a.plan_sha256,a.output.parent/'rc-native-outputs'));return 0
    result=one(a.inputs,a.plan_sha256,a.index,a.output) if a.action=='one' else run(a.inputs,a.plan_sha256,a.output)
    return 0 if result['numeric_passed' if a.action=='one' else 'passed'] else 2


if __name__=='__main__':raise SystemExit(main())
