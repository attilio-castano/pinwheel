"""Two-call supplementary five-layer C consumer; Root alone admits Native.

Retained TYP rules/default widths only. Complete empirical reference prerequisites
remain mandatory before provisional comparisons; full BEM/model authority false.
"""
import argparse
from decimal import Decimal as D
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import sys
import time

sys.path.insert(0,str(Path(__file__).resolve().parent))
import streaming_8x4_rc_consumer_cap as C
import streaming_8x4_rc_cap_all_layers_geometry as G
import streaming_8x4_rc_reference_only as F
import streaming_8x4_rc_reference_only_readback as R

P,Q,need,write,cgroups=C.P,C.Q,C.need,C.write,C.cgroups
BASELINE_HASH='abc8418dab6fe1b93873861078bfad540017be3436dc951bbc75a5da5a496bf2'
REFERENCE32_HASH='bd24cf673c33be53a2a83a1d4c27d3c14ea989208cfb8689a09d861baec69e32'
PROPOSAL_HASH='efb7664565d43a934c3b2b71e21a7dd189652ea5a7f71064174e8fce7b103884'
OUTPUT='rc-cap-all-layers-01'
JOBS=G.JOBS
NEW=('streaming_8x4_rc_cap_all_layers.py','streaming_8x4_rc_cap_all_layers_geometry.py','streaming_8x4_rc_cap_all_layers_readback.py')


def protocol():
    value=C.protocol();del value['width_um'],value['pair_spacing_um']
    value.update(case_ids=[r['name'] for r in G.CASES],default_layer_widths_DBU=G.WIDTHS,
        calls=2,work_seconds=90,outer_seconds=120,case_count=9,nets_per_call=39,ports_per_call=78,
        fixture_groups_per_call=27,no_NDR=True,no_fitting_or_coefficient_changes=True,
        physical_reference_prerequisite='complete unchanged original FVM25 and separately typed reference-only32 raw/resource empirical pass; no relaxation on reference failure',
        qualification_scope='supplementary nominal TYP five-layer consumer measurement only; provisional numerical comparisons separate from finite BEM/full accuracy',
        full_accuracy_status='unmeasured',finite_BEM_passed=False,qualified_timing=False)
    return value


def tcl():
    text=C.tcl();anchor='write_def before.def\n'
    widths='foreach layer {Metal1 Metal2 Metal3 Metal4 TopMetal1} {\nputs "PINWHEEL_CAP_WIDTH layer=$layer dbu_width=[[$tech findLayer $layer] getWidth]"\n}\n'
    need(text.count(anchor)==1,'Frozen C1 Tcl adaptation anchor differs')
    return text.replace(anchor,widths+anchor)


def producers(old,reference):
    result=dict(old['producer_sha256'])
    for name,digest in reference['producer_sha256'].items():
        need(name not in result or result[name]==digest,'Conflicting frozen inherited source')
        result[name]=digest
    result.update({n:P.sha(Path(__file__).with_name(n)) for n in NEW})
    return dict(sorted(result.items()))


def physical(base):
    reference=F.verify(base/'reference32-inputs',REFERENCE32_HASH)
    old=json.loads((base/'baseline-C1/reference-plan.json').read_text())
    cases=G.physical_cases(reference,old)
    declared=json.loads((base/'approved-proposal.json').read_text())
    need(cases==declared['cases'],'Exact approved nine-case physical universe differs')
    return reference,cases


def expected_files(base):
    files={'tech.lef':(base/'baseline-C1/tech.lef').read_bytes(),
        'rules.txt':(base/'baseline-C1/rules.txt').read_bytes(),'run.tcl':tcl().encode()}
    files.update({j+'.def':G.fixture(G.definition(j)).encode() for j in JOBS})
    return files


def prepare(baseline,reference32,approved_proposal,output):
    old=C.verify(baseline,BASELINE_HASH);F.verify(reference32,REFERENCE32_HASH)
    need(P.sha(approved_proposal)==PROPOSAL_HASH and not output.exists() and output.parent.is_dir(),
        'Exact approved scope/fresh supplementary C owner required')
    output.mkdir();shutil.copytree(baseline,output/'baseline-C1');shutil.copytree(reference32,output/'reference32-inputs')
    shutil.copyfile(approved_proposal,output/'approved-proposal.json');reference,cases=physical(output)
    files=expected_files(output)
    for name,data in files.items():(output/name).write_bytes(data)
    row=dict(schema='pinwheel.streaming-8x4-rc-cap-all-layers-plan.v1',qualified=False,model_qualified=False,
        qualified_timing=False,finite_BEM_passed=False,native_executed=False,root_go_required=True,
        baseline_C1_plan_sha256=BASELINE_HASH,reference32_plan_sha256=REFERENCE32_HASH,
        original_M1_reference_plan_sha256=C.REFERENCE_HASH,approved_proposal_sha256=PROPOSAL_HASH,
        protocol=protocol(),jobs=[G.definition(j) for j in JOBS],cases=cases,
        producer_sha256=producers(old,reference),files_sha256={n:hashlib.sha256(d).hexdigest() for n,d in files.items()},
        original_M1_FVM_control_authority=reference['original_M1_FVM_control_authority'],
        reference32_execution_status_at_preparation='not assumed; actual closed authority required at comparison',
        full_accuracy_status='unmeasured',provisional_comparison_status='unmeasured until full reference prerequisites supplied')
    write(output/'plan.json',row);verify(output,P.sha(output/'plan.json'))
    return dict(plan_sha256=P.sha(output/'plan.json'),native_executed=False,model_qualified=False)


def verify(base,digest):
    need(P.sha(base/'plan.json')==digest,'Supplementary C plan identity differs')
    plan=json.loads((base/'plan.json').read_text());old=C.verify(base/'baseline-C1',BASELINE_HASH)
    need(P.sha(base/'approved-proposal.json')==PROPOSAL_HASH,'Supplementary C approved proposal changed')
    reference,cases=physical(base);files=expected_files(base)
    need(plan['schema']=='pinwheel.streaming-8x4-rc-cap-all-layers-plan.v1'
        and all(plan[k] is False for k in ('qualified','model_qualified','qualified_timing','finite_BEM_passed','native_executed'))
        and plan['root_go_required'] is True and plan['baseline_C1_plan_sha256']==BASELINE_HASH
        and plan['reference32_plan_sha256']==REFERENCE32_HASH and plan['original_M1_reference_plan_sha256']==C.REFERENCE_HASH
        and plan['approved_proposal_sha256']==PROPOSAL_HASH and plan['protocol']==protocol()
        and plan['jobs']==[G.definition(j) for j in JOBS] and plan['cases']==cases
        and plan['producer_sha256']==producers(old,reference)
        and plan['files_sha256']=={n:hashlib.sha256(d).hexdigest() for n,d in files.items()}
        and plan['original_M1_FVM_control_authority']==reference['original_M1_FVM_control_authority']
        and plan['reference32_execution_status_at_preparation']=='not assumed; actual closed authority required at comparison'
        and plan['full_accuracy_status']=='unmeasured'
        and plan['provisional_comparison_status']=='unmeasured until full reference prerequisites supplied',
        'Supplementary C exact scope/source/physical/reference prerequisites differ')
    for name,data in files.items():
        path=base/name;need(path.is_file() and not path.is_symlink() and path.read_bytes()==data,
            'Supplementary C owned actual file bytes differ')
    need(P.sha(base/'tech.lef')==C.TECH_HASH and P.sha(base/'rules.txt')==C.TABLE_HASH,
        'Retained TYP technology/table differs')
    return plan


def parse_leaf(directory,job):
    raw=(directory/'native.log').read_text()
    need(not re.search(r'(?im)\b(?:warning|warn|error|fatal)\b',raw) and raw.count('PINWHEEL_CAP_TERMINAL')==1,
        'Supplementary C Native warning/error/terminal gap')
    need(re.findall(r'PINWHEEL_CAP_INVENTORY insts=(\d+) iterms=(\d+) nets=(\d+) bterms=(\d+)',raw)==[('0','0','39','78')]
        and re.findall(r'PINWHEEL_CAP_TECH dbu=(\d+) m1_width=(\d+)',raw)==[('1000','160')]
        and re.findall(r'PINWHEEL_CAP_WIDTH layer=(\w+) dbu_width=(\d+)',raw)==[(m,str(G.WIDTHS[m])) for m in G.METALS],
        'Supplementary C actual cells/unit/default-five-width inventory differs')
    before,after=directory/'before.def',directory/'after.def'
    need(before.read_bytes()==after.read_bytes(),'Supplementary C Native geometry bytes changed')
    G.validate(before.read_text(),job)
    return Q.parse((directory/'result.spef').read_text(),[r['net'] for r in job['rows']],job['partners'])


def measurements(rows):
    need([r['job'] for r in rows]==JOBS,'Complete ordered supplementary two-call membership required')
    results=[];controls=[]
    for row in rows:
        for case in G.CASES:
            groups=[g for g in row['values']['groups'] if all(n.startswith(case['prefix']+'_L') for n in g['names'])]
            expected=[[r['net'] for r in G.definition(row['job'])['rows'] if r['case']==case['name'] and r['length_um']==length] for length in (50,100,150)]
            need(len(groups)==3 and sorted(tuple(g['names']) for g in groups)==sorted(tuple(n) for n in expected),
                'Supplementary C exact three-length matrix membership differs')
            slopes=C.slopes(None,dict(groups=groups));change=C.relative(C.vector(slopes[0]),C.vector(slopes[1]))
            results.append(dict(job=row['job'],case=case['name'],slopes=slopes,consecutive_slope_difference=str(change),passed=change<=D('.05')))
    index={(r['job'],r['case']):r for r in results}
    for case in G.CASES:
        a,b=(index[(j,case['name'])]['slopes'] for j in JOBS)
        changes=[C.relative(C.vector(x),C.vector(y)) for x,y in zip(a,b)]
        controls.append(dict(case=case['name'],relative_differences=list(map(str,changes)),passed=max(changes)<=D('.02'),physical_boundary_test=False))
    return dict(jobs=results,spacing_isolation_controls=controls,
        measurement_controls_passed=all(r['passed'] for r in results+controls),full_accuracy_status='unmeasured',
        finite_BEM_passed=False,model_qualified=False,qualified_timing=False)


def command_proposal(base,digest,output_parent,require_fresh=True):
    plan=verify(base,digest);need(not require_fresh or not (output_parent/OUTPUT).exists(),'Fresh supplementary C Native output required')
    previous=C.command_proposal(base/'baseline-C1',BASELINE_HASH,output_parent,require_fresh=False);argv=list(previous['argv'])
    replacements={'pinwheel-8x4-rc-consumer-cap-01':'pinwheel-8x4-'+OUTPUT,
        'type=bind,src='+str((base/'baseline-C1').resolve())+',dst=/rc-inputs,readonly':'type=bind,src='+str(base.resolve())+',dst=/rc-inputs,readonly',
        '/rc-source/streaming_8x4_rc_consumer_cap.py':'/rc-source/'+NEW[0],BASELINE_HASH:digest,
        '/rc-output-parent/'+C.OUTPUT:'/rc-output-parent/'+OUTPUT}
    for before,after in replacements.items():need(argv.count(before)==1,'Exact supplementary C argv adaptation differs');argv[argv.index(before)]=after
    return dict(schema='pinwheel.streaming-8x4-rc-cap-all-layers-command-proposal.v1',root_go_required=True,admitted=False,
        native_executed=False,qualified=False,model_qualified=False,qualified_timing=False,finite_BEM_passed=False,
        container_name='pinwheel-8x4-'+OUTPUT,timeout_seconds=120,work_seconds=90,maximum_calls=2,
        plan_path=str((base/'plan.json').resolve()),plan_sha256=digest,producer_sha256=plan['producer_sha256'],argv=argv)


def run(base, plan_hash, output):
    plan = verify(base, plan_hash); cg = cgroups()
    need(not output.exists() and output.parent.is_dir(), 'Cap native output must be fresh')
    output.mkdir(); start = time.monotonic(); jobs = []
    report = {'schema': 'pinwheel.streaming-8x4-rc-cap-all-layers-execution.v1', 'plan_sha256': plan_hash,
        'qualified': False, 'model_qualified': False, 'passed': False, 'measurement_packet_completed': False,
        'accuracy_status': 'unmeasured', 'independent_accuracy_passed': False, 'jobs': jobs, 'cgroups': cg}
    try:
        for job in plan['jobs']:
            need(time.monotonic() - start < 55, 'Insufficient fixed cap packet work budget')
            owner = output / job['job']; owner.mkdir()
            for name in ('tech.lef', 'rules.txt', 'run.tcl'):
                shutil.copyfile(base / name, owner / name)
            shutil.copyfile(base / (job['job'] + '.def'), owner / 'fixture.def')
            before = {p.name: P.sha(p) for p in owner.iterdir()}; child = None; timed_out = False
            command = ['openroad', '-no_init', '-exit', 'run.tcl']; leaf = {'job': job['job'], 'passed': False}
            with (owner / 'native.log').open('wb') as stream:
                child = subprocess.Popen(command, cwd=owner, stdout=stream, stderr=subprocess.STDOUT, start_new_session=True)
                try:
                    code = child.wait(timeout=30)
                except subprocess.TimeoutExpired:
                    timed_out = True; os.killpg(child.pid, signal.SIGKILL); code = child.wait()
            try:
                os.killpg(child.pid, 0)
            except ProcessLookupError:
                reaped = True
            else:
                os.killpg(child.pid, signal.SIGKILL); raise ValueError('Cap child left a process group')
            need(all(P.sha(owner / n) == h for n, h in before.items()), 'Copied cap inputs changed')
            leaf.update(argv=command, exit_code=code, timed_out=timed_out, process_tree_reaped=reaped,
                        copied_inputs_unchanged=True, copied_input_sha256=before, native_log_sha256=P.sha(owner / 'native.log'))
            try:
                need(type(code) is int and code == 0 and not timed_out, 'Cap OpenROAD exit/timeout failed')
                leaf['values'] = parse_leaf(owner, job); leaf['passed'] = True
            except (ValueError, OSError) as error:
                leaf['error'] = type(error).__name__ + ': ' + str(error)
            leaf['raw_output_sha256'] = {n: P.sha(owner / n) for n in ('before.def', 'after.def', 'result.spef') if (owner / n).is_file()}
            write(owner / 'report.json', leaf); jobs.append(dict(job=job['job'], passed=leaf['passed'], report_sha256=P.sha(owner / 'report.json')))
            # Preserve numeric failures and finish both fixed calls; no adaptive retry.
        report['measurement_packet_completed'] = len(jobs) == 2
        if all(j['passed'] for j in jobs):
            leaves = [json.loads((output / j['job'] / 'report.json').read_text()) for j in jobs]
            report['analysis'] = measurements(leaves); report['passed'] = report['analysis']['measurement_controls_passed']
    except Exception as error:
        report['error'] = type(error).__name__ + ': ' + str(error)
    report['inputs_unchanged'] = verify(base, plan_hash) == plan
    report['wall_seconds'] = time.monotonic() - start; write(output / 'report.json', report)
    return report


def main():
    parser=argparse.ArgumentParser(description=__doc__);sub=parser.add_subparsers(dest='action',required=True)
    p=sub.add_parser('prepare')
    for n in ('baseline','reference32','approved-proposal','output'):p.add_argument('--'+n,type=Path,required=True)
    for action in ('verify','proposal','run'):
        p=sub.add_parser(action);p.add_argument('--inputs',type=Path,required=True);p.add_argument('--plan-sha256',required=True)
        if action!='verify':p.add_argument('--output',type=Path,required=True)
        if action=='proposal':p.add_argument('--output-parent',type=Path,required=True)
    a=parser.parse_args()
    if a.action=='prepare':result=prepare(a.baseline,a.reference32,a.approved_proposal,a.output)
    elif a.action=='verify':result=dict(verified=bool(verify(a.inputs,a.plan_sha256)),native_executed=False)
    elif a.action=='proposal':result=command_proposal(a.inputs,a.plan_sha256,a.output_parent);write(a.output,result)
    else:result=run(a.inputs,a.plan_sha256,a.output)
    print(json.dumps(result,indent=2));return 2 if a.action=='run' and not result['passed'] else 0


if __name__=='__main__':raise SystemExit(main())
