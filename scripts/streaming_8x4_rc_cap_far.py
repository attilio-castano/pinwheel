"""Separate v1 finite-endpoint development study; no foundry/model qualification.

Only isolated .16um FVM trains the synthetic last fringe. Original table rows,
all near-spacing coefficients and untuned validation/stress targets are frozen.
"""
import argparse
import copy
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

sys.path.insert(0, str(Path(__file__).resolve().parent))
import streaming_8x4_rc_consumer_cap as C
import streaming_8x4_rc_cap_far_geometry as G
import streaming_8x4_rc_layered_analyze as H

P, Q, need, write, cgroups = C.P, C.Q, C.need, C.write, C.cgroups
BASELINE_HASH = 'abc8418dab6fe1b93873861078bfad540017be3436dc951bbc75a5da5a496bf2'
PROPOSAL_HASH = '621baa705264eff5e68ecdc575a44e61893bf89a5ed57daf302d92869c787a65'
CANDIDATE_HASH = '28418aef896dbb35c404723cd23d6f00157a29a7527c9df55fe2b327261c051f'
REFERENCE_AUDIT_HASH = '128681523cd638cf4ef8be0c1aa57cb601f07cef581b72bd62014b1d8c2e2906'
CAUSAL_SOURCE_HASH = 'ef1c7ae013237229066e66c7032bdd161c1702f9b1b0ecee4843a8067d03c5f8'
OUTPUT = 'rc-cap-far-01'
JOBS = G.JOBS
EXTRA = ('streaming_8x4_rc_cap_far.py', 'streaming_8x4_rc_cap_far_geometry.py', 'streaming_8x4_rc_cap_far_readback.py')


def protocol():
    value = C.protocol(); del value['width_um'], value['pair_spacing_um']
    value.update(widths_um=['.16','.32'], pair_spacings_um=['.18','.36'],case_ids=[r[1] for r in G.CASES], jobs=JOBS,
        qualification_scope='finite synthetic v1 endpoint development only; fitted training is not independent validation',
        candidate_fit_only='isolated TYP .16um FVM C/2; no pair or wider reference enters fit',
        original_table_rows_unchanged=True, all_near_coefficients_unchanged=True,
        held_out_larger_gap_predicted_coupling_failure=True, wider_stress_is_not_width_range_qualification=True,
        full_accuracy_status='unmeasured', original_BEM_prerequisite_passed=False)
    return value


def table_transform(original, training):
    need(hashlib.sha256(original.encode()).hexdigest() == C.TABLE_HASH, 'Exact retained TYP table differs')
    need(training['case_id'] == 'TYP-w.16-self' and training['names'] == ['W1']
         and training['mesh_step_um'] == .02 and training['extent_um'] == 32
         and training['plan_sha256'] == C.REFERENCE_HASH, 'Isolated training membership differs')
    target = D(str(training['matrix_F_per_m'][0][0])); fringe = target / D('2e-6')
    need(target == D('8.505504630513887e-11'), 'Exact isolated training authority differs')
    matches = list(re.finditer(r'(?ms)(^Metal 1 OVER 0\n)DIST count 5 width 0.16\n(.*?)^END DIST\n', original))
    need(len(matches) == 1, 'Ambiguous regular M1 target table')
    m = matches[0]; appended = '9 0 ' + str(fringe) + ' 0\n'
    replacement = m[1] + 'DIST count 6 width 0.16\n' + m[2] + appended + 'END DIST\n'
    result = original[:m.start()] + replacement + original[m.end():]
    need(hashlib.sha256(result.encode()).hexdigest() == CANDIDATE_HASH, 'Exact approved synthetic endpoint bytes differ')
    return result, dict(target_F_per_m=str(target), fitted_fringe_fF_per_nm=str(fringe), appended_row=appended.strip(),
        all_original_rows_and_other_bytes_unchanged=True, candidate_table_sha256=CANDIDATE_HASH,
        finite_endpoint_um='9', synthetic_zero_coupling_is_not_measured_physics=True,
        interpolation_from_point9_to9um_unvalidated=True, reserved99_100um_sentinels_not_used=True)


def source_evidence(base):
    need(P.sha(base/'manifest.json') == CAUSAL_SOURCE_HASH, 'Far-row exact causal source manifest differs')
    manifest = json.loads((base/'manifest.json').read_text())
    need(manifest['downloaded_code_executed'] is False
         and [r['name'] for r in manifest['files']] == ['extRCmodel.cpp','extRCap.h','extmeasure_couple.cpp','extmeasure_dist.cpp'],
         'Far-row causal source membership/scope differs')
    for row in manifest['files']:
        path=base/row['name']; data=path.read_bytes()
        need(path.is_file() and not path.is_symlink() and len(data)==row['bytes']
             and hashlib.sha256(data).hexdigest()==row['sha256']
             and hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==row['git_blob'],
             'Far-row exact causal source Git blob/SHA differs')
    return manifest


def prepare(baseline, reference_directory, reference_audit, development_proposal, causal_source, output):
    old = C.verify(baseline, BASELINE_HASH)
    reference, raw = H.read_reference(baseline / 'reference-plan.json', C.REFERENCE_HASH, reference_directory)
    source_evidence(causal_source)
    need(P.sha(reference_audit) == REFERENCE_AUDIT_HASH and P.sha(development_proposal) == PROPOSAL_HASH,
         'Approved proposal/full reference audit identity differs')
    need(not output.exists() and output.parent.is_dir(), 'Far-row preparation owner must be fresh')
    output.mkdir(); shutil.copytree(baseline, output / 'baseline-C1')
    shutil.copytree(causal_source, output/'causal-source')
    shutil.copyfile(reference_audit, output / 'reference-audit.json'); shutil.copyfile(development_proposal, output / 'development-proposal.json')
    shutil.copyfile(reference_directory / 'report.json', output / 'reference-report.json')
    fine = {}; targets = {}; reference_files = {}
    for name, case, _, _, _ in G.CASES:
        selected = [(i,j) for i,j in enumerate(raw['jobs']) if j['case'] == case and j['step'] == '.02' and j['extent'] == '32' and not j['uniform_control']]
        need(len(selected) == 1, 'Exact far-row reference target membership differs')
        index, job = selected[0]; path = reference_directory / f'case-{index:03}.json'
        row = json.loads(path.read_text()); need(P.sha(path) == job['output_sha256'], 'Actual target reference raw hash differs')
        target = output / (name + '-reference.json'); shutil.copyfile(path,target)
        fine[name] = row; reference_files[name] = dict(file=target.name, sha256=P.sha(target), job_index=index)
        targets[case] = dict(matrix_F_per_m=row['matrix_F_per_m'], ground_F_per_m=row['ground_C_F_per_m'])
    candidate, witness = table_transform((baseline / 'rules.txt').read_text(), fine['self16'])
    files = {'tech.lef': (baseline / 'tech.lef').read_bytes(), 'retained_rules.txt': (baseline / 'rules.txt').read_bytes(),
             'far_rules.txt': candidate.encode(), 'run.tcl': C.tcl().encode()}
    for job in JOBS: files[job + '.def'] = G.fixture(G.definition(job)).encode()
    for name,data in files.items(): (output/name).write_bytes(data)
    producers = dict(old['producer_sha256']); producers.update({n:P.sha(Path(__file__).with_name(n)) for n in EXTRA})
    plan = dict(schema='pinwheel.streaming-8x4-rc-cap-far-plan.v1', qualified=False, model_qualified=False,
        native_executed=False, root_go_required=True, baseline_C1_plan_sha256=BASELINE_HASH, protocol=protocol(),
        producer_sha256=dict(sorted(producers.items())), files_sha256={n:hashlib.sha256(d).hexdigest() for n,d in files.items()},
        jobs=[G.definition(j) for j in JOBS], reference_files=reference_files, targets=targets, table_witness=witness,
        reference_audit_sha256=REFERENCE_AUDIT_HASH, development_proposal_sha256=PROPOSAL_HASH,
        reference_report_sha256=P.sha(output/'reference-report.json'),
        predictions=json.loads(development_proposal.read_text())['source_arithmetic_predictions'],
        fit_and_validation_roles=[dict(prefix=n,case=c,role=r) for n,c,_,_,r in G.CASES],
        full_accuracy_status='unmeasured', original_BEM_prerequisite_passed=False,
        candidate_table_file_created=True, causal_source_manifest_sha256=CAUSAL_SOURCE_HASH,
        exact_physical_join=G.physical_join([next(c for c in reference['cases'] if c['name']==r[1]) for r in G.CASES]),
        limits=json.loads(development_proposal.read_text())['limits'])
    write(output/'plan.json',plan); verify(output,P.sha(output/'plan.json'))
    return dict(plan_sha256=P.sha(output/'plan.json'),candidate_table_sha256=CANDIDATE_HASH,native_executed=False,model_qualified=False)


def verify(base, plan_hash):
    need(P.sha(base/'plan.json') == plan_hash, 'Far-row plan identity differs')
    plan = json.loads((base/'plan.json').read_text()); old = C.verify(base/'baseline-C1',BASELINE_HASH)
    need(plan['schema']=='pinwheel.streaming-8x4-rc-cap-far-plan.v1' and all(plan[k] is False for k in ('qualified','model_qualified','native_executed'))
         and plan['root_go_required'] is True and plan['baseline_C1_plan_sha256']==BASELINE_HASH
         and plan['protocol']==protocol() and plan['jobs']==[G.definition(j) for j in JOBS]
         and plan['full_accuracy_status']=='unmeasured' and plan['original_BEM_prerequisite_passed'] is False
         and plan['candidate_table_file_created'] is True,
         'Far-row typed policy/membership/promotion differs')
    source_evidence(base/'causal-source')
    reference=json.loads((base/'baseline-C1/reference-plan.json').read_text())
    need(plan['causal_source_manifest_sha256']==CAUSAL_SOURCE_HASH
         and plan['exact_physical_join']==G.physical_join([next(c for c in reference['cases'] if c['name']==r[1]) for r in G.CASES]),
         'Far-row causal source/physical witness differs')
    producers=dict(old['producer_sha256']);producers.update({n:P.sha(Path(__file__).with_name(n)) for n in EXTRA})
    need(plan['producer_sha256']==dict(sorted(producers.items())), 'Far-row transitive source identity differs')
    need(P.sha(base/'reference-audit.json')==plan['reference_audit_sha256']==REFERENCE_AUDIT_HASH
         and P.sha(base/'development-proposal.json')==plan['development_proposal_sha256']==PROPOSAL_HASH
         and P.sha(base/'reference-report.json')==plan['reference_report_sha256'], 'Far-row evidence authority differs')
    raw=json.loads((base/'reference-report.json').read_text())
    need(raw['plan_sha256']==C.REFERENCE_HASH and raw['passed'] is True and raw['analysis']['passed'] is True
         and len(raw['jobs'])==25 and raw['model_qualified'] is False, 'Full empirical reference prerequisite differs')
    need(set(plan['reference_files'])=={r[0] for r in G.CASES},'Far-row complete reference target set differs')
    targets={};fine={}
    for prefix,case,_,_,_ in G.CASES:
        info=plan['reference_files'][prefix];path=base/info['file'];need(path.parent==base and not path.is_symlink()
             and P.sha(path)==info['sha256']==raw['jobs'][info['job_index']]['output_sha256'], 'Far-row actual target raw identity differs')
        row=json.loads(path.read_text());job=raw['jobs'][info['job_index']]
        need(row['case_id']==case and row['plan_sha256']==C.REFERENCE_HASH and row['mesh_step_um']==.02 and row['extent_um']==32
             and (job['case'],job['step'],job['extent'],job['uniform_control'])==(case,'.02','32',False),'Far-row target case/mesh/domain differs')
        fine[prefix]=row;targets[case]=dict(matrix_F_per_m=row['matrix_F_per_m'],ground_F_per_m=row['ground_C_F_per_m'])
    candidate,witness=table_transform((base/'baseline-C1/rules.txt').read_text(),fine['self16'])
    expected_files={'tech.lef':(base/'baseline-C1/tech.lef').read_bytes(),'retained_rules.txt':(base/'baseline-C1/rules.txt').read_bytes(),
                    'far_rules.txt':candidate.encode(),'run.tcl':C.tcl().encode()}
    expected_files.update({j+'.def':G.fixture(G.definition(j)).encode() for j in JOBS})
    need(set(plan['files_sha256'])==set(expected_files) and plan['table_witness']==witness and plan['targets']==targets,
         'Far-row exact fit/targets/file membership differs')
    proposal=json.loads((base/'development-proposal.json').read_text())
    need(plan['predictions']==proposal['source_arithmetic_predictions'] and plan['limits']==proposal['limits']
         and plan['fit_and_validation_roles']==[dict(prefix=n,case=c,role=r) for n,c,_,_,r in G.CASES], 'Far-row held-out/limitation contract differs')
    for name,data in expected_files.items():
        path=base/name;need(path.is_file() and not path.is_symlink() and path.read_bytes()==data
            and P.sha(path)==plan['files_sha256'][name], 'Far-row actual input bytes differ')
    return plan


def parse_leaf(directory,job):
    raw=(directory/'native.log').read_text();n=len(job['rows'])
    need(not re.search(r'(?im)\b(?:warning|warn|error|fatal)\b',raw) and raw.count('PINWHEEL_CAP_TERMINAL')==1,
         'Far-row Native warning/error/terminal gap')
    need(re.findall(r'PINWHEEL_CAP_INVENTORY insts=(\d+) iterms=(\d+) nets=(\d+) bterms=(\d+)',raw)==[('0','0',str(n),str(2*n))]
         and re.findall(r'PINWHEEL_CAP_TECH dbu=(\d+) m1_width=(\d+)',raw)==[('1000','160')], 'Far-row actual cell/unit/default-width inventory differs')
    before,after=directory/'before.def',directory/'after.def'
    need(before.read_bytes()==after.read_bytes(),'Far-row Native geometry bytes changed')
    G.validate(before.read_text(),job)
    return Q.parse((directory/'result.spef').read_text(),[r['net'] for r in job['rows']],job['partners'])


def measurements(plan,rows):
    need([r['job'] for r in rows]==JOBS,'Far-row four-call membership differs')
    results=[];comparisons=[]
    for row in rows:
        for prefix,case,_,_,role in G.CASES:
            groups=[g for g in row['values']['groups'] if all(n.startswith(prefix+'_') for n in g['names'])]
            need(len(groups)==3,'Far-row exact three-length case membership differs')
            slopes=C.slopes(None,dict(groups=groups));change=C.relative(C.vector(slopes[0]),C.vector(slopes[1]))
            target=plan['targets'][case];ref=[D(str(x)) for line in target['matrix_F_per_m'] for x in line]+[D(str(x)) for x in target['ground_F_per_m']]
            errors=[C.relative(C.vector(s),ref) for s in slopes]
            results.append(dict(job=row['job'],case=case,role=role,slopes=slopes,consecutive_slope_difference=str(change),passed=change<=D('.05')))
            comparisons.append(dict(job=row['job'],case=case,role=role,complete_matrix_ground_relative_errors=list(map(str,errors)),
                within_10percent_numerically=max(errors)<=D('.10'),independent_validation=role=='held_out_consumer'))
    index={(r['job'],r['case']):r for r in results};isolation=[]
    for policy in ('retained','far'):
        for _,case,_,_,_ in G.CASES:
            a,b=(index[(policy+'-isolation'+str(s),case)]['slopes'] for s in (512,1024))
            changes=[C.relative(C.vector(x),C.vector(y)) for x,y in zip(a,b)]
            isolation.append(dict(policy=policy,case=case,relative_differences=list(map(str,changes)),passed=max(changes)<=D('.02'),physical_boundary_test=False))
    controls=all(r['passed'] for r in results+isolation)
    candidate=controls and all(r['within_10percent_numerically'] for r in comparisons if r['job'].startswith('far-'))
    return dict(jobs=results,spacing_isolation_controls=isolation,development_reference_comparisons=comparisons,
        measurement_controls_passed=controls,candidate_development_gates_passed=candidate,
        full_accuracy_status='unmeasured',original_BEM_prerequisite_passed=False,model_qualified=False,
        trained_fit_is_independent_validation=False,held_out_failure_must_not_retune_policy=True)


def command_proposal(base,plan_hash,output_parent,require_fresh=True):
    plan=verify(base,plan_hash);need(not require_fresh or not (output_parent/OUTPUT).exists(),'Far-row output must be fresh')
    old=C.command_proposal(base/'baseline-C1',BASELINE_HASH,output_parent,require_fresh=False);argv=list(old['argv'])
    replacements={'pinwheel-8x4-rc-consumer-cap-01':'pinwheel-8x4-rc-cap-far-01',
        'type=bind,src='+str((base/'baseline-C1').resolve())+',dst=/rc-inputs,readonly':'type=bind,src='+str(base.resolve())+',dst=/rc-inputs,readonly',
        '/rc-source/streaming_8x4_rc_consumer_cap.py':'/rc-source/streaming_8x4_rc_cap_far.py',BASELINE_HASH:plan_hash,
        '/rc-output-parent/'+C.OUTPUT:'/rc-output-parent/'+OUTPUT}
    for before,after in replacements.items():need(argv.count(before)==1,'Far-row exact argv adaptation differs');argv[argv.index(before)]=after
    return dict(schema='pinwheel.streaming-8x4-rc-cap-far-command-proposal.v1',root_go_required=True,admitted=False,native_executed=False,
        model_qualified=False,container_name='pinwheel-8x4-rc-cap-far-01',timeout_seconds=180,work_seconds=150,maximum_calls=4,
        plan_path=str((base/'plan.json').resolve()),plan_sha256=plan_hash,producer_sha256=plan['producer_sha256'],argv=argv)


def run(base, plan_hash, output):
    plan = verify(base, plan_hash); cg = cgroups()
    need(not output.exists() and output.parent.is_dir(), 'Cap native output must be fresh')
    output.mkdir(); start = time.monotonic(); jobs = []
    report = {'schema': 'pinwheel.streaming-8x4-rc-cap-far-execution.v1', 'plan_sha256': plan_hash,
        'qualified': False, 'model_qualified': False, 'passed': False, 'measurement_packet_completed': False,
        'accuracy_status': 'unmeasured', 'independent_accuracy_passed': False, 'jobs': jobs, 'cgroups': cg}
    try:
        for job in plan['jobs']:
            need(time.monotonic() - start < 115, 'Insufficient fixed cap packet work budget')
            owner = output / job['job']; owner.mkdir()
            for name in ('tech.lef', 'run.tcl'):
                shutil.copyfile(base / name, owner / name)
            shutil.copyfile(base / (job['policy'] + '_rules.txt'), owner / 'rules.txt')
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
            # Preserve numeric failures and finish the fixed four calls; no adaptive retry.
        report['measurement_packet_completed'] = len(jobs) == 4
        if all(j['passed'] for j in jobs):
            leaves = [json.loads((output / j['job'] / 'report.json').read_text()) for j in jobs]
            report['analysis'] = measurements(plan, leaves); report['passed'] = report['analysis']['candidate_development_gates_passed']
    except Exception as error:
        report['error'] = type(error).__name__ + ': ' + str(error)
    report['inputs_unchanged'] = verify(base, plan_hash) == plan
    report['wall_seconds'] = time.monotonic() - start; write(output / 'report.json', report)
    return report


def main():
    p=argparse.ArgumentParser(description=__doc__);sub=p.add_subparsers(dest='action',required=True)
    q=sub.add_parser('prepare')
    for n in ('baseline','reference-directory','reference-audit','development-proposal','causal-source','output'):q.add_argument('--'+n,type=Path,required=True)
    for action in ('verify','proposal','run'):
        q=sub.add_parser(action);q.add_argument('--inputs',type=Path,required=True);q.add_argument('--plan-sha256',required=True)
        if action!='verify':q.add_argument('--output',type=Path,required=True)
        if action=='proposal':q.add_argument('--output-parent',type=Path,required=True)
    a=p.parse_args()
    if a.action=='prepare':result=prepare(a.baseline,a.reference_directory,a.reference_audit,a.development_proposal,a.causal_source,a.output)
    elif a.action=='verify':result=verify(a.inputs,a.plan_sha256)
    elif a.action=='run':result=run(a.inputs,a.plan_sha256,a.output)
    else:result=command_proposal(a.inputs,a.plan_sha256,a.output_parent);write(a.output,result)
    print(json.dumps(result,indent=2))
    if a.action=='run' and not result['passed']:raise SystemExit(2)


if __name__=='__main__':main()
