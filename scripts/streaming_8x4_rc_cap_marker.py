"""Two-call v1 zero-distance lookup discriminator; synthetic marker, no fit.

Root alone admits Native. Original strict baseline failure is preserved; a
successful marker is evidence of dispatch only, never physical accuracy.
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
import streaming_8x4_rc_cap_all_layers as A
import streaming_8x4_rc_cap_marker_geometry as G
import streaming_8x4_rc_cap_marker_spef as Z

C,P,Q,need,write=A.C,A.P,A.Q,A.need,A.write
BASELINE_HASH='886670431c23b57f77d4251b8fedc985628a44c4efcd598f84503cbb27db34d2'
BASELINE_RESULT_HASH='834764b8725748294ce22792bfa596fa487062112d3f7d95f7549e8d0bd932e3'
MARKER_HASH='b212c4ddd5e092288564a0190813e8528082ca7828e6fe22c403c8ddd25ef71c'
INTAKES={'marker-source':'95da0f94b1eccd8a91e5f5ca121f1cba9d4b9cb3807af33823e6383bce3a766b',
    'model-source':'ef1c7ae013237229066e66c7032bdd161c1702f9b1b0ecee4843a8067d03c5f8',
    'dispatch-source':'1ca4151ea0db56eb503b41b6edeb445c6f9358394e65a4f68e31146c71e283b7'}
OUTPUT='rc-cap-marker-01'
JOBS=G.JOBS
NEW=('streaming_8x4_rc_cap_marker.py','streaming_8x4_rc_cap_marker_geometry.py',
    'streaming_8x4_rc_cap_marker_spef.py','streaming_8x4_rc_cap_marker_readback.py')
STRICT_ERROR='Missing intended coupling or incident total differs'


def protocol():
    return dict(calls=2,case='TYP-Metal1-Metal2-centered',lengths_um=[50,100,150],nets=6,ports=12,
        command_version='1.0',table_format_version='1.2',coupling_threshold='0.0',cc_model='10.0',
        context_depth=5,lef_res=False,merge_via_wire_res=False,zero_cells_ITerms_vias=True,no_NDR=True,
        coefficient_change='only Metal 1 DIAGUNDER 2 first distance-zero fringe token 0 -> 0.000001',
        retained_table_sha256=C.TABLE_HASH,marker_table_sha256=MARKER_HASH,
        marker_coefficient_fF_per_nm='0.000001',predicted_coupling_slope_F_per_m='1e-12',
        predicted_coupling_slope_tolerance='0.001',coupling_consecutive_slope_tolerance='0.001',
        full_matrix_ground_consecutive_slope_tolerance='0.05',
        static_prediction_is_not_runtime_proof=True,absolute_endpoint_intercept_not_predicted=True,
        baseline_positive_coupling_failure_mandatory=True,baseline_Maxwell_matrix_claimed=False,
        synthetic_lookup_marker_not_physical_coefficient=True,no_fit=True,
        leaf_seconds=30,work_seconds=90,outer_seconds=120,cpu=1,memory_bytes=2147483648,
        tmpfs_bytes=134217728,extra_swap=False,full_accuracy_status='unmeasured',
        finite_BEM_passed=False,model_qualified=False,qualified_timing=False)


def marker(data):
    need(hashlib.sha256(data).hexdigest()==C.TABLE_HASH,'Exact retained table required')
    anchor=b'Metal 1 DIAGUNDER 2\nDIST count 10 width 0.16\n0 0 0 0\n'
    changed=b'Metal 1 DIAGUNDER 2\nDIST count 10 width 0.16\n0 0 0.000001 0\n'
    need(data.count(anchor)==1,'Unique exact zero-distance fringe anchor required')
    result=data.replace(anchor,changed)
    need(result.replace(changed,anchor)==data and hashlib.sha256(result).hexdigest()==MARKER_HASH,
        'Marker token-only transform differs')
    return result


def source_intake(base,name):
    owner=base/name;path=owner/'manifest.json'
    need(path.is_file() and not path.is_symlink() and P.sha(path)==INTAKES[name],'Marker exact source intake differs')
    manifest=json.loads(path.read_text());rows=manifest['files']
    need(rows and len({r['name'] for r in rows})==len(rows),'Complete source file membership required')
    for row in rows:
        n=row['name'];p=owner/n
        need(Path(n).name==n and p.is_file() and not p.is_symlink(),'Source file alias/path differs')
        data=p.read_bytes();need(len(data)==row['bytes'] and hashlib.sha256(data).hexdigest()==row['sha256']
            and hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==row['git_blob'],
            'Exact upstream source bytes/blob differ')
    return dict(manifest_sha256=P.sha(path),files=rows,source_data_only=True,downloaded_code_executed=False)


def producers(old):
    result=dict(old['producer_sha256']);result.update({n:P.sha(Path(__file__).with_name(n)) for n in NEW})
    return dict(sorted(result.items()))


def expected_files(base):
    original=(base/'baseline-C5L/rules.txt').read_bytes()
    result={'tech.lef':(base/'baseline-C5L/tech.lef').read_bytes(),'retained-rules.txt':original,
        'marker-rules.txt':marker(original),'run.tcl':A.tcl().encode()}
    result.update({j+'.def':G.fixture(G.definition(j)).encode() for j in JOBS})
    return result


def physical(base):
    ref=json.loads((base/'baseline-C5L/reference32-inputs/plan.json').read_text())
    old=json.loads((base/'baseline-C5L/baseline-C1/reference-plan.json').read_text())
    return G.physical_cases(ref,old)


def prepare(baseline,baseline_result,marker_source,model_source,dispatch_source,output):
    old=A.verify(baseline,BASELINE_HASH)
    need(P.sha(baseline_result)==BASELINE_RESULT_HASH and not output.exists() and output.parent.is_dir(),
        'Exact retained failure/fresh marker owner required')
    output.mkdir();shutil.copytree(baseline,output/'baseline-C5L')
    shutil.copyfile(baseline_result,output/'baseline-failed-readback.json')
    for name,source in zip(INTAKES,(marker_source,model_source,dispatch_source)):shutil.copytree(source,output/name)
    sources={n:source_intake(output,n) for n in INTAKES};files=expected_files(output)
    for n,data in files.items():(output/n).write_bytes(data)
    plan=dict(schema='pinwheel.streaming-8x4-rc-cap-marker-plan.v1',qualified=False,model_qualified=False,
        qualified_timing=False,finite_BEM_passed=False,native_executed=False,root_go_required=True,
        baseline_plan_sha256=BASELINE_HASH,baseline_failed_readback_sha256=BASELINE_RESULT_HASH,
        protocol=protocol(),cases=physical(output),jobs=[G.definition(j) for j in JOBS],
        source_intakes=sources,producer_sha256=producers(old),
        files_sha256={n:hashlib.sha256(d).hexdigest() for n,d in files.items()})
    write(output/'plan.json',plan);verify(output,P.sha(output/'plan.json'))
    return dict(plan_sha256=P.sha(output/'plan.json'),native_executed=False,model_qualified=False)


def verify(base,digest):
    need(P.sha(base/'plan.json')==digest,'Marker plan identity differs')
    plan=json.loads((base/'plan.json').read_text());old=A.verify(base/'baseline-C5L',BASELINE_HASH)
    need(P.sha(base/'baseline-failed-readback.json')==BASELINE_RESULT_HASH,'Original C5L failure changed')
    failed=json.loads((base/'baseline-failed-readback.json').read_text())
    need(failed['measurement_controls_passed'] is False and failed['model_qualified'] is False,
        'Original C5L failure cannot be promoted')
    files=expected_files(base)
    expected=dict(schema='pinwheel.streaming-8x4-rc-cap-marker-plan.v1',qualified=False,model_qualified=False,
        qualified_timing=False,finite_BEM_passed=False,native_executed=False,root_go_required=True,
        baseline_plan_sha256=BASELINE_HASH,baseline_failed_readback_sha256=BASELINE_RESULT_HASH,
        protocol=protocol(),cases=physical(base),jobs=[G.definition(j) for j in JOBS],
        source_intakes={n:source_intake(base,n) for n in INTAKES},producer_sha256=producers(old),
        files_sha256={n:hashlib.sha256(d).hexdigest() for n,d in files.items()})
    need(plan==expected,'Marker exact source/physical/scope/policy universe differs')
    for n,data in files.items():need((base/n).is_file() and not (base/n).is_symlink() and (base/n).read_bytes()==data,
        'Marker owned bytes changed')
    return plan


def parse_leaf(directory,job):
    raw=(directory/'native.log').read_text()
    need(not re.search(r'(?im)\b(?:warning|warn|error|fatal)\b',raw) and raw.count('PINWHEEL_CAP_TERMINAL')==1,
        'Marker Native warning/error/terminal gap')
    need(re.findall(r'PINWHEEL_CAP_INVENTORY insts=(\d+) iterms=(\d+) nets=(\d+) bterms=(\d+)',raw)==[('0','0','6','12')]
        and re.findall(r'PINWHEEL_CAP_TECH dbu=(\d+) m1_width=(\d+)',raw)==[('1000','160')]
        and re.findall(r'PINWHEEL_CAP_WIDTH layer=(\w+) dbu_width=(\d+)',raw)==[(m,str(G.WIDTHS[m])) for m in G.METALS],
        'Marker actual cells/unit/default widths differ')
    need((directory/'before.def').read_bytes()==(directory/'after.def').read_bytes(),'Marker geometry bytes changed')
    G.validate((directory/'before.def').read_text(),job)
    spef=(directory/'result.spef').read_text();names=[r['net'] for r in job['rows']]
    if job['job']=='marker':
        return dict(strict_physics_passed=True,values=Q.parse(spef,names,job['partners']))
    failure=None
    try:Q.parse(spef,names,job['partners'])
    except ValueError as error:failure=str(error)
    need(failure==STRICT_ERROR,'Retained original strict positive-coupling failure not preserved')
    return dict(strict_physics_passed=False,strict_failure='ValueError: '+failure,
        zero_inventory=Z.zero_inventory(spef,names,job['partners']))


def measurements(rows):
    need([r['job'] for r in rows]==JOBS,'Complete retained/marker ordered membership required')
    retained,tagged=[r['values'] for r in rows]
    need(retained['strict_physics_passed'] is False and retained['strict_failure']=='ValueError: '+STRICT_ERROR
        and retained['zero_inventory']['all_three_intended_couplings_exactly_zero'] is True
        and tagged['strict_physics_passed'] is True,'Marker baseline/positive strict scope differs')
    groups=tagged['values']['groups'];job=G.definition('marker')
    expected=[[r['net'] for r in job['rows'] if r['length_um']==length] for length in (50,100,150)]
    need(len(groups)==3 and sorted(tuple(g['names']) for g in groups)==sorted(tuple(n) for n in expected),
        'Marker exact three-length matrix membership differs')
    slopes=C.slopes(None,dict(groups=groups));couplings=[-D(s['matrix_F_per_m'][0][1]) for s in slopes]
    errors=[abs(k/D('1e-12')-1) for k in couplings]
    consecutive=abs(couplings[0]/couplings[1]-1);change=C.relative(C.vector(slopes[0]),C.vector(slopes[1]))
    passed=max(errors)<=D('.001') and consecutive<=D('.001') and change<=D('.05')
    return dict(lookup_marker_diagnostic_passed=passed,baseline_strict_physics_passed=False,
        baseline_zero_failure_preserved=True,marker_full_strict_physics_passed=True,slopes=slopes,
        coupling_slopes_F_per_m=list(map(str,couplings)),predicted_coupling_slope_F_per_m='1e-12',
        relative_prediction_errors=list(map(str,errors)),coupling_consecutive_slope_difference=str(consecutive),
        full_matrix_ground_consecutive_slope_difference=str(change),absolute_endpoint_intercept_not_predicted=True,
        full_accuracy_status='unmeasured',coefficient_fitted=False,finite_BEM_passed=False,
        model_qualified=False,qualified_timing=False)


def command_proposal(base,digest,output_parent,require_fresh=True):
    plan=verify(base,digest);need(not require_fresh or not (output_parent/OUTPUT).exists(),'Fresh marker Native output required')
    old=A.command_proposal(base/'baseline-C5L',BASELINE_HASH,output_parent,require_fresh=False);argv=list(old['argv'])
    for before,after in [('pinwheel-8x4-'+A.OUTPUT,'pinwheel-8x4-'+OUTPUT),
        ('type=bind,src='+str((base/'baseline-C5L').resolve())+',dst=/rc-inputs,readonly','type=bind,src='+str(base.resolve())+',dst=/rc-inputs,readonly'),
        ('/rc-source/'+A.NEW[0],'/rc-source/'+NEW[0]),(BASELINE_HASH,digest),('/rc-output-parent/'+A.OUTPUT,'/rc-output-parent/'+OUTPUT)]:
        need(argv.count(before)==1,'Exact marker argv adaptation differs');argv[argv.index(before)]=after
    return dict(schema='pinwheel.streaming-8x4-rc-cap-marker-command-proposal.v1',root_go_required=True,
        admitted=False,native_executed=False,qualified=False,model_qualified=False,qualified_timing=False,
        finite_BEM_passed=False,container_name='pinwheel-8x4-'+OUTPUT,timeout_seconds=120,work_seconds=90,
        maximum_calls=2,plan_path=str((base/'plan.json').resolve()),plan_sha256=digest,
        producer_sha256=plan['producer_sha256'],argv=argv)


def run(base,plan_hash,output):
    plan=verify(base,plan_hash);cg=C.cgroups();need(not output.exists() and output.parent.is_dir(),'Fresh marker output required')
    output.mkdir();start=time.monotonic();jobs=[]
    report=dict(schema='pinwheel.streaming-8x4-rc-cap-marker-execution.v1',plan_sha256=plan_hash,
        qualified=False,model_qualified=False,qualified_timing=False,finite_BEM_passed=False,
        full_accuracy_status='unmeasured',passed=False,measurement_packet_completed=False,jobs=jobs,cgroups=cg)
    try:
        for job in plan['jobs']:
            need(time.monotonic()-start<55,'Insufficient fixed marker work budget')
            owner=output/job['job'];owner.mkdir()
            for n in ('tech.lef','run.tcl'):shutil.copyfile(base/n,owner/n)
            shutil.copyfile(base/(job['job']+'-rules.txt'),owner/'rules.txt')
            shutil.copyfile(base/(job['job']+'.def'),owner/'fixture.def')
            before={p.name:P.sha(p) for p in owner.iterdir()};command=['openroad','-no_init','-exit','run.tcl']
            leaf=dict(job=job['job'],passed=False);timed_out=False
            with (owner/'native.log').open('wb') as stream:
                child=subprocess.Popen(command,cwd=owner,stdout=stream,stderr=subprocess.STDOUT,start_new_session=True)
                try:code=child.wait(timeout=30)
                except subprocess.TimeoutExpired:timed_out=True;os.killpg(child.pid,signal.SIGKILL);code=child.wait()
            try:os.killpg(child.pid,0)
            except ProcessLookupError:reaped=True
            else:os.killpg(child.pid,signal.SIGKILL);raise ValueError('Marker child left process group')
            need(all(P.sha(owner/n)==h for n,h in before.items()),'Copied marker inputs changed')
            leaf.update(argv=command,exit_code=code,timed_out=timed_out,process_tree_reaped=reaped,
                copied_inputs_unchanged=True,copied_input_sha256=before,native_log_sha256=P.sha(owner/'native.log'))
            try:
                need(type(code) is int and code==0 and not timed_out,'Marker OpenROAD exit/timeout failed')
                leaf['values']=parse_leaf(owner,job);leaf['passed']=True
            except (ValueError,OSError) as error:leaf['error']=type(error).__name__+': '+str(error)
            leaf['raw_output_sha256']={n:P.sha(owner/n) for n in ('before.def','after.def','result.spef') if (owner/n).is_file()}
            write(owner/'report.json',leaf);jobs.append(dict(job=job['job'],passed=leaf['passed'],report_sha256=P.sha(owner/'report.json')))
        report['measurement_packet_completed']=len(jobs)==2
        if all(j['passed'] for j in jobs):
            report['analysis']=measurements([json.loads((output/j['job']/'report.json').read_text()) for j in jobs])
    except Exception as error:report['error']=type(error).__name__+': '+str(error)
    report['inputs_unchanged']=verify(base,plan_hash)==plan
    elapsed=time.monotonic()-start;report.update(actual_work_seconds=elapsed,wall_seconds=elapsed,work_budget_passed=elapsed<=90)
    report['passed']=report['measurement_packet_completed'] and report['work_budget_passed'] and report.get('analysis',{}).get('lookup_marker_diagnostic_passed',False)
    write(output/'report.json',report);return report


def main():
    p=argparse.ArgumentParser(description=__doc__);sub=p.add_subparsers(dest='action',required=True)
    s=sub.add_parser('prepare')
    for n in ('baseline','baseline-result','marker-source','model-source','dispatch-source','output'):s.add_argument('--'+n,type=Path,required=True)
    for action in ('verify','proposal','run'):
        s=sub.add_parser(action);s.add_argument('--inputs',type=Path,required=True);s.add_argument('--plan-sha256',required=True)
        if action!='verify':s.add_argument('--output',type=Path,required=True)
        if action=='proposal':s.add_argument('--output-parent',type=Path,required=True)
    a=p.parse_args()
    if a.action=='prepare':result=prepare(a.baseline,a.baseline_result,a.marker_source,a.model_source,a.dispatch_source,a.output)
    elif a.action=='verify':result=dict(verified=bool(verify(a.inputs,a.plan_sha256)),native_executed=False)
    elif a.action=='proposal':result=command_proposal(a.inputs,a.plan_sha256,a.output_parent);write(a.output,result)
    else:result=run(a.inputs,a.plan_sha256,a.output)
    print(json.dumps(result,indent=2));return 2 if a.action=='run' and not result['passed'] else 0


if __name__=='__main__':raise SystemExit(main())
