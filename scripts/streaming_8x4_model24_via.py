"""Fixed six-call source-policy via arithmetic diagnostic; Root GO only.

No FCap/FVM, physical fit, new corner correlation or SPECIALNETS extraction.
The old R90, census, producers, receipts and shared PDK remain unchanged.
"""
import argparse
import ast
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
import streaming_8x4_model24_via_geometry as G
import streaming_8x4_model24_via_observe as O
import streaming_8x4_model24_r_annotations as A
import streaming_8x4_model24_process as SOURCE

P,E,I,S=A.P,A.E,A.I,A.S
ROOT=A.ROOT
need=P.need
write=A.write
NEW=('streaming_8x4_model24_via.py','streaming_8x4_model24_via_geometry.py','streaming_8x4_model24_via_observe.py','streaming_8x4_model24_via_readback.py')
OUTPUT='model24-actual-via-arithmetic-01'
CONTAINER='pinwheel-'+OUTPUT
SOURCE_MANIFEST='5370e196b42ccf9904996dcedc32740eb46c40d3f7f81ff2ce3c7fcee1d92f00'
CENSUS='f4e9a6b4f8204719feefad2417c750013fd5cbff15fcc289b0afc6f9fdca8dd5'
R90='83feadf529ca88c65096462c872e240052f1d6a77bd8d0d032a325f45c3d87eb'
POLICIES=('baseline','source_aligned')
CORNERS=('ITF_MIN','ITF_TYP','ITF_MAX')


def policy():
    return dict(schema='pinwheel.model24-via-arithmetic-policy.v1',maximum_calls=6,seconds_per_leaf=30,
        work_seconds=210,outer_seconds=240,cpus=1,memory_bytes=2147483648,scratch_bytes=134217728,
        extra_swap_bytes=0,pids=128,maximum_output_bytes=16*1024**2,memory_preempt_fraction='.95',
        exact_policies=list(POLICIES),exact_corner_labels=list(CORNERS),nets_per_call=45,ports_per_call=90,
        via_chains_per_call=21,wire_controls_per_call=24,extractor_version='1.0',lef_res=True,no_merge_via_res=True,
        wire_relative_tolerance='.001',via_relative_tolerance='.001',via_absolute_tolerance_ohm='.001',
        all_warnings_fatal=True,no_retry=True,stop_suffix_on_resource_geometry_or_custody_failure=True,
        baseline_expected_ITF_via_alignment_failures=42,reference='ideal uniform sheet legs plus declared independent parallel per-cut RPV/n; no fitted subtraction',
        geometry='actual seven census families, N orientation; explicit zero at every vertex including immediately after each via',
        generated_families_remain_block_dbVia=True,internal_RC_property_operands_observed=False,
        source_aligned_delta='only four actual named VIARES coefficient tokens and three CUT-layer LEF resistance tokens; existing source-sheet policy unchanged',
        numerical_conditioning_stop_preserved=True,physical_fit=False,SPECIALNETS_extraction_qualified=False,
        model_execution_cutoff_utc='2026-10-25T02:38:15Z',Root_full_M_priority_preserved=True,
        contact_spreading_and_independent_cut_physics_qualified=False,foundry_corner_correlation_qualified=False,
        capacitance_qualified=False,full_via_coverage_qualified=False,model_qualified=False,qualified_timing=False)


def jobs():return [dict(index=i,policy=p,corner=c,id=p+'-'+c)for i,(p,c)in enumerate((p,c)for p in POLICIES for c in CORNERS)]


def sources():
    pending=list(NEW)+['streaming_8x4_closure24_resources.py'];done={}
    while pending:
        name=pending.pop()
        if name in done:continue
        path=Path(__file__).with_name(name);done[name]=E.sha(path)
        for node in ast.walk(ast.parse(path.read_text())):
            names=[x.name for x in node.names]if isinstance(node,ast.Import)else([node.module]if isinstance(node,ast.ImportFrom)and node.module else[])
            pending += [n+'.py'for n in names if n.startswith('streaming_')and'.'not in n]
    return dict(sorted(done.items()))


def source_data(inputs):
    owner=inputs/'via-source';need(E.sha(owner/'manifest.json')==SOURCE_MANIFEST,'Pinned via source-data identity differs')
    row=json.loads((owner/'manifest.json').read_text());need(row['openroad_commit']==A.COMMIT and row['source_data_only']is True and row['imported_or_executed']is False,'Source-data scope differs')
    need({p.name for p in owner.iterdir()}=={'manifest.json'}|{r['name']for r in row['sources']},'Via source membership differs')
    for r in row['sources']:
        path=owner/r['name'];need(path.is_file()and not path.is_symlink()and Path(r['name']).name==r['name'],'Aliased source')
        b=path.read_bytes();need(len(b)==r['bytes']and hashlib.sha256(b).hexdigest()==r['sha256']and hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==r['computed_git_blob'],'Source byte/Git blob differs')
        if r['name']=='dbVia.cpp':need(r['observed_git_blob']==r['computed_git_blob']and r['primary_file_API_blob_verified']is True,'Generated-via primary observed Git blob differs')
    return row


def authorities(inputs):
    need(E.sha(inputs/'census.json')==CENSUS and E.sha(inputs/'R90.json')==R90,'Exact final census/R90 authorities differ')
    census=json.loads((inputs/'census.json').read_text());r=json.loads((inputs/'R90.json').read_text())
    need(census['exact_same_target_fresh_view_authority_closed']is True and census['selected_final_ODB_sha256']=='f516ffbca3cd86e5cd214c515ca0be457a91a517dbe715caa47336aec907eee0','Actual final census identity/scope differs')
    need(r['ideal_uniform_sheet_endface_controls_passed']is True and r['absolute_controls']==90 and r['absolute_failures']==0 and r['model_qualified']is False,'Old R90 scoped pass differs')
    need(E.sha(inputs/'rules-original.txt')==A.RETAINED_RULES and E.sha(inputs/'original-tech.lef')==G.OLD.LEF.S.TECH_SHA,'Exact R90 LEF/rules differ')
    return G.definitions(census)


def corner_data(inputs):
    result={}
    for c in CORNERS:
        path=inputs/(c+'.itf');need(E.sha(path)==SOURCE.ITF_SHA[c],'Exact existing ITF corner differs')
        rows=SOURCE.G.parse_itf(path.read_text());stack=SOURCE.G.stack(rows)
        result[c]=dict(sheets={m:stack['metals'][m]['RPSQ']for m in G.METALS},cuts={m:rows[m]['RPV']for m in ('Via1','Via2','Via3')})
    return result


def token_replace(text,changes):
    edits=[]
    for pattern,value,label in changes:
        matches=list(re.finditer(pattern,text,re.M|re.S));need(len(matches)==1,'Ambiguous eligible coefficient: '+label)
        m=matches[0];need(D(value).is_finite()and D(value)>0,'Invalid positive coefficient')
        edits.append((m.start(1),m.end(1),str(value),m[1],label))
    result=text
    for a,b,value,_,_ in sorted(edits,reverse=True):result=result[:a]+value+result[b:]
    # Independent whole-byte witness via fixed literal spans and rederived output.
    pos=0;parts=[]
    for a,b,value,old,label in sorted(edits):parts.extend([text[pos:a],value]);pos=b
    parts.append(text[pos:]);need(''.join(parts)==result,'Token-only reconstruction differs')
    return result,[dict(label=label,old=old,new=value,start=a,end=b)for a,b,value,old,label in sorted(edits)]


def files(inputs):
    defs=authorities(inputs);corners=corner_data(inputs);original=(inputs/'original-tech.lef').read_text();rules=(inputs/'rules-original.txt').read_text()
    need(all(re.search(r'(?m)^9 '+re.escape(n)+r' cuts 1 ',rules)for n in G.NAMED),'Baseline actual named-via predictions changed')
    out={'fixture.def':G.fixture(defs).encode(),'run.tcl':O.tcl().encode()};witness={}
    for j in jobs():
        c,p=j['corner'],j['policy'];data=corners[c];lef,sheet=G.OLD.LEF.local_lef(original,data['sheets']);newrules=rules;edits=[]
        if p=='source_aligned':
            lef,le=token_replace(lef,[(r'^LAYER\s+'+m+r'\s*\n(?:(?!^END\s).)*?^\s*RESISTANCE\s+([0-9.eE+-]+)\s*;',data['cuts'][m],m)for m in ('Via1','Via2','Via3')])
            newrules,repl=token_replace(rules,[(r'^([0-9.eE+-]+) '+re.escape(n)+r' cuts 1 ',data['cuts'][defs[n]['layers'][1]],n)for n in G.NAMED]);edits=[*le,*repl]
        out[j['id']+'.lef']=lef.encode();out[j['id']+'.rules']=newrules.encode();witness[j['id']]=dict(sheet_policy=sheet,eligible_token_edits=edits,
            actual_CUT_R={m:data['cuts'][m]if p=='source_aligned'else'20'for m in ('Via1','Via2','Via3')},all_other_rule_and_LEF_bytes_unchanged=True)
        G.geometry(out['fixture.def'].decode(),lef,defs)
    return out,witness


def prepare(prior_inputs,census,r90,intake,output):
    A.verify(prior_inputs,E.sha(prior_inputs/'plan.json'));need(not output.exists()and output.parent.is_dir(),'Fresh owned preparation required');output.mkdir()
    for n in ('original-tech.lef',*[(c+'.itf')for c in CORNERS]):shutil.copyfile(prior_inputs/n,output/n)
    shutil.copyfile(prior_inputs/'rules.txt',output/'rules-original.txt');shutil.copyfile(census,output/'census.json');shutil.copyfile(r90,output/'R90.json');shutil.copytree(intake,output/'via-source')
    expected,witness=files(output)
    for n,data in expected.items():(output/n).write_bytes(data)
    defs=authorities(output);row=dict(schema='pinwheel.model24-via-arithmetic-plan.v1',policy=policy(),jobs=jobs(),definitions=defs,
        fixture_rows=G.cases(defs),corner_data=corner_data(output),token_witnesses=witness,source_intake=source_data(output),
        R90_sha256=R90,census_sha256=CENSUS,producer_sha256=sources(),files=I.W.input_files(output),root_go_required=True,native_executed=False,model_qualified=False,qualified_timing=False)
    write(output/'plan.json',row);verify(output,E.sha(output/'plan.json'));return row


def verify(inputs,digest):
    need(E.sha(inputs/'plan.json')==digest,'Via plan identity differs');row=json.loads((inputs/'plan.json').read_text());expected,witness=files(inputs);defs=authorities(inputs)
    need(all((inputs/n).read_bytes()==data for n,data in expected.items()),'Exact selected fixture/Tcl/LEF/rule input differs')
    need(all(r['kind']=='file'for r in I.W.input_files(inputs).values()),'Input symlinks forbidden')
    need(row==dict(schema='pinwheel.model24-via-arithmetic-plan.v1',policy=policy(),jobs=jobs(),definitions=defs,fixture_rows=G.cases(defs),corner_data=corner_data(inputs),token_witnesses=witness,source_intake=source_data(inputs),R90_sha256=R90,census_sha256=CENSUS,producer_sha256=sources(),files=I.W.input_files(inputs),root_go_required=True,native_executed=False,model_qualified=False,qualified_timing=False),'Complete plan/source/protocol/input membership differs')
    return row


def analyze(values,plan,job):
    defs=plan['definitions'];corner=plan['corner_data'][job['corner']];aligned=job['policy']=='source_aligned';audits=[]
    need(set(values)=={r['name']for r in G.cases(defs)},'Exact complete SPEF net membership differs')
    for r in G.cases(defs):
        wire=sum(D(corner['sheets'][m])*r['length_um']*1000/w for m,w in zip(r['layers'],r['widths']));actual=D(values[r['name']]['R_ohm']);via=D(0);itf=D(0)
        if r['family']:
            cut=defs[r['family']]['layers'][1];itf=D(corner['cuts'][cut])/r['cut_count'];via=itf if aligned else(D(20)/r['cut_count']if r['pg']else D(9))
        target=wire+via;relative=abs(actual/target-1);passed=relative<=D('.001');residual=actual-wire
        via_pass=not r['family']or abs(residual-via)<=max(D('.001'),abs(via)*D('.001'))
        alignment=not r['family']or abs(residual-itf)<=max(D('.001'),abs(itf)*D('.001'))
        audits.append(dict(name=r['name'],family=r['family'],actual_R_ohm=str(actual),source_policy_wire_R_ohm=str(wire),source_policy_via_R_ohm=str(via),ITF_ideal_via_R_ohm=str(itf),source_policy_total_R_ohm=str(target),relative_total_error=str(relative),analytic_via_residual_R_ohm=str(residual),absolute_total_passed=passed,source_policy_via_passed=via_pass,ITF_via_alignment_passed=alignment))
    return dict(audits=audits,source_policy_arithmetic_passed=all(r['absolute_total_passed']and r['source_policy_via_passed']for r in audits),
        ITF_via_alignment_failures=sum(not r['ITF_via_alignment_passed']for r in audits),no_fitted_subtraction=True,model_qualified=False)


def parse_leaf(owner,plan,job):
    raw=(owner/'native.log').read_text();need(not re.search(r'(?im)\b(?:warning|warn|error|fatal)\b|segmentation fault|killed|timeout',raw),'Native warning/failure')
    m=re.findall(r'^MODEL24_VIA_VERSION_BEGIN\n(.*?)^MODEL24_VIA_VERSION_END$',raw,re.M|re.S);need(len(m)==1 and raw.count('MODEL24_VIA_VERSION_BEGIN')==raw.count('MODEL24_VIA_VERSION_END')==1,'Actual version missing/duplicate')
    h=[x for x in re.findall(r'[0-9a-f]+',m[0])if len(x)>=40];need(h and set(h)=={A.COMMIT},'Actual full OpenROAD revision differs')
    need(raw.count('MODEL24_VIA_TERMINAL')==1 and raw.index('MODEL24_VIA_VERSION_END')<raw.index('MODEL24_VIA_TERMINAL'),'Missing/early terminal')
    need((owner/'before.def').read_bytes()==(owner/'after.def').read_bytes(),'Complete pre/post DEF changed')
    geometry=G.geometry((owner/'before.def').read_text(),(owner/'tech.lef').read_text(),plan['definitions']);corner=plan['corner_data'][job['corner']]
    cuts=plan['token_witnesses'][job['id']]['actual_CUT_R'];native=O.pair((owner/'before.tsv').read_text(),(owner/'after.tsv').read_text(),plan['definitions'],corner['sheets'],cuts)
    values=G.OLD.C.parse_spef((owner/'result.spef').read_text(),{r['name']for r in G.cases(plan['definitions'])})
    return dict(geometry=geometry,native=native,values=values,**analyze(values,plan,job))


def copied(job):return {'tech.lef':job['id']+'.lef','rules.txt':job['id']+'.rules','fixture.def':'fixture.def','run.tcl':'run.tcl'}


def leaf(inputs,digest,plan,job,owner):
    owner.mkdir()
    for dst,src in copied(job).items():shutil.copyfile(inputs/src,owner/dst)
    exe=shutil.which('openroad');need(exe and E.sha(Path(exe).resolve())==A.OPENROAD_SHA,'Pinned OpenROAD executable differs')
    start=time.monotonic();env=dict(PATH=os.environ['PATH'],HOME='/tmp',LANG='C',LC_ALL='C',TZ='UTC',OMP_NUM_THREADS='1',OMP_DYNAMIC='FALSE');child=None
    row=dict(schema='pinwheel.model24-via-arithmetic-leaf.v1',plan_sha256=digest,job=job,argv=[exe,'-no_init','-exit','run.tcl'],environment=env,openroad_sha256=A.OPENROAD_SHA,
        cgroups=A.cgroups(),cgroup_before=I.cgroup_snapshot(),exit_code=None,timed_out=False,memory_guard_triggered=False,output_guard_triggered=False,process_tree_reaped=False,native_executed=False,measurement_completed=False,analysis=None,resource_feasible=False,passed=False,model_qualified=False,qualified_timing=False)
    peak=row['cgroup_before']['memory_current']
    try:
        with (owner/'native.log').open('xb')as stream:
            child=subprocess.Popen(row['argv'],cwd=owner,env=env,stdout=stream,stderr=subprocess.STDOUT,start_new_session=True);row['native_executed']=True
            while child.poll()is None:
                current=I.cgroup_snapshot()['memory_current'];peak=max(peak,current);size=sum(p.stat().st_size for p in owner.rglob('*')if p.is_file()and not p.is_symlink())
                if time.monotonic()-start>=30 or current>=2147483648*95//100 or size>policy()['maximum_output_bytes']:
                    row['timed_out']=time.monotonic()-start>=30;row['memory_guard_triggered']=current>=2147483648*95//100;row['output_guard_triggered']=size>policy()['maximum_output_bytes'];os.killpg(child.pid,signal.SIGKILL);break
                try:child.wait(timeout=.25)
                except subprocess.TimeoutExpired:pass
            row['exit_code']=child.wait(timeout=2)
        try:os.killpg(child.pid,0)
        except ProcessLookupError:row['process_tree_reaped']=True
        else:os.killpg(child.pid,signal.SIGKILL);raise ValueError('Child process group remains live')
        need(row['exit_code']==0 and not row['timed_out']and not row['memory_guard_triggered']and not row['output_guard_triggered'],'Native resource/exit failed')
        row['analysis']=parse_leaf(owner,plan,job);row['measurement_completed']=True
    except BaseException as e:row['error']=type(e).__name__+': '+str(e)
    finally:
        if child is not None and child.poll()is None:os.killpg(child.pid,signal.SIGKILL);child.wait(timeout=2)
        row['inputs_sources_unchanged']=verify(inputs,digest)==plan;row['openroad_unchanged']=E.sha(Path(exe).resolve())==A.OPENROAD_SHA
        row['copied_inputs_unchanged']=all((owner/d).read_bytes()==(inputs/s).read_bytes()for d,s in copied(job).items());row['actual_work_seconds']=time.monotonic()-start;row['work_budget_passed']=row['actual_work_seconds']<=40
        row['cgroup_after']=I.cgroup_snapshot();row['cgroup_counter_deltas']=I.counters(row['cgroup_before'],row['cgroup_after']);row['maximum_polled_memory_current']=peak
        row['output_inventory']=A.owned_inventory(owner);row['native_log_sha256']=E.sha(owner/'native.log')if(owner/'native.log').exists()else None
        row['resource_feasible']=S.N.resource_observation(row)and row['work_budget_passed']and sum(x['bytes']for x in row['output_inventory'].values())<=policy()['maximum_output_bytes']
        row['passed']=row['measurement_completed']and row['analysis']['source_policy_arithmetic_passed']and row['resource_feasible']and row['inputs_sources_unchanged']and row['copied_inputs_unchanged']and row['openroad_unchanged'];write(owner/'report.json',row)
    return row


def packet_state(rows,duration):
    need(len(rows)<=6 and [r['job']for r in rows]==jobs()[:len(rows)],'Exact ordered six-call membership differs')
    complete=len(rows)==6 and all(r['measurement_completed']for r in rows);baseline=[r for r in rows if r['job']['policy']=='baseline'];candidate=[r for r in rows if r['job']['policy']=='source_aligned']
    failures=sum(r['analysis']['ITF_via_alignment_failures']for r in baseline if r['analysis']);candidate_failures=sum(r['analysis']['ITF_via_alignment_failures']for r in candidate if r['analysis'])
    passed=complete and all(r['passed']for r in rows)and duration<=210 and failures==42 and candidate_failures==0
    return dict(measurement_packet_completed=complete,baseline_ITF_via_alignment_failures=failures,source_aligned_ITF_via_alignment_failures=candidate_failures,
        expected_baseline_mismatches_preserved=complete and failures==42,source_policy_diagnostic_passed=passed,passed=passed)


def run(inputs,digest,output):
    start=time.monotonic();plan=verify(inputs,digest);need(not output.exists()and output.parent.is_dir()and output.name==OUTPUT,'Fresh owned output required');output.mkdir();rows=[]
    result=dict(schema='pinwheel.model24-via-arithmetic-execution.v1',plan_sha256=digest,policy=policy(),jobs=rows,passed=False,model_qualified=False,qualified_timing=False)
    try:
        for job in jobs():
            need(time.monotonic()-start<=170,'Insufficient fixed next-call/closeout budget');r=leaf(inputs,digest,plan,job,output/job['id']);rows.append(dict(job=job,report_sha256=E.sha(output/job['id']/'report.json'),**{k:r[k]for k in ('passed','resource_feasible','measurement_completed')}))
            need(r['resource_feasible']and r['measurement_completed']and r['inputs_sources_unchanged']and r['copied_inputs_unchanged']and r['openroad_unchanged'],'Resource/geometry/custody failure stops suffix')
    except BaseException as e:result['error']=type(e).__name__+': '+str(e)
    full=[json.loads((output/r['job']['id']/'report.json').read_text())for r in rows];unchanged=verify(inputs,digest)==plan;duration=time.monotonic()-start
    result.update(actual_work_seconds=duration,work_budget_passed=duration<=210,inputs_sources_unchanged=unchanged,**packet_state(full,duration));result['passed']=result['passed']and result['inputs_sources_unchanged'];write(output/'report.json',result);return result


def proposal(inputs,digest,parent,require_fresh=True):
    plan=verify(inputs,digest);need(parent.is_dir()and(not require_fresh or not(parent/OUTPUT).exists()),'Fresh output parent required')
    argv=['docker','run','--name',CONTAINER,'--rm','--pull','never','--network','none','--read-only','--cpus','1','--memory','2g','--memory-swap','2g','--pids-limit','128','--tmpfs','/tmp:rw,nosuid,noexec,size=134217728',
        '--mount',f'type=bind,src={Path(__file__).resolve().parent},dst=/model24-source,readonly','--mount',f'type=bind,src={inputs.resolve()},dst=/model24-inputs,readonly','--mount',f'type=bind,src={parent.resolve()},dst=/model24-output-parent',
        '--entrypoint',S.N.C.PYTHON,S.N.C.IMAGE,'-I','-B','/model24-source/'+NEW[0],'run','--inputs','/model24-inputs','--plan-sha256',digest,'--output','/model24-output-parent/'+OUTPUT]
    return dict(schema='pinwheel.model24-via-arithmetic-command.v1',root_go_required=True,admitted=False,native_executed=False,model_qualified=False,qualified_timing=False,plan_path=str((inputs/'plan.json').resolve()),plan_sha256=digest,producer_sha256=plan['producer_sha256'],timeout_seconds=240,policy=policy(),container_name=CONTAINER,argv=argv)


def main():
    q=argparse.ArgumentParser(description=__doc__);sub=q.add_subparsers(dest='action',required=True);p=sub.add_parser('prepare')
    for n in ('prior-inputs','census','R90','intake','output'):p.add_argument('--'+n,type=Path,required=True)
    for action in ('verify','proposal','run'):
        p=sub.add_parser(action);p.add_argument('--inputs',type=Path,required=True);p.add_argument('--plan-sha256',required=True)
        if action!='verify':p.add_argument('--output',type=Path,required=True)
        if action=='proposal':p.add_argument('--output-parent',type=Path,required=True)
    a=q.parse_args()
    if a.action=='prepare':prepare(a.prior_inputs,a.census,a.R90,a.intake,a.output);return 0
    if a.action=='verify':verify(a.inputs,a.plan_sha256);return 0
    if a.action=='proposal':write(a.output,proposal(a.inputs,a.plan_sha256,a.output_parent));return 0
    return 0 if run(a.inputs,a.plan_sha256,a.output)['passed']else 2
if __name__=='__main__':raise SystemExit(main())
