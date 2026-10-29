"""Three fixed source-corner ideal-endface R controls; Root alone admits Native.

This checks a declared uniform-sheet reference and consumer endpoint convention.
It cannot qualify arbitrary terminals, vias, whole-route R, C, process or timing.
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
import streaming_8x4_model24_r_endpoint_geometry as G
import streaming_8x4_model24_smoke as S
import streaming_8x4_model24_process as SOURCE

P,E,I=S.P,S.E,S.I
ROOT=S.ROOT
write=S.write
NEW=('streaming_8x4_model24_r_endpoint.py','streaming_8x4_model24_r_endpoint_geometry.py','streaming_8x4_model24_r_endpoint_readback.py')
OUTPUT='model24-r-endpoint-01';CONTAINER='pinwheel-'+OUTPUT
INTAKE='5671eccd32df1d2407c26dac7f61bc6a9f86dcc932a222086a4107c7e90b03d8'
HISTORY='9e4394463fb1a1ac7f12e53410826968a5cac35248bc59c4e3ccd165db57c7b4'
OPENROAD_SHA='b2159d4a99a9b236a6e95bbf6efc88bcfd2b843df273e97f169b456bc3b0453b'
COMMIT='dcf36133a369abc8f3c5e5738cd4d82e4903c0e0'
RETAINED_RULES='bf2af2235b102d7bb58fe782d8d8b41a64cb3efde46593562314a499e9c4a612'


def policy():
    return dict(schema='pinwheel.model24-r-endpoint-policy.v1',calls=3,corners=list(G.CORNERS),nets_per_call=30,
        ports_per_call=60,layers=list(G.METALS),width_multiples=[1,2],lengths_um=list(G.LENGTHS),
        reference='Rsheet*L/W: uniform isotropic sheet, ideal complete end-face contacts, explicit zero end extensions',
        resistance_relative_tolerance='0.001',no_fitted_subtraction=True,extractor_version='1.0',lef_res=True,
        geometry_witness='complete actual DEF plus native global BPin rectangles, layer/default/NDR widths and dbWire.getLength=L-W',
        contact_spreading_and_via_physics_qualified=False,arbitrary_route_R_qualified=False,capacitance_qualified=False,
        source_corner_policy='exact merged ITF_MIN/TYP/MAX RPSQ; no invented geometry/cell-corner correlation',
        leaf_seconds=30,leaf_closeout_seconds=40,work_seconds=120,outer_seconds=180,cpu=1,memory_bytes=2147483648,
        pids=128,tmpfs_bytes=134217728,maximum_output_bytes=134217728,extra_swap=False,
        original_R26_absolute_failures=123,original_R26_absolute_controls=126,original_via_passes=30,
        old_absolute_audit_remains_failed=True,model_qualified=False,qualified_timing=False)


def sources():
    pending=list(NEW)+['streaming_8x4_closure24_resources.py'];done={}
    while pending:
        name=pending.pop()
        if name in done:continue
        path=Path(__file__).with_name(name);done[name]=E.sha(path)
        for node in ast.walk(ast.parse(path.read_text())):
            names=[n.name for n in node.names] if isinstance(node,ast.Import) else ([node.module] if isinstance(node,ast.ImportFrom) and node.module else [])
            pending += [n+'.py' for n in names if n.startswith('streaming_') and '.' not in n]
    return dict(sorted(done.items()))


def source_intake(inputs):
    owner=inputs/'endpoint-source';path=owner/'manifest.json';P.need(E.sha(path)==INTAKE,'Exact endpoint source intake differs')
    row=json.loads(path.read_text());P.need(row['openroad_commit']==COMMIT and row['source_data_only'] is True and row['imported_or_executed'] is False,'Endpoint primary source scope differs')
    P.need({p.name for p in owner.iterdir()}=={'manifest.json'}|{r['name'] for r in row['sources']},'Endpoint source membership differs')
    for r in row['sources']:
        p=owner/r['name'];P.need(p.is_file() and not p.is_symlink() and Path(r['name']).name==r['name'],'Aliased endpoint source')
        b=p.read_bytes();P.need(len(b)==r['bytes'] and hashlib.sha256(b).hexdigest()==r['sha256'] and hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==r['computed_git_blob'],'Endpoint source bytes/blob differ')
    return row


def tcl():
    return '''puts "MODEL24_R_VERSION_BEGIN"
set version [ord::openroad_version]
puts $version
puts "MODEL24_R_VERSION_END"
read_lef tech.lef
read_def fixture.def
proc endpoint_snapshot {path} {
    set f [open $path w]
    set b [ord::get_db_block]
    set tech [[ord::get_db] getTech]
    puts $f [join [list BLOCK [$tech getDbUnitsPerMicron] [llength [$b getInsts]] [llength [$b getITerms]] [llength [$b getNets]] [llength [$b getBTerms]] [llength [$b getNonDefaultRules]]] "\t"]
    foreach m {Metal1 Metal2 Metal3 Metal4 TopMetal1} {
        set l [$tech findLayer $m]
        puts $f [join [list LAYER $m [$l getWidth] [$l getDirection] [$l getResistance]] "\t"]
    }
    foreach ndr [$b getNonDefaultRules] {
        foreach m {Metal1 Metal2 Metal3 Metal4 TopMetal1} {
            set lr [$ndr getLayerRule [$tech findLayer $m]]
            puts $f [join [list NDR [$ndr getName] $m [$lr getWidth] [$lr getSpacing]] "\t"]
        }
    }
    foreach net [$b getNets] {
        set rule [$net getNonDefaultRule];set name -
        if {$rule ne "NULL"} {set name [$rule getName]}
        set wire [$net getWire]
        if {$wire eq "NULL"} {error "Missing actual routed wire"}
        puts $f [join [list NET [$net getName] [$wire getLength] $name [llength [$net getITerms]] [llength [$net getBTerms]] [llength [$net getSWires]] [$net isSpecial] [$net getSigType]] "\t"]
    }
    foreach term [$b getBTerms] {
        puts $f [join [list BTERM [$term getName] [[$term getNet] getName] [$term getIoType] [$term getSigType] [llength [$term getBPins]]] "\t"]
        foreach pin [$term getBPins] {
            foreach box [$pin getBoxes] {
                puts $f [join [list BPIN [$term getName] [[$box getTechLayer] getName] [$box xMin] [$box yMin] [$box xMax] [$box yMax] [$pin getPlacementStatus]] "\t"]
            }
        }
    }
    close $f
}
endpoint_snapshot before.tsv
write_def before.def
define_process_corner -ext_model_index 0 endpoint
extract_parasitics -lef_res -ext_model_file rules.txt -no_merge_via_res -version 1.0
write_spef result.spef
write_def after.def
endpoint_snapshot after.tsv
puts "MODEL24_R_TERMINAL"
exit
'''


def corner_data(inputs):
    result={}
    for c in G.CORNERS:
        path=inputs/(c+'.itf');P.need(E.sha(path)==SOURCE.ITF_SHA[c],'Exact source ITF corner differs')
        stack=SOURCE.G.stack(SOURCE.G.parse_itf(path.read_text()))
        result[c]={m:stack['metals'][m]['RPSQ'] for m in G.METALS}
    return result


def files(inputs):
    original=(inputs/'original-tech.lef').read_text();P.need(G.LEF.restore_original(original)==original,'Exact original technology required')
    P.need(E.sha(inputs/'rules.txt')==RETAINED_RULES,'Exact retained unqualified TYP C table differs')
    result={'fixture.def':G.fixture().encode(),'run.tcl':tcl().encode()};witnesses={}
    for c,sheets in corner_data(inputs).items():
        lef,witnesses[c]=G.LEF.local_lef(original,sheets);result[c+'-local.lef']=lef.encode()
    return result,witnesses


def historical(inputs):
    path=inputs/'historical-R26-closeout.json';P.need(E.sha(path)==HISTORY,'Exact old R26 failure authority differs')
    old=json.loads(path.read_text());a=old['raw_readback']['analysis']
    P.need(old['resource_custody_closed'] is True and a['new_absolute_wire_controls']==126 and a['new_absolute_wire_failures']==123
        and a['original_17net_absolute_wire_failures']==72 and a['original_17net_via_difference_passes']==30,'Old absolute failures/counts must remain preserved')
    return dict(sha256=HISTORY,new_absolute_wire_controls=126,new_absolute_wire_failures=123,original_17net_wire_failures=72,original_via_passes=30,old_absolute_audit_passed=False)


def prepare(process_intake,tech_lef,retained_rules,endpoint_intake,history,output):
    P.need(not output.exists() and output.parent.is_dir() and E.sha(process_intake/'manifest.json')==SOURCE.INTAKE_MANIFEST,'Fresh endpoint preparation/exact process intake required');values,_=SOURCE.P.verify_intake(process_intake);output.mkdir()
    for c in G.CORNERS:(output/(c+'.itf')).write_text(values['itf_'+c[4:].lower()])
    shutil.copyfile(tech_lef,output/'original-tech.lef');shutil.copyfile(retained_rules,output/'rules.txt');shutil.copyfile(history,output/'historical-R26-closeout.json');shutil.copytree(endpoint_intake,output/'endpoint-source')
    expected,witnesses=files(output)
    for n,b in expected.items():(output/n).write_bytes(b)
    row=dict(schema='pinwheel.model24-r-endpoint-plan.v1',policy=policy(),corner_sheet_R=corner_data(output),fixture_rows=G.cases(),
        local_LEF_witnesses=witnesses,source_intake=source_intake(output),historical_failures=historical(output),
        retained_rules_sha256=E.sha(output/'rules.txt'),producer_sha256=sources(),files=I.W.input_files(output),
        root_go_required=True,native_executed=False,model_qualified=False,qualified_timing=False)
    write(output/'plan.json',row);verify(output,E.sha(output/'plan.json'));return row


def verify(inputs,digest):
    P.need(E.sha(inputs/'plan.json')==digest,'Endpoint plan identity differs');row=json.loads((inputs/'plan.json').read_text());expected,witnesses=files(inputs)
    P.need(all((inputs/n).read_bytes()==b and not(inputs/n).is_symlink() for n,b in expected.items()),'Endpoint exact fixture/LEF/Tcl bytes differ')
    # The retained unqualified C table is a fixed dependency for the software
    # extractor; no capacitance accuracy is asserted by this R-only reference.
    P.need(all(r['kind']=='file' for r in I.W.input_files(inputs).values()),'Endpoint input aliases forbidden')
    P.need(row['schema']=='pinwheel.model24-r-endpoint-plan.v1' and row['policy']==policy() and row['corner_sheet_R']==corner_data(inputs)
        and row['fixture_rows']==G.cases() and row['local_LEF_witnesses']==witnesses and row['source_intake']==source_intake(inputs)
        and row['historical_failures']==historical(inputs) and row['retained_rules_sha256']==E.sha(inputs/'rules.txt')
        and row['producer_sha256']==sources() and row['files']==I.W.input_files(inputs) and row['root_go_required'] is True
        and all(row[k] is False for k in ('native_executed','model_qualified','qualified_timing')),'Endpoint complete source/input/reference/scope differs')
    G.geometry((inputs/'fixture.def').read_text());return row


def native_geometry(text,sheets):
    rows=[line.split('\t') for line in text.splitlines()];expected=[['BLOCK','1000','0','0','30','60','1']]
    for m in G.METALS:expected.append(['LAYER',m,str(int(D(G.WIDTHS[m])*1000)),G.DIRECTIONS[m],str(sheets[m])])
    for m in G.METALS:
        w=str(int(D(G.WIDTHS[m])*2000));expected.append(['NDR','WIDE',m,w,w])
    for r in G.cases():expected.append(['NET',r['name'],str(r['native_shape_length_minus_width_dbu']),r['ndr'] or '-','0','2','0','0','SIGNAL'])
    for r in G.cases():
        for i,(suffix,direction,point) in enumerate((('A','INPUT',r['start']),('B','OUTPUT',r['end']))):
            n=r['name']+'_'+suffix;box=r['contact_boxes'][i];glob=[box[0]+point[0],box[1]+point[1],box[2]+point[0],box[3]+point[1]]
            expected.append(['BTERM',n,r['name'],direction,'SIGNAL','1']);expected.append(['BPIN',n,r['layer'],*map(str,glob),'FIRM'])
    # dbSet iteration order is not an engineering property. Exact typed row
    # membership, duplicates and all numeric fields are independently checked.
    def normal(row):
        v=list(row)
        if v[0]=='LAYER' and len(v)==5:v[4]=str(D(v[4]).normalize())
        return v
    P.need(sorted(map(normal,rows))==sorted(map(normal,expected)),'Actual complete native geometry/width/end-face/extent inventory differs')
    return dict(nets=30,ports=60,layers=5,wide_layer_rules=5,components=0,ITerms=0,special_wires=0,
        exact_native_zero_extension_length_minus_width_checked=True,all_global_full_endface_contacts_checked=True,all_rows=rows)


def parse_leaf(owner,sheets):
    raw=(owner/'native.log').read_text();P.need(not re.search(r'(?im)\b(?:warning|warn|error|fatal)\b|segmentation fault|killed|timeout',raw),'Endpoint Native warning/error')
    matches=re.findall(r'^MODEL24_R_VERSION_BEGIN\n(.*?)^MODEL24_R_VERSION_END$',raw,re.M|re.S)
    P.need(len(matches)==1 and raw.count('MODEL24_R_VERSION_BEGIN')==raw.count('MODEL24_R_VERSION_END')==1,'Endpoint version missing/duplicated')
    hashes=[v for v in re.findall(r'[0-9a-f]+',matches[0]) if len(v)>=40];P.need(hashes and set(hashes)=={COMMIT},'Endpoint full actual revision differs')
    P.need(raw.count('MODEL24_R_TERMINAL')==1 and raw.index('MODEL24_R_VERSION_END')<raw.index('MODEL24_R_TERMINAL'),'Endpoint terminal missing/early')
    P.need((owner/'before.def').read_bytes()==(owner/'after.def').read_bytes() and (owner/'before.tsv').read_bytes()==(owner/'after.tsv').read_bytes(),'Endpoint extraction changed actual geometry')
    physical=G.geometry((owner/'before.def').read_text());native=native_geometry((owner/'before.tsv').read_text(),sheets)
    values=G.C.parse_spef((owner/'result.spef').read_text(),{r['name'] for r in G.cases()});targets=G.resistance(sheets);audits=[]
    for n,target in targets.items():
        actual=D(values[n]['R_ohm']);difference=abs(actual/target-1)
        audits.append(dict(name=n,actual_R_ohm=str(actual),ideal_uniform_sheet_R_ohm=str(target),relative_difference=str(difference),passed=difference<=D('.001')))
    return dict(physical_geometry=physical,native_geometry=native,values=values,absolute_audits=audits,
        ideal_endface_controls_passed=all(r['passed'] for r in audits),model_qualified=False,qualified_timing=False)


def owned_inventory(owner):
    result={}
    for p in sorted(owner.rglob('*')):
        P.need(not p.is_symlink(),'Endpoint output aliases forbidden')
        if p.is_file() and p!=owner/'report.json':result[str(p.relative_to(owner))]=dict(bytes=p.stat().st_size,sha256=E.sha(p))
    return result


def cgroups():
    b=Path('/sys/fs/cgroup');r={n.replace('.','_'):(b/n).read_text().strip() for n in ('cpu.max','memory.max','memory.swap.max','pids.max')};cpu=r['cpu_max'].split()
    P.need(len(cpu)==2 and all(v.isdigit() for v in cpu) and 0<int(cpu[0])<=int(cpu[1]) and r['memory_max']=='2147483648' and r['memory_swap_max']=='0' and r['pids_max']=='128','Endpoint actual cgroup policy differs');return r


def copied(inputs,corner):return {'tech.lef':corner+'-local.lef','fixture.def':'fixture.def','run.tcl':'run.tcl','rules.txt':'rules.txt'}


def leaf(inputs,digest,plan,corner,owner):
    owner.mkdir()
    for dst,src in copied(inputs,corner).items():shutil.copyfile(inputs/src,owner/dst)
    exe=shutil.which('openroad');P.need(exe and E.sha(Path(exe).resolve())==OPENROAD_SHA,'Exact observed OpenROAD executable differs')
    start=time.monotonic();env=dict(PATH=os.environ['PATH'],HOME='/tmp',LANG='C',LC_ALL='C',TZ='UTC',OMP_NUM_THREADS='1',OMP_DYNAMIC='FALSE');child=None
    row=dict(schema='pinwheel.model24-r-endpoint-leaf.v1',plan_sha256=digest,corner=corner,argv=[exe,'-no_init','-exit','run.tcl'],environment=env,openroad_sha256=OPENROAD_SHA,
        cgroups=cgroups(),cgroup_before=I.cgroup_snapshot(),exit_code=None,timed_out=False,memory_guard_triggered=False,output_guard_triggered=False,
        process_tree_reaped=False,native_executed=False,measurement_completed=False,analysis=None,resource_feasible=False,passed=False,model_qualified=False,qualified_timing=False)
    peak=row['cgroup_before']['memory_current']
    try:
        with (owner/'native.log').open('xb') as stream:
            child=subprocess.Popen(row['argv'],cwd=owner,env=env,stdout=stream,stderr=subprocess.STDOUT,start_new_session=True);row['native_executed']=True
            while child.poll() is None:
                current=I.cgroup_snapshot()['memory_current'];peak=max(peak,current);size=sum(p.stat().st_size for p in owner.rglob('*') if p.is_file() and not p.is_symlink())
                if time.monotonic()-start>=30 or current>=2147483648*95//100 or size>policy()['maximum_output_bytes']:
                    row['timed_out']=time.monotonic()-start>=30;row['memory_guard_triggered']=current>=2147483648*95//100;row['output_guard_triggered']=size>policy()['maximum_output_bytes'];os.killpg(child.pid,signal.SIGKILL);break
                try:child.wait(timeout=.25)
                except subprocess.TimeoutExpired:pass
            row['exit_code']=child.wait(timeout=2)
        try:os.killpg(child.pid,0)
        except ProcessLookupError:row['process_tree_reaped']=True
        else:os.killpg(child.pid,signal.SIGKILL);raise ValueError('Endpoint child process group remains live')
        P.need(row['exit_code']==0 and not row['timed_out'] and not row['memory_guard_triggered'] and not row['output_guard_triggered'],'Endpoint native resource/exit failed')
        row['analysis']=parse_leaf(owner,plan['corner_sheet_R'][corner]);row['measurement_completed']=True
    except BaseException as e:row['error']=type(e).__name__+': '+str(e)
    finally:
        if child is not None and child.poll() is None:os.killpg(child.pid,signal.SIGKILL);child.wait(timeout=2)
        row['inputs_sources_unchanged']=verify(inputs,digest)==plan;row['openroad_unchanged']=E.sha(Path(exe).resolve())==OPENROAD_SHA
        row['copied_inputs_unchanged']=all((owner/d).read_bytes()==(inputs/s).read_bytes() for d,s in copied(inputs,corner).items())
        row['actual_work_seconds']=time.monotonic()-start;row['work_budget_passed']=row['actual_work_seconds']<=40
        row['cgroup_after']=I.cgroup_snapshot();row['cgroup_counter_deltas']=I.counters(row['cgroup_before'],row['cgroup_after']);row['maximum_polled_memory_current']=peak
        row['output_inventory']=owned_inventory(owner);row['native_log_sha256']=E.sha(owner/'native.log') if(owner/'native.log').exists() else None
        row['resource_feasible']=S.N.resource_observation(row) and row['work_budget_passed'] and sum(r['bytes'] for r in row['output_inventory'].values())<=policy()['maximum_output_bytes']
        row['passed']=row['measurement_completed'] and row['analysis']['ideal_endface_controls_passed'] and row['resource_feasible'] and row['inputs_sources_unchanged'] and row['copied_inputs_unchanged'] and row['openroad_unchanged'];write(owner/'report.json',row)
    return row


def run(inputs,digest,output):
    start=time.monotonic();plan=verify(inputs,digest);P.need(not output.exists() and output.parent.is_dir() and output.name==OUTPUT,'Fresh endpoint output required');output.mkdir();jobs=[]
    row=dict(schema='pinwheel.model24-r-endpoint-execution.v1',plan_sha256=digest,policy=policy(),jobs=jobs,passed=False,measurement_packet_completed=False,model_qualified=False,qualified_timing=False)
    try:
        for c in G.CORNERS:
            P.need(time.monotonic()-start<=80,'Insufficient fixed next-call budget');owner=output/c;r=leaf(inputs,digest,plan,c,owner)
            jobs.append(dict(corner=c,passed=r['passed'],resource_feasible=r['resource_feasible'],measurement_completed=r['measurement_completed'],report_sha256=E.sha(owner/'report.json')))
            P.need(r['resource_feasible'] and r['measurement_completed'] and r['inputs_sources_unchanged'] and r['copied_inputs_unchanged'] and r['openroad_unchanged'],'Endpoint resource/geometry/custody failure stops suffix')
    except BaseException as e:row['error']=type(e).__name__+': '+str(e)
    row['actual_work_seconds']=time.monotonic()-start;row['work_budget_passed']=row['actual_work_seconds']<=120;row['measurement_packet_completed']=len(jobs)==3 and all(r['measurement_completed'] for r in jobs)
    row['inputs_sources_unchanged']=verify(inputs,digest)==plan;row['passed']=row['measurement_packet_completed'] and all(r['passed'] for r in jobs) and row['work_budget_passed'] and row['inputs_sources_unchanged'];write(output/'report.json',row);return row


def proposal(inputs,digest,parent,require_fresh=True):
    plan=verify(inputs,digest);P.need(parent.is_dir() and (not require_fresh or not(parent/OUTPUT).exists()),'Fresh endpoint output required')
    argv=['docker','run','--name',CONTAINER,'--rm','--pull','never','--network','none','--read-only','--cpus','1','--memory','2g','--memory-swap','2g','--pids-limit','128','--tmpfs','/tmp:rw,nosuid,noexec,size=134217728',
        '--mount',f'type=bind,src={Path(__file__).resolve().parent},dst=/model24-source,readonly','--mount',f'type=bind,src={inputs.resolve()},dst=/model24-inputs,readonly','--mount',f'type=bind,src={parent.resolve()},dst=/model24-output-parent',
        '--entrypoint',S.N.C.PYTHON,S.N.C.IMAGE,'-I','-B','/model24-source/'+NEW[0],'run','--inputs','/model24-inputs','--plan-sha256',digest,'--output','/model24-output-parent/'+OUTPUT]
    return dict(schema='pinwheel.model24-r-endpoint-command-proposal.v1',root_go_required=True,admitted=False,native_executed=False,model_qualified=False,qualified_timing=False,
        plan_path=str((inputs/'plan.json').resolve()),plan_sha256=digest,producer_sha256=plan['producer_sha256'],timeout_seconds=180,policy=policy(),container_name=CONTAINER,argv=argv)


def main():
    q=argparse.ArgumentParser(description=__doc__);sub=q.add_subparsers(dest='action',required=True);p=sub.add_parser('prepare')
    for n in ('process-intake','tech-lef','retained-rules','endpoint-intake','history','output'):p.add_argument('--'+n,type=Path,required=True)
    for n in ('verify','proposal','run'):
        p=sub.add_parser(n);p.add_argument('--inputs',type=Path,required=True);p.add_argument('--plan-sha256',required=True)
        if n!='verify':p.add_argument('--output',type=Path,required=True)
        if n=='proposal':p.add_argument('--output-parent',type=Path,required=True)
    a=q.parse_args()
    if a.action=='prepare':prepare(a.process_intake,a.tech_lef,a.retained_rules,a.endpoint_intake,a.history,a.output);print(E.sha(a.output/'plan.json'));return 0
    if a.action=='verify':verify(a.inputs,a.plan_sha256);print('verified');return 0
    if a.action=='proposal':write(a.output,proposal(a.inputs,a.plan_sha256,a.output_parent));return 0
    r=run(a.inputs,a.plan_sha256,a.output);return 0 if r['passed'] else 2
if __name__=='__main__':raise SystemExit(main())
