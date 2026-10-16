"""One source-bound offline diagnostic; root owns scheduling of all CAD operations."""
import argparse
import math
from pathlib import Path
import re
import shutil
import sys
import time
from common import ROOT, IMAGE, execute, read, sha, write
from admission import validate, SOURCE_ODB_SHA

CAPS={'route':(175,230,4,'3g'),'timing':(115,170,3,'3g'),
      'export':(50,105,1,'1g'),'power':(25,80,1,'1g')}

def assert_hashes(values,base=ROOT):
    for name,digest in values.items():
        p=Path(name)
        if not p.is_absolute():p=base/p
        assert sha(p)==digest,('Changed source',str(p))

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--operation',choices=list(CAPS),required=True)
    parser.add_argument('--arm',choices=('control','candidate'),required=True)
    parser.add_argument('--selection',type=Path,required=True)
    parser.add_argument('--admission',type=Path)
    parser.add_argument('--tag',required=True)
    args=parser.parse_args();started=time.monotonic()
    assert re.fullmatch('[A-Za-z0-9_-]+',args.tag)
    assert args.operation in ('route','timing') or args.arm=='candidate'
    tools=Path(__file__).resolve().parent
    prepared=read(tools/'prepared.json')
    assert_hashes(prepared['tool_sha256'],tools)
    assert_hashes(prepared['derivation_sha256'])
    selection=read(args.selection)
    assert selection['schema']=='pinwheel-buffered-tt-access-incremental-selection-v1'
    for key,p in (('intake',ROOT/prepared['intake']['path']),('validation_tools',tools/'prepared.json')):
        ref=selection['references'][key]
        assert (ROOT/ref['path']).resolve()==p.resolve() and ref['sha256']==sha(p)
    for ref in selection['references'].values():
        assert sha(ROOT/ref['path'])==ref['sha256']
    intake_path=ROOT/prepared['intake']['path'];intake=read(intake_path)
    assert sha(intake_path)==prepared['intake']['sha256']
    for k in ('protected_sources_sha256','prior_current_source_sha256','references_sha256',
              'original_checkpoint_views_sha256','original_recipe_sha256'):
        assert_hashes(intake[k])
    for name,m in intake['prior_manifests'].items():
        assert sha(ROOT/name)==m['sha256'];assert_hashes(m['evidence_sha256'])
    reference=intake['source_checkpoint']
    source_database=ROOT/reference['database']
    source_state=ROOT/reference['state']
    source_env=ROOT/reference['environment']
    recipe=ROOT/reference['design']
    assert sha(source_database)==reference['database_sha256']==SOURCE_ODB_SHA
    assert sha(source_state)==reference['state_sha256'] and sha(source_env)==reference['environment_sha256']
    source=read(source_state)
    source_producer=read(recipe/'continuation-invocation.json')
    assert source_producer['status']=='failed' and source_producer['exit_code']==2
    assert source['metrics']['design__power_grid_violation__count']==30396
    assert source['metrics']['design__power_grid_violation__count__net:VGND']==10392
    assert source['metrics']['design__power_grid_violation__count__net:VPWR']==20004
    assert re.findall(r'^set ::env\(CURRENT_ODB\) (\S+)\s*$',source_env.read_text(),re.M)==[source['odb']]
    database,descriptor=source_database,source_state
    admitted={};qualification=dict(source_reference_native_flow_status='failed',
        source_reference_native_flow_exit_code=2,source_reference_inherited_power_count=30396,
        fresh_native_checks_waived=False)
    if args.arm=='candidate':
        assert args.admission is not None
        admitted,database,descriptor,qualification=validate(args.admission,args.selection)
    else:
        assert args.admission is None
    digest=sha(database)
    out=ROOT/('build/tt-buffered/netlist' if args.operation=='export' else 'build/physical')/args.tag
    out.mkdir()
    paths=[database,descriptor,source_database,source_state,source_env,intake_path,args.selection,
        tools/'prepared.json',Path(__file__),tools/'admission.py',tools/'common.py',
        recipe/'core.json',recipe/'core.sdc',ROOT/'scripts/run-buffered-tt-physical.py',
        recipe/'continuation-invocation.json',
        ROOT/'tools/physical-toolchain.json',ROOT/'build/physical/pdk/installed.json',
        *[Path(p) for p in admitted],*[Path(p) for p in intake['protected_sources_sha256']]]
    if args.admission is not None:paths.append(args.admission)
    expected={str(database.resolve()):digest,**admitted}
    def copy(source,name):
        target=out/name;target.parent.mkdir(parents=True,exist_ok=True)
        shutil.copyfile(source,target);assert sha(source)==sha(target)
        paths.extend((source,target));expected[str(target.resolve())]=sha(source)
        return target
    extra={**qualification,'arm':args.arm,'source_database':str(database.relative_to(ROOT)),
        'source_database_sha256':digest,'source_state':str(descriptor.relative_to(ROOT)),
        'selection_sha256':sha(args.selection),'reference_database_sha256':SOURCE_ODB_SHA}
    if args.operation=='route':
        prior=ROOT/'build/physical/tt-buffered-access-placement-control-route-01'
        prior_report=read(prior/'report.json')
        assert prior_report['status']=='passed' and prior_report['source_database_sha256']==SOURCE_ODB_SHA
        assert prior_report['measurement']['native_overflow']==5840 and prior_report['native_extra_iterations']==5
        paths.append(prior/'report.json')
        for name in ('baseline-env.tcl','corner-env.tcl','core.sdc'):
            assert sha(prior/name)==prior_report['artifact_sha256'][name];copy(prior/name,name)
        assert sha(recipe/'core.sdc')==sha(prior/'core.sdc')
        for p in sorted((prior/'lib').glob('*.lib')):
            name=str(p.relative_to(prior));assert sha(p)==prior_report['artifact_sha256'][name];copy(p,name)
        assert len(list((out/'lib').glob('*.lib')))==3
        assert re.findall(r'^set ::env\(GRT_OVERFLOW_ITERS\) (\d+)\s*$',(out/'corner-env.tcl').read_text(),re.M)==['5']
        copy(database,'postcts.odb');copy(descriptor,'source-state.json');copy(recipe/'core.json','source-config.json')
        copy(tools/'route.tcl','route.tcl');copy(tools/'route-coordinator.py','coordinator.py')
        copy(tools/'export_geometry.py','export_geometry.py')
        argv=['python3','-B','/work/diagnostic/coordinator.py']
        schema='pinwheel-buffered-tt-access-incremental-route-v1'
        scope='Matched coarse5 native congestion-allowed routing of exact repairedR0 control or admitted incremental candidate; native automatic clock-NDR fallback retained. No cell optimization or accepted routing/signoff.'
        extra.update(native_extra_iterations=5,native_fallback_policy='unchanged native automatic retries',
            container_design_root='/work/recovery',accepted_route=False,retained_control_native_overflow=5840)
    elif args.operation=='timing':
        prior=ROOT/'build/physical/tt-buffered-postcts-timing-01'
        prior_inputs,prior_report=read(prior/'inputs.json'),read(prior/'report.json')
        paths.extend((prior/'inputs.json',prior/'report.json'))
        assert sha(recipe/'core.sdc')==prior_inputs['files']['core.sdc']['sha256']
        copy(database,'checkpoint.odb');copy(recipe/'core.sdc','core.sdc');copy(source_env,'baseline-env.tcl')
        copy(tools/'timing-worker.py','timing-worker.py')
        for entry in prior_inputs['corners']:
            for relative in entry['libs']:
                retained=prior_inputs['files'][relative];name=Path(relative).name
                p=recipe/'macro'/name if name.startswith('RM_') else ROOT/retained['source_path']
                assert sha(p)==retained['sha256'];copy(p,relative)
        scope='Fresh three-corner estimated STA of exact control/candidate ODB under identical referenceenv/9libraries/SDC. No inherited candidate metrics/SDF/SPEF; no routing mutation, extracted timing or signoff. Fast screening uses -40C logic/I/O with -55C SRAM conditionally.'
        nominal='nom_typ_1p20V_25C'
        inputs=dict(corners=prior_inputs['corners'],native_script_sha256=prior_report['native_script_sha256'],scope=scope,
            nominal_reference=dict(state=str(source_state.relative_to(ROOT)),state_sha256=sha(source_state),
                odb_sha256=SOURCE_ODB_SHA,same_database=args.arm=='control',
                setup_ns=source['metrics']['timing__setup__ws__corner:'+nominal],
                hold_ns=source['metrics']['timing__hold__ws__corner:'+nominal]))
        write(out/'inputs.json',inputs);paths.append(out/'inputs.json')
        argv=['python3','-B','/work/diagnostic/timing-worker.py'];schema='pinwheel-buffered-tt-access-incremental-timing-v1'
        extra.update(exact_library_count=9,clock_period_ns=20,io_max_ns=4,io_min_ns=.2,
            candidate_metrics_copied_from_source=False)
    elif args.operation=='export':
        copy(database,'source.odb')
        (out/'export.tcl').write_text('read_db /work/diagnostic/source.odb\nwrite_verilog /work/diagnostic/checkpoint.nl.v\nset receipt [open /work/diagnostic/measurement.json w]\nputs $receipt {{"status":"measured","operation":"read_db; write_verilog only"}}\nclose $receipt\nexit\n')
        paths.append(out/'export.tcl')
        argv=['openroad','-exit','-no_splash','/work/diagnostic/export.tcl'];schema='pinwheel-mapped-odb-export-v1'
        scope='Fresh logical export of exact admitted scratch incremental candidate ODB; no placement, resizing, routing or STA.'
    else:
        policy_path=ROOT/selection['references']['policy']['path']
        for p,name in ((database,'input.odb'),(source_database,'reference.odb'),(recipe/'power-columns.json','power-columns.json'),(policy_path,'policy.json')):
            copy(p,name)
        copy(tools/'check_grid.tcl','check_grid.tcl');copy(tools/'metadata.py','metadata.py')
        copy(tools/'power-coordinator.py','coordinator.py')
        argv=['python3','-B','/work/diagnostic/coordinator.py'];schema='pinwheel-buffered-tt-access-incremental-power-movement-v1'
        scope='Fresh both-net PSM connectivity, whole supply geometry, R0 footprints/contacts,43TTpins and independent full movement/clock/status/master/topology readback against exact repaired source. No CAD mutation or signoff.'
    work,cap,cpus,memory=CAPS[args.operation]
    stage_seconds=time.monotonic()-started
    assert stage_seconds<=5,('Staging exceeded frozen5second reserve',stage_seconds)
    work_bound=min(work,math.floor(cap-stage_seconds-50))
    assert work_bound>0
    report=execute(out,paths,argv,seconds=work_bound,cpus=cpus,memory=memory,schema=schema,
        scope=scope,extra=extra,expected_hashes=expected)
    if args.operation=='export' and report['status']=='passed':
        nl=out/'checkpoint.nl.v';assert nl.is_file() and nl.stat().st_size
        report.update(netlist=str(nl.relative_to(ROOT)),netlist_sha256=sha(nl),source_unchanged=report['inputs_unchanged'])
    if args.operation=='timing' and report['status']=='passed' and args.arm=='control':
        retained=read(ROOT/intake['retained_primary']['repaired_timing']['path'])
        for corner,value in report['measurement']['corners'].items():
            baseline=retained['measurement']['corners'][corner]
            for k in ('setup_worst_slack_ns','hold_worst_slack_ns'):
                assert abs(value[k]-baseline[k])<=1e-5,('Fresh matched-control reference changed',corner,k)
        report['all_control_corners_reproduce_retained_reference']=True
    report['all_in_elapsed_seconds']=round(time.monotonic()-started,3)
    report['host_staging_seconds']=round(stage_seconds,3)
    report['overall_bound_seconds']=cap
    report['all_in_scope']='Host source staging (<=5s), Docker work, owned cleanup (<=50s), recustody/artifact hashing; only final report write/print excluded.'
    if report['all_in_elapsed_seconds']>cap:report['status']='bound_exceeded'
    write(out/'report.json',report);print(out/'report.json',flush=True)
    sys.exit(0 if report['status']=='passed' else 1)

if __name__=='__main__':main()
