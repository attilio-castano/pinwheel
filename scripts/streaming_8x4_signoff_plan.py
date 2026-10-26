"""HOST-only final8x4 view/signoff inventory and bounded execution requests.

This module launches no shell, container, CAD, interpreter or proof worker.
Requests are reviewable preparation only. Every execution needs a fresh Root
GO, exact fixed-target inputs, the shared heavy lease and actual closeout.
"""
import argparse
import json
from pathlib import Path
import re
import shutil

import streaming_8x4_prepare as P
import streaming_8x4_final_target as T
import streaming_tt_signoff as S
from streaming_8x4_geometry import ALLOCATION, admit, regular, require, sha
from streaming_8x4_run import receipt_value

TOP='tt_um_pinwheel_streaming_ready_d2'
OFFICIAL_CHECKS=(
    'KLayout pin label overlapping drawing','KLayout SG13CMOS5L DRC','KLayout zero area',
    'KLayout Checks','Pin check','Boundary check','Layer check','Cell name check','Analog pin check')
OMITTED=('timing','transistor LVS','antenna','CMOS5L power-pin checking')
INHERITED_DISABLED=('RUN_EQY','RUN_KLAYOUT_XOR','RUN_LINTER')
NATIVE_EXPORT='scripts/streaming_tt_export_signoff.py'


def bound(path):
    path=regular(path).resolve()
    return dict(path=str(path),sha256=sha(path))


def fixed_path(root,container,prefix='/work/run'):
    require(type(container) is str and container.startswith(prefix+'/'),'Unresolved fixed-target view')
    relative=Path(container[len(prefix)+1:])
    require(not relative.is_absolute() and '..' not in relative.parts,'Escaping fixed-target view')
    path=regular(root/relative).resolve()
    require(path.is_relative_to(root.resolve()),'Fixed-target view escaped native root')
    return path


def evidence_inventory(report_path,target):
    report_path=regular(report_path).resolve();report=P.read(report_path);root=report_path.parent
    flow=root/'flow';rows=[];gds_joins=[]
    for row in report.get('states',[]):
        state=regular(row['state']);raw=P.read(state)
        require(sha(state)==row['state_sha256']==report['artifact_sha256'].get(str(state.relative_to(root))),
            'Signoff inventory native-state seal changed')
        views={}
        for kind in ('odb','gds','lef','nl','pnl','cdl','spef','sdc'):
            value=raw.get(kind)
            if type(value) is str and value.startswith('/work/run/'):
                path=fixed_path(flow,value)
                require(report['artifact_sha256'].get(str(path.relative_to(root)))==sha(path),
                    'Signoff inventory actual view differs: '+kind)
                views[kind]=bound(path)
        stage=row['step_directory']
        outputs={name:value for name,value in report['artifact_sha256'].items()
            if name.startswith('flow/'+stage+'/') and any(part in name.lower() for part in
                ('report','rpt','log','metrics','xml','lvs','spice','spef','drc','json','commands'))}
        item=dict(stage=stage,state=bound(state),views=views,raw_observations=receipt_value(raw.get('metrics',{})),
            recorded_stage_outputs=outputs,execution_or_pass_not_inferred_from_state_presence=True)
        rows.append(item)
        # A carried GDS is usable only if its originating streamout state is
        # completed and paired with this exact final authoritative database.
        if (stage.endswith(('-klayout-streamout','-magic-streamout')) and 'gds' in views and 'odb' in views and
                views['odb']['sha256']==target['actual_odb']['sha256']):
            gds_joins.append(dict(producer_stage=stage,state=bound(state),actual_odb=views['odb'],gds=views['gds']))
    resolved=regular(flow/'resolved.json')
    require(report['artifact_sha256'].get('flow/resolved.json')==sha(resolved),'Final resolved configuration changed')
    config=P.read(resolved)
    return dict(schema='pinwheel.streaming-8x4-signoff-inventory.v1',physical_report=bound(report_path),target=target,
        resolved_configuration=bound(resolved),completed_states=rows,actual_same_odb_gds_joins=gds_joins,
        inherited_disabled_checks={key:config.get(key) for key in INHERITED_DISABLED if config.get(key) is False},
        extraction_configuration={key:config.get(key) for key in ('RCX_RULESETS','RCX_SDC_FILE','STA_CORNERS',
            'TIMING_VIOLATION_CORNERS','LIB','CELL_LIBS') if key in config},
        nominal_cell_corners_do_not_qualify_rc_corners=True,extraction_model_qualified=False,
        qualified=False,physical_acceptance=False,all_signoff_results_still_require_interpretation=True)


def official_sources(support,template):
    support=Path(support).resolve(strict=True);lock=P.read(P.ROOT/'tools/streaming-tt-signoff.json')
    source_map=S.verify_support(support,lock)
    manifest=P.read(ALLOCATION)
    extra=support/manifest['template_path']
    require(sha(regular(extra))==sha(regular(template))==manifest['template_sha256'],
        'Official8x4 template is absent/different in selected support snapshot')
    checks=S.selected_checks((support/'precheck/precheck.py').read_text(),lock['tech'])
    require(tuple(checks)==OFFICIAL_CHECKS,'Applicable unchanged official9-check inventory changed')
    source_map[str(extra)]=sha(extra)
    return lock,source_map,checks


def requests(target,inventory,packet,prepared,support,python):
    template=prepared/'inputs/tt_block_8x4_pgvdd.def'
    lock,sources,checks=official_sources(support,template)
    python=Path(python).absolute();require(python.is_file(),'Missing selected precheck Python')
    actual_python=python.resolve(strict=True)
    require(actual_python.is_file(),'Broken precheck Python alias')
    source_odb=target['actual_odb'];config=inventory['resolved_configuration']
    views=dict(schema='pinwheel.streaming-8x4-final-view-request.v1',target=target,
        canonical_native_exporter=bound(P.ROOT/NATIVE_EXPORT),source_odb=source_odb,
        resolved_configuration=config,pdk_root=packet['pdk_root'],top=TOP,source_ff_bits=6039,
        native_argv=['python3','-B','/worker/'+NATIVE_EXPORT,'--database','/input/actual.odb',
            '--config','/input/resolved.json','--out','/outputs/signoff-views'],
        required_mounts=dict(worker='read-only committed producer snapshot',actual_odb='read-only',resolved='read-only',
            pdk='/work/pdk read-only',outputs='new owned directory'),
        expected_outputs=['implemented.v','implemented.power.v','implemented.cdl','implemented.lef','report.json'],
        gds_requirement='Use the authenticated actual same-ODB streamout join, or freshly stream out this exact ODB with complete consumed GDS/LEF hashes.',
        native_limits=dict(cpus=1,memory_mib=2048,memory_plus_swap_mib=2048,timeout_seconds=300,network='none'),
        require_root_go=True,executed=False,qualified=False,physical_acceptance=False)
    official=dict(schema='pinwheel.streaming-8x4-official-precheck-request.v1',target=target,tech=lock['tech'],tiles='8x4',
        support_commit=lock['support_commit'],official_source_sha256=sources,selected_checks=checks,
        selected_checks_must_all_execute_in_order=True,skips_waivers_or_filtered_failures_forbidden=True,
        extra8x4_template=dict(relative= P.read(ALLOCATION)['template_path'],sha256=sha(template)),
        required_input_relationship='Fresh GDS, exact-coordinate LEF and powered Verilog from the same actual final ODB; no GRT/probe substitution.',
        required_staged_design_files=[TOP+'.gds',TOP+'.lef',TOP+'.v','info.yaml'],
        info_yaml=dict(project=dict(top_module=TOP,tiles='8x4',analog_pins=0,uses_3v3=False),pinout={}),
        precheck_python=dict(declared=str(python),resolved=str(actual_python),sha256=sha(actual_python),
            required_version_prefix=lock['python_version_prefix'],required_packages=lock['precheck_python_packages'],
            actual_identity_and_complete_import_payload_must_be_checked_before_and_after=True),
        canonical_source_adapter=bound(P.ROOT/'scripts/streaming_tt_signoff.py'),
        native_klayout_adapter='Use unchanged native_klayout/native_journal functions with a newly owned native-config.json. Never call the historical6x4 main packaging function.',
        cwd='<fresh-out>/tt/precheck',argv=[str(python),'-B','precheck.py','--gds','<fresh-out>/design/'+TOP+'.gds','--tech',lock['tech']],
        environment=dict(PDK_ROOT=packet['pdk_root'],PDK=lock['tech'],PYTHONDONTWRITEBYTECODE='1',
            PYTHONNOUSERSITE='1',PYTHONPATH='',PATH='<fresh-out>/bin:<reviewed-path>'),
        native_calls=dict(expected_klayout_processes=3,cpus_each=1,memory_mib_each=2048,
            memory_plus_swap_mib_each=2048,network='none',rootfs_read_only=True,tmpfs_mib=256,timeout_seconds_total=900),
        expected_result='reports/results.xml with exact nine testcase names/order and no skipped cases; six closed native journal records for three KLayout calls.',
        official_omissions=list(OMITTED),require_root_go=True,executed=False,qualified=False,physical_acceptance=False)
    native=dict(schema='pinwheel.streaming-8x4-independent-layout-request.v1',target=target,
        requirements=dict(
            transistor_lvs='Fresh ODB CDL top plus exact used-cell master closure; nonzero device inventory; actual final GDS; require all used leaf pairs and top Match.',
            antenna='Run unchanged complete foundry antenna deck and strict reader; all23 declared categories, no missing category and zero violations.',
            drc='Retain native router DRC and independent unchanged foundry GDS deck; completion and zero failures required.',
            overlap_connectivity='Actual final ODB disconnected-pin/overlap results and geometric power connectivity; logical net-name equality alone is insufficient.',
            power='All actual implemented supply terminals, package rail geometry and applicable IR-drop evidence; no inference from pincheck alone.',
            view_consistency='Final ODB, GDS, LEF, powered/unpowered Verilog and CDL must refer to the same implemented cell/pin/rail topology.',
            timing='Fresh annotated extracted setup/hold/electrical at declared cell and qualified CMOS5L RC corners; stale carried metrics are not observations.'),
        canonical_native_layout=bound(P.ROOT/'scripts/streaming_tt_native_layout.py'),
        canonical_result_reader=bound(P.ROOT/'scripts/streaming_tt_layout.py'),
        complete_used_cell_cdl_context=bound(P.ROOT/'scripts/streaming_tt_cdl_context.py'),
        historical_layout_host_coordinator_cannot_admit_8x4_report=True,
        native_limits=dict(cpus=1,memory_mib=2048,memory_plus_swap_mib=2048,timeout_seconds_each=900,network='none'),
        executed=False,require_root_go=True,qualified=False,physical_acceptance=False)
    return views,official,native


def prepare(report,report_sha256,prepared,support,python,output):
    prepared=Path(prepared).resolve(strict=True);packet=P.verify(prepared)
    target=T.select_report(report,report_sha256,prepared,packet)
    candidate=T.candidate_identity(target,prepared)
    inventory=evidence_inventory(report,target)
    inventory['physical_candidate']=candidate
    views,official,native=requests(target,inventory,packet,prepared,support,python)
    for request in (views,official,native):request['physical_candidate']=candidate
    output=Path(output).absolute();require(not output.exists(),'Preserve earlier fixed-target signoff plan')
    output.mkdir(parents=True)
    files={'target.json':target,'evidence-inventory.json':inventory,'fresh-views-request.json':views,
           'official-precheck-request.json':official,'independent-layout-request.json':native}
    for name,value in files.items():P.write(output/name,value)
    result=dict(schema='pinwheel.streaming-8x4-signoff-plan.v1',target=target,physical_candidate=candidate,
        file_sha256={name:sha(output/name) for name in files},executed=False,qualified=False,physical_acceptance=False,
        source_sha256={name:sha(P.ROOT/name) for name in ('scripts/streaming_8x4_signoff_plan.py',
            'scripts/streaming_8x4_final_target.py','scripts/streaming_tt_signoff.py',NATIVE_EXPORT,
            'scripts/streaming_tt_native_layout.py','scripts/streaming_tt_layout.py','tools/streaming-tt-signoff.json')},
        boundary='HOST preparation and evidence inventory only. No source helper, request, scheduled step or copied result is execution or signoff acceptance.')
    P.write(output/'report.json',result)
    return result


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    for name in ('physical-report','prepared','support','python','output'):parser.add_argument('--'+name,type=Path,required=True)
    parser.add_argument('--physical-report-sha256',required=True)
    args=parser.parse_args();prepare(args.physical_report,args.physical_report_sha256,args.prepared,args.support,args.python,args.output)
    print(args.output/'report.json')


if __name__=='__main__':main()
