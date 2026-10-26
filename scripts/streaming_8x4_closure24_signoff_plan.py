"""HOST-only new24 final8x4 view/signoff inventory and bounded execution requests.

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
import streaming_8x4_closure24_final_target as T
from streaming_8x4_closure24_final_connectivity import owned
import streaming_8x4_signoff_plan as ORIGINAL
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


bound = ORIGINAL.bound


fixed_path = ORIGINAL.fixed_path


def evidence_inventory(report_path, target):
    value = ORIGINAL.evidence_inventory(report_path, target)
    return dict(value, schema='pinwheel.closure24-signoff-inventory.v1')


official_sources = ORIGINAL.official_sources


def requests(target,inventory,packet,prepared,support,python):
    template=prepared/'inputs/tt_block_8x4_pgvdd.def'
    lock,sources,checks=official_sources(support,template)
    python=Path(python).absolute();require(python.is_file(),'Missing selected precheck Python')
    actual_python=python.resolve(strict=True)
    require(actual_python.is_file(),'Broken precheck Python alias')
    source_odb=target['actual_odb'];config=inventory['resolved_configuration']
    views=dict(schema='pinwheel.closure24-final-view-request.v1',target=target,
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
    official=dict(schema='pinwheel.closure24-official-precheck-request.v1',target=target,tech=lock['tech'],tiles='8x4',
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
    native=dict(schema='pinwheel.closure24-independent-layout-request.v1',target=target,
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
        native_limits=dict(cpus=1,memory_mib=2048,memory_plus_swap_mib=2048,timeout_seconds_each=750,
            outer_seconds=1800,reader_cleanup_reserve_seconds=300,network='none'),
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
    output=owned(output,P.ROOT);require(not output.exists(),'Preserve earlier fixed-target signoff plan')
    output.mkdir(parents=True)
    files={'target.json':target,'evidence-inventory.json':inventory,'fresh-views-request.json':views,
           'official-precheck-request.json':official,'independent-layout-request.json':native}
    for name,value in files.items():P.write(output/name,value)
    result=dict(schema='pinwheel.closure24-signoff-plan.v1',target=target,physical_candidate=candidate,
        file_sha256={name:sha(output/name) for name in files},executed=False,qualified=False,physical_acceptance=False,
        source_sha256={name:sha(P.ROOT/name) for name in ('scripts/streaming_8x4_signoff_plan.py',
            'scripts/streaming_8x4_closure24_final_connectivity.py','scripts/streaming_8x4_closure24_signoff_plan.py',
            'scripts/streaming_8x4_closure24_final_target.py','scripts/streaming_tt_signoff.py',NATIVE_EXPORT,
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
