#!/usr/bin/env python3
"""Run unchanged native antenna/LVS measurements on a closed diagnostic GDS.

Only a scoped input provider adapts provenance; the original layout API,
native decks, command loop and interpretation remain unchanged and pinned.
"""
import argparse
from contextlib import contextmanager
import hashlib
import importlib.util
from pathlib import Path
import subprocess
import time

import streaming_tt_gds_diagnostic as G
import streaming_tt_physical as P
from streaming_tt_intake import dependency_closure
from streaming_tt_signoff import read,regular,require,sha,unchanged,write
from validation_run import fresh_directory

LAYOUT_SHA256='c960f6bf02179f69e792a4cdbee9c5ccc2fcddf69f878bbf5569152880502e5e'
ENTRIES=('scripts/streaming_tt_native_layout_diagnostic.py','scripts/streaming_tt_layout.py',
    'tools/physical-toolchain.json','tools/streaming-tt-signoff.json')
BOUNDARY=('Diagnostic antenna/LVS measurements on independently closed actual ODB-derived GDS and CDL. '
    'The original physical producer status and all original failures remain unchanged. '
    'No candidate flow completion, source correspondence, extracted timing, DRC, power or official TT acceptance is granted.')


def layout_api():
    path=P.ROOT/'scripts/streaming_tt_native_layout.py'
    require(sha(regular(path))==LAYOUT_SHA256,'Review changed original layout measurement module before adapting it')
    spec=importlib.util.spec_from_file_location('_streaming_tt_diagnostic_layout',Path(__file__).with_name('streaming_tt_native_layout.py'))
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);return module


@contextmanager
def input_provider(module,provider):
    original=module.actual_inputs;module.actual_inputs=provider
    try:yield
    finally:module.actual_inputs=original


def actual_inputs(export_path):
    export_path=regular(export_path);packet=read(export_path);source=export_path.parent
    require(packet.get('schema')=='pinwheel.streaming-tt-gds-view-host.v1' and
        packet.get('status')=='views_exported' and packet.get('view_export_completed') is True and
        type(packet.get('exit_code')) is int and packet['exit_code']==0 and
        packet.get('candidate_flow_completed') is False and packet.get('qualified') is False and
        packet.get('physical_acceptance_claim') is False and packet.get('inputs_unchanged') is True and
        packet.get('runtime_unchanged') is True and packet.get('pdk_unchanged') is True and
        packet.get('container_termination',{}).get('status')=='absent','Diagnostic GDS source is not closed')
    artifacts={str(path.relative_to(source)):sha(path) for path in sorted(source.rglob('*')) if path.is_file() and
        not path.is_relative_to(source/'producer') and path!=export_path}
    require(artifacts==packet.get('artifact_sha256'),'Diagnostic GDS artifact membership or bytes changed')
    report,roots,odb,database,frozen=G.intake(packet['physical_report'],packet['physical_state'])
    request=read(source/'request.json');views=G.validate_native(source,request,config_path=roots['/work/run']/'resolved.json')
    require(views==packet.get('streamout') and sha(database)==packet.get('actual_database_sha256') and
        report['source_commit']==packet.get('physical_source_commit') and
        report.get('producer_commit')==packet.get('physical_producer_commit'),
        'Diagnostic GDS differs from the original closed actual ODB/producer')
    exported=G.export_api().validate_native(source/'native',database=(odb,database),config=roots['/work/run']/'resolved.json')
    require(exported==packet.get('signoff_views'),'Fresh actual ODB-derived CDL/signoff receipt differs')
    closure=packet.get('producer_closure',{});files=closure.get('files')
    require(type(files) is list and len(files)==len(set(files)),'Missing diagnostic GDS producer closure')
    staged={}
    for name in files:
        path=regular(source/'producer'/P.relative_path(name))
        require(packet.get('input_sha256_before',{}).get(str(path))==sha(path),'Diagnostic GDS producer snapshot changed')
        staged[name]=sha(path);frozen[str(path)]=sha(path)
    require({str(path.relative_to(source/'producer')) for path in (source/'producer').rglob('*') if path.is_file()}==set(files) and
        dependency_closure(source/'producer',files)==closure,'Diagnostic producer closure membership differs')
    for name in ('scripts/streaming_tt_gds_diagnostic.py','scripts/streaming_tt_export_signoff.py'):
        require(staged.get(name)==sha(P.ROOT/name),'Actual current GDS/export API differs from reviewed selected source')
    gds=regular(source/views['views']['gds']['relative']);cdl=regular(source/'native/implemented.cdl')
    frozen.update({str(path):sha(path) for path in (export_path,gds,cdl,source/'native/report.json',source/'native-report.json')})
    for name,value in artifacts.items():frozen[str(regular(source/name))]=value
    return (report,roots,exported['top'],gds,cdl,frozen),packet


def validate_measurement(path,expected):
    path=regular(path);packet=read(path);out=path.parent
    require(packet.get('schema')=='pinwheel.streaming-tt-native-layout-host.v1' and
        packet.get('status')=='completed' and packet.get('measurements_completed') is True and
        type(packet.get('passed')) is bool and packet.get('qualified') is False and
        packet.get('physical_acceptance_claim') is False and packet.get('inputs_unchanged') is True and
        all(packet.get('input_sha256',{}).get(name)==value for name,value in expected.items()),
        'Unchanged native layout measurement did not close against the adapted actual inputs')
    commands=packet.get('commands');require(type(commands) is list and len(commands)==4 and all(
        row.get('status')=='completed' and type(row.get('exit_code')) is int and row['exit_code']==0 and
        row.get('owned_container_absent') is True for row in commands),'Native layout command/cleanup closeout incomplete')
    actual={str(item.relative_to(out)):sha(item) for item in sorted(out.rglob('*')) if item.is_file() and item!=path}
    require(actual==packet.get('artifacts_sha256'),'Original native measurement artifacts changed')
    return packet


def run(export_path,tag,timeout):
    require(1<=timeout<=3600,'Diagnostic native layout timeout outside1..3600s')
    G.export_api().check_environment();values,exported=actual_inputs(export_path)
    report,roots,top,gds,cdl,frozen=values
    module=layout_api();closure=dependency_closure(P.ROOT,ENTRIES)
    commit=subprocess.check_output(['git','rev-parse','HEAD'],cwd=P.ROOT,text=True).strip()
    producer={name:hashlib.sha256(P.committed(P.ROOT/name)).hexdigest() for name in closure['files']}
    frozen.update({str(P.ROOT/name):value for name,value in producer.items()})
    out=fresh_directory(P.ROOT/'build/streaming-tt-layout-diagnostic',tag).resolve()
    measurement=P.ROOT/'build/streaming-tt-layout'/tag/'report.json'
    require(not measurement.exists() and not measurement.parent.exists(),'Preserve previous native layout measurement tag')
    packet=dict(schema='pinwheel.streaming-tt-native-layout-diagnostic.v1',qualified=False,physical_acceptance_claim=False,
        candidate_flow_completed=False,diagnostic_only=True,measurements_completed=False,passed=False,status='intent',
        original_physical_report=exported['physical_report'],original_physical_state=exported['physical_state'],
        original_physical_stage=Path(exported['physical_state']).parent.name,
        original_physical_status=report['status'],original_physical_exit_code=report['exit_code'],
        gds_export_report=str(regular(export_path)),gds_export_report_sha256=sha(export_path),actual_gds_sha256=sha(gds),
        actual_cdl_sha256=sha(cdl),actual_odb_sha256=exported['actual_database_sha256'],
        original_layout_module_sha256=LAYOUT_SHA256,producer_commit=commit,producer_sha256=producer,
        producer_dependency_closure=closure,input_sha256_before=frozen,old_measurement_report_absent_before_run=True,
        adapter='Scoped/restored actual_inputs provider only; original measurement module remains unchanged.',boundary=BOUNDARY)
    write(out/'report.json',packet);started=time.monotonic()
    def provider(physical,state,reference):
        require(regular(physical)==regular(exported['physical_report']) and regular(state)==regular(exported['physical_state']) and
            regular(reference)==regular(Path(export_path).parent/'native/report.json'),'Unexpected original measurement intake arguments')
        return report,roots,top,gds,cdl,dict(frozen)
    try:
        packet['status']='running';write(out/'report.json',packet)
        with input_provider(module,provider):
            result=module.run(Path(exported['physical_report']),Path(exported['physical_state']),
                Path(export_path).parent/'native/report.json',tag,timeout)
        require(regular(result)==regular(measurement),'Original measurement returned a different report')
        before=sha(measurement);observed=validate_measurement(measurement,frozen)
        packet.update(status='completed',measurements_completed=True,passed=observed['passed'],
            antenna=observed['antenna'],lvs=observed['lvs'],old_measurement_report_sha256_before_closeout=before)
    except BaseException as error:
        packet.update(status='failed',error=type(error).__name__+': '+str(error));raise
    finally:
        try:
            if measurement.is_file():
                packet.setdefault('old_measurement_report_sha256_before_closeout',sha(measurement))
            unchanged(frozen);require(sha(P.ROOT/'scripts/streaming_tt_native_layout.py')==LAYOUT_SHA256,'Original layout source changed')
            packet.update(inputs_unchanged=True,input_sha256_after=frozen,producer_unchanged=True)
            if measurement.is_file():
                packet.update(old_measurement_report=str(measurement),old_measurement_report_sha256_after_closeout=sha(measurement))
                if 'old_measurement_report_sha256_before_closeout' in packet:
                    require(packet['old_measurement_report_sha256_before_closeout']==sha(measurement),'Original measurement report changed during closeout')
        except BaseException as error:
            packet.update(status='closeout_failed',passed=False,measurements_completed=False,closeout_error=type(error).__name__+': '+str(error));raise
        finally:packet['elapsed_seconds']=round(time.monotonic()-started,3);write(out/'report.json',packet)
    return out/'report.json'


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--gds-export-report',required=True,type=Path)
    parser.add_argument('--tag',required=True);parser.add_argument('--timeout',type=int,default=1800);args=parser.parse_args()
    print(run(args.gds_export_report,args.tag,args.timeout),flush=True)


if __name__=='__main__':main()
