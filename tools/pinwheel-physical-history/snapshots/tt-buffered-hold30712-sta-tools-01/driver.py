"""Fresh saved-route timing. Explicit options; no inherited or expired deadlines."""
import argparse, hashlib, json, re, shutil, time
from pathlib import Path
from admission import (Options, PRODUCER_SHA, ODB_SHA, PREFLIGHT_SHA, NATIVE_SECONDS,
    ALL_IN_SECONDS, utc_epoch, validate_deadlines, validate_libraries, validate_producer,
    validate_fresh_control, contained, merge_hashes)
from common import ROOT, IMAGE, read, sha, write, execute
from segments import parse_segments

TOOLS = Path(__file__).resolve().parent
PRODUCER = ROOT/'build/physical/tt-buffered-hold30712-route-02'
PREFLIGHT = ROOT/'build/physical/tt-buffered-hold30712-preflight-01'
LIB_STAGE = PREFLIGHT/'preflight'

def expected_sources(prepared, producer):
    expected = {}
    merge_hashes(expected, prepared['source_sha256'])
    merge_hashes(expected, producer['input_sha256'])
    merge_hashes(expected, {str(PRODUCER/name):digest for name,digest in producer['artifact_sha256'].items()})
    return expected

def verify_expected(expected):
    for source_path, expected_digest in expected.items():
        assert sha(source_path) == expected_digest, ('Changed input', source_path)

def structural_admission(options, prepared):
    assert options.arm in ('control','candidate')
    assert sha(options.selection) == options.selection_sha256
    selection = read(options.selection)
    assert selection['schema'] == 'pinwheel-buffered-tt-hold30712-sta-selection-v1'
    assert sha(PRODUCER/'report.json') == PRODUCER_SHA
    producer = read(PRODUCER/'report.json'); validate_producer(producer, IMAGE)
    assert sha(PREFLIGHT/'report.json') == PREFLIGHT_SHA
    preflight = read(PREFLIGHT/'report.json')
    assert preflight['status'] == 'passed' and preflight['inputs_unchanged']
    assert preflight['container_termination']['status'] == 'absent'
    assert sha(TOOLS/'prepared.json') == selection['source_bindings_sha256'][str((TOOLS/'prepared.json').relative_to(ROOT))]
    verification = read(options.verification)
    assert verification['status']=='passed' and verification['no_CAD_launched'] is True
    assert verification['prepared_sha256'] == sha(TOOLS/'prepared.json')
    assert verification['negative_controls_passed'] >= 10
    folder = PRODUCER/('baseline' if options.arm=='control' else 'candidate')
    assert sha(folder/'routed.odb') == ODB_SHA[options.arm]
    libraries = {file.name:sha(file) for file in (PRODUCER/'lib').glob('*.lib')}
    timing_libraries = {file.name:sha(file) for file in (LIB_STAGE/'lib').glob('*.lib')}
    validate_libraries(libraries, timing_libraries)
    native = read(folder/'native-inventory.json')
    assert native['nets']['_03216_']['terminals'] == [['_29930_','Y','OUTPUT'],['timing_eco_hold_30712','A','INPUT']]
    assert native['nets']['timing_eco_hold_30712_D']['terminals'] == [['_30712_','D','INPUT'],['timing_eco_hold_30712','X','OUTPUT']]
    # The real no-edit control was exact before physical movement. Its proof is
    # checked independently here, while new numeric control is always measured.
    baseline, noop = PRODUCER/'baseline', PRODUCER/'noop'
    assert read(baseline/'native-inventory.json') == read(noop/'native-inventory.json')
    assert parse_segments(baseline/'after_grt.segments') == parse_segments(noop/'after_grt.segments')
    for name in ['after.v','estimated.spef','native-raw-capacity.json','typ-timing.json']:
        assert sha(baseline/name) == sha(noop/name), ('Dirty no-op input differs', name)
    geometry_baseline, geometry_noop = read(baseline/'geometry.json'), read(noop/'geometry.json')
    assert {k:v for k,v in geometry_baseline.items() if k!='database_sha256'} == {k:v for k,v in geometry_noop.items() if k!='database_sha256'}
    assert sha(PRODUCER/'core.sdc') == sha(LIB_STAGE/'core.sdc')
    expected = expected_sources(prepared, producer)
    merge_hashes(expected,{str(ROOT/name):digest for name,digest in selection['source_bindings_sha256'].items()})
    merge_hashes(expected,{str(ROOT/name):digest for name,digest in selection['protected_sources_sha256'].items()})
    assert len(selection['protected_sources_sha256']) == 507
    for name,digest in prepared['tool_sha256'].items():merge_hashes(expected,{str(TOOLS/name):digest})
    merge_hashes(expected,{str(options.selection):options.selection_sha256,str(options.verification):sha(options.verification)})
    if options.arm == 'candidate':
        assert options.control_report is not None
        control = read(options.control_report);validate_fresh_control(control)
        merge_hashes(expected,control['input_sha256'])
        merge_hashes(expected,{str(options.control_report.parent/name):digest for name,digest in control['artifact_sha256'].items()})
        merge_hashes(expected,{str(options.control_report):sha(options.control_report)})
    return folder, native, expected, preflight

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--arm',choices=['control','candidate'],required=True)
    parser.add_argument('--selection',type=Path,required=True)
    parser.add_argument('--selection-sha256',required=True)
    parser.add_argument('--verification',type=Path,required=True)
    parser.add_argument('--native-stop',required=True)
    parser.add_argument('--deadline',required=True)
    parser.add_argument('--control-report',type=Path)
    cli=parser.parse_args()
    options=Options(cli.arm,contained(ROOT,cli.selection),cli.selection_sha256,
        contained(ROOT,cli.verification),utc_epoch(cli.native_stop),utc_epoch(cli.deadline),
        contained(ROOT,cli.control_report) if cli.control_report else None)
    started=time.monotonic();validate_deadlines(options.native_stop,options.deadline,time.time())
    out=ROOT/'build/physical'/('tt-buffered-hold30712-'+options.arm+'-sta-01');out.mkdir()
    prepared=read(TOOLS/'prepared.json')
    folder,native,expected,preflight=structural_admission(options,prepared)
    # Rehash each unique frozen source once, rather than repeatedly walking the
    # same historical receipt chain. Staged copies are independently rehashed.
    verify_expected(expected)
    def copy(source, destination):
        target=out/destination;target.parent.mkdir(parents=True,exist_ok=True)
        shutil.copyfile(source,target)
        digest=sha(source);assert sha(target)==digest
        merge_hashes(expected,{str(source):digest,str(target):digest})
    for name in ['timing-worker.py','coordinator.py','segments.py']:copy(TOOLS/name,name)
    stage=options.arm
    copy(folder/'routed.odb',stage+'/checkpoint.odb')
    copy(folder/'after_grt.segments',stage+'/after_grt.segments')
    copy(TOOLS/'route-corner.tcl',stage+'/route-corner.tcl')
    for name in ['baseline-env.tcl','core.sdc']:copy(LIB_STAGE/name,stage+'/'+name)
    for library in sorted((LIB_STAGE/'lib').glob('*.lib')):copy(library,stage+'/lib/'+library.name)
    assert len(list((out/stage/'lib').glob('*.lib'))) == 9
    previous_inputs=read(LIB_STAGE/'inputs.json')
    sections=re.findall(r'(?ms)^NONDEFAULTRULES\s+\d+\s*;.*?^END NONDEFAULTRULES',(folder/'routed.def').read_text())
    assert len(sections)==1 and not re.search(r'\+\s+(?:VIA|USEVIA|USEVIARULE)\b',sections[0])
    inputs=dict(corners=previous_inputs['corners'],native_script_sha256=previous_inputs['native_script_sha256'],
        route_source_report_sha256=PRODUCER_SHA,routed_database_sha256=ODB_SHA[options.arm],
        route_segments_sha256=sha(folder/'after_grt.segments'),netlist_sha256=sha(folder/'after.v'),
        post_route_ndr_map={name:net['nondefault_rule'] for name,net in native['nets'].items()},
        canonical_block_NDR_DEF_sha256=hashlib.sha256(sections[0].encode()).hexdigest(),
        endpoints=['_30712_/D'],reproduction_required=options.arm=='control',
        retained_reference_corners=preflight['measurement']['corners'],
        scope='Fresh saved-route RC, nine pinned Libs, exactSDC; full global STA/electrical reports and explicit30712 max/min. Conditional fast logic−40/SRAM−55; no optimizer, placementestimate, routing or signoff.')
    write(out/stage/'inputs.json',inputs)
    write(out/'stage-plan.json',dict(stages=[options.arm],arm=options.arm,producer_report_sha256=PRODUCER_SHA))
    for generated in [out/stage/'inputs.json',out/'stage-plan.json']:merge_hashes(expected,{str(generated):sha(generated)})
    verify_expected(expected)
    validate_deadlines(options.native_stop,options.deadline,time.time())
    phase_limit=min(ALL_IN_SECONDS,options.deadline-time.time()+time.monotonic()-started)
    report=execute(out,list(expected),['python3','-B','/work/diagnostic/coordinator.py'],
        seconds=NATIVE_SECONDS,cpus=3,memory='3g',schema='pinwheel-buffered-tt-hold30712-fresh-sta-v1',
        scope='One fresh three-corner computational arm with global+targeted30712STA; exactsavedODB/segments/9Lib/SDC, no reroute/placement/optimization.',
        expected_hashes=expected,absolute_work_stop=options.native_stop,
        all_in_deadline_monotonic=started+phase_limit,phase_started_monotonic=started,host_stage_seconds=60,
        extra=dict(arm=options.arm,native_process_count_expected=3,selection_sha256=options.selection_sha256,
            selection=str(options.selection.relative_to(ROOT)),verification_sha256=sha(options.verification),
            producer_report_sha256=PRODUCER_SHA,route_based_only=True,parasitic_model='estimate_parasitics -global_routing',
            absolute_native_work_stop_utc=cli.native_stop,hard_deadline_utc=cli.deadline,
            fresh_control_required_before_candidate=True,
            fresh_control_report_sha256=sha(options.control_report) if options.control_report else None))
    report['all_in_elapsed_seconds']=round(time.monotonic()-started,3)
    report['overall_bound_seconds']=ALL_IN_SECONDS
    if report['all_in_elapsed_seconds']>ALL_IN_SECONDS or time.time()>options.deadline:report['status']='bound_exceeded'
    write(out/'report.json',report)
    print(out/'report.json',report['status'],report['all_in_elapsed_seconds'],flush=True)
    return 0 if report['status']=='passed' else 1

if __name__=='__main__':raise SystemExit(main())
