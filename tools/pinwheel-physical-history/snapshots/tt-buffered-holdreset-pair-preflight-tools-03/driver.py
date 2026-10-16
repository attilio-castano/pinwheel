"""Fresh saved-route timing. Explicit options; no inherited or expired deadlines."""
import argparse, hashlib, json, re, shutil, time
from pathlib import Path
from admission import (PRODUCER_SHA, utc_epoch, validate_libraries, validate_producer, contained, merge_hashes)
from common import ROOT, IMAGE, read, sha, write, execute
from segments import parse_segments

TOOLS = Path(__file__).resolve().parent
PRODUCER = ROOT/'build/physical/tt-buffered-hold30712-route-02'
PREFLIGHT = ROOT/'build/physical/tt-buffered-hold30712-candidate-sta-01'
LIB_STAGE = PREFLIGHT/'candidate'

def expected_sources(prepared, producer):
    expected = {}
    merge_hashes(expected, prepared['source_sha256'])
    merge_hashes(expected, producer['input_sha256'])
    merge_hashes(expected, {str(PRODUCER/name):digest for name,digest in producer['artifact_sha256'].items()})
    return expected

def verify_expected(expected):
    for source_path, expected_digest in expected.items():
        assert sha(source_path) == expected_digest, ('Changed input', source_path)

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--selection',type=Path,required=True)
    parser.add_argument('--selection-sha256',required=True)
    parser.add_argument('--native-stop',required=True)
    parser.add_argument('--deadline',required=True)
    cli=parser.parse_args();started=time.monotonic()
    native_stop=utc_epoch(cli.native_stop);deadline=utc_epoch(cli.deadline)
    selection=contained(ROOT,cli.selection);assert sha(selection)==cli.selection_sha256
    selected=read(selection);assert selected['schema']=='pinwheel-buffered-tt-fanout913914-selection-v1'
    assert native_stop==utc_epoch(selected['native_stop_utc']) and deadline==utc_epoch(selected['deadline_utc'])
    assert time.time()+300<=native_stop and deadline-native_stop>=120
    prepared=read(TOOLS/'prepared.json');producer=read(PRODUCER/'report.json');validate_producer(producer,IMAGE)
    assert sha(PRODUCER/'report.json')==PRODUCER_SHA
    assert sha(PREFLIGHT/'report.json')=='f98fd7831274ecf351d49b0b59af9c6413fd9adf54003df34f032870599fc35c'
    preflight=read(PREFLIGHT/'report.json');assert preflight['status']=='passed' and preflight['inputs_unchanged']
    folder=PRODUCER/'candidate';native=read(folder/'native-inventory.json')
    assert sha(folder/'routed.odb')=='8c3079c61f73f0f2819d4e0d21d0af2775d4afb76c620494e2841ace4b1dd063'
    validate_libraries({p.name:sha(p) for p in (PRODUCER/'lib').glob('*.lib')},{p.name:sha(p) for p in (LIB_STAGE/'lib').glob('*.lib')})
    for instance in ['fanout914','fanout913']:assert native['instances'][instance]['master']=='sg13cmos5l_buf_1'
    expected=expected_sources(prepared,producer)
    merge_hashes(expected,preflight['input_sha256'])
    merge_hashes(expected,{str(PREFLIGHT/name):digest for name,digest in preflight['artifact_sha256'].items()})
    for name,digest in prepared['tool_sha256'].items():merge_hashes(expected,{str(TOOLS/name):digest})
    merge_hashes(expected,{str(TOOLS/'prepared.json'):sha(TOOLS/'prepared.json'),str(selection):sha(selection)})
    merge_hashes(expected,{str(ROOT/name):digest for name,digest in selected['source_bindings_sha256'].items()});merge_hashes(expected,{str(ROOT/name):digest for name,digest in selected['protected_sources_sha256'].items()});assert len(selected['protected_sources_sha256'])==507
    verify_expected(expected)
    out=ROOT/'build/physical/tt-buffered-holdreset-pair-preflight-01';out.mkdir()
    def copy(source, destination):
        target=out/destination;target.parent.mkdir(parents=True,exist_ok=True)
        shutil.copyfile(source,target)
        digest=sha(source);assert sha(target)==digest
        merge_hashes(expected,{str(source):digest,str(target):digest})
    for name in ['timing-worker.py','coordinator.py','segments.py','pair_analysis.py']:copy(TOOLS/name,name)
    stage='preflight'
    copy(folder/'routed.odb',stage+'/checkpoint.odb')
    copy(folder/'after_grt.segments',stage+'/after_grt.segments')
    copy(TOOLS/'route-corner.tcl',stage+'/route-corner.tcl')
    for name in ['baseline-env.tcl','core.sdc']:copy(LIB_STAGE/name,stage+'/'+name)
    for library in sorted((LIB_STAGE/'lib').glob('*.lib')):copy(library,stage+'/lib/'+library.name)
    assert len(list((out/stage/'lib').glob('*.lib'))) == 9
    previous_inputs=read(LIB_STAGE/'inputs.json')
    sections=re.findall(r'(?ms)^NONDEFAULTRULES\s+\d+\s*;.*?^END NONDEFAULTRULES',(folder/'routed.def').read_text())
    assert len(sections)==1 and not re.search(r'\+\s+(?:VIA|USEVIA|USEVIARULE)\b',sections[0])
    normalized_spef={}
    for corner in preflight['measurement']['corners']:
        spef_lines=(LIB_STAGE/corner/'estimated.spef').read_text().splitlines(keepends=True)
        assert len([line for line in spef_lines if line.startswith('*DATE ')])==1
        normalized_spef[corner]=hashlib.sha256(''.join(line for line in spef_lines if not line.startswith('*DATE ')).encode()).hexdigest()
    inputs=dict(standard_lib_by_corner={corner:[str(Path('/work/diagnostic')/stage/'lib'/name.split('/')[-1]) for name in entry['libs']] for corner in preflight['measurement']['corners'] for entry in previous_inputs['corners'] if entry['name']==corner},retained_control_normalized_spef_sha256=normalized_spef,corners=previous_inputs['corners'],native_script_sha256=previous_inputs['native_script_sha256'],
        route_source_report_sha256=PRODUCER_SHA,routed_database_sha256=sha(folder/'routed.odb'),
        route_segments_sha256=sha(folder/'after_grt.segments'),netlist_sha256=sha(folder/'after.v'),
        post_route_ndr_map={name:net['nondefault_rule'] for name,net in native['nets'].items()},
        canonical_block_NDR_DEF_sha256=hashlib.sha256(sections[0].encode()).hexdigest(),
        endpoints=['_30712_/D'],reproduction_required=True,
        retained_reference_corners=preflight['measurement']['corners'],
        scope='Fresh saved-route RC, nine pinned Libs, exactSDC; full global STA/electrical reports and explicit30712 max/min. Conditional fast logic−40/SRAM−55; no optimizer, placementestimate, routing or signoff.')
    write(out/stage/'inputs.json',inputs)
    write(out/'stage-plan.json',dict(stages=['preflight'],arm='preflight',producer_report_sha256=PRODUCER_SHA))
    for generated in [out/stage/'inputs.json',out/'stage-plan.json']:merge_hashes(expected,{str(generated):sha(generated)})
    verify_expected(expected)
    assert time.time()+300<=native_stop,'Insufficient conservative native reserve after all staging'
    phase_limit=min(420,deadline-time.time()+time.monotonic()-started)
    report=execute(out,list(expected),['python3','-B','/work/diagnostic/coordinator.py'],seconds=300,cpus=3,memory='3g',schema='pinwheel-buffered-tt-holdreset-pair-preflight-v1',scope='Fresh3corners exactbase plus every transitive constrained resetpair endpoint max/min; no optimization/mutation.',expected_hashes=expected,absolute_work_stop=native_stop,all_in_deadline_monotonic=started+phase_limit,phase_started_monotonic=started,host_stage_seconds=60,extra=dict(selection_sha256=cli.selection_sha256,base_database_sha256=sha(folder/'routed.odb'),source_STA_report_sha256=sha(PREFLIGHT/'report.json'),native_process_count_expected=3,route_based_only=True,absolute_native_stop_utc=cli.native_stop,hard_deadline_utc=cli.deadline))
    report['all_in_elapsed_seconds']=round(time.monotonic()-started,3);report['overall_bound_seconds']=420
    if report['all_in_elapsed_seconds']>420 or time.time()>deadline:report['status']='bound_exceeded'
    write(out/'report.json',report)
    print(out/'report.json',report['status'],report['all_in_elapsed_seconds'],flush=True)
    return 0 if report['status']=='passed' else 1

if __name__=='__main__':raise SystemExit(main())
