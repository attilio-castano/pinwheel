"""Prepare fresh all-state mapping and public-wire authority for an 8x4 target.

HOST only. This authenticates a new closed 8x4 connectivity export and reuses
the existing complete state/sampler mapping APIs. It never translates an old
physical receipt, runs Lean, or grants actual-M equivalence. The unchanged
public-wire worker receives a fresh committed source archive and exact runtime
identity. Root must separately authorize and guard any worker execution.
"""
import argparse
import hashlib
from pathlib import Path
import subprocess
import sys

sys.dont_write_bytecode = True
import streaming_8x4_final_connectivity as C
import streaming_8x4_final_runtime as R
from streaming_8x4_geometry import regular, require, sha

ROOT = Path(__file__).resolve().parents[1]
LIBRARIES = {
    'typ': ('typ_1p20V_25C', '34163f3e7de9f854afac57332ba06f1739b78e7ac35660a8a5ddd39c570124ad'),
    'fast': ('fast_1p32V_m40C', 'af12d75a72d19648fa690027d29843fbae550aa91f4e40dd3339c7116d6e425d'),
    'slow': ('slow_1p08V_125C', '3ee222c580ba33acb2131ac2bf224ff8ee9700751835b73aaec72b670bb31d3c')}


def bind(path): return dict(path=str(regular(path).resolve()), sha256=sha(path))


def closed_export(report_path, expected_sha256):
    """Use the fresh 8x4 authority, not the historical export HOST schema."""
    report_path = regular(report_path).resolve(); require(sha(report_path) == expected_sha256, 'Final export report changed')
    report = R.read(report_path)
    require(report.get('schema') == 'pinwheel.streaming-8x4-final-connectivity-run.v1' and
        report.get('passed') is True and report.get('status') == 'exported' and type(report.get('exit_code')) is int and
        report['exit_code'] == 0 and report.get('inputs_runtime_unchanged') is True and
        report.get('container_termination', {}).get('status') == 'absent' and report.get('qualified') is False and
        report.get('physical_acceptance') is False and report.get('final_correspondence_proved') is False,
        'Successfully closed fresh 8x4 native connectivity export required')
    preparation = report.get('preparation', {})
    require(Path(preparation.get('path', '')).resolve() == report_path.parent / 'preparation.json' and
            sha(preparation['path']) == preparation.get('sha256'), 'Final export preparation differs')
    packet = C.verify(report_path.parent, ROOT)
    require(report['target'] == packet['request']['target'] and report.get('source_sha256') == packet['producer_sha256'] and
            report.get('producer_commit') == packet['producer_commit'] and
            type(report.get('physical_candidate')) is dict and
            report['physical_candidate'] == packet['request'].get('physical_candidate') and
            report.get('native_binding') == C.validate_native(report_path.parent, packet), 'Final export closeout binding differs')
    require(C.P.inventory(report_path.parent / 'native') ==
            {name.removeprefix('native/'): value for name, value in report.get('artifact_sha256', {}).items()
             if name.startswith('native/')} and all(name.startswith('native/') for name in report['artifact_sha256']),
            'Final export complete artifact membership changed')
    require(sha(report_path.parent / 'native.log') == report.get('native_log_sha256') and sha(report_path) == expected_sha256,
            'Final export log/report changed')
    return report, packet


def map_all_state(candidate, source_map, flat, flat_map, actual, library):
    """All 6039 bits: proposed names, actual Q/D/clock/reset and cell functions."""
    import streaming_tt_wire_binding as W
    documents = [R.read(path) for path in (candidate, flat, actual)]
    used = {cell['type'] for document in documents for body in document['modules'].values()
            for cell in body.get('cells', {}).values() if cell['type'].startswith('sg13cmos5l_')}
    lib = W.read_library(library, used, expected_sha256=LIBRARIES['typ'][1])
    graphs = [W.parse_graph(document, W.TOP, lib) for document in documents]
    source = W.labels(graphs[0], R.read(source_map)['rows'], source=True)
    flattened = W.labels(graphs[1], R.read(flat_map)['rows'])
    require(set(source) == set(flattened) and all(W.signature(lib.cells[source[key].cell]) ==
            W.signature(lib.cells[flattened[key].cell]) for key in source), 'Source/flat semantic state or FF behavior differs')
    return W.actual_rows(graphs[2], flattened, lib)


def corners(pdk):
    root = Path(pdk) / 'ihp-sg13cmos5l/libs.ref/sg13cmos5l_stdcell/lib'
    result = {name: dict(path=str(regular(root / ('sg13cmos5l_stdcell_' + suffix + '.lib')).resolve()), sha256=pin)
              for name, (suffix, pin) in LIBRARIES.items()}
    require(all(sha(item['path']) == item['sha256'] for item in result.values()), 'Pinned final-wire Liberty changed')
    return result


def verify(path):
    """Recheck a fresh authority before generation or a separately guarded worker."""
    path = regular(path).resolve(); record = R.read(path)
    require(record.get('schema') == 'pinwheel.streaming-8x4-final-authority.v1' and record.get('passed') is True and
        record.get('qualified') is False and record.get('native_executed') is False and
        record.get('final_public_wire_passed') is False and record.get('final_correspondence_proved') is False and
        record.get('physical_acceptance') is False and record.get('actual_state_bits') == 6039,
        'Complete fresh final state authority required')
    require(all(sha(item) == pin for item, pin in record['input_sha256'].items()), 'Final state authority input changed')
    for key in ('export_report','runtime_report','selected_archive','semantic_state_map','sampler_binding','worker_config','M_intake'):
        item = record[key]; require(sha(item['path']) == item['sha256'], 'Final authority artifact changed: ' + key)
    selected = record['selected_source']
    wire = R.load('_streaming8_final_verify_wire', ROOT / 'scripts/run-streaming-tt-wire.py')
    require(wire.membership(Path(selected['root']), selected['tree'], selected['object_format']) == selected['sha256'],
        'Final authority selected source membership changed')
    report, packet = closed_export(record['export_report']['path'], record['export_report']['sha256'])
    require(record['target'] == report['target'] and record['source_candidate_commit'] == packet['request']['source_candidate_commit'],
        'Final authority target/source changed')
    require(record.get('physical_candidate') == report['physical_candidate'], 'Final authority selected another physical candidate')
    runtime = R.closed_report(record['runtime_report']['path'])
    config = R.read(record['worker_config']['path']); mapping = R.read(record['semantic_state_map']['path'])
    native = Path(record['export_report']['path']).parent/'native/export'
    request = packet['request']
    expected_export = dict(directory=str(native),receipt_sha256=sha(native/'receipt.json'),
        database=record['target']['actual_odb']['path'],reference=request['original_flat_reference']['path'])
    require(config.get('schema') == 'pinwheel.streaming-tt-wire-request.v1' and
        config['source_commit'] == config['producer_commit'] == record['producer_commit'] and
        config['source_sha256'] == selected['sha256'] and config['root'] == selected['root'] and
        config['tools'] == runtime['tools'] and config['tool_identity'] == runtime['tool_identity_after'] and
        config['export'] == expected_export and config['compile_timeout'] == 300 and
        config['physical_stage'] == 'actual-closed-8x4-'+record['target']['latest_step'] and
        config['corners'] == corners(C.P.read(Path(request['preparation']['path']).parent/'preparation.json')['pdk_root']) and
        mapping.get('database_sha256') == record['target']['actual_odb']['sha256'] and
        len(mapping.get('rows',[])) == 6039, 'Final authority worker/mapping contract changed')
    candidate = R.read(record['M_intake']['path'])['source_candidate']['path']
    binding = wire.sampler_binding(record['sampler_binding']['path'],record['semantic_state_map']['path'],
        candidate=candidate,database=record['target']['actual_odb']['path'],
        connectivity=Path(config['export']['directory'])/'connectivity.json')
    require(sha(config['sampler_binding']['path']) == config['sampler_binding']['sha256'] and
        R.read(config['sampler_binding']['path']) == binding, 'Final worker actual sampler binding changed')
    return record


def prepare(export_report, export_sha256, runtime_report, output):
    from streaming_tt_wire_binding import make_binding
    report, packet = closed_export(export_report, export_sha256)
    runtime = R.closed_report(runtime_report)
    output = Path(output).absolute(); require(not output.exists(), 'Preserve earlier final-state authority')
    commit = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True, timeout=30).strip()
    own = 'scripts/streaming_8x4_final_authority.py'
    require(hashlib.sha256(subprocess.check_output(['git', 'show', commit + ':' + own], cwd=ROOT, timeout=30)).hexdigest() == sha(__file__),
            'Commit fresh final-state authority producer first')
    wire = R.load('_streaming8_final_wire_api', ROOT / 'scripts/run-streaming-tt-wire.py'); wire.check_environment()
    output.mkdir(parents=True)
    selected, archive, tree, algorithm = wire.archive_sources(output, commit)
    sources = wire.membership(selected, tree, algorithm)
    # Every local helper imported by this HOST process must match the selected
    # committed bytes. The separate Native worker starts a clean interpreter.
    def source_check():
        for name, module in tuple(sys.modules.items()):
            path = getattr(module, '__file__', None)
            if not path: continue
            path = Path(path).resolve()
            if path.is_relative_to(ROOT / 'scripts'):
                relative = str(path.relative_to(ROOT))
                require(relative in sources and sha(path) == sources[relative], 'HOST mapping helper differs from selected source')
        require(wire.membership(selected, tree, algorithm) == sources, 'Selected final-state authority source changed')
    source_check()
    request = packet['request']; prepared = Path(request['preparation']['path']).parent
    baseline = Path(C.P.read(prepared / 'preparation.json')['historical_parent']['path']).parent
    candidate = prepared / 'inputs/certified.json'; source_map = prepared / 'inputs/semantic-q-map.json'
    flat = Path(request['original_flat_reference']['path']); flat_map = flat.with_name('flat-reimport-semantic-q-map.json')
    historical = C.P.read(prepared / 'inputs/historical-parent-inputs.json')
    require(flat.parent == baseline / 'inputs/physical-verilog' and
            sha(flat_map) == historical['input_sha256'].get('physical-verilog/flat-reimport-semantic-q-map.json'),
            'Original source flat semantic map differs from historical custody')
    native = Path(export_report).resolve().parent / 'native/export'
    libs = corners(C.P.read(prepared / 'preparation.json')['pdk_root'])
    inputs = [export_report, runtime_report, candidate, source_map, flat, flat_map, libs['typ']['path'],
              native / 'receipt.json', native / 'connectivity.json', native / 'inventory.json', prepared / 'preparation.json']
    frozen = {str(regular(path).resolve()): sha(path) for path in inputs}
    rows, resized = map_all_state(candidate, source_map, flat, flat_map, native / 'connectivity.json', libs['typ']['path'])
    source_check()
    map_path = output / 'semantic-state-map.json'
    mapping = dict(schema='pinwheel.streaming-tt-semantic-state-map.v1', qualified=False, physical_acceptance_claim=False,
        database_sha256=request['target']['actual_odb']['sha256'], connectivity_sha256=sha(native / 'connectivity.json'),
        source_candidate_sha256=sha(candidate), rows=rows,
        boundary='Complete actual FF bijection and parsed sequential functions only; full transition/output/clock/packing M proof remains mandatory.')
    C.P.write(map_path, mapping)
    basis = {name: bind(path) for name, path in [('source-candidate', candidate), ('source-semantic-q-map', source_map),
        ('flat-netlist', flat), ('flat-semantic-q-map', flat_map), ('pinned-library', libs['typ']['path']),
        ('fresh-8x4-export', export_report), ('fresh-runtime-custody', runtime_report), ('actual-state-pairing', map_path)]}
    binding_path = output / 'sampler-binding.json'
    C.P.write(binding_path, make_binding(rows, basis, sha(native / 'connectivity.json')))
    binding = wire.sampler_binding(binding_path, map_path, candidate=candidate,
        database=request['target']['actual_odb']['path'], connectivity=native / 'connectivity.json')
    worker_binding = output / 'worker-sampler-binding.json'; C.P.write(worker_binding, binding)
    config = dict(schema='pinwheel.streaming-tt-wire-request.v1', source_commit=commit, producer_commit=commit,
        root=str(selected), source_sha256=sources, physical_stage='actual-closed-8x4-' + request['target']['latest_step'],
        tools=runtime['tools'], tool_identity=runtime['tool_identity_after'], corners=libs, compile_timeout=300,
        export=dict(directory=str(native), receipt_sha256=sha(native / 'receipt.json'),
            database=request['target']['actual_odb']['path'], reference=str(flat)), sampler_binding=bind(worker_binding))
    C.P.write(output / 'worker-config.json', config)
    # Fresh target intake is deliberately not accepted by the old GEN04 schema.
    # It is reviewable input to a new adapter, never an executable old receipt.
    m_intake = dict(schema='pinwheel.streaming-8x4-final-M-intake.v1', target=request['target'],
        physical_candidate=request['physical_candidate'],
        source_candidate_commit=request['source_candidate_commit'], source_candidate=bind(candidate),
        source_semantic_map=bind(source_map), original_flat_reference=bind(flat), original_flat_semantic_map=bind(flat_map),
        export_report=bind(export_report), export_receipt=bind(native / 'receipt.json'),
        export_inventory=bind(native / 'inventory.json'), export_connectivity=bind(native / 'connectivity.json'),
        semantic_state_map=bind(map_path), target_scope='final-routed-digital', state_bits=6039,
        required_coverage=['all-state transitions', 'all outputs', 'all actual clock/reset cones', 'packing and initialization',
            'complete generated namespace/import resolution', 'positive native Lean execution', 'whole-M private audit and negative controls'],
        executable_plan=False, actual_M_executed=False, correspondence_proved=False,
        blocked_prerequisites=['Fresh reviewed 8x4 GEN04 physical-target and relocated same-foundation authority adapter',
            'Verified complete positive-only F03 foundation and exact source-N replay dependency closure',
            'Fresh complete M source generation and import plan; no module-count or stop-at override',
            'Root heavy admission with separate private-control/audit/cleanup reserve'], qualified=False)
    C.P.write(output / 'M-intake.json', m_intake)
    require(all(sha(path) == pin for path, pin in frozen.items()) and
            closed_export(export_report, export_sha256)[0] == report, 'Final-state authority input changed during preparation')
    source_check()
    C.P.write(output / 'preparation.json', dict(schema='pinwheel.streaming-8x4-final-authority.v1', passed=True,
        producer_commit=commit, source_candidate_commit=request['source_candidate_commit'], target=request['target'],
        physical_candidate=request['physical_candidate'],
        export_report=bind(export_report), runtime_report=bind(runtime_report), selected_archive=bind(archive),
        selected_source=dict(root=str(selected), tree=tree, object_format=algorithm, sha256=sources),
        input_sha256=frozen, semantic_state_map=bind(map_path), sampler_binding=bind(binding_path),
        worker_config=bind(output / 'worker-config.json'), M_intake=bind(output / 'M-intake.json'),
        resized_sequential_masters=resized, actual_state_bits=len(rows), native_executed=False,
        final_public_wire_passed=False, final_correspondence_proved=False, qualified=False, physical_acceptance=False,
        boundary='Fresh full state/sampler mapping and immutable public-wire request only. M, finite Native wire execution and physical acceptance are independent pending gates.'))
    return output / 'preparation.json'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ('export-report', 'runtime-report', 'output'): parser.add_argument('--' + name, type=Path, required=True)
    parser.add_argument('--export-report-sha256', required=True); args = parser.parse_args()
    print(prepare(args.export_report, args.export_report_sha256, args.runtime_report, args.output))


if __name__ == '__main__': main()
