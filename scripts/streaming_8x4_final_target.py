"""Authenticate an eventual 8x4 final ODB and prepare its Boolean-export request.

HOST only: no tools, proofs, containers or artifact copies are launched. This
does not adapt an old receipt to a new schema or grant any acceptance. The
unchanged streaming_tt_export_odb.py can consume the requested ODB/reference
inside a separately reviewed Root-owned native export. Its native body already
accounts for actual signal cells, physical-only cells, power terminals and
unconnected outputs. Its existing HOST coordinator does not accept 8x4 receipts.

Full final-M adaptation also needs the archived GEN04 preparation/generation,
resolver06, runner05, executor01 and private03 sources plus the complete closed
same-foundation source-N dependency. Those owners hard-code old authority and
paths; they must receive a fresh reviewed 8x4 authority layer rather than edits
to historical receipts. A mapping/export request is not that proof execution.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess

import streaming_8x4_prepare as P
from streaming_8x4_geometry import regular, require, sha


TOP = 'tt_um_pinwheel_streaming_ready_d2'
FLAT_REFERENCE_SHA256 = 'da19eccfaa31dca8836f40bd693b4f125759470959cb06a0ed9ee3df34a2d1a4'
NATIVE_EXPORTER_SHA256 = '98666a2554c79001daca9e0ac122d30c71f5435f998c5e65fff86cb8ea942881'


def bound(path):
    path = regular(path).resolve()
    return dict(path=str(path), sha256=sha(path))


def closed_file(root, relative, expected):
    require(type(relative) is str and relative and not Path(relative).is_absolute() and
            '..' not in Path(relative).parts, 'Escaping final-target artifact')
    path = regular(root / relative).resolve()
    require(path.is_relative_to(root.resolve()) and sha(path) == expected,
            'Closed final-target artifact changed: ' + relative)
    return path


def base_preparation(report_path):
    """Resolve only an explicitly typed original or separate repair authority."""
    report = P.read(regular(report_path))
    if report.get('schema') == 'pinwheel.streaming-8x4-native-run.v1':
        require(type(report.get('prepared')) is str, 'Original run lacks its original preparation authority')
        path = Path(report['prepared']).resolve(strict=True)
        require(path.is_dir(), 'Original preparation must be a directory')
        return path
    if report.get('schema') == 'pinwheel.streaming-8x4-postantenna-repair-run.v1':
        original = report.get('original_preparation')
        require(type(original) is dict and set(original) == {'path', 'sha256'},
                'Repair run lacks an exact original preparation binding')
        path = regular(original['path']).resolve()
        require(path.name == 'preparation.json' and bound(path) == original,
                'Repair original preparation binding changed')
        return path.parent
    raise ValueError('Unknown physical candidate run schema; no legacy or parent-prefix fallback')


def candidate_identity(target, prepared):
    """Keep repaired and original implementations distinct through every gate."""
    prepared = Path(prepared).resolve(strict=True)
    identity = dict(schema='pinwheel.streaming-8x4-physical-candidate.v1',
        target_schema=target.get('schema'), original_preparation=bound(prepared/'preparation.json'),
        physical_report=target['physical_report'], actual_odb=target['actual_odb'],
        source_ff_bits=6039, clock_period_ns=20, tiles='8x4')
    for name in ('physical_report','actual_odb'):
        require(bound(target[name]['path']) == target[name], 'Selected candidate identity changed: '+name)
    if target.get('schema') == 'pinwheel.streaming-8x4-final-target.v1':
        require(not any(name in target for name in ('repair_preparation','original_parent_report','physical_candidate_kind')),
                'Original target mixes separate repair authority')
        identity['kind'] = 'original-8x4'
    elif target.get('schema') == 'pinwheel.streaming-8x4-repair-final-target.v1':
        require(target.get('physical_candidate_kind') == 'canonical-postantenna-repair' and
                target.get('original_preparation') == identity['original_preparation'],
                'Repair target changes the original source preparation')
        identity['kind'] = 'canonical-postantenna-repair'
        for name in ('repair_preparation','original_parent_report','measured_fanout','actual_repair_state'):
            require(bound(target[name]['path']) == target[name], 'Repair candidate authority changed: '+name)
            identity[name] = target[name]
    else:
        raise ValueError('Unknown final candidate identity; no schema translation is permitted')
    return identity


def select_report(report_path, report_sha256, prepared, packet):
    """Select latest completed state only after an actual completed DRT step."""
    report_path = regular(report_path).resolve()
    require(sha(report_path) == report_sha256, 'Physical report changed before final selection')
    report = P.read(report_path)
    if report.get('schema') == 'pinwheel.streaming-8x4-postantenna-repair-run.v1':
        import streaming_8x4_postantenna_repair as repair
        require(base_preparation(report_path) == prepared.resolve(), 'Repair report selects another original preparation')
        return repair.select_report(report_path, report_sha256, prepared, packet)
    terminal = type(report.get('exit_code')) is int and (
        (report.get('status') == 'flow_completed' and report['exit_code'] == 0) or
        (report.get('status') == 'failed' and report['exit_code'] != 0))
    require(report.get('schema') == 'pinwheel.streaming-8x4-native-run.v1' and report.get('mode') == 'full' and
            terminal and report.get('inputs_pdk_runtime_unchanged') is True and
            report.get('container_termination', {}).get('status') == 'absent' and
            report.get('qualified') is False and report.get('physical_acceptance') is False,
            'Final target requires a closed full 8x4 run; probe/coarse/timeout is insufficient')
    require(Path(report.get('prepared', '')).resolve() == prepared.resolve() and
            report.get('prepared_input_sha256') == sha(prepared / 'preparation.json') and
            report.get('tiles') == packet['tiles'] == '8x4' and
            report.get('source_ff_bits') == packet['source_ff_bits'] == 6039 and
            report.get('clock_period_ns') == packet['clock_period_ns'] == 20,
            'Final target changes prepared source/clock/allocation contract')
    artifacts = report.get('artifact_sha256')
    require(type(artifacts) is dict and artifacts, 'Final run lacks complete recorded artifacts')
    for relative, expected in artifacts.items():
        closed_file(report_path.parent, relative, expected)
    rows, ordinals, state_paths, nested_states = [], set(), set(), []
    for row in report.get('states', []):
        require(type(row) is dict and type(row.get('step_directory')) is str,
                'Malformed closed final state')
        ordinal = re.fullmatch(r'(\d+)-(.+)', row['step_directory'])
        require(ordinal is not None, 'Malformed native step ordinal')
        number = int(ordinal[1])
        state_path = regular(row['state']).resolve()
        require(state_path.is_relative_to((report_path.parent / 'flow').resolve()) and
                state_path not in state_paths and
                state_path.parent.name == row['step_directory'] and state_path.name == 'state_out.json' and
                row['state_sha256'] == sha(state_path) == artifacts.get(str(state_path.relative_to(report_path.parent))),
                'Final state is not a closed native artifact')
        state_paths.add(state_path)
        top_level = state_path.parent.parent == (report_path.parent / 'flow').resolve()
        if top_level:
            require(number not in ordinals, 'Ambiguous top-level native step ordinal')
            ordinals.add(number)
        else:
            nested_states.append(bound(state_path))
        state = P.read(state_path)
        view = row.get('views', {}).get('odb')
        if view is None and state.get('odb') is None:
            # Metadata/netlist-only early steps may precede the first ODB.
            if top_level: rows.append((number, row, state_path, None))
            continue
        require(type(view) is dict and {'path', 'sha256', 'container'} <= set(view), 'Closed state lacks actual ODB')
        odb = regular(view['path']).resolve()
        require(odb.is_relative_to((report_path.parent / 'flow').resolve()) and
                sha(odb) == view['sha256'] == artifacts.get(str(odb.relative_to(report_path.parent))) and
                state.get('odb') == view['container'] == '/work/run/' + str(odb.relative_to(report_path.parent / 'flow')),
                'Native state does not select its authenticated ODB')
        if top_level: rows.append((number, row, state_path, odb))
    drt = [row for row in rows if row[1]['step_directory'].endswith('-openroad-detailedrouting')]
    require(len(drt) == 1, 'No unique completed DetailedRouting state; partial routing is not a final target')
    require(rows, 'No completed native states')
    latest = max(rows, key=lambda row: row[0])
    require(latest[0] >= drt[0][0] and drt[0][3] is not None and latest[3] is not None,
            'Latest/completed DetailedRouting state lacks authoritative ODB')
    require(sha(report_path) == report_sha256, 'Physical report changed during final selection')
    return dict(schema='pinwheel.streaming-8x4-final-target.v1', physical_report=bound(report_path),
                physical_status=report['status'], physical_exit_code=report['exit_code'],
                completed_detailed_route_state=bound(drt[0][2]), physical_state=bound(latest[2]), actual_odb=bound(latest[3]),
                latest_step=latest[1]['step_directory'], target_scope='final-routed-digital-pending-proof',
                selection_policy='latest completed top-level flow state; nested substep evidence authenticated but not promoted',
                authenticated_nested_states=nested_states,
                physical_acceptance=False, post_pnr_equivalence_proved=False,
                boundary='A completed route artifact may still fail physical checks. Final proof and signoff remain unexecuted.')


def request(report_path, report_sha256, prepared, reference):
    prepared = Path(prepared).resolve(strict=True)
    packet = P.verify(prepared)
    target = select_report(report_path, report_sha256, prepared, packet)
    reference = regular(reference).resolve()
    historical = P.read(prepared / 'inputs/historical-parent-inputs.json')
    require(sha(reference) == FLAT_REFERENCE_SHA256 == historical['input_sha256'].get('physical-verilog/flat-reimport.json'),
            'Final export needs exact historically certified flat reference')
    exporter = regular(P.ROOT / 'scripts/streaming_tt_export_odb.py')
    require(sha(exporter) == NATIVE_EXPORTER_SHA256, 'Canonical native Boolean exporter changed')
    head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=P.ROOT, text=True, timeout=30).strip()
    native_argv = ['openroad', '-no_init', '-exit', '-python', '<fresh-root-owned-launch.py>']
    return dict(schema='pinwheel.streaming-8x4-final-connectivity-request.v1', producer_commit=head,
        producer=bound(__file__), target=target, preparation=bound(prepared / 'preparation.json'),
        physical_candidate=candidate_identity(target,prepared),
        source_candidate_commit=packet['candidate_source_commit'], original_flat_reference=bound(reference),
        native_exporter=bound(exporter), top=TOP, source_ff_bits=6039,
        native_exporter_argv=['/inputs/export.py', '--database', '/inputs/actual.odb', '--reference',
                              '/inputs/reference.json', '--top', TOP, '--out', '/outputs/export'],
        native_launcher_argv=native_argv, native_limits=dict(cpus=1, memory_mib=2048, swap_mib=2048,
            timeout_seconds=120, network='none', read_only_rootfs=True, cap_drop='ALL', no_new_privileges=True),
        expected_outputs=['connectivity.json', 'inventory.json', 'receipt.json'],
        export_closeout_required=['same ODB/reference/native-exporter hashes', 'complete artifact membership',
            'actual input/runtime identities unchanged', 'owned cleanup confirmed'],
        next_obligations=['fresh complete semantic-state map and all actual FF clock/reset accounting',
            'fresh 8x4 authority adapter for archived full GEN04 source generation/resolver/executor/private audit',
            'same-foundation complete source-N dependency with actual positive/private closure',
            'full actual-M execution without stop-at/count overrides', 'independent final-target public-wire corpus'],
        native_execution_authorized=False, native_executed=False, final_correspondence_proved=False,
        physical_acceptance=False, boundary='HOST request only; canonical HOST export coordinator and old receipts are not relabelled.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--physical-report', type=Path, required=True)
    parser.add_argument('--physical-report-sha256', required=True)
    parser.add_argument('--prepared', type=Path, required=True)
    parser.add_argument('--reference', type=Path, required=True)
    args = parser.parse_args()
    print(json.dumps(request(args.physical_report, args.physical_report_sha256, args.prepared, args.reference), indent=2))


if __name__ == '__main__':
    main()
