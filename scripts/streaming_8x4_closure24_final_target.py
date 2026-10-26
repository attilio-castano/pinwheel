"""New24 final-target admission; historical/internal ODBs remain seed-only.

This module reuses the certified source/reference and unchanged native Boolean
exporter. Only the new PG full-flow selector can supply physical authority.
Selection is independent of clean DRC, model qualification, proof and signoff.
"""
from pathlib import Path
import subprocess

import streaming_8x4_prepare as P
import streaming_8x4_pg_flow24 as PG
from streaming_8x4_geometry import regular, require, sha

TOP = 'tt_um_pinwheel_streaming_ready_d2'
FLAT_REFERENCE_SHA256 = 'da19eccfaa31dca8836f40bd693b4f125759470959cb06a0ed9ee3df34a2d1a4'
NATIVE_EXPORTER_SHA256 = '98666a2554c79001daca9e0ac122d30c71f5435f998c5e65fff86cb8ea942881'
TARGET_SCHEMA = 'pinwheel.closure24-pg-final-target.v1'


def bound(path):
    path = regular(path).resolve()
    return dict(path=str(path), sha256=sha(path))


def base_preparation(report_path):
    report = P.read(regular(report_path))
    require(report.get('schema') == 'pinwheel.closure24-pg-native-run.v1',
            'Only the new24 physical run can supply base authority')
    item = report.get('original_preparation')
    require(type(item) is dict and set(item) == {'path', 'sha256'} and
            Path(item['path']).name == 'preparation.json' and bound(item['path']) == item,
            'New24 run lacks exact original certified preparation')
    return Path(item['path']).resolve().parent


def select_report(report_path, report_sha256, prepared, packet):
    prepared = Path(prepared).resolve(strict=True)
    require(base_preparation(report_path) == prepared and P.verify(prepared) == packet,
            'New24 selection changes certified source preparation')
    target = PG.select_report(report_path, report_sha256, workspace=P.ROOT)
    require(target.get('schema') == TARGET_SCHEMA and target.get('parent_is_not_final_target') is True and
            target.get('physical_candidate_kind') == 'pg-aware-antenna-access24' and
            target.get('original_preparation') == bound(prepared / 'preparation.json') and
            target.get('physical_acceptance') is False and target.get('post_pnr_equivalence_proved') is False and
            target.get('model_qualified') is False,
            'No legacy/internal/probe authority can enter new24 final export')
    return target


def candidate_identity(target, prepared):
    prepared = Path(prepared).resolve(strict=True)
    require(target.get('schema') == TARGET_SCHEMA and
            target.get('original_preparation') == bound(prepared / 'preparation.json'),
            'New24 candidate changes original source authority')
    for name in ('physical_report', 'physical_state', 'actual_odb', 'pg_preparation'):
        require(bound(target[name]['path']) == target[name], 'New24 candidate artifact changed: ' + name)
    variant = target.get('variant')
    require(type(variant) is dict and type(variant.get('ordinal')) is int and variant['ordinal'] in (1, 2) and
            variant.get('policy') in ('A', 'B') and variant.get('maximum_variants') == 2 and
            variant.get('semantic_state_bits') == 6039 and variant.get('clock_period_ns') == 20,
            'New24 candidate variant/source/clock contract differs')
    return dict(schema='pinwheel.closure24-final-physical-candidate.v1', kind='pg-aware-antenna-access24',
        target_schema=TARGET_SCHEMA, original_preparation=target['original_preparation'],
        pg_preparation=target['pg_preparation'], physical_report=target['physical_report'],
        physical_state=target['physical_state'], actual_odb=target['actual_odb'], variant=variant,
        source_ff_bits=6039, clock_period_ns=20, tiles='8x4', parent_is_not_final_target=True)


def request(report_path, report_sha256, prepared, reference):
    prepared = Path(prepared).resolve(strict=True); packet = P.verify(prepared)
    target = select_report(report_path, report_sha256, prepared, packet)
    reference = regular(reference).resolve()
    historical = P.read(prepared / 'inputs/historical-parent-inputs.json')
    require(sha(reference) == FLAT_REFERENCE_SHA256 == historical['input_sha256'].get('physical-verilog/flat-reimport.json'),
            'Final export requires the exact certified source flat reference')
    exporter = regular(P.ROOT / 'scripts/streaming_tt_export_odb.py')
    require(sha(exporter) == NATIVE_EXPORTER_SHA256, 'Canonical native Boolean exporter changed')
    head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=P.ROOT, text=True, timeout=30).strip()
    return dict(schema='pinwheel.closure24-final-connectivity-request.v1', producer_commit=head,
        producer=bound(__file__), target=target, preparation=bound(prepared / 'preparation.json'),
        physical_candidate=candidate_identity(target, prepared),
        source_candidate_commit=packet['candidate_source_commit'], original_flat_reference=bound(reference),
        native_exporter=bound(exporter), top=TOP, source_ff_bits=6039,
        native_exporter_argv=['/inputs/export.py', '--database', '/inputs/actual.odb', '--reference',
            '/inputs/reference.json', '--top', TOP, '--out', '/outputs/export'],
        native_launcher_argv=['openroad', '-no_init', '-exit', '-python', '<fresh-root-owned-launch.py>'],
        native_limits=dict(cpus=1, memory_mib=2048, swap_mib=2048, timeout_seconds=120,
            network='none', read_only_rootfs=True, cap_drop='ALL', no_new_privileges=True),
        expected_outputs=['connectivity.json', 'inventory.json', 'receipt.json'],
        export_closeout_required=['same new24 ODB/reference/native-exporter hashes', 'complete artifact membership',
            'fresh new24 full-flow selector reobservation', 'same actual runtime', 'owned container absent'],
        qualified=False, physical_acceptance=False, final_correspondence_proved=False)
