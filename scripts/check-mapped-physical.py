#!/usr/bin/env python3
"""Export and remeasure one completed mapped-chip checkpoint, without rerouting.

The default selects the last completed step. --step selects an earlier completed
directory from the same settled run, for comparisons at the same physical stage.
Successful collection may contain timing/electrical violations; it is not closure.
"""
import argparse
from collections import Counter
import importlib.util
import json
from pathlib import Path
import shutil
import subprocess
import sys
import time

import physical_checkpoint
import physical_target
from physical_checkpoint_sta import analysis_tcl, measurement_quality
from validation_run import Commands, fresh_directory, sha

ROOT = Path(__file__).resolve().parents[1]


def checkpoint(physical, design, step=None):
    """Only a completed stage of this exact reported run is admissible."""
    selected = step or physical['last_completed_step']
    if selected not in physical['completed_steps']:
        raise ValueError('Select a completed step from the reported run')
    path = Path(design) / 'runs' / physical['tag'] / selected / 'state_out.json'
    if selected == physical['last_completed_step'] and sha(path) != physical['state_sha256']:
        raise ValueError('Changed reported final state')
    state = json.loads(path.read_text())
    odb = physical_checkpoint.artifact_path(state['odb'], Path(design))
    if selected == physical['last_completed_step']:
        if sha(odb) != physical['artifact_sha256'].get(str(odb.relative_to(ROOT))):
            raise ValueError('Changed reported final database')
    return path, state, odb


def estimation_mode(log):
    if 'PINWHEEL_PROPAGATED_CLOCK 1' not in log:
        raise ValueError('Clock propagation not confirmed')
    modes = [name for flag, name in [('0', 'placement'), ('1', 'global_routing')]
             if 'PINWHEEL_ESTIMATION_GLOBAL_ROUTES ' + flag in log]
    if len(modes) != 1:
        raise ValueError('Missing or ambiguous parasitic estimate')
    return modes[0]


def repair_checkpoint(path, source, physical_tag):
    """Admit only a completed local probe derived from this exact checkpoint."""
    path, source = Path(path).resolve(), Path(source).resolve()
    probe = json.loads(path.read_text())
    if (probe.get('status') != 'passed' or not probe.get('source_unchanged') or
            probe.get('physical_tag') != physical_tag or
            probe.get('source_database') != str(source.relative_to(ROOT)) or
            probe.get('source_database_sha256') != sha(source) or
            not probe.get('containers') or set(probe['containers'].values()) - {'absent', 'stopped'}):
        raise ValueError('Incomplete or unmatched local repair probe')
    for name, digest in probe['inputs_sha256'].items():
        if sha(name) != digest:
            raise ValueError('Changed local probe input: ' + name)
    database = path.parent / 'repaired.odb'
    if sha(database) != probe['artifacts_sha256'].get('repaired.odb'):
        raise ValueError('Changed local repair database')
    return database, probe


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--physical-tag', required=True)
    parser.add_argument('--tag', required=True, help='Fresh diagnostic receipt name')
    parser.add_argument('--step', help='Exact completed step directory; defaults to the final one')
    parser.add_argument('--target-bundle', type=Path,
                        help='Prepared roles for an older run with the identical mapped input and constraints')
    parser.add_argument('--repair-probe', type=Path, help='Completed local probe receipt derived from the selected checkpoint')
    parser.add_argument('--nominal-layer-rc', action='store_true',
                        help='Explicitly use and verify nominal LEF RC when no source override exists')
    parser.add_argument('--pins', type=Path, help='JSON list of physical pins for fresh per-net load reports')
    parser.add_argument('--verify-nominal-layer-rc', action='store_true',
                        help='Require explicit layer RC to match the database technology LEF in every corner')
    args = parser.parse_args()
    if not args.physical_tag.replace('-', '').replace('_', '').isalnum():
        parser.error('Invalid physical tag')
    extra_request = dict(pins=json.loads(args.pins.read_text()) if args.pins else [],
                         verify_nominal_layer_rc=args.verify_nominal_layer_rc)
    analysis_tcl(extra_request)  # Reject malformed names before Docker or output creation.
    spec = importlib.util.spec_from_file_location('import_check', ROOT / 'scripts/check-mapped-import.py')
    check = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(check)
    invocation_path = ROOT / 'build/physical' / (args.physical_tag + '-invocation.json')
    inv = json.loads(invocation_path.read_text())
    if 'exit_code' not in inv:
        raise ValueError('Physical run is still active')
    termination = check.observe_container('pinwheel-' + args.physical_tag)
    if termination not in ('absent', 'stopped'):
        raise ValueError('Physical container is not settled')
    design = ROOT / 'build/physical' / inv['design']
    inputs = json.loads((design / 'inputs.json').read_text())
    if args.target_bundle and inputs.get('physical_target'):
        raise ValueError('A physical target already owns its roles')
    bundle = (design if inputs.get('physical_target') else
              physical_target.matching_bundle(design, args.target_bundle.resolve()) if args.target_bundle else None)
    if bundle:
        extra_request['path_roles'] = json.loads((bundle / 'path-roles.json').read_text())
        extra_request['path_expected'] = physical_target.path_expectations(
            json.loads((bundle / 'mapped.json').read_text())['modules']['tt_um_pinwheel'], extra_request['path_roles'])
        analysis_tcl(extra_request)
    if 'mapped_input' not in inputs or sha(design / 'inputs.json') != inv['inputs_sha256']:
        raise ValueError('Changed or nonmapped preparation')
    for name, digest in inputs['files_sha256'].items():
        if sha(design / name) != digest:
            raise ValueError('Changed prepared view: ' + name)
    out = fresh_directory(ROOT / 'build/physical/mapped-diagnostics', args.tag)
    run = Commands(ROOT, out, default_timeout=120)
    started = time.monotonic()
    report = dict(schema=1, status='running', physical_tag=args.physical_tag, commands=run.records,
                  physical_container=termination, containers={}, inputs_sha256={})

    def freeze(path):
        path = Path(path)
        key = str(path.relative_to(ROOT)) if path.is_relative_to(ROOT) else str(path)
        report['inputs_sha256'][key] = sha(path)
        return path

    repair_mount = []

    def container(label, command):
        name = 'pinwheel-diagnostic-' + args.tag + '-' + label
        report['containers'][name] = 'unconfirmed'
        try:
            extra_mounts = ['--mount', f'type=bind,source={bundle},target=/target,readonly'] if bundle else []
            run(['docker', 'run', '--rm', '--pull', 'never', '--name', name, '--network', 'none',
                 '--read-only', '--cpus', '2', '--memory', '2g', '--tmpfs', '/tmp:rw,size=128m',
                 '--mount', f'type=bind,source={design},target=/work/core,readonly',
                 '--mount', f'type=bind,source={inv["pdk_root"]},target=/work/pdk,readonly',
                 '--mount', f'type=bind,source={ROOT / "scripts"},target=/scripts,readonly',
                 '--mount', f'type=bind,source={out},target=/probe', '--workdir', '/probe',
                 *extra_mounts, *repair_mount, inv['image_id'], *command], label)
        except BaseException:
            subprocess.run(['docker', 'stop', '--time', '2', name], capture_output=True, timeout=15)
            raise
        finally:
            report['containers'][name] = check.observe_container(name)
            if report['containers'][name] not in ('absent', 'stopped'):
                raise RuntimeError('Diagnostic container termination unconfirmed')

    try:
        worker = ROOT / 'scripts/physical_checkpoint_sta.py'
        if args.pins:
            freeze(args.pins.resolve())
        if bundle:
            for file in ['inputs.json', 'mapped.json', 'path-roles.json', 'state-ownership.json', 'target.json', 'macro-geometry.json']:
                freeze(bundle / file)
            freeze(ROOT / 'scripts/physical_target.py')
            freeze(ROOT / 'scripts/physical_target_odb.py')
        resolved = design / 'runs' / args.physical_tag / 'resolved.json'
        for path in [Path(__file__).resolve(), worker, invocation_path, design / 'inputs.json', resolved,
                     ROOT / 'scripts/check-mapped-import.py', ROOT / 'scripts/report-physical.py',
                     ROOT / 'scripts/routing_context.py', ROOT / 'scripts/routing_evidence.py',
                     ROOT / 'scripts/physical_floorplan.py', ROOT / 'scripts/physical_checkpoint.py',
                     ROOT / 'scripts/validation_run.py', ROOT / 'scripts/process_group.py',
                     Path(inv['pdk_root']) / 'installed.json']:
            freeze(path)
        if sha(Path(inv['pdk_root']) / 'installed.json') != inv['pdk_receipt_sha256']:
            raise ValueError('Changed installed PDK identity')
        if args.nominal_layer_rc:
            from physical_route_intake import ihp_layer_rc
            cfg = json.loads(resolved.read_text())
            if cfg.get('LAYERS_RC') or cfg.get('VIAS_R'):
                raise ValueError('Cannot replace existing RC overrides')
            tech = freeze(Path(inv['pdk_root']) / 'ihp-sg13cmos5l/libs.ref/sg13cmos5l_stdcell/lef/sg13cmos5l_tech.lef')
            freeze(ROOT / 'scripts/physical_route_intake.py')
            extra_request.update(nominal_layer_rc=ihp_layer_rc(tech), verify_nominal_layer_rc=True)
        physical_report = ROOT / 'build/physical' / (args.physical_tag + '-report.json')
        if not physical_report.exists():
            run([sys.executable, '-B', ROOT / 'scripts/report-physical.py', '--tag', args.physical_tag],
                'physical-report')
        freeze(physical_report)
        physical = json.loads(physical_report.read_text())
        if physical['invocation_sha256'] != sha(invocation_path) or physical['resolved_config_sha256'] != sha(resolved):
            raise ValueError('Changed reported invocation or resolved configuration')
        state_path, state, odb = checkpoint(physical, design, args.step)
        freeze(state_path)
        freeze(odb)
        if args.repair_probe:
            probe_path = freeze(args.repair_probe.resolve())
            odb, probe = repair_checkpoint(probe_path, odb, args.physical_tag)
            for name in probe['containers']:
                if check.observe_container(name) not in ('absent', 'stopped'):
                    raise ValueError('Local repair container remains active')
            freeze(odb)
            repair_mount = ['--mount', f'type=bind,source={probe_path.parent},target=/repair,readonly']
            state = dict(state, odb='/repair/repaired.odb')
            report['repair_probe'] = dict(path=str(probe_path.relative_to(ROOT)), sha256=sha(probe_path),
                                          source_database_sha256=probe['source_database_sha256'],
                                          optimization_layer_rc=probe.get('nominal_layer_rc'))
        report['measurement_layer_rc'] = extra_request.get('nominal_layer_rc', 'retained-flow-configuration')
        report.update(source_database=str(odb.relative_to(ROOT)), source_database_sha256=sha(odb),
                      state_path=str(state_path.relative_to(ROOT)), state_sha256=sha(state_path),
                      selected_step=state_path.parent.name, last_completed_step=physical['last_completed_step'],
                      flow_exit_code=inv['exit_code'], physical_report=str(physical_report.relative_to(ROOT)),
                      physical_report_sha256=sha(physical_report))
        (out / 'export.tcl').write_text(f'read_db {state["odb"]}\nwrite_verilog /probe/implemented.v\nexit\n')
        container('export', ['openroad', '-exit', '/probe/export.tcl'])
        report.update(netlist=str((out / 'implemented.v').relative_to(ROOT)), netlist_sha256=sha(out / 'implemented.v'))
        container('geometry', ['openroad', '-python', '/scripts/routing_context.py', state['odb'],
                              '/probe/context.json', '--placement-exclusions', '/work/core/placement-exclusions.json'])
        if bundle:
            (out / 'target-request.json').write_text(json.dumps(dict(database=state['odb'], design='/target', placed_macros=True)))
            container('target', ['openroad', '-python', '/scripts/physical_target_odb.py'])
            report['target'] = json.loads((out / 'target-odb.json').read_text())
            if report['target']['database_sha256'] != sha(odb):
                raise ValueError('Target role source database changed')
        context = json.loads((out / 'context.json').read_text())
        if context['database_sha256'] != sha(odb) or not context['exclusions']['clear']:
            raise ValueError('Changed geometry source or occupied reserved corridor')
        units = context['dbu_per_micron']
        census = Counter(v['cell'] for v in context['instances'].values())
        area = sum((v['bbox_dbu'][2]-v['bbox_dbu'][0])*(v['bbox_dbu'][3]-v['bbox_dbu'][1])
                   for v in context['instances'].values()) / units**2
        report.update(cell_types=dict(sorted(census.items())), placed_instance_area_um2=round(area, 4),
                      corridor_clear=True, macros={k: v for k, v in context['instances'].items() if v['macro']})
        shutil.copyfile(worker, out / 'physical_checkpoint_sta.py')
        request = dict(config='/work/core/' + str(resolved.relative_to(design)), database=state['odb'],
                       **extra_request)
        (out / 'request.json').write_text(json.dumps(request, indent=2) + '\n')
        container('fresh-sta', ['python3', '/probe/physical_checkpoint_sta.py'])
        report['fresh_timing'] = json.loads((out / 'fresh-timing.json').read_text())
        if bundle:
            report['target_path_timing'] = json.loads((out / 'target-path-timing.json').read_text())
            report['target_path_expected'] = extra_request['path_expected']
            report['measurement_quality'] = {}
            for corner, measured in report['fresh_timing'].items():
                quality = measurement_quality((out / corner / 'checks.rpt').read_text(), context,
                                              report['target']['disconnected_outputs'])
                count = measured['design__max_fanout_violation__count__corner:' + corner]
                if len(quality['fanout_violations']) != count:
                    raise ValueError('Fanout driver list differs from fresh metric')
                report['measurement_quality'][corner] = quality
        report['estimation_modes'] = {corner: estimation_mode((out / corner / 'openroad-stamidpnr.log').read_text())
                                      for corner in report['fresh_timing']}
        if extra_request['verify_nominal_layer_rc']:
            for corner in report['fresh_timing']:
                if 'PINWHEEL_NOMINAL_LAYER_RC_VERIFIED' not in (out / corner / 'openroad-stamidpnr.log').read_text():
                    raise ValueError('Nominal layer RC verification missing')
            report['nominal_layer_rc_verified'] = True
        if any(sha(ROOT / p) != digest for p, digest in report['inputs_sha256'].items()):
            raise ValueError('Inputs changed during diagnostics')
        report.update(status='passed', boundary='Fresh export, geometry and independent corner STA of the selected completed ODB. Propagated clocks and explicit placement/coarse-route RC mode; no inherited timing metrics. Fast screen mixes -40 C cells/-55 C SRAM. Diagnostic completion is not timing/electrical closure or extracted timing.')
    except BaseException as error:
        report.update(status='failed', error=f'{type(error).__name__}: {error}')
        raise
    finally:
        report['elapsed_seconds'] = round(time.monotonic()-started, 3)
        report['artifacts_sha256'] = {str(p.relative_to(out)): sha(p) for p in out.rglob('*')
                                    if p.is_file() and p.name != 'report.json'}
        (out / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
        print(out / 'report.json', flush=True)


if __name__ == '__main__':
    main()
