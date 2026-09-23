#!/usr/bin/env python3
"""Run one capped local Tcl repair against a settled physical checkpoint.

The source design and PDK are read-only. The copied recipe writes only probe
artifacts; a successful probe is not functional validation or routed closure.
"""
import argparse
import importlib.util
import json
from pathlib import Path
import shutil
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]


def worker():
    from librelane.flows.classic import Classic
    from librelane.state import State
    from librelane.steps.openroad import STAMidPNR
    from physical_checkpoint_sta import analysis_tcl

    out = Path('/probe')
    request = json.loads((out / 'request.json').read_text())
    cfg = json.loads(Path(request['config']).read_text())
    if request.get('nominal_layer_rc'):
        cfg['LAYERS_RC'] = request['nominal_layer_rc']
    extra = out / 'executed.tcl'
    extra.write_text(analysis_tcl({'verify_nominal_layer_rc': True}) +
                     (out / 'recipe.tcl').read_text())
    cfg.update(DEFAULT_CORNER=request['corner'], STA_CORNERS=[request['corner']],
               OPENROAD_THREADS=2, STA_EXTRA_CORNER_TCL_FILE=str(extra))
    config = Classic(cfg, pdk_root='/work/pdk', pdk='ihp-sg13cmos5l',
                     design_dir='/work/core').config
    fresh = State.load({'odb': request['database'], 'metrics': {}})
    STAMidPNR(config=config, state_in=fresh).start(step_dir=str(out / 'sta'))


def host():
    from validation_run import Commands, fresh_directory, sha

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--physical-tag', required=True)
    parser.add_argument('--tag', required=True)
    parser.add_argument('--recipe', type=Path, required=True)
    parser.add_argument('--corner', default='nom_slow_1p08V_125C')
    parser.add_argument('--nominal-layer-rc', action='store_true',
                        help='Set verified nominal LEF layer RC when the source has no explicit RC override')
    args = parser.parse_args()
    if not args.physical_tag.replace('-', '').replace('_', '').isalnum():
        parser.error('Invalid physical tag')
    modules = {}
    for name, file in [('check', 'check-mapped-import.py'), ('diagnostic', 'check-mapped-physical.py')]:
        spec = importlib.util.spec_from_file_location(name, ROOT / 'scripts' / file)
        modules[name] = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(modules[name])
    check, diagnostic = modules['check'], modules['diagnostic']
    inv_path = ROOT / 'build/physical' / (args.physical_tag + '-invocation.json')
    physical_path = ROOT / 'build/physical' / (args.physical_tag + '-report.json')
    inv, physical = [json.loads(p.read_text()) for p in [inv_path, physical_path]]
    if ('exit_code' not in inv or physical['invocation_sha256'] != sha(inv_path) or
            check.observe_container('pinwheel-' + args.physical_tag) not in ('absent', 'stopped')):
        raise ValueError('Require a settled, reported physical run')
    design = ROOT / 'build/physical' / inv['design']
    resolved = design / 'runs' / args.physical_tag / 'resolved.json'
    if (sha(resolved) != physical['resolved_config_sha256'] or
            sha(design / 'inputs.json') != inv['inputs_sha256'] or
            sha(Path(inv['pdk_root']) / 'installed.json') != inv['pdk_receipt_sha256']):
        raise ValueError('Changed physical preparation, configuration or PDK identity')
    for name, digest in json.loads((design / 'inputs.json').read_text())['files_sha256'].items():
        if sha(design / name) != digest:
            raise ValueError('Changed prepared view: ' + name)
    cfg = json.loads(resolved.read_text())
    nominal = None
    if args.nominal_layer_rc:
        from physical_route_intake import ihp_layer_rc
        if cfg.get('LAYERS_RC') or cfg.get('VIAS_R'):
            raise ValueError('Cannot replace an existing RC override with nominal values')
        tech_lef = Path(inv['pdk_root']) / 'ihp-sg13cmos5l/libs.ref/sg13cmos5l_stdcell/lef/sg13cmos5l_tech.lef'
        nominal = ihp_layer_rc(tech_lef)
    if args.corner not in cfg['STA_CORNERS'] or not (cfg.get('LAYERS_RC') or nominal):
        raise ValueError('Require a configured corner and explicit layer RC')
    state_path, state, database = diagnostic.checkpoint(physical, design)
    out = fresh_directory(ROOT / 'build/physical/repair-probes', args.tag)
    recipe = args.recipe.resolve()
    helper = ROOT / 'scripts/physical_checkpoint_sta.py'
    for source, destination in [(recipe, 'recipe.tcl'), (Path(__file__), 'probe.py'),
                                (helper, helper.name)]:
        shutil.copyfile(source, out / destination)
    request = dict(config='/work/core/' + str(resolved.relative_to(design)),
                   database=state['odb'], corner=args.corner, nominal_layer_rc=nominal)
    (out / 'request.json').write_text(json.dumps(request, indent=2) + '\n')
    run = Commands(ROOT, out, default_timeout=120)
    name = 'pinwheel-repair-' + args.tag
    dependencies = [Path(__file__), helper, recipe, state_path, database, resolved,
                    inv_path, physical_path, design / 'inputs.json', Path(inv['pdk_root']) / 'installed.json',
                    ROOT / 'scripts/check-mapped-physical.py', ROOT / 'scripts/check-mapped-import.py',
                    ROOT / 'scripts/physical_checkpoint.py', ROOT / 'scripts/validation_run.py',
                    ROOT / 'scripts/process_group.py']
    if nominal:
        dependencies += [tech_lef, ROOT / 'scripts/physical_route_intake.py']
    report = dict(schema=1, status='running', commands=run.records, source_database=str(database.relative_to(ROOT)),
                  source_database_sha256=sha(database), physical_tag=args.physical_tag,
                  inputs_sha256={str(p.resolve()): sha(p) for p in dependencies},
                  containers={name: 'unconfirmed'}, image_id=inv['image_id'],
                  bounds=dict(seconds=120, cpus=2, memory_gib=2), nominal_layer_rc=nominal)
    started = time.monotonic()

    def save():
        (out / 'report.json').write_text(json.dumps(report, indent=2) + '\n')

    save()
    try:
        run(['docker', 'run', '--rm', '--pull', 'never', '--name', name, '--network', 'none',
             '--read-only', '--cpus', '2', '--memory', '2g', '--tmpfs', '/tmp:rw,size=128m',
             '--mount', f'type=bind,source={design},target=/work/core,readonly',
             '--mount', f'type=bind,source={inv["pdk_root"]},target=/work/pdk,readonly',
             '--mount', f'type=bind,source={out},target=/probe', '--workdir', '/probe',
             inv['image_id'], 'python3', '-B', '/probe/probe.py', '--worker'], 'probe')
        report.update(status='passed', boundary='Local recipe execution only; fresh functional, geometry and matched timing validation remain required. Source design and PDK mounted read-only.')
    except BaseException as error:
        report.update(status='failed', error=f'{type(error).__name__}: {error}')
        save()
        subprocess.run(['docker', 'stop', '--time', '2', name], capture_output=True, timeout=15)
        raise
    finally:
        report['containers'][name] = check.observe_container(name)
        report['elapsed_seconds'] = round(time.monotonic() - started, 3)
        report['source_unchanged'] = all(sha(p) == h for p, h in report['inputs_sha256'].items())
        report['artifacts_sha256'] = {str(p.relative_to(out)): sha(p) for p in out.rglob('*')
                                    if p.is_file() and p.name != 'report.json'}
        if report['containers'][name] not in ('absent', 'stopped') or not report['source_unchanged']:
            report['status'] = 'failed'
        save()
        print(out / 'report.json', flush=True)
        if report['status'] != 'passed':
            raise RuntimeError('Probe failed; inspect its preserved receipt')


if __name__ == '__main__':
    if sys.argv[1:] == ['--worker']:
        worker()
    else:
        host()
