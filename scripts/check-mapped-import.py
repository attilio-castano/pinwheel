#!/usr/bin/env python3
"""Verify the actual floorplan ODB preserves the selected mapping before placement."""
import argparse
import json
from pathlib import Path
import subprocess
import shutil
import time

from mapped_physical import compare_connections, signal_view
import physical_checkpoint
from validation_run import Commands, fresh_directory, sha

ROOT = Path(__file__).resolve().parents[1]


def observe_container(name):
    result = subprocess.run(['docker', 'inspect', '--type', 'container', name],
                            capture_output=True, text=True, timeout=15)
    if result.returncode:
        if 'No such ' in result.stderr and name in result.stderr:
            return 'absent'
        raise RuntimeError('Cannot confirm container termination: ' + result.stderr)
    return 'running' if json.loads(result.stdout)[0]['State']['Running'] else 'stopped'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--tag', required=True, help='Completed physical-run tag')
    parser.add_argument('--check-tag', help='Fresh receipt name; defaults to the physical-run tag')
    parser.add_argument('--placed-macros', action='store_true', help='Check a completed GeneratePDN checkpoint before cell placement')
    args = parser.parse_args()
    invocation_path = ROOT / 'build/physical' / (args.tag + '-invocation.json')
    invocation = json.loads(invocation_path.read_text())
    stop = 'OpenROAD.GeneratePDN' if args.placed_macros else 'OpenROAD.Floorplan'
    if invocation.get('exit_code') != 0 or invocation['stop_step'] != stop:
        raise ValueError('Require a completed bounded floorplan import')
    if observe_container('pinwheel-' + args.tag) not in ('absent', 'stopped'):
        raise ValueError('Import container still active')
    design = ROOT / 'build/physical' / invocation['design']
    inputs_path = design / 'inputs.json'
    inputs = json.loads(inputs_path.read_text())
    if sha(inputs_path) != invocation['inputs_sha256'] or 'mapped_input' not in inputs:
        raise ValueError('Changed or nonmapped preparation')
    for rel, digest in inputs['files_sha256'].items():
        if sha(design / rel) != digest:
            raise ValueError('Changed prepared input: ' + rel)
    states = list((design / 'runs' / args.tag).glob('*-' + stop.lower().replace('.', '-') + '/state_out.json'))
    if len(states) != 1:
        raise ValueError('Ambiguous floorplan state')
    state_path = states[0]
    state = json.loads(state_path.read_text())
    odb = physical_checkpoint.artifact_path(state['odb'], design)
    nl = physical_checkpoint.artifact_path(state['nl'], design)
    library = ROOT / 'build/tools/ihp-cmos5l/sg13cmos5l_stdcell_typ_1p20V_25C.lib'
    provenance = inputs['mapped_input']
    master = (json.loads((design / 'target.json').read_text())['macro']['master']
              if inputs.get('physical_target') else 'RM_IHPSG13_1P_64x64_c2_bm_bist')
    macro = design / ('macro/' + master + '_typ_1p20V_25C.lib')
    if (sha(library) != provenance['libraries_sha256']['typical'] or
            sha(macro) != provenance['macro_views_sha256']['lib/' + macro.name]):
        raise ValueError('Changed import read-back library')
    check_tag = args.check_tag or args.tag
    out = fresh_directory(design / 'checks', check_tag)
    run = Commands(ROOT, out, default_timeout=120)
    started = time.monotonic()
    frozen_paths = [Path(__file__), ROOT / 'scripts/mapped_physical.py',
                    ROOT / 'scripts/validation_run.py', ROOT / 'scripts/process_group.py',
                    ROOT / 'scripts/physical_checkpoint.py', invocation_path, inputs_path,
                    state_path, odb, nl, design / 'mapped.json', library, macro]
    frozen = {str(p.relative_to(ROOT)): sha(p) for p in frozen_paths}
    if args.placed_macros and not inputs.get('physical_target'):
        raise ValueError('Placed macro verification requires an explicit physical target')
    if inputs.get('physical_target'):
        for p in [ROOT / 'scripts/physical_target_odb.py', *[design / n for n in
                  ['target.json', 'state-ownership.json', 'path-roles.json', 'macro-geometry.json']]]:
            frozen[str(p.relative_to(ROOT))] = sha(p)
    report = dict(schema=1, status='running', commands=run.records, inputs_sha256=frozen,
                  flow_container='absent-or-stopped', containers={})
    name = 'pinwheel-mapped-readback-' + check_tag
    try:
        (out / 'export.tcl').write_text(f'read_db {state["odb"]}\nwrite_verilog /probe/odb.v\nexit\n')
        commands = ['openroad', '-exit', '/probe/export.tcl']
        if inputs.get('physical_target'):
            shutil.copyfile(ROOT / 'scripts/physical_target_odb.py', out / 'target-odb.py')
            (out / 'target-request.json').write_text(json.dumps(dict(database=state['odb'], design='/work/core',
                                                                  placed_macros=args.placed_macros)))
            (out / 'export.tcl').write_text((out / 'export.tcl').read_text().replace('exit\n', ''))
            (out / 'driver.py').write_text('import subprocess\nsubprocess.run(["openroad", "-exit", "/probe/export.tcl"], check=True)\nsubprocess.run(["openroad", "-python", "/probe/target-odb.py"], check=True)\n')
            commands = ['python3', '/probe/driver.py']
        report['containers'][name] = 'unconfirmed'
        try:
            run(['docker', 'run', '--rm', '--pull', 'never', '--name', name,
                 '--network', 'none', '--read-only', '--cpus', '2', '--memory', '2g',
                 '--tmpfs', '/tmp:rw,size=64m', '--mount', f'type=bind,source={design},target=/work/core,readonly',
                 '--mount', f'type=bind,source={out},target=/probe', '--workdir', '/probe',
                 invocation['image_id'], *commands], 'odb-export')
        except BaseException:
            subprocess.run(['docker', 'stop', '--time', '2', name], capture_output=True, timeout=15)
            raise
        finally:
            report['containers'][name] = observe_container(name)
            if report['containers'][name] == 'running':
                raise RuntimeError('Read-back container remains active')
        cad = ROOT / 'build/tools/oss-cad-suite/bin/yosys'
        frozen[str(cad.relative_to(ROOT))] = sha(cad)
        reference = json.loads((design / 'mapped.json').read_text())['modules']['tt_um_pinwheel']
        if inputs.get('physical_target'):
            report['target'] = json.loads((out / 'target-odb.json').read_text())
            if report['target']['database_sha256'] != sha(odb):
                raise ValueError('Target endpoint export came from another database')
        report['comparisons'] = {}
        report['explicit_power_ports'] = {}
        for label, file in [('odb', out / 'odb.v'), ('state-netlist', nl)]:
            script = out / (label + '.ys')
            mapped = out / (label + '.json')
            script.write_text('\n'.join([f'read_liberty -lib {library}', f'read_liberty -lib {macro}',
                f'read_verilog {file}', 'hierarchy -check -top tt_um_pinwheel',
                'check -assert', f'write_json {mapped}', '']))
            run([cad, '-Q', '-T', '-s', script], label + '-readback')
            module = json.loads(mapped.read_text())['modules']['tt_um_pinwheel']
            if args.placed_macros:
                module, removed = signal_view(module, report['target']['power_ports'])
                report['explicit_power_ports'][label] = removed
            report['comparisons'][label] = compare_connections(reference, module)
        if report['comparisons']['odb'] != report['comparisons']['state-netlist']:
            raise ValueError('ODB and saved netlist comparisons differ')
        if any(sha(ROOT / p) != h for p, h in frozen.items()):
            raise ValueError('Input changed during import verification')
        report.update(status='passed', state_sha256=sha(state_path),
                      boundary='Every retained named signal cell/pin and package-bit connection preserved in a fresh ODB export and the saved NL. Known ties folded and counted; declared isolated power ports checked separately in OpenDB. Target geometry checks are explicit; no cell placement, repair or routing claim.')
    except BaseException as error:
        report.update(status='failed', error=f'{type(error).__name__}: {error}')
        raise
    finally:
        report['elapsed_seconds'] = round(time.monotonic()-started, 3)
        report['artifacts_sha256'] = {p.name: sha(p) for p in out.iterdir() if p.is_file() and p.name != 'report.json'}
        (out / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
        print(out / 'report.json', flush=True)
    verified = dict(status='passed', inputs_sha256=sha(inputs_path), state_sha256=sha(state_path),
                    state=str(state_path), report=str(out / 'report.json'), report_sha256=sha(out / 'report.json'))
    verified['continuation_step'] = 'Odb.RemovePDNObstructions' if args.placed_macros else 'OpenROAD.DumpRCValues'
    with (design / ('macro-verified.json' if args.placed_macros else 'import-verified.json')).open('x') as stream:
        stream.write(json.dumps(verified, indent=2) + '\n')
    physical_checkpoint.capture(state_path, out / 'continuation-manifest.json', design)


if __name__ == '__main__':
    main()
