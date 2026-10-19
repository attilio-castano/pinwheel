"""Bounded, isolated PDN geometry experiment; never a candidate flow/signoff.

Prepare on the host; run only under the campaign's single CAD resource lease.
The retained pre-placement ODB is read only. A new fixture places its43 public
pins at the exact frozen template before generating the proposed power grid.
No placement, CTS, routing, timing repair, or shared-PDK modification runs.
"""
import argparse
from datetime import datetime, timezone
import fnmatch
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import time


ROOT = Path(__file__).resolve().parents[1]
OLD = ROOT / 'build/physical/streaming-tt-optimized-d2-coarse-07/flow'
DESIGN = ROOT / 'build/physical/streaming-tt-optimized-d2-07'
SUPPORT = ROOT / 'build/streaming-tt-signoff/optimized-07-grt-final-fallback-official-fp3-02/tt/precheck'
PYTHON = ROOT / 'build/streaming-tt-signoff/precheck-venv/bin/python'
ENTRIES = ('scripts/streaming_tt_pdn_probe.py', 'scripts/streaming_tt_pdn_geometry.py',
           'physical/streaming_tt/pdn.tcl')
OFFICIAL_DECK = {
    'pin_check.py': '276bfb85dae4078039b15fc13fe4ae0647e10eb34d5cdb2d6edb7bc176e27d39',
    'tech_data.py': '01c72c24c0f62f0a94818b0bcd044efae43f2cc4b1b6d9e8dadcf75bffb10e6d',
    'precheck_failure.py': 'da88e75a22052948f4d8bd3abba4f6f2a608acd232ccea94df1a1b6728c45990'}


def require(value, message):
    if not value:
        raise ValueError(message)


def sha(path):
    with Path(path).open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def write(path, value):
    Path(path).write_text(json.dumps(value, indent=2, allow_nan=False) + '\n')


def inventory(directory):
    files = sorted(Path(directory).rglob('*'))
    require(not any(path.is_symlink() for path in files), 'Aliased probe input')
    return {str(path.relative_to(directory)): sha(path) for path in files if path.is_file()}


def prepare(out):
    import streaming_tt_physical as P
    from streaming_tt_intake import dependency_closure
    from streaming_tt_pdn_geometry import admit
    out = Path(out).resolve()
    closure = dependency_closure(ROOT, (*ENTRIES, 'scripts/streaming_tt_physical.py', 'scripts/streaming_tt_lef_format.py'))
    sources = {name: hashlib.sha256(P.committed(ROOT / name)).hexdigest() for name in closure['files']}
    parent = OLD.parent / 'report.json'
    prior = json.loads(parent.read_text())
    require(prior.get('status') == 'flow_completed' and type(prior.get('exit_code')) is int and prior['exit_code'] == 0 and
            prior.get('inputs_unchanged_after_run') is True and prior.get('container_termination', {}).get('status') == 'absent',
            'Source floorplan producer is not closed')
    for name in ('11-openroad-tapendcapinsertion/tt_um_pinwheel_streaming_ready_d2.odb',
                 '13-openroad-generatepdn/_env.tcl', 'resolved.json'):
        require(sha(OLD / name) == prior.get('artifact_sha256', {}).get('flow/' + name), 'Source floorplan artifact changed: ' + name)
    template = DESIGN / 'inputs/tt_block_6x4_pgvdd.def'
    admission = admit(template, ROOT / 'physical/streaming_tt/pdn.tcl')
    out.mkdir(parents=True, exist_ok=False)
    inputs = out / 'inputs'; inputs.mkdir()
    for source, name in [(OLD / '11-openroad-tapendcapinsertion/tt_um_pinwheel_streaming_ready_d2.odb', 'source.odb'),
                         (OLD / '13-openroad-generatepdn/_env.tcl', 'environment.tcl'),
                         (OLD / 'resolved.json', 'resolved.json'), (template, 'template.def'),
                         (ROOT / ENTRIES[0], 'streaming_tt_pdn_probe.py'),
                         (ROOT / ENTRIES[1], 'streaming_tt_pdn_geometry.py'),
                         (ROOT / ENTRIES[2], 'pdn.tcl')]:
        require(source.is_file() and not source.is_symlink(), 'Missing regular probe input: ' + str(source))
        shutil.copyfile(source, inputs / name)
    deck = inputs / 'official'; deck.mkdir()
    for name, expected in OFFICIAL_DECK.items():
        require(sha(SUPPORT / name) == expected, 'Pinned official Pincheck source changed')
        shutil.copyfile(SUPPORT / name, deck / name)
    source_head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip()
    request = dict(schema='pinwheel.streaming-tt-pdn-probe-request.v1', qualified=False,
                   source_head=source_head, producer_sha256=sources, geometry_admission=admission,
                   source_database=str(OLD / '11-openroad-tapendcapinsertion/tt_um_pinwheel_streaming_ready_d2.odb'),
                   source_database_sha256=sha(inputs / 'source.odb'), pdk=str(DESIGN / 'pdk'),
                   parent_report=str(parent), parent_report_sha256=sha(parent),
                   timeout_seconds=180,
                   boundary='Geometry-only pre-placement fixture, no candidate flow or physical acceptance.')
    write(inputs / 'request.json', request)
    seal = dict(schema='pinwheel.streaming-tt-pdn-probe-preparation.v1', prepared_utc=datetime.now(timezone.utc).isoformat(),
                qualified=False, native_executed=False, source_head=source_head, input_sha256=inventory(inputs),
                geometry_admission=admission, producer_sha256=sources, pdk=str(DESIGN / 'pdk'),
                source_lock_sha256=sha(ROOT / 'tools/physical-toolchain.json'))
    write(out / 'preparation.json', seal)
    return seal


def container_command(out, image_id, name):
    require(name.startswith('pinwheel-') and name.replace('-', '').replace('_', '').isalnum(), 'Unsafe owned container name')
    out = Path(out).resolve()
    return ['docker', 'run', '--rm', '--name', name, '--network', 'none', '--cpus', '4',
            '--memory', '6g', '--memory-swap', '6g',
            '--mount', f'type=bind,source={out},target=/probe',
            '--mount', f'type=bind,source={out / "inputs"},target=/probe/inputs,readonly',
            '--mount', f'type=bind,source={DESIGN / "pdk"},target=/work/pdk,readonly',
            '--workdir', '/probe', '--entrypoint', 'python3', image_id,
            '-B', '/probe/inputs/streaming_tt_pdn_probe.py', '--native', '/probe/inputs/request.json']


def native(request_path):
    import librelane
    out = Path('/probe'); inputs = out / 'inputs'
    request = json.loads(Path(request_path).read_text())
    require(request['schema'] == 'pinwheel.streaming-tt-pdn-probe-request.v1' and request['timeout_seconds'] == 180,
            'Invalid native PDN probe request')
    require(sha(inputs / 'source.odb') == request['source_database_sha256'], 'Source floorplan changed')
    before = inventory(inputs)
    start = time.monotonic()
    events = []
    def run(argv, name):
        executable = Path(shutil.which(argv[0]) or argv[0]).resolve(strict=True)
        hashes = {str(Path(arg)): sha(arg) for arg in argv if Path(arg).is_absolute() and Path(arg).is_file()}
        row = dict(name=name, argv=argv, executable=str(executable), executable_sha256=sha(executable), input_sha256=hashes)
        with (out / (name + '.log')).open('w') as log:
            result = subprocess.run(argv, stdout=log, stderr=subprocess.STDOUT,
                                    timeout=max(1, 120 - (time.monotonic() - start)))
        row.update(exit_code=result.returncode, executable_sha256_after=sha(executable),
                   input_sha256_after={path: sha(path) for path in hashes}, log_sha256=sha(out / (name + '.log')))
        events.append(row); write(out / 'native-journal.json', events)
        require(row['executable_sha256'] == row['executable_sha256_after'] and hashes == row['input_sha256_after'],
                'Native executable/input changed')
        require(result.returncode == 0, 'Native probe phase failed: ' + name)
    package = Path(librelane.__file__).resolve().parent
    scripts = package / 'scripts'
    captured = out / 'pinned-tool-source'; captured.mkdir()
    capture = {}
    for relative in ('scripts/openroad/cts.tcl', 'steps/openroad.py', 'scripts/openroad/common/set_global_connections.tcl'):
        source = package / relative
        require(source.is_file(), 'Missing pinned tool implementation: ' + relative)
        target = captured / relative.replace('/', '__'); shutil.copyfile(source, target)
        capture[relative] = dict(source=str(source), sha256=sha(source), captured_sha256=sha(target))
    config = json.loads((inputs / 'resolved.json').read_text())
    write(captured / 'resolved-cts.json', {key: value for key, value in config.items() if 'CTS' in key or key == 'MAX_FANOUT_CONSTRAINT'})
    write(captured / 'manifest.json', capture)
    for name in ('fixture', 'readback'):
        (out / (name + '-launch.py')).write_text('import sys\nsys.path.insert(0, "/probe/inputs")\n'
             'from streaming_tt_pdn_probe import odb_' + name + '\nodb_' + name + '()\n')
    run(['openroad', '-exit', '-python', str(out / 'fixture-launch.py')], 'fixture')
    # Include exact status for every Tcl command, not a successful log prefix.
    commands = [f'source {{{inputs / "environment.tcl"}}}', f'set ::env(SCRIPTS_DIR) {{{scripts}}}',
                'set ::env(VDD_NET) VPWR', 'set ::env(GND_NET) VGND',
                'read_db {/probe/fixture.odb}', 'source {/probe/inputs/pdn.tcl}',
                'pdngen -failed_via_report {/probe/failed-vias.rpt}',
                'write_db {/probe/generated.odb}', 'write_def {/probe/generated.def}',
                'write_abstract_lef {/probe/generated.lef}']
    lines = ['set journal [open {/probe/tcl-status.txt} w]']
    for index, command in enumerate(commands):
        lines += ['set code [catch {' + command + '} result]', f'puts $journal "{index} $code"',
                  'flush $journal', 'if {$code != 0} {puts stderr $result;close $journal;exit 1}']
    lines += ['close $journal']
    (out / 'probe.tcl').write_text('\n'.join(lines) + '\n')
    run(['openroad', '-exit', '-no_init', '-threads', '4', str(out / 'probe.tcl')], 'pdn')
    require((out / 'tcl-status.txt').read_text().splitlines() == [f'{k} 0' for k in range(len(commands))], 'Missing final Tcl status')
    run(['openroad', '-exit', '-python', str(out / 'readback-launch.py')], 'readback')
    argv = [sys.executable, str(scripts / 'klayout/stream_out.py'), '/probe/generated.def', '--output', '/probe/generated.gds',
            '--top', config['DESIGN_NAME'], '--conflict-resolution', 'RenameCell']
    for key, flag in [('KLAYOUT_PROPERTIES', '--lyp'), ('KLAYOUT_TECH', '--lyt'), ('KLAYOUT_DEF_LAYER_MAP', '--lym')]:
        argv += [flag, config[key]]
    tech = [path for pattern, path in config['TECH_LEFS'].items() if fnmatch.fnmatch(config['DEFAULT_CORNER'], pattern)]
    require(len(tech) == 1 and not config.get('MACROS'), 'Unsupported streamout view closure')
    for path in tech + (config.get('CELL_LEFS') or []) + (config.get('EXTRA_LEFS') or []) + (config.get('PAD_LEFS') or []):
        argv += ['--input-lef', path]
    for path in (config.get('CELL_GDS') or []) + (config.get('EXTRA_GDS') or []) + (config.get('PAD_GDS') or []):
        argv += ['--with-gds-file', path]
    run(argv, 'streamout')
    require(inventory(inputs) == before, 'Frozen probe inputs changed')
    require(all(sha(row['source']) == row['sha256'] for row in capture.values()), 'Pinned CTS/PG source changed')
    write(out / 'native-report.json', dict(schema='pinwheel.streaming-tt-pdn-probe-native.v1', completed=True,
          qualified=False, physical_acceptance=False, request_sha256=sha(request_path),
          source_database_sha256=request['source_database_sha256'], generated_database_sha256=sha(out / 'generated.odb'),
          geometry_readback_sha256=sha(out / 'geometry-readback.json'), generated_lef_sha256=sha(out / 'generated.lef'),
          generated_gds_sha256=sha(out / 'generated.gds'), input_sha256=before, inputs_unchanged=True,
          elapsed_seconds=time.monotonic() - start, boundary=request['boundary']))


def odb_fixture():
    """Only called by OpenROAD's embedded Python, where the odb API is pinned."""
    import odb
    from streaming_tt_pdn_geometry import template_pins
    out = Path('/probe'); inputs = out / 'inputs'
    pins = template_pins((inputs / 'template.def').read_text())
    db = odb.read_db(odb.dbDatabase.create(), str(inputs / 'source.odb'))
    block = db.getChip().getBlock()
    require(block.getDbUnitsPerMicron() == 1000, 'Wrong native source DBU scale')
    terms = {term.getName(): term for term in block.getBTerms()}
    signal_terms = {name: term for name, term in terms.items() if str(term.getSigType()) not in ('POWER', 'GROUND')}
    require(set(signal_terms) == set(pins) and all(not list(term.getBPins()) for term in terms.values()),
            'Source is not the fresh retained unplaced43-pin/no-PG-port floorplan')
    require(all(not list(net.getSWires()) for net in block.getNets() if str(net.getSigType()) in ('POWER', 'GROUND')),
            'Source contains an existing special-wire power grid')
    instance_count = len(list(block.getInsts()))
    layer = db.getTech().findLayer('Metal4'); require(layer is not None, 'Missing Metal4')
    for name, bounds in pins.items():
        pin = odb.dbBPin_create(terms[name]); pin.setPlacementStatus('FIRM')
        odb.dbBox_create(pin, layer, *bounds)
    odb.write_db(db, str(out / 'fixture.odb'))
    write(out / 'fixture-report.json', dict(source_instance_count=instance_count, qualified=False,
          source_sha256=sha(inputs / 'source.odb'), fixture_sha256=sha(out / 'fixture.odb')))


def odb_readback():
    import odb
    from streaming_tt_pdn_geometry import template_pins, Grid, validate_power_ports, clearance
    out = Path('/probe'); inputs = out / 'inputs'
    pins = template_pins((inputs / 'template.def').read_text())
    instance_count = json.loads((out / 'fixture-report.json').read_text())['source_instance_count']
    generated_db = odb.read_db(odb.dbDatabase.create(), str(out / 'generated.odb'))
    generated = generated_db.getChip().getBlock()
    require(len(list(generated.getInsts())) == instance_count, 'PDN probe changed the instance inventory')
    ports, power = [], []
    for term in generated.getBTerms():
        if str(term.getSigType()) in ('POWER', 'GROUND'):
            for pin in term.getBPins():
                for box in pin.getBoxes():
                    ports.append(dict(net=term.getName(), layer=box.getTechLayer().getName(),
                                      bounds_dbu=[box.xMin(), box.yMin(), box.xMax(), box.yMax()]))
    grid = Grid.from_tcl((inputs / 'pdn.tcl').read_text())
    port_result = validate_power_ports(ports, grid)
    for net in generated.getNets():
        if str(net.getSigType()) not in ('POWER', 'GROUND'):
            continue
        for wire in net.getSWires():
            for box in wire.getWires():
                # A via's entire translated bounding box conservatively covers
                # its M4 enclosure; including all via layers can only reject.
                if box.isVia() or box.getTechLayer().getName() == 'Metal4':
                    power.append(dict(net=net.getName(), kind='via_all_layers_bbox' if box.isVia() else 'Metal4_wire',
                                      bounds_dbu=[box.xMin(), box.yMin(), box.xMax(), box.yMax()]))
    require(power, 'Missing actual power geometry')
    minimum = min(clearance(row['bounds_dbu'], pin) for row in power for pin in pins.values())
    require(minimum >= grid.public_clearance, 'Actual power metal/via bounding box violates public-pin clearance')
    write(out / 'geometry-readback.json', dict(ports=ports, power_shapes=power, power_port_result=port_result,
          minimum_actual_public_clearance_dbu=minimum, source_instance_count=instance_count,
          public_pins_placed_from_frozen_template=True, qualified=False))


def pincheck(out):
    out = Path(out).resolve()
    import gdstk
    require(sys.version_info[:2] == (3, 12) and sys.flags.optimize == 0 and gdstk.__version__ == '0.9.52',
            'Official Pincheck requires unoptimized pinned Python3.12/gdstk0.9.52')
    require(inventory(out / 'inputs/official') == OFFICIAL_DECK, 'Official Pincheck source membership/bytes changed')
    sys.path.insert(0, str(out / 'inputs/official'))
    import pin_check
    pin_check.pin_check(str(out / 'generated.gds'), str(out / 'official-format.lef'),
                        str(out / 'inputs/template.def'), 'tt_um_pinwheel_streaming_ready_d2', False, 'ihp-sg13cmos5l')
    write(out / 'pincheck-result.json', dict(official_pincheck_passed=True, qualified=False,
          gds_sha256=sha(out / 'generated.gds'), lef_sha256=sha(out / 'official-format.lef'),
          checker_sha256=sha(out / 'inputs/official/pin_check.py')))


def run_host(out, name):
    import streaming_tt_physical as P
    from streaming_tt_pdk import verify_complete_pdk
    from streaming_tt_lef_format import canonicalize
    out = Path(out).resolve()
    require({path.name for path in out.iterdir()} == {'inputs', 'preparation.json'}, 'Probe output is not a fresh prepared directory')
    seal = json.loads((out / 'preparation.json').read_text())
    require(inventory(out / 'inputs') == seal['input_sha256'], 'Prepared probe inputs changed')
    P.verify_files(ROOT, seal['producer_sha256'])
    require(sha(ROOT / 'tools/physical-toolchain.json') == seal['source_lock_sha256'], 'Pinned toolchain lock changed')
    lock = P.read(ROOT / 'tools/physical-toolchain.json')
    verify_complete_pdk(DESIGN / 'pdk', lock, P.read(ROOT / 'tools/streaming-tt-signoff.json'))
    pdk_before = inventory_pdk(DESIGN / 'pdk')
    runtime = P.inspect_runtime(lock)
    command = container_command(out, runtime['image_id'], name)
    with (out / 'container.log').open('w') as log:
        result = subprocess.run(command, stdout=log, stderr=subprocess.STDOUT, timeout=140)
    require(result.returncode == 0, 'Native PDN geometry probe failed; retain logs/outputs')
    validate_native(out, seal)
    formatted, formatting = canonicalize((out / 'generated.lef').read_text())
    (out / 'official-format.lef').write_text(formatted)
    write(out / 'lef-format.json', formatting)
    argv = [str(PYTHON), '-B', str(out / 'inputs/streaming_tt_pdn_probe.py'), '--pincheck', str(out)]
    with (out / 'pincheck.log').open('w') as log:
        result = subprocess.run(argv, stdout=log, stderr=subprocess.STDOUT, timeout=20,
                                env=dict(os.environ, PYTHONDONTWRITEBYTECODE='1', PYTHONNOUSERSITE='1', PYTHONPATH='', PYTHONOPTIMIZE='0'))
    require(result.returncode == 0 and (out / 'pincheck-result.json').is_file(), 'Unchanged official Pincheck failed')
    require(inventory(out / 'inputs') == seal['input_sha256'] and P.inspect_runtime(P.read(ROOT / 'tools/physical-toolchain.json')) == runtime,
            'Probe inputs/runtime changed after official Pincheck')
    P.verify_files(ROOT, seal['producer_sha256'])
    require(inventory_pdk(DESIGN / 'pdk') == pdk_before, 'Pinned PDK changed during probe')
    write(out / 'report.json', dict(schema='pinwheel.streaming-tt-pdn-probe-host.v1', geometry_probe_completed=True,
          qualified=False, physical_acceptance=False, candidate_flow_completed=False,
          preparation_sha256=sha(out / 'preparation.json'), native_report_sha256=sha(out / 'native-report.json'),
          official_pincheck_sha256=sha(out / 'pincheck-result.json'), runtime=runtime, argv=command,
          input_sha256=seal['input_sha256'], inputs_unchanged=True, pdk_before_after=pdk_before,
          artifact_sha256=inventory(out),
          boundary='Only isolated PG/public-pin geometry admitted. Full candidate DRC/LVS/connectivity/timing remain mandatory.'))


def validate_native(out, seal):
    from streaming_tt_pdn_geometry import Grid, validate_power_ports
    out = Path(out)
    report = json.loads((out / 'native-report.json').read_text())
    request = json.loads((out / 'inputs/request.json').read_text())
    require(report.get('schema') == 'pinwheel.streaming-tt-pdn-probe-native.v1' and report.get('completed') is True and
            report.get('qualified') is False and report.get('physical_acceptance') is False and
            report.get('inputs_unchanged') is True and report.get('input_sha256') == seal['input_sha256'] and
            inventory(out / 'inputs') == seal['input_sha256'] and
            report.get('request_sha256') == sha(out / 'inputs/request.json') and
            report.get('source_database_sha256') == request['source_database_sha256'],
            'Native probe did not close on frozen inputs')
    for key, name in [('generated_database_sha256', 'generated.odb'), ('geometry_readback_sha256', 'geometry-readback.json'),
                      ('generated_lef_sha256', 'generated.lef'), ('generated_gds_sha256', 'generated.gds')]:
        require(report.get(key) == sha(out / name) and (out / name).stat().st_size > 0, 'Native output binding changed: ' + name)
    geometry = json.loads((out / 'geometry-readback.json').read_text())
    grid = Grid.from_tcl((out / 'inputs/pdn.tcl').read_text())
    require(geometry.get('qualified') is False and geometry.get('power_port_result') == validate_power_ports(geometry['ports'], grid) and
            type(geometry.get('minimum_actual_public_clearance_dbu')) is int and
            geometry['minimum_actual_public_clearance_dbu'] >= grid.public_clearance,
            'Actual PG geometry readback is inconsistent')
    journal = json.loads((out / 'native-journal.json').read_text())
    require([row.get('name') for row in journal] == ['fixture', 'pdn', 'readback', 'streamout'] and
            all(type(row.get('exit_code')) is int and row['exit_code'] == 0 and
                row.get('executable_sha256') == row.get('executable_sha256_after') and
                row.get('input_sha256') == row.get('input_sha256_after') and
                row.get('log_sha256') == sha(out / (row['name'] + '.log')) for row in journal), 'Native phases did not both close')
    return report


def inventory_pdk(path):
    """Hash contents and exact link spellings/targets without mutating the PDK."""
    root = Path(path).resolve(strict=True)
    result = {}
    for path in sorted(root.rglob('*')):
        relative = str(path.relative_to(root))
        if path.is_symlink():
            target = path.resolve(strict=True)
            require(target.is_relative_to(root) and (target.is_file() or target.is_dir()), 'Escaping/broken PDK symlink')
            result[relative] = dict(link=os.readlink(path), target=str(target),
                                   sha256=sha(target) if target.is_file() else None,
                                   directory=target.is_dir())
        elif path.is_file():
            result[relative] = dict(sha256=sha(path))
    require(result, 'Empty PDK inventory')
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--prepare', type=Path)
    mode.add_argument('--run', type=Path)
    mode.add_argument('--native', type=Path)
    mode.add_argument('--pincheck', type=Path)
    parser.add_argument('--container-name')
    args = parser.parse_args()
    if args.prepare: prepare(args.prepare)
    elif args.run: run_host(args.run, args.container_name or '')
    elif args.native: native(args.native)
    else: pincheck(args.pincheck)


if __name__ == '__main__': main()
