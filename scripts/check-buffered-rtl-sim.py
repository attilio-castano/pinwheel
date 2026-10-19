#!/usr/bin/env python3
"""Fresh finite Icarus replay of emitted buffered serial RTL and digital memory.

The selected source archive and committed producer archive are separate. This
gate does not call the historical serial gate's main, predecessor, synthesis,
mapping or vendor macro paths. It reuses its public-pin peers and finite
frontend fixture, under the explicit digital SRAM law below.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tarfile
import time
import types

ROOT = Path(__file__).resolve().parents[1]
DRIVER = 'scripts/check-buffered-rtl-sim.py'
PRODUCER = (DRIVER, 'scripts/validation_run.py', 'scripts/process_group.py',
            'test/test_buffered_rtl_sim.py')
REQUIRED = ('lean-toolchain', 'lakefile.toml', 'lake-manifest.json',
    'tools/hardware-toolchain.json', 'scripts/check-buffered-sram-serial.py',
    'test/BufferedSramSerialExport.lean', 'test/SramArtifactEmit.lean',
    'physical/buffered_sram_serial_wrapper.sv', 'physical/buffered_sram_memory.sv',
    'physical/buffered_sram_serial_host_bridge.sv')
SCHEMA = 'pinwheel.buffered-rtl-simulator.v1'
BOUNDARY = ('Finite independent Icarus simulation of newly emitted frontend/controller RTL, '
    'the actual package/memory wrappers and a public-pin bridge, under an explicit synchronous '
    'digital SRAM model with distinct initial bank contents and Q values. Frontend replay checks '
    'typed pre-edge outputs and post-edge outputs/registers; three independent public-pin '
    'SPI/JTAG/I2C peers check protocol behavior and repeated retained reads. No historical RTL '
    'or receipt input, synthesis, ABC, mapping, vendor macro timing/electrical claim, universal '
    'simulation proof, or generic Verilog/Yosys/CIRCT correctness claim.')

DIGITAL_MEMORY = '''module RM_IHPSG13_1P_64x64_c2_bm_bist(
input A_CLK,A_MEN,A_DLY,A_WEN,A_REN,
input [5:0] A_ADDR, input [63:0] A_DIN,A_BM, output reg [63:0] A_DOUT,
input A_BIST_CLK,A_BIST_EN,A_BIST_MEN,A_BIST_WEN,A_BIST_REN,
input [5:0] A_BIST_ADDR, input [63:0] A_BIST_DIN,A_BIST_BM);
// Explicit digital law only: writes win; writes/idle hold Q; read returns
// the pre-edge cell. The actual wrapper ties MEN high, BM all ones and BIST off.
reg [63:0] memory [0:63];
integer k;
always @(posedge A_CLK) if(A_MEN) begin
  if(A_WEN) begin
    for(k=0;k<64;k=k+1) if(A_BM[k]) memory[A_ADDR][k] <= A_DIN[k];
  end else if(A_REN) A_DOUT <= memory[A_ADDR];
end
endmodule
'''
POISON_SEEDS = (0x96a53cc36a5ac33c, 0x695ac33c95a53cc3)


def digest(path):
    value = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b''):
            value.update(block)
    return value.hexdigest()


def write_json(path, value):
    path = Path(path)
    temporary = path.with_name(path.name + '.tmp')
    temporary.write_text(json.dumps(value, indent=2) + '\n')
    temporary.replace(path)


def parse_tree(text):
    tree = {}
    for entry in text.split('\0'):
        if not entry:
            continue
        metadata, path = entry.split('\t', 1)
        mode, kind, oid = metadata.split()
        if (path in tree or Path(path).is_absolute() or '..' in Path(path).parts or
                '\n' in path or '\r' in path or kind != 'blob' or mode not in ('100644', '100755')):
            raise RuntimeError('Expected unambiguous regular committed file: ' + path)
        tree[path] = oid
    if not tree:
        raise RuntimeError('Selected source tree is empty')
    return tree


def membership(root, tree, algorithm):
    root, hashes = Path(root).resolve(), {}
    for relative, oid in sorted(tree.items()):
        path = root / relative
        if path.is_symlink() or not path.is_file() or not path.resolve().is_relative_to(root):
            raise RuntimeError('Missing or redirected committed input: ' + relative)
        data = path.read_bytes()
        actual = hashlib.new(algorithm, f'blob {len(data)}\0'.encode() + data).hexdigest()
        if actual != oid:
            raise RuntimeError('Input differs from selected committed source: ' + relative)
        hashes[relative] = hashlib.sha256(data).hexdigest()
    return hashes


def fresh_snapshot(root):
    root = Path(root)
    if any((root / name).exists() for name in ('.git', '.lake', 'build')) or any(
            path.suffix in ('.pyc', '.olean') for path in root.rglob('*')):
        raise RuntimeError('Archive contains prior repository/build/cache state')


def check_environment(environment=None):
    environment = os.environ if environment is None else environment
    fixed = {'PYTHONPATH', 'PYTHONHOME', 'PYTHONSTARTUP', 'PYTHONPYCACHEPREFIX',
             'LEAN_PATH', 'LEAN_SRC_PATH', 'LEAN_SYSROOT', 'LAKE_HOME', 'LAKE_PACKAGES_DIR',
             'LAKE_CACHE_DIR', 'LD_PRELOAD', 'LD_LIBRARY_PATH', 'IVERILOG_ROOT', 'VPI_MODULE_PATH'}
    bad = sorted(key for key, value in environment.items()
                 if value and (key in fixed or key.startswith('DYLD_')))
    if bad:
        raise RuntimeError('Refuse import/compiler/cache/loader overrides: ' + ', '.join(bad))


def load_helpers(root):
    for name in ('process_group', 'validation_run'):
        path = Path(root) / 'scripts' / (name + '.py')
        module = types.ModuleType(name)
        module.__file__ = str(path)
        sys.modules[name] = module
        exec(compile(path.read_bytes(), str(path), 'exec'), module.__dict__)
    return sys.modules['validation_run']


def tool_identity(paths, manifest):
    """Include Icarus wrappers, payloads, preprocessor, targets, VPI and configs."""
    tools = {name: Path(path) for name, path in paths.items()}
    if any(not path.is_absolute() for path in tools.values()):
        raise RuntimeError('Selected tool paths must be absolute')
    circt = tools['circt'].parent.parent
    oss = tools['iverilog'].parent.parent
    lean = tools['lean'].parent.parent
    packages = manifest['packages']
    if (tools['circt'] != circt / 'bin/circt-opt' or
            circt.name != packages['circt']['directory'] or
            oss.name != packages['oss-cad-suite']['directory'] or
            tools['iverilog'] != oss / 'bin/iverilog' or tools['vvp'] != oss / 'bin/vvp' or
            tools['lake'] != lean / 'bin/lake'):
        raise RuntimeError('Selected tool paths do not match pinned package layout')
    for name, package in [('circt', circt), ('iverilog', oss), ('vvp', oss),
                          ('lean', lean), ('lake', lean)]:
        if not tools[name].resolve().is_relative_to(package.resolve()):
            raise RuntimeError('Selected executable escapes package: ' + name)
    if tools['lean'].read_bytes()[:4] not in (
            b'\xcf\xfa\xed\xfe', b'\xfe\xed\xfa\xcf', b'\xca\xfe\xba\xbe', b'\x7fELF'):
        raise RuntimeError('Selected Lean must be native')
    indexed = set(tools.values())
    indexed.update(oss / 'libexec' / name for name in ('iverilog', 'vvp', 'ivl', 'ivlpp', 'realpath'))
    ivl = oss / 'lib/ivl'
    if not ivl.is_dir() or not (ivl / 'vvp.conf').is_file() or not (ivl / 'vvp.tgt').is_file():
        raise RuntimeError('Missing Icarus backend/configuration directory')
    indexed.update(path for path in ivl.rglob('*') if path.is_file())
    for package in (circt, oss, lean):
        indexed.update((package / 'lib').glob('*.dylib'))
        indexed.update((package / 'lib').glob('*.so*'))
    indexed.update((lean / 'lib/lean').glob('*.dylib'))
    indexed.update((lean / 'lib/lean').glob('*.so*'))
    files = {}
    for path in sorted(indexed):
        if not path.is_file():
            raise RuntimeError('Missing selected tool dependency: ' + str(path))
        if path not in tools.values() and not any(
                path.resolve().is_relative_to(package.resolve()) for package in (circt, oss, lean)):
            raise RuntimeError('Selected tool dependency escapes package: ' + str(path))
        files[str(path)] = dict(sha256=digest(path), resolved=str(path.resolve()))
    archives = {}
    for key, package in [('circt', circt), ('oss-cad-suite', oss)]:
        archive = package.parent / packages[key]['archive']
        if not archive.is_file() or digest(archive) != packages[key]['sha256']:
            raise RuntimeError('Missing or changed pinned official archive: ' + str(archive))
        archives[str(archive)] = packages[key]['sha256']
    return dict(files=files, archives=archives, installed_payload_archive_membership_proved=False,
        scope='Selected native executables, Icarus/vvp wrappers and payloads, ivl/ivlpp/realpath, '
              'all recursive lib/ivl backend/config/header/VPI files, top-level CIRCT/OSS/Lean dynamic '
              'libraries, Lean lib/lean dynamic libraries and pinned official archives. Host OS libraries, '
              'shell tools and Python standard library/site initialization remain runtime trust assumptions.')


def check_versions(versions, expected, manifest):
    version = re.escape(expected)
    if (expected != '4.33.1' or
            not re.search(r'Lean \(version ' + version + r'(?:,|\s)', versions['lean']) or
            not re.search(r'\(Lean version ' + version + r'\)', versions['lake']) or
            'CIRCT ' + manifest['packages']['circt']['release'] not in versions['circt'] or
            not versions['iverilog'].startswith('Icarus Verilog version 14.0 (devel) '
                '(s20260301-436-gd254ea49e-dirty)') or
            not versions['vvp'].startswith('Icarus Verilog runtime version 14.0 (devel) '
                '(s20260301-436-gd254ea49e-dirty)')):
        raise RuntimeError('Selected native compiler/simulator version mismatch')


def poison_bridge(text):
    anchor = '  pinwheel_buffered_shared_branches_sram_serial dut (.*);'
    if text.count(anchor) != 1:
        raise RuntimeError('Public bridge poison fixture anchor changed')
    lines = ['integer poison; initial begin']
    for bank, seed in enumerate(POISON_SEEDS):
        lines += [f"dut.memory.storage{bank}.A_DOUT = 64'h{seed:016x};",
            'for(poison=0;poison<64;poison=poison+1)',
            f"dut.memory.storage{bank}.memory[poison] = 64'h{seed:016x} ^ poison;"]
    return text.replace(anchor, anchor + '\n' + '\n'.join(lines + ['end']))


def freeze(report, root, paths):
    frozen = report.setdefault('input_sha256_before_use', {})
    for path in paths:
        path = Path(path)
        if path.is_symlink() or not path.is_file() or not path.resolve().is_relative_to(Path(root).resolve()):
            raise RuntimeError('Missing or redirected simulator input: ' + str(path))
        relative, value = str(path.relative_to(root)), digest(path)
        if relative in frozen and frozen[relative] != value:
            raise RuntimeError('Already frozen simulator input changed: ' + relative)
        frozen[relative] = value


def check_frozen(report, root):
    for relative, expected in report.get('input_sha256_before_use', {}).items():
        path = Path(root) / relative
        if path.is_symlink() or not path.is_file() or digest(path) != expected:
            raise RuntimeError('Frozen simulator input changed: ' + relative)


def check_results(frontend, peers):
    if any(frontend.get(key, 0) <= 0 for key in
           ('cases', 'edges', 'pre_output_checks', 'post_output_checks', 'register_checks')):
        raise RuntimeError('Frontend replay must perform all nonempty pre/post/register checks')
    if (peers.get('cases') != 3 or any(peers.get(key) != 1 for key in
            ('spi_cases', 'jtag_cases', 'i2c_cases')) or
            peers.get('physical_edges', 0) <= 0 or peers.get('requests', 0) <= 0 or
            peers.get('requests') != peers.get('responses') or
            peers.get('results_retained_twice') is not True or
            len(peers.get('peer_results', [])) != 3 or
            any(value.get('outcome') != 'complete' for value in peers['peer_results'])):
        raise RuntimeError('Public-pin replay does not satisfy the three-peer receipt contract')


def completion_marker(output, expected):
    # Recent Icarus also prints the source location/time of $finish. The
    # independently generated exact success marker must occur once as a line.
    if output.splitlines().count(expected) != 1:
        raise RuntimeError('Missing or duplicated exact finite replay completion marker')


def worker(config_path):
    config = json.loads(Path(config_path).read_text())
    snapshot, out = Path(config['snapshot']), Path(config['worker_out'])
    out.mkdir()
    (out / 'logs').mkdir()
    helper = load_helpers(ROOT)
    commands = helper.Commands(snapshot, out / 'logs', default_timeout=900)
    report = dict(schema=SCHEMA, passed=False, boundary=BOUNDARY,
        source_commit=config['source_commit'], producer_commit=config['producer_commit'],
        commands=commands.records, operations=[], input_sha256_before_use={})
    started, failure = time.monotonic(), None

    def run(argv, label, **kwargs):
        # Persist the exact intended command and all already-frozen artifacts before use.
        report['next_command'] = dict(label=label, argv=list(map(str, argv)))
        write_json(out / 'worker-report.json', report)
        return commands(argv, label, **kwargs)

    try:
        check_environment()
        if membership(ROOT, config['producer_tree'], config['object_format']) != config['producer_sha256']:
            raise RuntimeError('Producer archive membership changed before worker use')
        if membership(snapshot, config['source_tree'], config['object_format']) != config['source_sha256']:
            raise RuntimeError('Source archive membership changed before worker use')
        manifest = json.loads((snapshot / 'tools/hardware-toolchain.json').read_text())
        if json.loads((snapshot / 'lake-manifest.json').read_text()).get('packages'):
            raise RuntimeError('Simulator gate expects no external Lake packages')
        tools = config['tool_paths']
        if tool_identity(tools, manifest) != config['tool_identity']:
            raise RuntimeError('Tool identity changed before worker use')
        versions = {name: run([tools[name], *flags], name + '-version', timeout=30).strip()
                    for name, flags in [('lean', ['--version']), ('lake', ['--version']),
                        ('circt', ['--version']), ('iverilog', ['-V']), ('vvp', ['-V'])]}
        expected = (snapshot / 'lean-toolchain').read_text().strip().split(':v')[-1]
        check_versions(versions, expected, manifest)
        report['tool_versions'] = versions
        selected = run([tools['lake'], 'env', 'which', 'lean'], 'lake-selected-lean', timeout=30).strip()
        if Path(selected).resolve() != Path(tools['lean']).resolve():
            raise RuntimeError('Lake did not select the fingerprinted native Lean')
        search = run([tools['lake'], 'env', 'printenv', 'LEAN_PATH'], 'lake-search-path', timeout=30).strip()
        if set(search.split(os.pathsep)) != {str(snapshot / '.lake/build/lib/lean'),
                str(Path(tools['lean']).parent.parent / 'lib/lean')}:
            raise RuntimeError('Lake search path includes unselected cached modules')
        report['lean_search_path'] = search.split(os.pathsep)
        run([tools['lake'], 'build', 'Pinwheel.Hardware.Buffered.Serial',
             'Pinwheel.Hardware.Buffered.Sram'], 'fresh-component-build')
        sys.path.insert(0, str(snapshot / 'scripts'))
        spec = importlib.util.spec_from_file_location('selected_serial_gate', snapshot / REQUIRED[4])
        gate = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(gate)
        gate.CAD = Path(tools['iverilog']).parent
        # Refuse accidental future use of the historical acceptance path.
        gate.predecessor = lambda: (_ for _ in ()).throw(RuntimeError('Historical predecessor forbidden'))
        request = out / 'frontend-input.json'
        request.write_text(json.dumps(gate.frontend_input()) + '\n')
        freeze(report, out, [request])
        front, core = out / 'frontend', out / 'controller'
        run([tools['lake'], 'env', 'lean', '-DwarningAsError=true', '--run',
            'test/BufferedSramSerialExport.lean', request, front], 'emit-frontend')
        run([tools['lake'], 'env', 'lean', '-DwarningAsError=true', '--run',
            'test/SramArtifactEmit.lean', core], 'emit-controller')
        for label, mlir in [('frontend', front / 'frontend.mlir'), ('controller', core / 'core.mlir')]:
            freeze(report, out, [mlir])
            text = run([tools['circt'], mlir, '--canonicalize', '--lower-seq-to-sv',
                '--lower-hw-to-sv', '--hw-legalize-modules', '--export-verilog', '-o', '/dev/null'],
                'lower-' + label)
            (out / (label + '.sv')).write_text(text)
        freeze(report, out, [front / 'assembly.json', front / 'vectors.json'])
        tb, frontend = gate.frontend_tb(out, json.loads((front / 'assembly.json').read_text()),
                                      json.loads((front / 'vectors.json').read_text()))
        fixture, frontend_sv = out / 'frontend-fixture.txt', out / 'frontend.sv'
        freeze(report, out, [tb, fixture, frontend_sv])
        executable = out / 'frontend.vvp'
        run([tools['iverilog'], '-g2012', '-s', 'buffered_sram_serial_frontend_tb',
             '-o', executable, frontend_sv, tb], 'frontend-compile')
        freeze(report, out, [executable])
        output = run([tools['vvp'], executable], 'frontend-replay')
        completion_marker(output, 'Frontend finite replay ' + str(frontend['edges']) + ' edges')
        report['frontend_replay'] = frontend
        model, bridge = out / 'digital-memory.sv', out / 'bridge-poison.sv'
        model.write_text(DIGITAL_MEMORY)
        bridge.write_text(poison_bridge(gate.BRIDGE.read_text()))
        freeze(report, out, [model, bridge, out / 'controller.sv'])
        executable = gate.compile_package(run, out, frontend_sv, out / 'controller.sv',
            'digital-package', [model], bridge=bridge)
        freeze(report, out, [executable])
        report['operations'].append(dict(api='selected_serial_gate.wire_cases', bounded=True,
            vvp=tools['vvp'], executable=str(executable), expected_protocols=['spi', 'jtag', 'i2c']))
        write_json(out / 'worker-report.json', report)
        pins, schedule, peers = gate.wire_cases(executable, bounded=True)
        check_results(frontend, peers)
        report['public_pin_peers'] = peers
        report['memory_model'] = dict(law='synchronous write-priority; masked writes; read pre-edge cell; '
            'write/idle hold Q; explicit digital model only',
            initial_bank_q=[f'{seed:016x}' for seed in POISON_SEEDS],
            initial_cell='bank_seed XOR physical_index', macro_qualified=False)
        for label, values in [('pins', pins), ('schedule', schedule)]:
            (out / (label + '.jsonl')).write_text(''.join(
                json.dumps(value, separators=(',', ':')) + '\n' for value in values))
        report['passed'] = True
    except BaseException as error:
        failure = error
        report['error'] = type(error).__name__ + ': ' + str(error)
    finally:
        try:
            if membership(snapshot, config['source_tree'], config['object_format']) != config['source_sha256']:
                raise RuntimeError('Source archive changed during simulator replay')
            if membership(ROOT, config['producer_tree'], config['object_format']) != config['producer_sha256']:
                raise RuntimeError('Producer archive changed during simulator replay')
            if tool_identity(config['tool_paths'], json.loads((snapshot / 'tools/hardware-toolchain.json').read_text())) != config['tool_identity']:
                raise RuntimeError('Tool/runtime inventory changed during simulator replay')
            check_frozen(report, out)
            report.update(archived_inputs_unchanged=True, producer_unchanged=True,
                          tool_identity_unchanged=True, frozen_artifacts_unchanged=True)
        except Exception as error:
            report.update(passed=False, closeout_error=str(error))
        report.pop('next_command', None)
        report['elapsed_seconds'] = round(time.monotonic() - started, 3)
        report['artifact_sha256'] = {str(path.relative_to(out)): digest(path)
            for path in sorted(out.rglob('*')) if path.is_file() and path != out / 'worker-report.json'}
        write_json(out / 'worker-report.json', report)
    if failure:
        raise failure
    if not report['passed']:
        raise RuntimeError('Simulator worker closeout rejected run')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--tag')
    parser.add_argument('--source-commit', default='HEAD')
    parser.add_argument('--circt')
    parser.add_argument('--iverilog')
    parser.add_argument('--vvp')
    parser.add_argument('--timeout-seconds', type=int, default=3600)
    parser.add_argument('--worker-config', help=argparse.SUPPRESS)
    args = parser.parse_args()
    if args.worker_config:
        worker(args.worker_config)
        return
    if (not args.tag or not re.fullmatch(r'[A-Za-z0-9_-]+', args.tag) or
            not all(args.__dict__[key] and Path(args.__dict__[key]).is_absolute()
                    for key in ('circt', 'iverilog', 'vvp')) or not 1 <= args.timeout_seconds <= 43200):
        parser.error('Provide --tag, absolute --circt/--iverilog/--vvp, and timeout 1..43200 seconds')
    check_environment()
    git = lambda *items: subprocess.check_output(['git', *items], cwd=ROOT, text=True, timeout=30)
    producer_commit = git('rev-parse', 'HEAD').strip()
    source_commit = git('rev-parse', '--verify', args.source_commit + '^{commit}').strip()
    algorithm = git('rev-parse', '--show-object-format').strip()
    tree = parse_tree(git('ls-tree', '-r', '-z', producer_commit))
    if any(path not in tree for path in PRODUCER):
        raise RuntimeError('Commit the simulator producer and focused tests before a qualified run')
    producer_tree = {path: tree[path] for path in PRODUCER}
    producer_hashes = membership(ROOT, producer_tree, algorithm)
    helper = load_helpers(ROOT)
    out = helper.fresh_directory(ROOT / 'build/validation', args.tag)
    (out / 'logs').mkdir()
    run = helper.Commands(ROOT, out / 'logs', default_timeout=60)
    report = dict(schema=SCHEMA, passed=False, boundary=BOUNDARY,
        started_utc=datetime.now(timezone.utc).isoformat(), source_commit=source_commit,
        producer_commit=producer_commit, producer_sha256=producer_hashes, commands=run.records,
        membership_scope='All regular files in selected source Git archive; committed producer archive '
            'separate. Working-tree source changes are neither consumed nor asserted identical.')
    started, failure, tool_before, snapshot, hashes = time.monotonic(), None, None, None, None
    try:
        source_tree = parse_tree(run(['git', 'ls-tree', '-r', '-z', source_commit], 'selected-tree'))
        if any(path not in source_tree for path in REQUIRED):
            raise RuntimeError('Selected commit lacks required emitters, wrappers or serial peer driver')
        for name, commit, paths in [('selected', source_commit, []), ('producer', producer_commit, list(PRODUCER))]:
            archive = out / (name + '-source.tar')
            command = ['git', 'archive', '--format=tar', '--output', archive, commit]
            if paths:
                command += ['--', *paths]
            run(command, name + '-archive')
            report[name + '_archive_sha256'] = digest(archive)
            directory = out / name
            directory.mkdir()
            with tarfile.open(archive) as bundle:
                bundle.extractall(directory, filter='data')
            fresh_snapshot(directory)
        snapshot = out / 'selected'
        hashes = membership(snapshot, source_tree, algorithm)
        if membership(out / 'producer', producer_tree, algorithm) != producer_hashes:
            raise RuntimeError('Producer archive membership mismatch')
        # The old pure helper imports validation_run; require identical helper bytes.
        for path in ('scripts/validation_run.py', 'scripts/process_group.py'):
            if hashes.get(path) != producer_hashes[path]:
                raise RuntimeError('Selected source and producer orchestration helpers differ')
        report.update(source_sha256=hashes, selected_git_objects=source_tree,
                      committed_archive_membership_verified_before=True)
        proxy = shutil.which('lake')
        if not proxy:
            raise RuntimeError('Native Lean/Lake must be installed')
        prefix = Path(run([proxy, 'env', 'lean', '--print-prefix'], 'native-toolchain-prefix').strip())
        tools = dict(circt=args.circt, iverilog=args.iverilog, vvp=args.vvp,
            lean=str(prefix / 'bin/lean'), lake=str(prefix / 'bin/lake'),
            python=str(Path(sys.executable).resolve()))
        manifest = json.loads((snapshot / 'tools/hardware-toolchain.json').read_text())
        tool_before = tool_identity(tools, manifest)
        report.update(tool_paths=tools, tool_identity_before=tool_before,
                      discovery_lake_proxy=dict(path=proxy, sha256=digest(proxy)))
        config = dict(snapshot=str(snapshot), worker_out=str(out / 'worker'), source_commit=source_commit,
            producer_commit=producer_commit, source_tree=source_tree, source_sha256=hashes,
            producer_tree=producer_tree, producer_sha256=producer_hashes, object_format=algorithm,
            tool_paths=tools, tool_identity=tool_before)
        config_path = out / 'worker-config.json'
        write_json(config_path, config)
        report['worker_config_sha256_before_use'] = digest(config_path)
        write_json(out / 'report.json', report)
        run([tools['python'], '-B', out / 'producer' / DRIVER, '--worker-config', config_path],
            'snapshot-worker', timeout=args.timeout_seconds)
        if digest(config_path) != report['worker_config_sha256_before_use']:
            raise RuntimeError('Worker configuration changed after use')
        child = json.loads((out / 'worker/worker-report.json').read_text())
        if (child.get('schema') != SCHEMA or child.get('source_commit') != source_commit or
                child.get('producer_commit') != producer_commit or not child.get('passed') or
                any(child.get(key) is not True for key in ('archived_inputs_unchanged',
                    'producer_unchanged', 'tool_identity_unchanged', 'frozen_artifacts_unchanged'))):
            raise RuntimeError('Worker receipt does not satisfy simulator contract')
        check_results(child['frontend_replay'], child['public_pin_peers'])
        report.update(worker=child, passed=True)
    except BaseException as error:
        failure = error
        report['error'] = type(error).__name__ + ': ' + str(error)
    finally:
        try:
            if membership(ROOT, producer_tree, algorithm) != producer_hashes:
                raise RuntimeError('Producer working bytes changed after intake')
            if hashes is not None and membership(snapshot, source_tree, algorithm) != hashes:
                raise RuntimeError('Selected source archive changed')
            if tool_before is not None:
                after = tool_identity(report['tool_paths'], manifest)
                if after != tool_before:
                    raise RuntimeError('Tool/runtime inventory changed after intake')
                report.update(tool_identity_after=after, tool_identity_unchanged=True)
            report['committed_archive_membership_verified_after'] = True
        except Exception as error:
            report.update(passed=False, closeout_error=str(error))
        report['elapsed_seconds'] = round(time.monotonic() - started, 3)
        write_json(out / 'report.json', report)
    if failure:
        raise failure
    if not report['passed']:
        raise RuntimeError('Simulator closeout rejected run')
    print('Finite Icarus simulator receipt: ' + str(out / 'report.json'), flush=True)


if __name__ == '__main__':
    main()
