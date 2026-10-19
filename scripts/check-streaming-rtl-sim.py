#!/usr/bin/env python3
"""Fresh finite public quad-wire Icarus qualification for streaming-quad-v1.

Both FIFO depths are emitted from an empty selected Git archive. This producer
uses the earlier simulator driver's pure archive/tool-fingerprint helpers only;
it never calls its worker, fixture, predecessor, mapping path or receipts.
"""
import argparse
from datetime import datetime, timezone
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

ROOT = Path(__file__).resolve().parents[1]
DRIVER = 'scripts/check-streaming-rtl-sim.py'
HELPER = 'scripts/check-buffered-rtl-sim.py'
PRODUCER = (DRIVER, HELPER, 'scripts/validation_run.py', 'scripts/process_group.py',
    'test/test_streaming_rtl_sim.py')
REQUIRED = ('lean-toolchain', 'lakefile.toml', 'lake-manifest.json', 'tools/hardware-toolchain.json',
    'test/StreamingArtifactEmit.lean', 'Pinwheel/Hardware/Streaming/Core.lean',
    'Pinwheel/Hardware/Streaming/Frontend.lean', 'Pinwheel/Program/StreamingCompile.lean',
    'scripts/streaming_compile.py', 'scripts/streaming_transport.py', 'scripts/streaming_peers.py',
    'scripts/streaming_rtl.py', 'scripts/streaming_wrapper.py', 'scripts/streaming_wire_cases.py',
    'scripts/pad_io.py', 'scripts/jtag_peers.py')
SCHEMA = 'pinwheel.streaming-quad-rtl-simulator.v1'
BOUNDARY = ('Finite independent Icarus simulation of newly emitted generic streaming core and '
    'quad frontend, complete named-port package/TT wiring, and public sampled pins. '
    'Independent SPI/JTAG peers check 4 KiB duplex SPI and 4097-bit JTAG under one START/owner at '
    'FIFO depths 2/4, low-phase backpressure, exact high phases, specified CRC/partial-read/replay '
    'errors and retained RX custody. Automatic closed Lean compiler checks precede wire I/O. '
    'No synthesis, mapping, physical SRAM macro, electrical/CDC/board timing, universal '
    'simulator correctness or arbitrary fault/authentication claim.')


def helpers():
    spec = importlib.util.spec_from_file_location('streaming_sim_archive_helpers', ROOT / HELPER)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def check_results(cases):
    expected = {(depth, protocol, bits, fault) for depth in (2, 4)
        for protocol, bits, fault in [('spi', 32768, None), ('jtag', 4097, None), ('spi', 0, None),
            ('spi', 8, 'request_close'), ('spi', 8, 'request_crc'),
            ('spi', 8, 'response_crc'), ('spi', 8, 'partial_read')]}
    actual = []
    custody = []
    for result in cases:
        if result.get('passed') is not True or result.get('trace', {}).get('edges', 0) <= 0:
            raise RuntimeError('Every public-wire case must pass with a nonempty physical trace')
        if result.get('kind') == 'custody':
            custody.append(result.get('depth'))
            if any(result.get(key) is not True for key in ('unacknowledged_release_rejected',
                    'rejected_request_custody_preserved', 'stale_owner_rejected',
                    'same_image_two_starts', 'stale_local_owner_no_io', 'stale_image_no_io')):
                raise RuntimeError('Retained custody/reuse controls did not distinguish their boundaries')
            continue
        key = tuple(result.get(name) for name in ('depth', 'protocol', 'bits', 'fault'))
        actual.append(key)
        if (result.get('start_count') != 1 or result.get('exchange_rx_max', 65) > 32 or
                result.get('physical_edges') != result['trace']['edges'] or
                result.get('owner_tag') != 65537):
            raise RuntimeError('Case did not establish its one-START and physical trace bounds')
        peer = result.get('peer', {})
        bits = result.get('bits')
        if peer.get('bits') != bits or bits and peer.get('high_phase_edges') != [4]:
            raise RuntimeError('Independent peer bit count or exact high timing differs')
        if bits > 128 and peer.get('low_extra_edges', 0) <= 0:
            raise RuntimeError('Long case did not actually exercise low-only stalls')
        if result['protocol'] == 'spi':
            if peer.get('continuous_cs') is not True or peer.get('clock_edges') != bits * 2:
                raise RuntimeError('SPI did not preserve one continuous selected transfer')
        elif (peer.get('clock_edges') != 2 * (bits + 11) or peer.get('clocks') != bits + 11 or
                peer.get('capture_count') != 1 or peer.get('update_count') != 1 or
                peer.get('last_bit_exits_shift_dr') is not True or
                peer.get('final_tap_state') != 'run_test_idle'):
            raise RuntimeError('JTAG navigation/last-bit/capture/update differs')
        if result.get('fault') is not None and (result.get('recoveries', 0) <= 0 or
                [value.get('kind') for value in result.get('faults', [])] != [result['fault']]):
            raise RuntimeError('Specified fault/recovery was not exercised exactly once')
    if len(actual) != len(expected) or set(actual) != expected or sorted(custody) != [2, 4]:
        raise RuntimeError('Missing, duplicated or unexpected depth/protocol/fault/custody case')


def worker(config_path):
    h = helpers()
    config = json.loads(Path(config_path).read_text())
    snapshot, out = Path(config['snapshot']), Path(config['worker_out'])
    out.mkdir()
    (out / 'logs').mkdir()
    orchestration = h.load_helpers(ROOT)
    commands = orchestration.Commands(snapshot, out / 'logs', default_timeout=900)
    report = dict(schema=SCHEMA, passed=False, boundary=BOUNDARY,
        source_commit=config['source_commit'], producer_commit=config['producer_commit'],
        commands=commands.records, cases=[], input_sha256_before_use={})
    started, failure = time.monotonic(), None

    def run(argv, label, **kwargs):
        report['next_command'] = dict(label=label, argv=list(map(str, argv)))
        h.write_json(out / 'worker-report.json', report)
        return commands(argv, label, **kwargs)

    try:
        h.check_environment()
        if h.membership(ROOT, config['producer_tree'], config['object_format']) != config['producer_sha256']:
            raise RuntimeError('Producer archive membership changed before use')
        if h.membership(snapshot, config['source_tree'], config['object_format']) != config['source_sha256']:
            raise RuntimeError('Selected archive membership changed before use')
        manifest = json.loads((snapshot / 'tools/hardware-toolchain.json').read_text())
        if json.loads((snapshot / 'lake-manifest.json').read_text()).get('packages'):
            raise RuntimeError('Streaming gate expects no external Lake packages')
        tools = config['tool_paths']
        if h.tool_identity(tools, manifest) != config['tool_identity']:
            raise RuntimeError('Selected tool inventory changed before use')
        versions = {name: run([tools[name], *flags], name + '-version', timeout=30).strip()
            for name, flags in [('lean', ['--version']), ('lake', ['--version']),
                ('circt', ['--version']), ('iverilog', ['-V']), ('vvp', ['-V'])]}
        h.check_versions(versions, (snapshot / 'lean-toolchain').read_text().strip().split(':v')[-1], manifest)
        report['tool_versions'] = versions
        selected = run([tools['lake'], 'env', 'which', 'lean'], 'lake-selected-lean', timeout=30).strip()
        if Path(selected).resolve() != Path(tools['lean']).resolve():
            raise RuntimeError('Lake did not select the fingerprinted native Lean')
        search = run([tools['lake'], 'env', 'printenv', 'LEAN_PATH'], 'lake-search-path', timeout=30).strip()
        if set(search.split(os.pathsep)) != {str(snapshot / '.lake/build/lib/lean'),
                str(Path(tools['lean']).parent.parent / 'lib/lean')}:
            raise RuntimeError('Lake search path includes unselected cached modules')
        report['lean_search_path'] = search.split(os.pathsep)
        run([tools['lake'], 'build', 'Pinwheel.Hardware.Streaming.FrontendEmit',
            'Pinwheel.Program.StreamingCompile'], 'fresh-streaming-build')
        sys.path.insert(0, str(snapshot / 'scripts'))
        from streaming_compile import jtag_image, lean_certificate, spi_image
        from streaming_wire_cases import run_custody, run_stream
        from streaming_wrapper import bridge_source, package_source, tt_source
        for protocol, image in [('spi', spi_image()), ('jtag', jtag_image())]:
            certificate = out / (protocol + '-image.lean')
            certificate.write_text(lean_certificate(image))
            h.freeze(report, out, [certificate])
            run([tools['lake'], 'env', 'lean', '-DwarningAsError=true', certificate],
                protocol + '-automatic-kernel-image-check')
        for depth in (2, 4):
            target = out / ('d' + str(depth))
            run([tools['lake'], 'env', 'lean', '-DwarningAsError=true', '--run',
                'test/StreamingArtifactEmit.lean', target, '1' if depth == 2 else '2'],
                'emit-d' + str(depth))
            h.freeze(report, out, [target / name for name in
                ('core.mlir', 'frontend.mlir', 'assembly.json', 'frontend-assembly.json')])
            core = json.loads((target / 'assembly.json').read_text())
            front = json.loads((target / 'frontend-assembly.json').read_text())
            for component in ('core', 'frontend'):
                source = run([tools['circt'], target / (component + '.mlir'), '--canonicalize',
                    '--lower-seq-to-sv', '--lower-hw-to-sv', '--hw-legalize-modules',
                    '--export-verilog', '-o', '/dev/null'], 'lower-d' + str(depth) + '-' + component)
                (target / (component + '.sv')).write_text(source)
            for name, source in [('package', package_source(core, front)), ('tt', tt_source(depth)),
                    ('bridge', bridge_source(depth))]:
                (target / (name + '.sv')).write_text(source)
            sources = [target / (name + '.sv') for name in ('core', 'frontend', 'package', 'tt', 'bridge')]
            h.freeze(report, out, sources)
            executable = target / 'chip.vvp'
            run([tools['iverilog'], '-g2012', '-s', 'streaming_quad_host_bridge', '-o', executable,
                *sources], 'compile-d' + str(depth))
            h.freeze(report, out, [executable])
            definitions = [('spi', 32768, None), ('jtag', 4097, None), ('spi', 0, None),
                ('spi', 8, 'request_close'), ('spi', 8, 'request_crc'),
                ('spi', 8, 'response_crc'), ('spi', 8, 'partial_read')]
            for protocol, bits, fault in definitions:
                name = protocol + '-' + str(bits) + '-' + (fault or 'clean')
                report['next_operation'] = dict(api='streaming_wire_cases.run_stream', depth=depth,
                    protocol=protocol, bits=bits, fault=fault, executable=str(executable))
                h.write_json(out / 'worker-report.json', report)
                result = run_stream(tools['vvp'], executable, target / name,
                    protocol=protocol, bits=bits, depth=depth, fault=fault)
                h.write_json(target / (name + '.json'), result)
                report['cases'].append(result)
                if result.get('passed') is not True:
                    raise RuntimeError('Actual public-wire case failed: ' + name + ': ' + result.get('error', 'unknown'))
            result = run_custody(tools['vvp'], executable, target / 'custody', depth=depth)
            result['kind'] = 'custody'
            h.write_json(target / 'custody.json', result)
            report['cases'].append(result)
            if result.get('passed') is not True:
                raise RuntimeError('Actual retained custody/reuse case failed: ' + result.get('error', 'unknown'))
        check_results(report['cases'])
        report['physical_edges'] = sum(case['physical_edges'] for case in report['cases'])
        report['trace_bytes'] = sum(case['trace']['bytes'] for case in report['cases'])
        report['passed'] = True
    except BaseException as error:
        failure = error
        report['error'] = type(error).__name__ + ': ' + str(error)
    finally:
        try:
            if h.membership(snapshot, config['source_tree'], config['object_format']) != config['source_sha256']:
                raise RuntimeError('Selected source archive changed during simulation')
            if h.membership(ROOT, config['producer_tree'], config['object_format']) != config['producer_sha256']:
                raise RuntimeError('Producer archive changed during simulation')
            if h.tool_identity(config['tool_paths'], json.loads((snapshot / 'tools/hardware-toolchain.json').read_text())) != config['tool_identity']:
                raise RuntimeError('Tool/runtime inventory changed during simulation')
            h.check_frozen(report, out)
            report.update(archived_inputs_unchanged=True, producer_unchanged=True,
                tool_identity_unchanged=True, frozen_artifacts_unchanged=True)
        except Exception as error:
            report.update(passed=False, closeout_error=str(error))
        report.pop('next_command', None)
        report.pop('next_operation', None)
        report['elapsed_seconds'] = round(time.monotonic() - started, 3)
        report['artifact_sha256'] = {str(path.relative_to(out)): h.digest(path)
            for path in sorted(out.rglob('*')) if path.is_file() and path != out / 'worker-report.json'}
        h.write_json(out / 'worker-report.json', report)
    if failure: raise failure
    if not report['passed']: raise RuntimeError('Streaming simulator worker closeout rejected run')


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
            not all(getattr(args, key) and Path(getattr(args, key)).is_absolute()
                for key in ('circt', 'iverilog', 'vvp')) or not 1 <= args.timeout_seconds <= 43200):
        parser.error('Provide --tag, absolute --circt/--iverilog/--vvp and timeout1..43200 seconds')
    h = helpers()
    h.check_environment()
    git = lambda *items: subprocess.check_output(['git', *items], cwd=ROOT, text=True, timeout=30)
    producer_commit = git('rev-parse', 'HEAD').strip()
    source_commit = git('rev-parse', '--verify', args.source_commit + '^{commit}').strip()
    algorithm = git('rev-parse', '--show-object-format').strip()
    tree = h.parse_tree(git('ls-tree', '-r', '-z', producer_commit))
    if any(path not in tree for path in PRODUCER):
        raise RuntimeError('Commit the producer and focused controls before a qualified run')
    producer_tree = {path: tree[path] for path in PRODUCER}
    producer_hashes = h.membership(ROOT, producer_tree, algorithm)
    orchestration = h.load_helpers(ROOT)
    out = orchestration.fresh_directory(ROOT / 'build/validation', args.tag)
    (out / 'logs').mkdir()
    run = orchestration.Commands(ROOT, out / 'logs', default_timeout=60)
    report = dict(schema=SCHEMA, passed=False, boundary=BOUNDARY,
        started_utc=datetime.now(timezone.utc).isoformat(), source_commit=source_commit,
        producer_commit=producer_commit, producer_sha256=producer_hashes, commands=run.records,
        membership_scope='All regular files in selected Git archive; producer archive separate. '
            'Working-tree source bytes are not consumed or claimed identical. Pure historical '
            'archive/tool helpers are reused; no prior worker, gate, fixture or receipt is invoked.')
    started, failure, before, snapshot, hashes = time.monotonic(), None, None, None, None
    try:
        source_tree = h.parse_tree(run(['git', 'ls-tree', '-r', '-z', source_commit], 'selected-tree'))
        if any(path not in source_tree for path in REQUIRED):
            raise RuntimeError('Selected commit lacks streaming emitters, compiler or wire corpus')
        for name, commit, paths in [('selected', source_commit, []), ('producer', producer_commit, list(PRODUCER))]:
            archive = out / (name + '-source.tar')
            argv = ['git', 'archive', '--format=tar', '--output', archive, commit]
            if paths: argv += ['--', *paths]
            run(argv, name + '-archive')
            report[name + '_archive_sha256'] = h.digest(archive)
            directory = out / name
            directory.mkdir()
            with tarfile.open(archive) as bundle: bundle.extractall(directory, filter='data')
            h.fresh_snapshot(directory)
        snapshot = out / 'selected'
        hashes = h.membership(snapshot, source_tree, algorithm)
        if h.membership(out / 'producer', producer_tree, algorithm) != producer_hashes:
            raise RuntimeError('Producer archive membership differs')
        for path in ('scripts/validation_run.py', 'scripts/process_group.py'):
            if hashes.get(path) != producer_hashes[path]:
                raise RuntimeError('Source and producer orchestration helpers differ')
        report.update(source_sha256=hashes, selected_git_objects=source_tree,
            committed_archive_membership_verified_before=True)
        proxy = shutil.which('lake')
        if not proxy: raise RuntimeError('Native Lean/Lake must be installed')
        prefix = Path(run([proxy, 'env', 'lean', '--print-prefix'], 'native-toolchain-prefix').strip())
        tools = dict(circt=args.circt, iverilog=args.iverilog, vvp=args.vvp,
            lean=str(prefix / 'bin/lean'), lake=str(prefix / 'bin/lake'),
            python=str(Path(sys.executable).resolve()))
        manifest = json.loads((snapshot / 'tools/hardware-toolchain.json').read_text())
        before = h.tool_identity(tools, manifest)
        report.update(tool_paths=tools, tool_identity_before=before,
            discovery_lake_proxy=dict(path=proxy, sha256=h.digest(proxy)))
        config = dict(snapshot=str(snapshot), worker_out=str(out / 'worker'), source_commit=source_commit,
            producer_commit=producer_commit, source_tree=source_tree, source_sha256=hashes,
            producer_tree=producer_tree, producer_sha256=producer_hashes, object_format=algorithm,
            tool_paths=tools, tool_identity=before)
        path = out / 'worker-config.json'
        h.write_json(path, config)
        report['worker_config_sha256_before_use'] = h.digest(path)
        h.write_json(out / 'report.json', report)
        run([tools['python'], '-B', out / 'producer' / DRIVER, '--worker-config', path],
            'snapshot-worker', timeout=args.timeout_seconds)
        if h.digest(path) != report['worker_config_sha256_before_use']:
            raise RuntimeError('Worker configuration changed after use')
        child = json.loads((out / 'worker/worker-report.json').read_text())
        if (child.get('schema') != SCHEMA or child.get('source_commit') != source_commit or
                child.get('producer_commit') != producer_commit or child.get('passed') is not True or
                any(child.get(key) is not True for key in ('archived_inputs_unchanged',
                    'producer_unchanged', 'tool_identity_unchanged', 'frozen_artifacts_unchanged'))):
            raise RuntimeError('Worker receipt does not satisfy streaming simulator contract')
        check_results(child['cases'])
        report.update(worker=child, passed=True)
    except BaseException as error:
        failure = error
        report['error'] = type(error).__name__ + ': ' + str(error)
    finally:
        try:
            if h.membership(ROOT, producer_tree, algorithm) != producer_hashes:
                raise RuntimeError('Producer working bytes changed after intake')
            if hashes is not None and h.membership(snapshot, source_tree, algorithm) != hashes:
                raise RuntimeError('Selected source archive changed')
            if before is not None:
                after = h.tool_identity(report['tool_paths'], manifest)
                if after != before: raise RuntimeError('Tool/runtime inventory changed after intake')
                report.update(tool_identity_after=after, tool_identity_unchanged=True)
            report['committed_archive_membership_verified_after'] = True
        except Exception as error:
            report.update(passed=False, closeout_error=str(error))
        report['elapsed_seconds'] = round(time.monotonic() - started, 3)
        h.write_json(out / 'report.json', report)
    if failure: raise failure
    if not report['passed']: raise RuntimeError('Streaming simulator closeout rejected run')
    print('Finite streaming quad-wire simulator receipt: ' + str(out / 'report.json'), flush=True)


if __name__ == '__main__': main()
