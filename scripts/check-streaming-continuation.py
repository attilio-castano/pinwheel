#!/usr/bin/env python3
"""Fresh committed-source coordinator for the streaming continuation.

Full acceptance requires raw component and actual wrapper certificates, the
two-depth public-wire/adversarial corpus, matched cost, a compiled source and
initialization composition, a complete private-declaration axiom audit and
distinguishing negative controls. Partial stages never claim full acceptance.
No prior report, generated proof, RTL artifact or compiled cache is an input.
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
DRIVER = 'scripts/check-streaming-continuation.py'
HELPER = 'scripts/check-buffered-rtl-sim.py'
PRODUCER = (DRIVER, HELPER, 'scripts/validation_run.py', 'scripts/process_group.py',
    'test/test_streaming_continuation.py')
SCHEMA = 'pinwheel.streaming-continuation.v1'
STAGES = ('full', 'components', 'wire', 'cost')
JOIN_THEOREMS = ('components_correct', 'physical_step_correct', 'physical_observe_correct',
    'physical_run_correct', 'source_runtime_step_correct', 'source_runtime_run_correct',
    'source_runtime_observe_correct', 'initialized_upload_correct', 'initialized_runtime_correct',
    'physical_warm_reset_correct', 'concrete_spi_initialized', 'concrete_jtag_initialized',
    'concrete_spi_runtime', 'concrete_jtag_runtime', 'concrete_spi_custody', 'concrete_jtag_custody',
    'concrete_spi_progress', 'concrete_jtag_progress')
BASE_REQUIRED = ('lean-toolchain', 'lakefile.toml', 'lake-manifest.json',
    'tools/hardware-toolchain.json', 'tools/technology-library.json', 'test/ProofAudit.lean',
    'test/StreamingArtifactEmit.lean', 'scripts/streaming_wrapper.py',
    'scripts/check-buffered-rtl-session.py', 'Pinwheel/Program/StreamingCompile.lean',
    'Pinwheel/Hardware/Streaming/FrontendEmit.lean')
REQUIRED_BY_STAGE = {
    'components': ('scripts/streaming_artifacts.py', 'scripts/streaming_readback.py',
        'scripts/streaming_wrapper_readback.py', 'scripts/check-buffered-rtl-session.py',
        'Pinwheel/Hardware/Streaming/TinyWiring.lean'),
    'wire': ('scripts/check-streaming-rtl-sim.py', 'scripts/streaming_wire_cases.py',
        'scripts/streaming_adversarial.py', 'scripts/streaming_transport.py',
        'scripts/streaming_peers.py', 'scripts/streaming_compile.py', 'scripts/streaming_rtl.py',
        'scripts/streaming_staging_race.py'),
    'cost': ('scripts/streaming_cost.py', 'test/BufferedSramSerialExport.lean',
        'test/SramArtifactEmit.lean', 'physical/buffered_sram_serial_wrapper.sv',
        'physical/buffered_sram_memory.sv', 'physical/tt_um_pinwheel_buffered.sv'),
    'join': ('scripts/streaming_composition.py',
        'Pinwheel/Hardware/Streaming/SessionCorrespondence.lean',
        'Pinwheel/Hardware/Streaming/Initialization.lean',
        'Pinwheel/Hardware/Streaming/InputCorrespondence.lean',
        'Pinwheel/Hardware/Streaming/InitializedSession.lean',
        'Pinwheel/Hardware/Streaming/WarmReset.lean',
        'Pinwheel/Hardware/Streaming/PublicPins.lean',
        'Pinwheel/Hardware/Streaming/BootCorrespondence.lean',
        'Pinwheel/Hardware/Streaming/BootUpload.lean',
        'Pinwheel/Hardware/Streaming/InitializedCustody.lean',
        'Pinwheel/Program/StreamingOwnerCut.lean',
        'Pinwheel/Program/StreamingEventualService.lean',
        'Pinwheel/Program/StreamingSessionProgress.lean',
        'Pinwheel/Program/StreamingLowTiming.lean',
        'Pinwheel/Program/StreamingTiming.lean')}
TARGETS = ('frontend + depth2/depth4: every raw register/output equation',
    'actual package + Tiny Tapeout wiring at both depths',
    'unchanged reimports, stored-state/output mutations, wire/clock/output mutations',
    'mandatory16-case two-depth public-wire corpus',
    'two additional adversarial suites, with sequence exhaustion explicitly host-only',
    'both terminal-staging race suites: HALT/FAULT, one/two TX beats, public-edge alignment',
    'matched four-row complete-storage synthesis cost and bounded ABC combinational Liberty delay estimate',
    'both source-runtime and concrete physical boot/runtime/custody/fair-service modules with all eighteen APIs',
    'all imported Pinwheel/generated declarations including private helpers use standard axioms only',
    'one additional injected private axiom is rejected by the complete final audit')
BOUNDARY = ('Kernel-checked two-state equations for the actual emitted raw components and '
    'interpreted package/TT wiring, composed with the checked source and initialization APIs. '
    'Finite independent Icarus public-pin SPI/JTAG and adversarial tests are separate evidence. '
    'Technology mapping contributes complete-cell cost and an ABC combinational Liberty delay estimate, '
    'with sequential and macro boundaries cut; no mapped equivalence, Fmax or timing signoff. '
    'CIRCT, Yosys and SMT supply artifacts/hints; the native Lean kernel checks proof certificates. '
    'Restricted RTL/wrapper interpretation, the pinned toolchain/runtime, host OS/Python and '
    'two-state digital sampling remain explicit trust boundaries. No electrical, CDC, board, '
    'placement/routing/signoff, silicon, arbitrary-fault or authentication claim.')


def load_file(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def helpers(): return load_file('_streaming_continuation_archive_helpers', ROOT / HELPER)


def required_inputs(stage):
    if stage not in STAGES:
        raise ValueError('Unknown continuation stage')
    kinds = ('components', 'wire', 'cost', 'join') if stage == 'full' else (stage,)
    return set(BASE_REQUIRED).union(*(set(REQUIRED_BY_STAGE[kind]) for kind in kinds))


def check_environment(h, environment=None):
    environment = os.environ if environment is None else environment
    h.check_environment(environment)
    bad = sorted(key for key, value in environment.items() if value and
        key.startswith(('YOSYS_', 'ABC_', 'Z3_', 'CIRCT_', 'VVP_')))
    if bad:
        raise RuntimeError('Refuse tool/data overrides: ' + ', '.join(bad))


def tool_identity(h, tools, manifest):
    """Include simulator/importer/mapping wrappers, payloads and backend data."""
    base = h.tool_identity({name: tools[name] for name in
        ('circt', 'iverilog', 'vvp', 'lean', 'lake', 'python')}, manifest)
    oss = Path(tools['iverilog']).parent.parent
    expected = dict(yosys=oss / 'bin/yosys', abc=oss / 'bin/yosys-abc', solver=oss / 'bin/z3')
    if any(Path(tools[name]) != path or not path.resolve().is_relative_to(oss.resolve())
            for name, path in expected.items()):
        raise RuntimeError('Importer/solver/ABC tool escapes the selected OSS package')
    paths = [*expected.values(), *(oss / 'libexec' / name for name in
        ('yosys', 'yosys-abc', 'z3', 'realpath'))]
    data = oss / 'share/yosys'
    if not data.is_dir():
        raise RuntimeError('Missing selected Yosys technology/mapping data')
    paths += [path for path in data.rglob('*') if path.is_file()]
    for path in sorted(set(paths)):
        if not path.is_file() or not path.resolve().is_relative_to(oss.resolve()):
            raise RuntimeError('Missing or redirected importer/mapping runtime dependency: ' + str(path))
        base['files'][str(path)] = dict(sha256=h.digest(path), resolved=str(path.resolve()))
    lean = Path(tools['lean']).parent.parent
    circt = Path(tools['circt']).parent.parent
    compiled = [path for path in (lean / 'lib/lean').rglob('*') if path.is_file() and
        ('.olean' in path.name or path.name.endswith(('.ir', '.ir.sig')))]
    native = [path for package in (lean, circt, oss) for path in (package / 'lib').rglob('*')
        if path.is_file() and (path.name.endswith('.dylib') or '.so' in path.name)]
    for path in sorted(set(compiled + native)):
        if not any(path.resolve().is_relative_to(package.resolve()) for package in (lean, circt, oss)):
            raise RuntimeError('Compiled standard library or runtime escapes its package')
        base['files'][str(path)] = dict(sha256=h.digest(path), resolved=str(path.resolve()))
    base['scope'] += (' Also includes Yosys, Z3 and yosys-abc wrappers AND their libexec payloads, '
        'every selected share/yosys technology/mapping data file, compiled Lean standard-library '
        '.olean/private/server and IR inputs, and recursive native libraries in all three packages.')
    return base


def check_mutations(report, names, *, private_axiom=False, stateless=False):
    records = report.get('mutations', [])
    if [record.get('name') for record in records] != list(names):
        raise RuntimeError('Missing, reordered or duplicate distinguishing artifact controls')
    for index, record in enumerate(records):
        if (record.get('passed') is not True or record.get('expected_rejection') is not (index != 0) or
                (not stateless and (record.get('all_state_reimport') is not (index == 0) or not record.get('operation'))) or
                (stateless and (not record.get('proof_directory') or not record.get('module')))):
            raise RuntimeError('Artifact control did not prove its declared unchanged/mutated boundary')
    if private_axiom and report.get('private_axiom_rejected') is not True:
        raise RuntimeError('Raw component did not reject its injected private axiom')


def check_component(report, kind, address_bits, assembly):
    prefix = 'CoreD' + str(2 ** address_bits) if kind == 'core' else 'QuadFrontend'
    modules = [prefix + name for name in ('Hints', 'Sources', 'Graphs', 'LocalProofs',
        'Links', 'Model', 'Endpoints', 'Proof')]
    if (report.get('passed') is not True or report.get('kind') != kind or
            report.get('addr_bits') != address_bits or report.get('all_state') is not True or
            report.get('all_outputs') is not True or report.get('frozen_inputs_unchanged') is not True or
            report.get('registers') != len(assembly['registers']) or
            report.get('state_bits') != sum(register['width'] for register in assembly['registers']) or
            report.get('outputs') != len(assembly['outputs']) or report.get('compiled_modules') != modules or
            min(report.get('source_nodes', 0), report.get('rtl_nodes', 0), report.get('partitions', 0)) <= 0 or
            {Path(path).name for path in report.get('emitted_input_sha256_before', {})} !=
                {'core.mlir', 'frontend.mlir', 'assembly.json', 'frontend-assembly.json'} or
            report.get('emitted_input_sha256_before') != report.get('emitted_input_sha256_after')):
        raise RuntimeError('Incomplete all-state/all-output raw component certificate')
    if len(re.findall(r'Pinwheel audit: \d+ declarations, \d+ theorems; standard axioms only\.',
            report.get('axiom_audit', ''))) != 1:
        raise RuntimeError('Raw component lacks an unambiguous private-declaration audit')
    check_mutations(report, ('unchanged', 'program-bank', 'owner-output') if kind == 'core' else
        ('unchanged', 'retained-export', 'ready-output'), private_axiom=True)


class SectionRun:
    def __init__(self, run, section): self.run, self.section = run, section
    def __call__(self, argv, label, **options):
        return self.run(argv, self.section + '--' + label, **options)


def expected_rejections(records, minimum):
    failures = [record for record in records if record.get('expected_failure')]
    if len(failures) < minimum or any(type(record.get('exit_code')) is not int or
            record['exit_code'] == 0 or record.get('error') for record in failures):
        raise RuntimeError('Distinguishing controls lack completed expected-failure commands')


def composition_texts(factory, addr_bits):
    texts = factory.generate(addr_bits)
    root = 'StreamingSessionD' + str(2 ** addr_bits)
    if (type(texts) is not dict or root not in texts or not texts or
            any(not re.fullmatch(r'[A-Za-z_][A-Za-z0-9_]*', name) or
                type(source) is not str or not source.strip() for name, source in texts.items())):
        raise RuntimeError('Composition factory must supply concrete named Lean modules and the required root')
    return texts, root


def join_checks(roots):
    if roots != ['StreamingSessionD2', 'StreamingSessionD4']:
        raise RuntimeError('Both distinct depth composition roots are mandatory')
    lines = ['import ' + name for name in roots]
    for root in roots:
        for theorem in JOIN_THEOREMS:
            lines.append('#check Pinwheel.Artifact.' + root + '.' + theorem)
    return '\n'.join(lines) + '\n'


def generated_closure(gate, snapshot, directories, roots, committed):
    frozen = {}
    for directory in directories:
        directory = Path(directory)
        for path in directory.glob('*.lean'):
            if path.name in frozen:
                raise RuntimeError('Ambiguous generated module across isolated proof directories')
            frozen[path.name] = gate.digest(path)
    return gate.proof_closure(snapshot, directories, roots, committed, frozen)


def archive_closeout(h, directory, report):
    for name in ('selected', 'producer'):
        expected = report.get(name + '_archive_sha256')
        path = Path(directory) / (name + '-source.tar')
        if expected is not None and (not path.is_file() or path.is_symlink() or h.digest(path) != expected):
            raise RuntimeError('Retained ' + name + ' archive changed after intake')


def validate_worker(report, config, *, closeout=False):
    selected = config['stage']
    full = selected == 'full'
    names = ['library', 'emission']
    if full or selected == 'components': names += ['raw-components', 'actual-wrappers']
    if full or selected == 'wire': names += ['public-wire']
    if full or selected == 'cost': names += ['matched-cost']
    if full: names += ['composition-and-audit']
    if (report.get('schema') != SCHEMA or report.get('stage') != selected or
            report.get('source_commit') != config['source_commit'] or
            report.get('producer_commit') != config['producer_commit'] or report.get('passed') is not True or
            report.get('full_qualification') is not full or list(report.get('stages', {})) != names or
            report.get('required_targets') != (list(TARGETS) if full else [])):
        raise RuntimeError('Worker receipt does not match the exact requested continuation scope')
    if any(report['stages'][name].get('passed') is not True for name in names):
        raise RuntimeError('Incomplete mandatory continuation stage')
    records = report.get('commands', [])
    if not records or any(type(record.get('exit_code')) is not int or record.get('error') or
            (record['exit_code'] == 0) == bool(record.get('expected_failure')) for record in records):
        raise RuntimeError('Missing or unexpected native command outcome')
    if full or selected == 'components':
        raw = report['stages']['raw-components']['result']
        interfaces = report['stages']['emission']['result']['interfaces']
        if set(raw) != {'frontend', 'core-d2', 'core-d4'}:
            raise RuntimeError('All three distinct raw components are mandatory')
        for name, kind, a in [('frontend', 'frontend', 1), ('core-d2', 'core', 1), ('core-d4', 'core', 2)]:
            check_component(raw[name], kind, a, interfaces[str(a)][kind])
            if not raw[name].get('positive_proof_closure') or not raw[name].get('private_control_proof_closure'):
                raise RuntimeError('Raw component lacks indexed positive/private proof closure')
        wrappers = report['stages']['actual-wrappers']['result']
        if set(wrappers) != {'2', '4'}:
            raise RuntimeError('Both actual wrapper boundaries are mandatory')
        for value in wrappers.values():
            check_mutations(value, ('unchanged', 'package-wire', 'package-clock', 'tiny-output'), stateless=True)
            if value.get('passed') is not True or value.get('inputs_unchanged') is not True:
                raise RuntimeError('Actual wrapper source binding did not close')
        expected_rejections(records, 15)
    if full:
        join = report['stages']['composition-and-audit']['result']
        if (join.get('passed') is not True or join.get('roots') != ['StreamingSessionD2', 'StreamingSessionD4'] or
                join.get('mandatory_theorems') != list(JOIN_THEOREMS) or
                join.get('private_axiom_rejected') is not True or
                join.get('full_source_and_initialization_composed') is not True or
                min(join.get('audited_declarations', 0), join.get('audited_theorems', 0)) <= 0 or
                not join.get('proof_dependency_closure') or
                any(name not in join.get('target_types', '') for name in JOIN_THEOREMS)):
            raise RuntimeError('Missing checked source/runtime/initialized-upload composition or final audit')
        expected_rejections(records, 16)
    if full or selected == 'wire':
        wire = report['stages']['public-wire']['result']
        if (wire.get('raw_certified_inputs') is not full or
                set(wire.get('adversarial', {})) != {'2', '4'} or
                set(wire.get('staging_races', {})) != {'2', '4'}):
            raise RuntimeError('Public-wire scope or depth coverage differs')
        contract = load_file('_selected_wire_closeout_contract',
            Path(config['snapshot']) / 'scripts/check-streaming-rtl-sim.py')
        contract.check_results(wire['cases'])
        from streaming_adversarial import check_adversarial
        from streaming_staging_race import check_races
        for value in wire['adversarial'].values(): check_adversarial(value)
        for value in wire['staging_races'].values(): check_races(value)
        if (wire.get('physical_edges') != sum(case['physical_edges'] for case in wire['cases']) +
                sum(value['physical_edges'] for value in wire['adversarial'].values()) +
                sum(value['physical_edges'] for value in wire['staging_races'].values())):
            raise RuntimeError('Complete public-wire aggregate edge count differs')
    if full or selected == 'cost':
        from streaming_cost import check_comparison
        value = report['stages']['matched-cost']['result']
        check_comparison(value)
        if full and len(value.get('raw_certified_input_binding', {})) != 12:
            raise RuntimeError('Mapped cost is not bound to the actual certified raw sources')
    if closeout and any(report.get(key) is not True for key in ('archived_inputs_unchanged',
            'producer_unchanged', 'tool_identity_unchanged', 'frozen_artifacts_unchanged')):
        raise RuntimeError('Continuation closeout failed an immutable input/runtime check')


def worker(config_path):
    h = helpers()
    config = json.loads(Path(config_path).read_text())
    snapshot, out = Path(config['snapshot']), Path(config['worker_out'])
    out.mkdir()
    (out / 'logs').mkdir()
    (out / 'stages').mkdir()
    orchestration = h.load_helpers(ROOT)
    commands = orchestration.Commands(snapshot, out / 'logs', default_timeout=900)
    report = dict(schema=SCHEMA, stage=config['stage'], passed=False, full_qualification=False,
        boundary=BOUNDARY, required_targets=list(TARGETS) if config['stage'] == 'full' else [],
        source_commit=config['source_commit'], producer_commit=config['producer_commit'],
        commands=commands.records, stages={}, input_sha256_before_use={})
    intents = (out / 'command-intents.jsonl').open('x', buffering=1)
    journal = (out / 'input-freeze.jsonl').open('x', buffering=1)
    started, failure = time.monotonic(), None

    def publish(): h.write_json(out / 'worker-report.json', report)

    def run(argv, label, **options):
        intents.write(json.dumps(dict(index=len(commands.records), label=label,
            argv=list(map(str, argv)), options=options)) + '\n')
        return commands(argv, label, **options)

    def freeze(paths):
        paths = [Path(path) for path in paths if not Path(path).is_dir()]
        if any(not path.is_file() for path in paths):
            raise RuntimeError('Expected a present generated input before consumption')
        h.freeze(report, out, paths)
        journal.write(json.dumps({str(path.relative_to(out)): h.digest(path) for path in paths}) + '\n')

    def stage(name, operation):
        receipt = out / 'stages' / (name + '.json')
        record = dict(name=name, passed=False, command_start=len(commands.records))
        report['stages'][name] = record
        publish()
        begin = time.monotonic()
        try:
            value = operation()
            record.update(passed=True, result=value)
            return value
        except BaseException as error:
            record['error'] = type(error).__name__ + ': ' + str(error)
            raise
        finally:
            record.update(command_end=len(commands.records), elapsed_seconds=round(time.monotonic() - begin, 3))
            h.write_json(receipt, record)
            freeze([receipt])
            publish()

    try:
        check_environment(h)
        if h.membership(ROOT, config['producer_tree'], config['object_format']) != config['producer_sha256']:
            raise RuntimeError('Producer archive membership changed before worker use')
        if h.membership(snapshot, config['source_tree'], config['object_format']) != config['source_sha256']:
            raise RuntimeError('Selected source archive changed before worker use')
        tools = config['tool_paths']
        manifest = json.loads((snapshot / 'tools/hardware-toolchain.json').read_text())
        if json.loads((snapshot / 'lake-manifest.json').read_text()).get('packages'):
            raise RuntimeError('Continuation coordinator expects no external Lake dependencies')
        if tool_identity(h, tools, manifest) != config['tool_identity']:
            raise RuntimeError('Selected tool/runtime inventory changed before worker use')
        versions = {name: run([tools[name], *flags], name + '-version', timeout=30).strip()
            for name, flags in [('lean', ['--version']), ('lake', ['--version']), ('circt', ['--version']),
                ('yosys', ['-V']), ('solver', ['-version']), ('abc', ['-c', 'version']),
                ('iverilog', ['-V']), ('vvp', ['-V'])]}
        expected = (snapshot / 'lean-toolchain').read_text().strip().split(':v')[-1]
        h.check_versions(versions, expected, manifest)
        report['tool_versions'] = versions
        sys.path.insert(0, str(snapshot / 'scripts'))
        gate = load_file('_streaming_continuation_proof_helpers', snapshot / 'scripts/check-buffered-rtl-session.py')
        gate.check_versions(versions, expected, manifest)
        if 'UC Berkeley, ABC 1.01 (compiled Sep 12 2026 06:24:20)' not in versions['abc']:
            raise RuntimeError('Unexpected selected ABC version')
        selected = run([tools['lake'], 'env', 'which', 'lean'], 'lake-selected-lean', timeout=30).strip()
        if Path(selected).resolve() != Path(tools['lean']).resolve():
            raise RuntimeError('Lake did not select the fingerprinted native Lean')
        search = run([tools['lake'], 'env', 'printenv', 'LEAN_PATH'], 'lake-search-path', timeout=30).strip()
        if set(search.split(os.pathsep)) != {str(snapshot / '.lake/build/lib/lean'),
                str(Path(tools['lean']).parent.parent / 'lib/lean')}:
            raise RuntimeError('Lake includes an unselected compiled proof cache')
        report['lean_search_path'] = search.split(os.pathsep)

        class ProofGate:
            def __getattr__(self, name): return getattr(gate, name)
            def freeze_inputs(self, child, root, paths):
                paths = list(paths)
                freeze(paths)
                return gate.freeze_inputs(child, root, paths)
        proof_gate = ProofGate()
        selected_stage = config['stage']
        full = selected_stage == 'full'
        build = ['Pinwheel.Hardware.Streaming.FrontendEmit', 'Pinwheel.Program.StreamingCompile']
        if full or selected_stage == 'components':
            build += ['Pinwheel.Hardware.Streaming.TinyWiring', 'Pinwheel.Hardware.Streaming.Readback']
        if full:
            build += ['Pinwheel.Hardware.Streaming.SessionCorrespondence',
                'Pinwheel.Hardware.Streaming.Initialization', 'Pinwheel.Hardware.Streaming.InputCorrespondence',
                'Pinwheel.Hardware.Streaming.InitializedSession', 'Pinwheel.Program.StreamingTiming']
        if full or selected_stage == 'cost':
            build += ['Pinwheel.Hardware.Buffered.Serial', 'Pinwheel.Hardware.Buffered.Sram']
        stage('library', lambda: dict(output=run([tools['lake'], 'build', *build], 'fresh-selected-library-build', timeout=3600)))
        from streaming_wrapper import bridge_source, package_source, tt_source
        emitted, wrappers, metadata = {}, {}, {}

        def emission():
            for a in (1, 2):
                depth = 2 ** a
                directory = out / 'emitted' / ('d' + str(depth))
                run([tools['lake'], 'env', 'lean', '-DwarningAsError=true', '--run',
                    'test/StreamingArtifactEmit.lean', directory, str(a)], 'emit-d' + str(depth))
                files = [directory / name for name in ('core.mlir', 'frontend.mlir', 'assembly.json', 'frontend-assembly.json')]
                freeze(files)
                emitted[a] = directory
                core = json.loads((directory / 'assembly.json').read_text())
                front = json.loads((directory / 'frontend-assembly.json').read_text())
                metadata[a] = dict(core=core, frontend=front)
                target = out / 'actual-wrappers' / ('d' + str(depth))
                target.mkdir(parents=True)
                for name, source in [('package', package_source(core, front)), ('tt', tt_source(depth)), ('bridge', bridge_source(depth))]:
                    (target / (name + '.sv')).write_text(source)
                freeze(target.glob('*.sv'))
                wrappers[a] = target
            for name in ('frontend.mlir', 'frontend-assembly.json'):
                if h.digest(emitted[1] / name) != h.digest(emitted[2] / name):
                    raise RuntimeError('Frontend must be exactly independent of FIFO depth')
            return dict(emitted={str(a): str(path) for a, path in emitted.items()},
                interfaces={str(a): value for a, value in metadata.items()}, frontend_depth_independent=True)
        stage('emission', emission)
        components, wrapper_reports, proof_dirs = {}, {}, []
        certified_sv = {}

        def component_proofs():
            import streaming_artifacts
            for kind, a in (('frontend', 1), ('core', 1), ('core', 2)):
                name = 'frontend' if kind == 'frontend' else 'core-d' + str(2 ** a)
                target = out / 'raw' / name
                first = len(commands.records)
                child = streaming_artifacts.component(kind, a, emitted[a], target, tools,
                    SectionRun(run, 'raw-' + name), gate=proof_gate)
                check_component(child, kind, a, metadata[a][kind])
                expected_rejections(commands.records[first:], 3)
                positive = target / 'proof'
                child['positive_proof_closure'] = generated_closure(gate, snapshot, [positive],
                    [child['compiled_modules'][-1]], config['source_sha256'])
                child['control_proof_closures'] = {}
                for control in child['mutations']:
                    directory = Path(control['proof_directory'])
                    if not directory.resolve().is_relative_to((target / 'controls').resolve()):
                        raise RuntimeError('Raw mutation proof escapes its new retained directory')
                    child['control_proof_closures'][control['name']] = generated_closure(gate,
                        snapshot, [directory, positive], control['modules'], config['source_sha256'])
                child['private_control_proof_closure'] = generated_closure(gate, snapshot, [positive],
                    child['private_control_modules'], config['source_sha256'])
                components[name] = child
                certified_sv[name] = target / (kind + '.sv')
                proof_dirs.append(target / 'proof')
                freeze(path for path in target.rglob('*') if path.is_file())
            return components
        if full or selected_stage == 'components':
            stage('raw-components', component_proofs)

            def wrapper_proofs():
                import streaming_wrapper_readback
                for a in (1, 2):
                    depth = 2 ** a
                    target = out / 'wrapper-proofs' / ('d' + str(depth))
                    first = len(commands.records)
                    child = streaming_wrapper_readback.certify(a, wrappers[a] / 'package.sv',
                        wrappers[a] / 'tt.sv', target, tools, SectionRun(run, 'wrapper-d' + str(depth)), gate=proof_gate)
                    check_mutations(child, ('unchanged', 'package-wire', 'package-clock', 'tiny-output'), stateless=True)
                    expected_rejections(commands.records[first:], 3)
                    name = 'StreamingWrappersD' + str(depth)
                    positive = Path(child.get('proof_directory', ''))
                    if (child.get('passed') is not True or child.get('inputs_unchanged') is not True or
                            positive.resolve() != (target / 'unchanged').resolve() or
                            not (positive / (name + '.lean')).is_file()):
                        raise RuntimeError('Wrapper worker omitted its concrete certificate module')
                    for label, file in [('package', 'package.sv'), ('tiny', 'tt.sv')]:
                        if h.digest(positive / (label + '.sv')) != h.digest(wrappers[a] / file):
                            raise RuntimeError('Positive wrapper certificate changed its actual input source')
                    proof_gate.compile_lean(SectionRun(run, 'wrapper-confirm-d' + str(depth)), tools, positive, name)
                    child['control_proof_closures'] = {}
                    for control in child['mutations']:
                        directory = Path(control['proof_directory'])
                        if not directory.resolve().is_relative_to(target.resolve()):
                            raise RuntimeError('Wrapper mutation proof escapes its retained directory')
                        child['control_proof_closures'][control['name']] = generated_closure(gate,
                            snapshot, [directory], [control['module']], config['source_sha256'])
                    proof_dirs.append(positive)
                    wrapper_reports[str(depth)] = child
                    freeze(path for path in target.rglob('*') if path.is_file())
                return wrapper_reports
            stage('actual-wrappers', wrapper_proofs)

        def ensure_sv():
            for name, a, component in [('frontend', 1, 'frontend'), ('core-d2', 1, 'core'), ('core-d4', 2, 'core')]:
                if name in certified_sv:
                    continue
                target = out / 'simulation-sv'
                target.mkdir(exist_ok=True)
                source = target / (name + '.sv')
                source.write_text(run([tools['circt'], emitted[a] / (component + '.mlir'), '--canonicalize',
                    '--lower-seq-to-sv', '--lower-hw-to-sv', '--hw-legalize-modules', '--export-verilog',
                    '-o', '/dev/null'], 'simulation-lower-' + name))
                freeze([source])
                certified_sv[name] = source

        def wire_tests():
            ensure_sv()
            from streaming_compile import jtag_image, lean_certificate, spi_image
            from streaming_wire_cases import run_custody, run_stream
            from streaming_adversarial import check_adversarial, run_adversarial
            from streaming_staging_race import check_races, image_for, run_races
            contract = load_file('_selected_streaming_wire_contract', snapshot / 'scripts/check-streaming-rtl-sim.py')
            target = out / 'wire'
            target.mkdir()
            report['operations'] = []
            cases, adverse, races, binding = [], {}, {}, {}
            for protocol, image in [('spi', spi_image()), ('jtag', jtag_image()),
                    ('race-halt', image_for('halt')), ('race-fault', image_for('fault'))]:
                path = target / (protocol + '-image.lean')
                path.write_text(lean_certificate(image))
                freeze([path])
                run([tools['lake'], 'env', 'lean', '-DwarningAsError=true', path],
                    protocol + '-automatic-kernel-image-check')
            for a in (1, 2):
                depth = 2 ** a
                directory = target / ('d' + str(depth))
                directory.mkdir()
                sources = [certified_sv['core-d' + str(depth)], certified_sv['frontend'],
                    wrappers[a] / 'package.sv', wrappers[a] / 'tt.sv', wrappers[a] / 'bridge.sv']
                freeze(sources)
                executable = directory / 'chip.vvp'
                run([tools['iverilog'], '-g2012', '-s', 'streaming_quad_host_bridge', '-o', executable,
                    *sources], 'wire-compile-d' + str(depth))
                freeze([executable])
                binding[str(depth)] = {str(path.relative_to(out)): h.digest(path) for path in sources}
                definitions = [('spi', 32768, None), ('jtag', 4097, None), ('spi', 0, None),
                    ('spi', 8, 'request_close'), ('spi', 8, 'request_crc'),
                    ('spi', 8, 'response_crc'), ('spi', 8, 'partial_read')]
                for protocol, bits, fault in definitions:
                    name = protocol + '-' + str(bits) + '-' + (fault or 'clean')
                    report['operations'].append(dict(api='streaming_wire_cases.run_stream',
                        argv=[tools['vvp'], str(executable)], depth=depth, protocol=protocol, bits=bits, fault=fault))
                    publish()
                    child = run_stream(tools['vvp'], executable, directory / name,
                        protocol=protocol, bits=bits, depth=depth, fault=fault)
                    h.write_json(directory / (name + '.json'), child)
                    cases.append(child)
                    if child.get('passed') is not True:
                        raise RuntimeError('Mandatory wire case failed: ' + name + ': ' + child.get('error', 'unknown'))
                report['operations'].append(dict(api='streaming_wire_cases.run_custody',
                    argv=[tools['vvp'], str(executable)], depth=depth))
                publish()
                child = run_custody(tools['vvp'], executable, directory / 'custody', depth=depth)
                child['kind'] = 'custody'
                h.write_json(directory / 'custody.json', child)
                cases.append(child)
                if child.get('passed') is not True:
                    raise RuntimeError('Mandatory retained custody/reuse case failed')
                report['operations'].append(dict(api='streaming_adversarial.run_adversarial',
                    argv=[tools['vvp'], str(executable)], depth=depth,
                    note='Six physical subcases, then one explicitly host-only sequence refusal'))
                publish()
                child = run_adversarial(tools['vvp'], executable, directory / 'adversarial', depth=depth)
                check_adversarial(child)
                adverse[str(depth)] = child
                report['operations'].append(dict(api='streaming_staging_race.run_races',
                    argv=[tools['vvp'], str(executable)], depth=depth,
                    note='HALT/FAULT at N33/TX32 and N65/TX64; align only from public protocol pins'))
                publish()
                child = run_races(tools['vvp'], executable, directory / 'terminal-staging-races', depth=depth)
                check_races(child)
                races[str(depth)] = child
                freeze(path for path in directory.rglob('*') if path.is_file())
            contract.check_results(cases)
            result = dict(cases=cases, adversarial=adverse, staging_races=races, raw_certified_inputs=full,
                source_binding=binding, physical_edges=sum(case['physical_edges'] for case in cases) +
                    sum(value['physical_edges'] for value in adverse.values()) +
                    sum(value['physical_edges'] for value in races.values()))
            h.write_json(target / 'report.json', result)
            freeze([target / 'report.json'])
            return result
        wire = stage('public-wire', wire_tests) if full or selected_stage == 'wire' else None

        def cost_tests():
            import streaming_cost
            library = Path(config['library']['staged'])
            if h.digest(library) != streaming_cost.LIBRARY_SHA256:
                raise RuntimeError('Selected cost library changed before use')
            target = out / 'cost'
            matched = {}

            def cost_run(argv, label, **options):
                # The helper freshly emits all rows. Bind each new streaming
                # reemission to its raw-certified source BEFORE any mapping.
                if full and label in ('streaming-d2', 'streaming-d4',
                        'buffered-v1-macro-excluded', 'buffered-v1-full-digital-ff'):
                    for a in (1, 2):
                        depth = 2 ** a
                        directory = target / 'emitted' / ('d' + str(depth))
                        expected_files = {'core.sv': certified_sv['core-d' + str(depth)],
                            'frontend.sv': certified_sv['frontend'], 'package.sv': wrappers[a] / 'package.sv',
                            'tt.sv': wrappers[a] / 'tt.sv', 'core.mlir': emitted[a] / 'core.mlir',
                            'frontend.mlir': emitted[a] / 'frontend.mlir'}
                        for name, expected_path in expected_files.items():
                            if h.digest(directory / name) != h.digest(expected_path):
                                raise RuntimeError('Cost reemission differs from raw-certified input: ' + name)
                            matched[str((directory / name).relative_to(out))] = h.digest(expected_path)
                if target.exists(): freeze(path for path in target.rglob('*') if path.is_file())
                value = run(argv, 'cost--' + label, **options)
                if target.exists(): freeze(path for path in target.rglob('*') if path.is_file())
                return value
            child = streaming_cost.compare(cost_run, target, root=snapshot, library=library,
                yosys=tools['yosys'], abc=tools['abc'], circt=tools['circt'], lake=tools['lake'])
            streaming_cost.check_comparison(child)
            if full and len(matched) != 12:
                raise RuntimeError('Cost inputs lack the exact two-depth raw-artifact binding')
            child['raw_certified_input_binding'] = matched
            freeze(path for path in target.rglob('*') if path.is_file())
            return child
        cost = stage('matched-cost', cost_tests) if full or selected_stage == 'cost' else None

        def composition():
            import streaming_composition
            target = out / 'composition'
            target.mkdir()
            texts, roots = {}, []
            for a in (1, 2):
                values, root = composition_texts(streaming_composition, a)
                if texts.keys() & values.keys():
                    raise RuntimeError('Composition modules collide across FIFO depths')
                texts.update(values)
                roots.append(root)
            texts['StreamingRequiredTargets'] = join_checks(roots)
            for name, source in texts.items(): (target / (name + '.lean')).write_text(source)
            freeze(target.glob('*.lean'))
            all_dirs = [*proof_dirs, target]
            frozen_generated = {}
            for directory in all_dirs:
                for path in directory.glob('*.lean'):
                    if path.name in frozen_generated:
                        raise RuntimeError('Ambiguous positive generated proof module: ' + path.name)
                    frozen_generated[path.name] = h.digest(path)
            closure = gate.proof_closure(snapshot, all_dirs, ['StreamingRequiredTargets'],
                config['source_sha256'], frozen_generated)
            imports = sorted({module for path in target.glob('*.lean') for module in gate.imports(path)
                if module.startswith('Pinwheel.')})
            if imports:
                run([tools['lake'], 'build', *imports], 'fresh-composition-library-build', timeout=3600)
            remaining = set(texts)
            compiled = []
            target_output = None
            while remaining:
                ready = sorted(name for name in remaining if not
                    (set(gate.imports(target / (name + '.lean'))) & remaining))
                if not ready:
                    raise RuntimeError('Cyclic generated composition imports')
                for name in ready:
                    output = proof_gate.compile_lean(SectionRun(run, 'composition'), tools, target,
                        name, paths=proof_dirs)
                    if name == 'StreamingRequiredTargets': target_output = output
                    remaining.remove(name)
                    compiled.append(name)
            if target_output is None or any(theorem not in target_output for theorem in JOIN_THEOREMS):
                raise RuntimeError('Native Lean omitted a mandatory typed composition target')
            template = (snapshot / 'test/ProofAudit.lean').read_text()
            modules = [path.stem for directory in all_dirs for path in directory.glob('*.lean')]
            audit = gate.audit_source(template, modules, root_module='StreamingRequiredTargets')
            private = 'StreamingFinalPrivateAxiom'
            reject = 'StreamingFinalRejectAxiom'
            (target / 'StreamingFinalAudit.lean').write_text(audit)
            (target / (private + '.lean')).write_text('import Init\nprivate axiom untrustedStreamingContinuation : False\n')
            (target / (reject + '.lean')).write_text(gate.audit_source(template, [*modules, private],
                root_module='StreamingRequiredTargets').replace('import StreamingRequiredTargets\n',
                'import StreamingRequiredTargets\nimport ' + private + '\n'))
            freeze([target / (name + '.lean') for name in ('StreamingFinalAudit', private, reject)])
            output = proof_gate.compile_lean(SectionRun(run, 'final-audit'), tools, target,
                'StreamingFinalAudit', paths=proof_dirs)
            matches = re.findall(r'Pinwheel audit: (\d+) declarations, (\d+) theorems; standard axioms only\.', output)
            if len(matches) != 1:
                raise RuntimeError('Missing complete final private-declaration axiom audit')
            proof_gate.compile_lean(SectionRun(run, 'final-audit'), tools, target, private, paths=proof_dirs)
            rejected = proof_gate.compile_lean(SectionRun(run, 'final-audit'), tools, target,
                reject, paths=proof_dirs, reject='Unapproved axioms in _private.')
            if 'untrustedStreamingContinuation' not in rejected:
                raise RuntimeError('Injected final private axiom was rejected for an unrelated declaration')
            if gate.proof_closure(snapshot, all_dirs, ['StreamingRequiredTargets'],
                    config['source_sha256'], frozen_generated) != closure:
                raise RuntimeError('Positive composition proof dependency closure changed')
            freeze(path for path in target.rglob('*') if path.is_file())
            return dict(passed=True, roots=roots, mandatory_theorems=list(JOIN_THEOREMS),
                compiled_modules=compiled, target_types=target_output, proof_dependency_closure=closure,
                audited_declarations=int(matches[0][0]), audited_theorems=int(matches[0][1]),
                private_axiom_rejected=True, full_source_and_initialization_composed=True)
        if full:
            stage('composition-and-audit', composition)
        report.update(passed=True, full_qualification=full,
            scope='full fresh continuation contract' if full else selected_stage + ' only; no full qualification')
        validate_worker(report, config)
    except BaseException as error:
        failure = error
        report.update(passed=False, full_qualification=False, error=type(error).__name__ + ': ' + str(error))
    finally:
        try:
            if h.membership(snapshot, config['source_tree'], config['object_format']) != config['source_sha256']:
                raise RuntimeError('Selected source archive changed during continuation gate')
            if h.membership(ROOT, config['producer_tree'], config['object_format']) != config['producer_sha256']:
                raise RuntimeError('Producer archive changed during continuation gate')
            if tool_identity(h, config['tool_paths'], json.loads((snapshot / 'tools/hardware-toolchain.json').read_text())) != config['tool_identity']:
                raise RuntimeError('Tool/runtime inventory changed during continuation gate')
            h.check_frozen(report, out)
            report.update(archived_inputs_unchanged=True, producer_unchanged=True,
                tool_identity_unchanged=True, frozen_artifacts_unchanged=True)
        except Exception as error:
            report.update(passed=False, full_qualification=False, closeout_error=str(error))
        intents.close()
        journal.close()
        report['elapsed_seconds'] = round(time.monotonic() - started, 3)
        report['artifact_sha256'] = {str(path.relative_to(out)): h.digest(path)
            for path in sorted(out.rglob('*')) if path.is_file() and path != out / 'worker-report.json'}
        publish()
    if failure: raise failure
    if not report['passed']: raise RuntimeError('Continuation worker closeout refused acceptance')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--tag')
    parser.add_argument('--source-commit', default='HEAD')
    parser.add_argument('--producer-commit', default='HEAD')
    parser.add_argument('--stage', choices=STAGES, default='full')
    parser.add_argument('--circt', default=str(ROOT / 'build/tools/firtool-1.159.0/bin/circt-opt'))
    for name, program in [('yosys', 'yosys'), ('abc', 'yosys-abc'), ('solver', 'z3'),
            ('iverilog', 'iverilog'), ('vvp', 'vvp')]:
        parser.add_argument('--' + name, default=str(ROOT / 'build/tools/oss-cad-suite/bin' / program))
    parser.add_argument('--liberty', help='Exact retained typical CMOS5L library; required for full/cost')
    parser.add_argument('--timeout-seconds', type=int, default=21600)
    parser.add_argument('--worker-config', help=argparse.SUPPRESS)
    args = parser.parse_args()
    if args.worker_config:
        worker(args.worker_config)
        return
    if (not args.tag or not re.fullmatch(r'[A-Za-z0-9_-]+', args.tag) or
            not 1 <= args.timeout_seconds <= 43200 or
            any(not Path(getattr(args, name)).is_absolute() for name in
                ('circt', 'yosys', 'abc', 'solver', 'iverilog', 'vvp')) or
            args.stage in ('full', 'cost') and (not args.liberty or not Path(args.liberty).is_absolute())):
        parser.error('Provide a fresh --tag, absolute tool paths, timeout1..43200, and --liberty for full/cost')
    h = helpers()
    check_environment(h)
    git = lambda *items: subprocess.check_output(['git', *items], cwd=ROOT, text=True, timeout=30)
    producer_commit = git('rev-parse', '--verify', args.producer_commit + '^{commit}').strip()
    source_commit = git('rev-parse', '--verify', args.source_commit + '^{commit}').strip()
    algorithm = git('rev-parse', '--show-object-format').strip()
    tree = h.parse_tree(git('ls-tree', '-r', '-z', producer_commit))
    if any(path not in tree for path in PRODUCER):
        raise RuntimeError('Commit coordinator, pure helpers and focused tests before running a qualified producer')
    producer_tree = {path: tree[path] for path in PRODUCER}
    producer_hashes = h.membership(ROOT, producer_tree, algorithm)
    orchestration = h.load_helpers(ROOT)
    out = orchestration.fresh_directory(ROOT / 'build/validation', args.tag)
    (out / 'logs').mkdir()
    run = orchestration.Commands(ROOT, out / 'logs', default_timeout=60)
    report = dict(schema=SCHEMA, stage=args.stage, passed=False, full_qualification=False,
        boundary=BOUNDARY, required_targets=list(TARGETS) if args.stage == 'full' else [],
        started_utc=datetime.now(timezone.utc).isoformat(), source_commit=source_commit,
        producer_commit=producer_commit, producer_sha256=producer_hashes, commands=run.records,
        membership_scope='Every regular file in the selected Git archive plus the separate committed '
            'producer archive. Working-tree source changes are neither consumed nor claimed identical. '
            'No historical receipt or generated artifact is an input. Partial-stage receipts are not '
            'reused to establish a later full qualification.')
    started, failure, before, snapshot, hashes, library = time.monotonic(), None, None, None, None, None
    try:
        source_tree = h.parse_tree(run(['git', 'ls-tree', '-r', '-z', source_commit], 'selected-tree'))
        missing = required_inputs(args.stage) - source_tree.keys()
        if missing:
            raise RuntimeError('Selected source lacks required committed inputs: ' + ', '.join(sorted(missing)))
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
            raise RuntimeError('Producer archive differs from its selected Git objects')
        for relative in ('scripts/validation_run.py', 'scripts/process_group.py'):
            if hashes.get(relative) != producer_hashes[relative]:
                raise RuntimeError('Selected source and producer orchestration helpers differ')
        report.update(source_sha256=hashes, selected_git_objects=source_tree,
            committed_archive_membership_verified_before=True)
        proxy = shutil.which('lake')
        if not proxy: raise RuntimeError('Native Lean/Lake must be installed')
        prefix = Path(run([proxy, 'env', 'lean', '--print-prefix'], 'native-toolchain-prefix').strip())
        tools = {name: getattr(args, name) for name in ('circt', 'yosys', 'abc', 'solver', 'iverilog', 'vvp')}
        tools.update(lean=str(prefix / 'bin/lean'), lake=str(prefix / 'bin/lake'),
            python=str(Path(sys.executable).resolve()))
        manifest = json.loads((snapshot / 'tools/hardware-toolchain.json').read_text())
        before = tool_identity(h, tools, manifest)
        report.update(tool_paths=tools, tool_identity_before=before,
            discovery_lake_proxy=dict(path=proxy, sha256=h.digest(proxy)))
        if args.stage in ('full', 'cost'):
            lock = json.loads((snapshot / 'tools/technology-library.json').read_text())
            expected = next(item['sha256'] for item in lock['files']
                if item['name'] == 'sg13cmos5l_stdcell_typ_1p20V_25C.lib')
            original = Path(args.liberty)
            if expected != '34163f3e7de9f854afac57332ba06f1739b78e7ac35660a8a5ddd39c570124ad' or h.digest(original) != expected:
                raise RuntimeError('Use the exact committed typical technology-library pin')
            (out / 'inputs').mkdir()
            staged = out / 'inputs/cells.lib'
            staged.write_bytes(original.read_bytes())
            if h.digest(staged) != expected: raise RuntimeError('Staged Liberty differs from its input')
            library = dict(original=str(original), staged=str(staged), sha256=expected)
            report['library_identity_before'] = library
        config = dict(snapshot=str(snapshot), worker_out=str(out / 'worker'), stage=args.stage,
            source_commit=source_commit, producer_commit=producer_commit,
            source_tree=source_tree, source_sha256=hashes, producer_tree=producer_tree,
            producer_sha256=producer_hashes, object_format=algorithm, tool_paths=tools,
            tool_identity=before, library=library)
        config_path = out / 'worker-config.json'
        h.write_json(config_path, config)
        report['worker_config_sha256_before_use'] = h.digest(config_path)
        h.write_json(out / 'report.json', report)
        run([tools['python'], '-B', out / 'producer' / DRIVER, '--worker-config', config_path],
            'fresh-continuation-worker', timeout=args.timeout_seconds)
        if h.digest(config_path) != report['worker_config_sha256_before_use']:
            raise RuntimeError('Worker configuration changed during use')
        child_path = out / 'worker/worker-report.json'
        report['worker_report_sha256'] = h.digest(child_path)
        child = json.loads(child_path.read_text())
        # Verification imports are also restricted to the selected archive.
        sys.path.insert(0, str(snapshot / 'scripts'))
        validate_worker(child, config, closeout=True)
        actual_artifacts = {}
        for path in sorted((out / 'worker').rglob('*')):
            if path.is_symlink(): raise RuntimeError('Worker artifact is a symlink')
            if path.is_file() and path != child_path:
                actual_artifacts[str(path.relative_to(out / 'worker'))] = h.digest(path)
        if child.get('artifact_sha256') != actual_artifacts:
            raise RuntimeError('Worker artifact inventory differs from actual retained bytes')
        intents = [json.loads(line) for line in (out / 'worker/command-intents.jsonl').read_text().splitlines()]
        if len(intents) != len(child['commands']) or any(
                intent.get('index') != index or intent.get('label') != record['label'] or
                intent.get('argv') != record['argv'] for index, (intent, record) in enumerate(zip(intents, child['commands']))):
            raise RuntimeError('Pre-use command journal differs from completed native commands')
        report.update(worker=child, passed=True, full_qualification=child['full_qualification'])
    except BaseException as error:
        failure = error
        report['error'] = type(error).__name__ + ': ' + str(error)
    finally:
        try:
            archive_closeout(h, out, report)
            if h.membership(ROOT, producer_tree, algorithm) != producer_hashes:
                raise RuntimeError('Producer working bytes changed after intake')
            if hashes is not None and h.membership(snapshot, source_tree, algorithm) != hashes:
                raise RuntimeError('Selected source archive changed after intake')
            if before is not None:
                after = tool_identity(h, report['tool_paths'], manifest)
                if after != before: raise RuntimeError('Tool/runtime inventory changed after intake')
                report.update(tool_identity_after=after, tool_identity_unchanged=True)
            if library is not None:
                if any(h.digest(library[name]) != library['sha256'] for name in ('original', 'staged')):
                    raise RuntimeError('Technology library input changed after intake')
                report.update(library_identity_after=library, library_unchanged=True)
            report['committed_archive_membership_verified_after'] = True
        except Exception as error:
            report.update(passed=False, full_qualification=False, closeout_error=str(error))
        report['elapsed_seconds'] = round(time.monotonic() - started, 3)
        h.write_json(out / 'report.json', report)
    if failure: raise failure
    if not report['passed']: raise RuntimeError('Continuation closeout refused acceptance')
    print('Streaming continuation ' + args.stage + ' receipt: ' + str(out / 'report.json'), flush=True)


if __name__ == '__main__': main()
