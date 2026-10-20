#!/usr/bin/env python3
"""Fresh committed raw-to-mapped whole-device validation.

Every invocation first runs the unchanged UART coordinator's components stage
in a new Git archive. That partial receipt is an input stage, never the final
claim. A worker from the same committed archive then reconstructs mapped word,
register, package and pad functions and checks the whole source/session join.
No historical receipt, compiled project cache or generated RTL is an input.
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
import struct
import subprocess
import sys
import tarfile
import time

ROOT = Path(__file__).resolve().parents[1]
DRIVER = 'scripts/check-streaming-mapped.py'
RAW_DRIVER = 'scripts/check-streaming-uart.py'
SCHEMA = 'pinwheel.streaming-mapped-full.v1'
LIBRARY_SHA256 = '34163f3e7de9f854afac57332ba06f1739b78e7ac35660a8a5ddd39c570124ad'
TRACE_FORMAT = ('u32 cycle; u8 initialize,csn,sck,mosi,peerLevels,peerEnabled,links,pullups,'
    'preMiso,postReady,postBusy,postLevels,postEnabled,postWires,postKnown,preRaw')
LABELS = ('frontend', 'core-d2', 'core-d4')
HELPERS = tuple('scripts/streaming_mapped_' + name + '.py' for name in
    ('arithmetic', 'campaign', 'certificate', 'component', 'composition', 'cost',
     'device', 'flow', 'hierarchy', 'liberty', 'netlist', 'reductions', 'runtime', 'simulation', 'uart_timing', 'wrapper'))
TESTS = tuple('test/test_streaming_mapped_' + name + '.py' for name in
    ('arithmetic', 'campaign', 'certificate', 'component', 'cost', 'flow', 'gate',
     'hierarchy', 'liberty', 'netlist', 'package', 'reductions', 'runtime', 'uart_timing', 'wrapper'))
GENERIC = tuple('Pinwheel/Hardware/StreamingMapped/' + name + '.lean' for name in
    ('Boolean', 'Ripple', 'Word', 'Reduction', 'Comparison', 'Ports',
     'ReductionLogic', 'ReductionAnd', 'Clauses', 'TinyWiring', 'UARTTiming'))
RAW_PRODUCER = (RAW_DRIVER, 'scripts/check-buffered-rtl-sim.py',
    'scripts/validation_run.py', 'scripts/process_group.py', 'test/test_streaming_uart_gate.py')
BUILD_ROOTS = ('Pinwheel',)
TARGETS = ('fresh same-commit raw component and wrapper input stage',
    'frontend and both cores: complete source FF bijection and every D/output equation',
    'actual pinned-Liberty arithmetic, Boolean, mux and reduction word functions',
    'all44 exact mapped physical/source/initialization/protocol session APIs',
    'six additional mapped public UART first-BUSY-drop APIs at both queue depths',
    'complete actual mapped package/pad wiring and direct common event clock',
    'complete two-depth cell-area and full-state inventory',
    'selected mapped UART24/depth, I2C20 total and long SPI/JTAG4 total public-pin cases',
    'carry/output/operator/storage, package/pad/clock and actual FF sampler controls',
    'all positive private/generated declarations use only standard axioms; injected private axioms reject')
BOUNDARY = ('Universal two-state digital mapped D/output equations through actual interpreted '
    'pinned Liberty cells, full source storage, package/pad wiring and source sessions. '
    'Restricted JSON/Liberty/RTL interpretation and native Lean/tool runtimes are explicit '
    'trust boundaries. Independent finite public-pin diagnostics are separate evidence. '
    'This proof-oriented mapping has its own cell-area bill; no equivalence claim for earlier '
    'cost netlists, electrical behavior, delay/Fmax, placement/routing or silicon signoff.')


def require(condition, message):
    if not condition: raise RuntimeError(message)


def digest(path):
    value = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b''): value.update(block)
    return value.hexdigest()


def decode_json(data):
    def pairs(items):
        result = {}
        for key, value in items:
            require(key not in result, 'Duplicate master JSON key')
            result[key] = value
        return result
    return json.loads(data, object_pairs_hook=pairs)


def read_json(path):
    return decode_json(Path(path).read_bytes())


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def generated_session_library_imports():
    """Read dependencies from the actual session and timing factory outputs."""
    import streaming_mapped_composition
    import streaming_mapped_uart_timing
    sources = {}
    for addr_bits in (1, 2):
        sources.update(streaming_mapped_composition.generate(addr_bits))
        sources.update(streaming_mapped_uart_timing.generate(addr_bits))
    modules = {module for text in sources.values()
        for line in re.findall(r'^import\s+([^\n]+)', text, re.MULTILINE)
        for module in line.split() if module.startswith('Pinwheel.')}
    require(modules, 'Session factories emitted no project library dependencies')
    return sorted(modules)


def library_import_preflight(directory, tools, run, *, modules=None):
    """Ask Lean to load all factory library dependencies before any campaign.

    Loading a parent .olean also loads its transitive imports, so a missing
    dependency cannot hide behind the presence of the direct import file.
    Generated component modules are compiled later by the campaign itself.
    """
    modules = generated_session_library_imports() if modules is None else modules
    require(type(modules) is list and modules and len(modules) == len(set(modules)) and
        all(type(module) is str and re.fullmatch(r'[A-Za-z_][A-Za-z0-9_.]*', module) for module in modules),
        'Invalid native library import preflight')
    source = Path(directory) / 'MappedSessionLibraryImports.lean'
    require(not source.exists(), 'Library import preflight requires a fresh source')
    source.write_text(''.join('import ' + module + '\n' for module in modules))
    before = digest(source)
    run([tools['lake'], 'env', tools['lean'], '-DwarningAsError=true', str(source)],
        'mapped-session-library-import-preflight', timeout=900)
    require(digest(source) == before, 'Library import preflight source changed during native execution')
    return dict(checked=True, modules=modules, source=str(source), sha256=before)


def validate_library_import_preflight(preflight, directory):
    modules = generated_session_library_imports()
    expected = Path(directory).resolve() / 'MappedSessionLibraryImports.lean'
    require(preflight.get('checked') is True and preflight.get('modules') == modules and
        preflight.get('source') == str(expected),
        'Actual generated session library imports were not preflighted at the retained worker path')
    verify_files({str(expected): preflight.get('sha256')})
    require(expected.read_text() == ''.join('import ' + module + '\n' for module in modules),
        'Native library preflight source differs from the actual generated session import set')


def mapped_path(path):
    return (path.startswith('scripts/streaming_mapped_') and path.endswith('.py') or
        path.startswith('test/test_streaming_mapped_') and path.endswith('.py') or
        path.startswith('Pinwheel/Hardware/StreamingMapped/') and path.endswith('.lean'))


def required_inputs(tree):
    return set((DRIVER, *RAW_PRODUCER, *HELPERS, *TESTS, *GENERIC,
        'tools/hardware-toolchain.json', 'tools/technology-library.json',
        'Pinwheel/Program/StreamingUARTFirstTerminal.lean', 'test/StreamingUARTFirstTerminal.lean')).union(
        path for path in tree if mapped_path(path))


def producer_inputs(root, tree):
    selected = required_inputs(tree)
    # An uncommitted mapped helper/test/proof must not silently disappear from
    # the selected producer surface just because it is absent from ls-tree.
    for pattern in ('scripts/streaming_mapped_*.py', 'test/test_streaming_mapped_*.py',
            'Pinwheel/Hardware/StreamingMapped/**/*.lean'):
        selected.update(str(path.relative_to(root)) for path in Path(root).glob(pattern))
    require(selected <= tree.keys(), 'Commit every mapped coordinator/helper/test/proof before qualification: ' +
        ', '.join(sorted(selected - tree.keys())))
    return {path: tree[path] for path in sorted(selected)}


def regular_inventory(directory, *, omit=()):
    directory, result = Path(directory), {}
    require(directory.is_dir() and not directory.is_symlink(), 'Missing regular artifact directory')
    for path in sorted(directory.rglob('*')):
        require(not path.is_symlink(), 'Symlink in retained artifact inventory')
        if path.is_file() and str(path.relative_to(directory)) not in omit:
            result[str(path.relative_to(directory))] = digest(path)
    return result


def verify_files(files):
    require(type(files) is dict and files, 'Missing frozen input inventory')
    for path, expected in files.items():
        selected = Path(path)
        require(selected.is_absolute() and selected.is_file() and not selected.is_symlink() and
            digest(selected) == expected, 'Frozen input changed: ' + path)


def command_inventory(records):
    require(type(records) is list and records, 'Missing completed native command inventory')
    for record in records:
        require(type(record.get('exit_code')) is int and not record.get('error') and
            (record['exit_code'] != 0) == bool(record.get('expected_failure')),
            'Unexpected, missing or interrupted native exit')


def verify_journal(directory, records):
    intents = [read_json_line(line) for line in (Path(directory) / 'command-intents.jsonl').read_text().splitlines()]
    require(len(intents) == len(records) and all(intent.get('index') == index and
        intent.get('label') == record.get('label') and intent.get('argv') == record.get('argv')
        for index, (intent, record) in enumerate(zip(intents, records))),
        'Pre-use command intents differ from completed commands')


def read_json_line(text):
    # Journals have no user-controlled duplicate object keys; parse through the
    # same strict decoder without writing a transient file.
    def pairs(items):
        result = {}
        for key, value in items:
            require(key not in result, 'Duplicate command intent key')
            result[key] = value
        return result
    return json.loads(text, object_pairs_hook=pairs)


def validate_raw(report, config, raw, source_commit, tree, hashes, h):
    require(report.get('schema') == raw.SCHEMA and report.get('stage') == 'components' and
        report.get('source_commit') == source_commit and report.get('producer_commit') == source_commit and
        report.get('passed') is True and report.get('full_qualification') is False and
        report.get('committed_archive_membership_verified_before') is True and
        report.get('committed_archive_membership_verified_after') is True and
        report.get('tool_identity_unchanged') is True and report.get('selected_git_objects') == tree and
        report.get('source_sha256') == hashes and config.get('source_tree') == tree and
        config.get('source_sha256') == hashes and config.get('source_commit') == source_commit and
        config.get('producer_commit') == source_commit,
        'Raw input stage is not the fresh same-commit partial boundary')
    child = report.get('worker', {})
    raw.validate_worker(child, config, closeout=True)
    command_inventory(report.get('commands'))
    command_inventory(child.get('commands'))
    directory = Path(config['worker_out'])
    worker_path = directory / 'worker-report.json'
    require(report.get('worker_report_sha256') == digest(worker_path) and read_json(worker_path) == child,
        'Raw outer receipt does not bind the actual worker receipt')
    require(child.get('artifact_sha256') == regular_inventory(directory, omit=('worker-report.json',)),
        'Raw worker artifact bytes differ from its closed receipt')
    verify_journal(directory, child['commands'])
    raw.archive_closeout(h, directory.parent, report)
    return child


def component_config(raw_root, raw_child):
    raw_root, result = Path(raw_root), {}
    for label in LABELS:
        child = raw_child['stages']['raw-components']['result'][label]
        prefix = 'ReadyQuadFrontend' if label == 'frontend' else 'ReadyCoreD' + label[-1]
        namespace = 'Pinwheel.Artifact.StreamingReadyFrontend' if label == 'frontend' else 'Pinwheel.Artifact.StreamingReadyCoreD' + label[-1]
        modules = [prefix + suffix for suffix in ('Hints', 'Sources', 'Graphs', 'LocalProofs', 'Links', 'Model', 'Endpoints', 'Proof')]
        require(child.get('compiled_modules') == modules, 'Raw positive module order changed')
        directory = raw_root / 'worker/raw' / label
        sources = {name: str(directory / 'proof' / (name + '.lean')) for name in modules}
        generated = {name: item['sha256'] for name, item in child['positive_proof_closure'].items()
            if item.get('origin') == 'generated'}
        require(set(generated) == set(modules) and all(digest(sources[name]) == generated[name] for name in modules),
            'Raw positive source closure is incomplete or changed')
        kind = 'frontend' if label == 'frontend' else 'core'
        result[label] = dict(raw_json=str(directory / 'import-rtl.json'), sv=str(directory / (kind + '.sv')),
            raw_module=modules[-1], raw_namespace=namespace, raw_sources=sources)
    return result


def expected_qnames(raw):
    return ['Pinwheel.Artifact.StreamingMappedSessionD' + str(depth) + '.' + theorem
        for depth in (2, 4) for theorem in raw.JOIN_THEOREMS]


def expected_extra_qnames():
    return ['Pinwheel.Artifact.StreamingMappedSessionD' + str(depth) + '.' + theorem
        for depth in (2, 4) for theorem in ('uart_first_terminal_correct',
            'uart_bad_stop_first_terminal_correct', 'uart_false_start_first_terminal_correct')]


def validate_cad_membership(result, expected):
    require(type(result) is dict and result == expected and
        result.get('schema') == 'pinwheel.streaming-mapped-selected-cad-archive-membership.v1' and
        result.get('cad_selected_archive_membership_verified') is True and
        result.get('installed_payload_archive_membership_proved') is False and
        set(result.get('packages', {})) == {'circt', 'oss-cad-suite'} and
        type(result.get('selected_cad_files')) is int and result['selected_cad_files'] > 0,
        'Selected CAD archive membership is absent, broadened or differs from independent audit')


def validate_trace(path, receipt, edges):
    path = Path(path)
    require(type(receipt) is dict and type(edges) is int and edges > 0 and
        type(receipt.get('edges')) is int and receipt['edges'] == edges and
        type(receipt.get('bytes')) is int and receipt['bytes'] == 20 * edges and
        receipt.get('format') == TRACE_FORMAT and type(receipt.get('sha256')) is str and
        re.fullmatch('[0-9a-f]{64}', receipt['sha256']) and
        path.is_absolute() and path.is_file() and not path.is_symlink(),
        'Missing exact retained physical-edge trace or changed trace format')
    before = path.stat()
    require(before.st_size == 20 * edges and before.st_nlink == 1,
        'Physical-edge trace is truncated, oversized or aliased')
    hashed, count = hashlib.sha256(), 0
    with path.open('rb') as stream:
        while block := stream.read(20 * 65536):
            require(len(block) % 20 == 0, 'Truncated physical-edge trace record')
            hashed.update(block)
            for row in struct.iter_unpack('<I16B', block):
                count += 1
                require(row[0] == count, 'Physical-edge trace cycles are missing, duplicated or reordered')
    after = path.stat()
    require(not path.is_symlink() and (before.st_dev, before.st_ino, before.st_size, before.st_mtime_ns) ==
        (after.st_dev, after.st_ino, after.st_size, after.st_mtime_ns) and count == edges and
        hashed.hexdigest() == receipt['sha256'], 'Physical-edge trace bytes differ from the receipt or changed during validation')


def validate_native(result, depth, tools):
    full = Path(result.get('complete_json', ''))
    require(full.is_absolute() and full.is_file() and not full.is_symlink() and
        digest(full) == result.get('complete_sha256'), 'Complete native hierarchy bytes differ')
    directory = full.parent
    intent = result.get('native_intent', {})
    require(intent.get('schema') == 'pinwheel.streaming-mapped-native-intent.v1' and
        intent.get('depth') == depth and intent.get('vvp') == tools['vvp'] and
        intent.get('scopes') == ['UART24', 'I2C10', 'SPI32768', 'JTAG4097'] and
        read_json(directory / 'native-intent.json') == intent,
        'Native pre-use intent does not bind the selected mapped scope')
    executables = {name: directory / (name + '.vvp') for name in ('complete', 'sampler-ff-pin')}
    require(intent.get('executable_sha256') == {name: digest(path) for name, path in executables.items()} and
        intent.get('source_sha256') == {name: digest(directory / (name + '.sv')) for name in executables} and
        intent.get('model_sha256') == digest(directory / 'cells.sv'),
        'Native executable/source/Liberty-model binding changed')
    runs = result.get('native_runs', [])
    require(type(runs) is list and len(runs) == 14 and [row.get('scope') for row in runs] ==
        ['uart'] * 2 + ['legacy'] * 2 + ['i2c'] * 10, 'All14 closed native processes/depth are mandatory')
    for index, row in enumerate(runs):
        name = 'sampler-ff-pin' if index == 1 else 'complete'
        argv = [tools['vvp'], str(executables[name])]
        require(row.get('index') == index and row.get('argv') == argv and row.get('actual_argv') == argv and
            type(row.get('native_exit_code')) is int and row['native_exit_code'] == 0 and
            row.get('client_succeeded') is True and type(row.get('physical_edges')) is int and row['physical_edges'] > 0 and
            row.get('executable_sha256_before') == intent['executable_sha256'][name] and
            row.get('executable_sha256_after') == intent['executable_sha256'][name],
            'Native process lacks actual selected argv, zero exit or unchanged executable')
    journal = Path(result.get('native_journal', ''))
    require(journal == directory / 'native.jsonl' and journal.is_file() and not journal.is_symlink() and
        digest(journal) == result.get('native_journal_sha256'), 'Native journal bytes differ')
    events = [read_json_line(line) for line in journal.read_text().splitlines()]
    require(len(events) == 28, 'Each native process requires a pre-use intent and closed result')
    for index, row in enumerate(runs):
        first, last = events[index * 2:index * 2 + 2]
        require(first == dict(event='intent', **{key: row[key] for key in
            ('index', 'scope', 'argv', 'executable_sha256_before')}) and last == dict(event='result', **row),
            'Native journal does not preserve actual pre-use and closed process evidence')
    groups = (('uart', runs[:2], result['uart']['native_runs']),
        ('legacy', runs[2:4], result['legacy']['cases']), ('i2c', runs[4:], result['i2c']['cases']))
    for name, rows, cases in groups:
        require(len(rows) == len(cases) and [row['physical_edges'] for row in rows] ==
            [case.get('physical_edges') for case in cases] and
            sum(row['physical_edges'] for row in rows) == result[name]['physical_edges'],
            'Closed native edges differ from the independent protocol receipt')
        if name == 'uart':
            paths = [directory / 'uart' / filename for filename in ('unchanged.bin', 'sampler-ff-pin.bin')]
        elif name == 'legacy':
            require([case.get('protocol') for case in cases] == ['spi', 'jtag'], 'Changed legacy physical-trace identities')
            paths = [directory / 'legacy' / protocol / 'wire.bin' for protocol in ('spi', 'jtag')]
        else:
            keys = [(direction, profile) for direction in ('read', 'write')
                for profile in ('clean', 'varying', 'lastpoll', 'timeout', 'address_nack')]
            require([(case.get('direction'), case.get('profile')) for case in cases] == keys,
                'Changed I2C physical-trace identities')
            paths = [directory / 'i2c' / (direction + '-' + profile) / 'wire.bin' for direction, profile in keys]
        for path, row, case in zip(paths, rows, cases):
            validate_trace(path, case.get('trace'), row['physical_edges'])
    require(result.get('physical_edges') == sum(row['physical_edges'] for row in runs),
        'Complete mapped device native edge aggregate differs')


def validate_cost(result, depth, library, measure):
    full, selected_library = Path(result.get('complete_json', '')), Path(library)
    require(full.is_absolute() and selected_library.is_absolute() and full.is_file() and
        not full.is_symlink() and selected_library.is_file() and not selected_library.is_symlink(),
        'Cost requires exact regular complete-netlist and selected-library inputs')
    cost = result.get('cost', {})
    require(digest(full) == result.get('complete_sha256') and digest(selected_library) == LIBRARY_SHA256 and
        cost.get('input_sha256') == {str(full): result['complete_sha256'], str(selected_library): LIBRARY_SHA256} and
        read_json(full.parent / 'cost.json') == cost,
        'Retained complete cost is stale or bound to different netlist/library bytes')
    expected = measure(full, 'tt_um_pinwheel_streaming_ready_d' + str(depth), selected_library,
        6039 if depth == 2 else 6195, complete=True)
    require(expected == cost, 'Independent complete cost recomputation differs from receipt')


def validate_device(metadata, qnames, *, uart_check, i2c_check, legacy_check, native_check, cost_check):
    flags = ('complete_device_checked', 'all_native_cases_checked',
        'all_device_mutations_checked', 'all_complete_costs_checked')
    require(type(metadata) is dict and all(metadata.get(flag) is True for flag in flags) and
        metadata.get('required_qnames') == qnames and metadata.get('extra_qnames') == expected_extra_qnames() and
        metadata.get('full_state_bits') == {'2': 6039, '4': 6195} and
        set(metadata.get('depths', {})) == {'2', '4'}, 'Missing exact complete mapped device obligations')
    for depth, bits in (('2', 6039), ('4', 6195)):
        result = metadata['depths'][depth]
        cost = result.get('cost', {})
        require(cost.get('schema') == 'pinwheel.streaming-mapped-cost.v1' and
            cost.get('scope') == 'complete-tiny-tapeout' and cost.get('top') == 'tt_um_pinwheel_streaming_ready_d' + depth and
            cost.get('declared_state_bits') == bits and cost.get('physical_ff_bits') == bits and
            cost.get('inputs_unchanged') is True and cost.get('timing_qualified') is False and
            cost.get('mapped_equivalence_proved') is False and cost.get('liberty_sha256') == LIBRARY_SHA256 and
            type(cost.get('combinational_cells')) is int and cost['combinational_cells'] > 0,
            'Incomplete complete-device cost or wrong storage boundary')
        cost_check(result, int(depth))
        for name, check in (('uart', uart_check), ('i2c', i2c_check), ('legacy', legacy_check)):
            receipt = result.get(name, {})
            require(receipt.get('depth') == int(depth), 'Native diagnostic depth differs from mapped device')
            check(receipt)
        native_check(result, int(depth))
        controls = result.get('controls', [])
        require([item.get('name') for item in controls] == ['changed-pad', 'status-wire', 'changed-clock'] and
            all(item.get('passed') is True and item.get('expected_rejection') is True for item in controls),
            'Missing distinguishing mapped package/pad/clock controls')
    return True


def validate_worker(report, config, campaign, qnames, checks, cad_membership):
    require(report.get('schema') == SCHEMA and report.get('source_commit') == config['source_commit'] and
        report.get('producer_commit') == config['producer_commit'] and report.get('passed') is True and
        report.get('full_qualification') is True and report.get('required_targets') == list(TARGETS),
        'Mapped worker did not close the exact full requested scope')
    child = report.get('campaign', {})
    require(child.get('passed') is True and child.get('extra_qnames_checked') is True and campaign.acceptance(child),
        'Mapped campaign or additional first-terminal API checks are incomplete')
    validate_device(child.get('wrapper_metadata'), qnames, **checks)
    validate_cad_membership(report.get('cad_runtime_archive_membership'), cad_membership)
    validate_library_import_preflight(report.get('library_import_preflight', {}), config['worker_out'])
    require(report.get('proof_dependency_closure') and all(report.get(flag) is True for flag in
        ('selected_inputs_unchanged', 'raw_inputs_unchanged', 'tool_identity_unchanged', 'campaign_inputs_unchanged')),
        'Mapped worker provenance/positive proof closure did not close')
    command_inventory(report.get('commands'))


def worker(config_path, expected_sha256):
    selected_config = Path(config_path).read_bytes()
    require(type(expected_sha256) is str and re.fullmatch('[0-9a-f]{64}', expected_sha256) and
        hashlib.sha256(selected_config).hexdigest() == expected_sha256,
        'Mapped worker must consume the exact parent-frozen configuration bytes')
    config = decode_json(selected_config)
    snapshot, out = Path(config['snapshot']).resolve(), Path(config['worker_out']).resolve()
    require(snapshot == ROOT.resolve(), 'Mapped worker must execute from the exact selected archive')
    out.mkdir(parents=True, exist_ok=False)
    (out / 'logs').mkdir()
    raw = load('_mapped_selected_raw', snapshot / RAW_DRIVER)
    h = raw.helpers()
    raw.check_environment(h)
    orchestration = h.load_helpers(snapshot)
    commands = orchestration.Commands(snapshot, out / 'logs', default_timeout=900)
    report = dict(schema=SCHEMA, source_commit=config['source_commit'], producer_commit=config['producer_commit'],
        passed=False, full_qualification=False, boundary=BOUNDARY, required_targets=list(TARGETS), commands=commands.records)
    intents = (out / 'command-intents.jsonl').open('x', buffering=1)
    started, failure = time.monotonic(), None

    def run(argv, label, **options):
        intents.write(json.dumps(dict(index=len(commands.records), label=label, argv=list(map(str, argv)))) + '\n')
        h.write_json(out / 'worker-report.json', report)
        return commands(argv, label, **options)

    try:
        require(h.membership(snapshot, config['source_tree'], config['object_format']) == config['source_sha256'],
            'Selected mapped source changed before execution')
        verify_files(config['raw_frozen_sha256'])
        manifest = read_json(snapshot / 'tools/hardware-toolchain.json')
        tools = config['tool_paths']
        require(raw.tool_identity(h, tools, manifest) == config['tool_identity'], 'Mapped tool/runtime changed before execution')
        sys.path.insert(0, str(snapshot / 'scripts'))
        from streaming_mapped_campaign import run_campaign
        import streaming_mapped_campaign as campaign
        from streaming_mapped_component import generate_component
        from streaming_mapped_device import wrapper_hook
        from streaming_mapped_runtime import audit as audit_runtime
        from streaming_mapped_simulation import check_uart_cases
        from streaming_mapped_cost import measure
        from streaming_ready_wire_cases import check_i2c_cases
        from streaming_uart_legacy_cases import check_legacy_cases
        cad_membership = audit_runtime(config['tool_identity'], manifest, tools)
        validate_cad_membership(cad_membership, cad_membership)
        report['cad_runtime_archive_membership'] = cad_membership
        # This .lake belongs only to the freshly archived raw stage. Build all
        # project library before campaign intake freezes its products. Narrow
        # UART roots omit other session-factory imports such as WarmReset.
        run([tools['lake'], 'build', *BUILD_ROOTS], 'fresh-mapped-library-build', timeout=3600)
        report['library_import_preflight'] = library_import_preflight(out, tools, run)
        run([tools['lake'], 'env', tools['lean'], '-DwarningAsError=true',
            'test/StreamingUARTFirstTerminal.lean'], 'uart-first-terminal-shape-and-audit', timeout=900)
        mapped_config = dict(root=str(snapshot), library=config['library']['staged'], tools=tools,
            components=config['components'], device=config['device'], build=False,
            source_commit=config['source_commit'], timeout=config['command_timeout'],
            source_files=[str(snapshot / path) for path in required_inputs(config['source_tree'])])
        child = run_campaign(out / 'campaign', mapped_config, run=run,
            component_generator=generate_component, wrapper_hook=wrapper_hook)
        report['campaign'] = child
        proof_gate = load('_mapped_selected_closure', snapshot / 'scripts/check-buffered-rtl-session.py')
        directories = [out / 'campaign' / label / 'proof' for label in LABELS] + [out / 'campaign/wrapper']
        generated = {}
        for directory in directories:
            for path in directory.glob('*.lean'):
                require(path.name not in generated, 'Ambiguous positive generated mapped module')
                generated[path.name] = digest(path)
        report['proof_dependency_closure'] = proof_gate.proof_closure(snapshot, directories,
            ['StreamingMappedRequiredTargets'], config['source_sha256'], generated)
        checks = dict(uart_check=check_uart_cases, i2c_check=check_i2c_cases, legacy_check=check_legacy_cases,
            native_check=lambda result, depth: validate_native(result, depth, tools),
            cost_check=lambda result, depth: validate_cost(result, depth, config['library']['staged'], measure))
        report.update(passed=True, full_qualification=True)
    except BaseException as error:
        failure = error
        report.update(passed=False, full_qualification=False, error=type(error).__name__ + ': ' + str(error))
    finally:
        try:
            require(h.membership(snapshot, config['source_tree'], config['object_format']) == config['source_sha256'],
                'Selected mapped source changed during execution')
            verify_files(config['raw_frozen_sha256'])
            require(raw.tool_identity(h, config['tool_paths'], read_json(snapshot / 'tools/hardware-toolchain.json')) ==
                config['tool_identity'], 'Mapped tool/runtime changed during execution')
            if 'campaign' in report:
                verify_files(report['campaign']['frozen_sha256'])
                report['campaign_inputs_unchanged'] = True
            report.update(selected_inputs_unchanged=True, raw_inputs_unchanged=True, tool_identity_unchanged=True)
            if report['passed']:
                validate_worker(report, config, campaign, expected_qnames(raw), checks, cad_membership)
        except BaseException as error:
            report.update(passed=False, full_qualification=False, closeout_error=type(error).__name__ + ': ' + str(error))
        intents.close()
        report['elapsed_seconds'] = round(time.monotonic() - started, 3)
        report['artifact_sha256'] = regular_inventory(out, omit=('worker-report.json',))
        h.write_json(out / 'worker-report.json', report)
    if failure: raise failure
    require(report['passed'], 'Mapped worker closeout refused acceptance')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--tag')
    parser.add_argument('--source-commit', default='HEAD')
    parser.add_argument('--producer-commit', default='HEAD')
    parser.add_argument('--circt', default=str(ROOT / 'build/tools/firtool-1.159.0/bin/circt-opt'))
    for name, program in [('yosys', 'yosys'), ('abc', 'yosys-abc'), ('solver', 'z3'), ('iverilog', 'iverilog'), ('vvp', 'vvp')]:
        parser.add_argument('--' + name, default=str(ROOT / 'build/tools/oss-cad-suite/bin' / program))
    parser.add_argument('--liberty', required=False)
    parser.add_argument('--timeout-seconds', type=int, default=21600)
    parser.add_argument('--worker-config', help=argparse.SUPPRESS)
    parser.add_argument('--worker-config-sha256', help=argparse.SUPPRESS)
    args = parser.parse_args()
    if args.worker_config:
        worker(args.worker_config, args.worker_config_sha256)
        return
    if (not args.tag or not re.fullmatch('[A-Za-z0-9_-]+', args.tag) or not 1 <= args.timeout_seconds <= 43200 or
            not args.liberty or any(not Path(getattr(args, name)).is_absolute() for name in
                ('circt', 'yosys', 'abc', 'solver', 'iverilog', 'vvp', 'liberty'))):
        parser.error('Use a fresh --tag, absolute tools/--liberty, and timeout1..43200')
    raw = load('_mapped_live_raw', ROOT / RAW_DRIVER)
    h = raw.helpers()
    raw.check_environment(h)
    git = lambda *items: subprocess.check_output(['git', *items], cwd=ROOT, text=True, timeout=30)
    commit = git('rev-parse', '--verify', args.source_commit + '^{commit}').strip()
    producer_commit = git('rev-parse', '--verify', args.producer_commit + '^{commit}').strip()
    require(commit == producer_commit, 'Mapped selected source and producer must be the same commit')
    algorithm = git('rev-parse', '--show-object-format').strip()
    tree = h.parse_tree(git('ls-tree', '-r', '-z', commit))
    producer_tree = producer_inputs(ROOT, tree)
    producer_hashes = h.membership(ROOT, producer_tree, algorithm)
    orchestration = h.load_helpers(ROOT)
    out = orchestration.fresh_directory(ROOT / 'build/validation', args.tag)
    raw_out = ROOT / 'build/validation' / (args.tag + '-raw')
    require(not raw_out.exists(), 'Fresh raw input-stage tag already exists')
    (out / 'logs').mkdir()
    run = orchestration.Commands(ROOT, out / 'logs', default_timeout=60)
    report = dict(schema=SCHEMA, source_commit=commit, producer_commit=commit, passed=False, full_qualification=False,
        boundary=BOUNDARY, required_targets=list(TARGETS), started_utc=datetime.now(timezone.utc).isoformat(),
        commands=run.records, producer_sha256=producer_hashes,
        membership_scope='Same-commit complete fresh Git archive from the newly executed raw input stage. '
            'Working dirty documentation is not consumed. All mapped helpers/tests/Lean source are committed producer inputs.')
    started, failure, snapshot, hashes, before, library = time.monotonic(), None, None, None, None, None
    frozen = {}
    try:
        archive = out / 'producer-source.tar'
        run(['git', 'archive', '--format=tar', '--output', archive, commit, '--', *producer_tree], 'mapped-producer-archive')
        report['producer_archive_sha256'] = digest(archive)
        producer = out / 'producer'; producer.mkdir()
        with tarfile.open(archive) as bundle: bundle.extractall(producer, filter='data')
        h.fresh_snapshot(producer)
        require(h.membership(producer, producer_tree, algorithm) == producer_hashes, 'Mapped producer archive differs from Git')
        proxy = shutil.which('lake')
        require(proxy, 'Native Lean/Lake must be installed')
        report['discovery_lake_proxy'] = dict(path=proxy, sha256=digest(proxy))
        prefix = Path(run([proxy, 'env', 'lean', '--print-prefix'], 'native-toolchain-prefix').strip())
        tools = {name: getattr(args, name) for name in ('circt', 'yosys', 'abc', 'solver', 'iverilog', 'vvp')}
        tools.update(lean=str(prefix / 'bin/lean'), lake=str(prefix / 'bin/lake'), python=str(Path(sys.executable).resolve()))
        manifest = read_json(producer / 'tools/hardware-toolchain.json')
        before = raw.tool_identity(h, tools, manifest)
        report.update(tool_paths=tools, tool_identity_before=before)
        lock = read_json(producer / 'tools/technology-library.json')
        require(any(item.get('name') == 'sg13cmos5l_stdcell_typ_1p20V_25C.lib' and item.get('sha256') == LIBRARY_SHA256
            for item in lock['files']) and digest(args.liberty) == LIBRARY_SHA256, 'Use the exact committed typical Liberty pin')
        (out / 'inputs').mkdir()
        staged = out / 'inputs/cells.lib'; staged.write_bytes(Path(args.liberty).read_bytes())
        require(digest(staged) == LIBRARY_SHA256, 'Staged Liberty differs from its pin')
        library = dict(original=str(Path(args.liberty)), staged=str(staged), sha256=LIBRARY_SHA256)
        report['library'] = library
        argv = [tools['python'], '-B', ROOT / RAW_DRIVER, '--tag', args.tag + '-raw', '--stage', 'components',
            '--source-commit', commit, '--producer-commit', commit, '--timeout-seconds', str(args.timeout_seconds)]
        for name in ('circt', 'yosys', 'abc', 'solver', 'iverilog', 'vvp'): argv += ['--' + name, tools[name]]
        run(argv, 'fresh-raw-components', timeout=args.timeout_seconds)
        raw_report_path, raw_config_path = raw_out / 'report.json', raw_out / 'worker-config.json'
        raw_report, raw_config = read_json(raw_report_path), read_json(raw_config_path)
        snapshot = (raw_out / 'selected').resolve()
        require(Path(raw_config['snapshot']).resolve() == snapshot and Path(raw_config['worker_out']).resolve() ==
            (raw_out / 'worker').resolve(), 'Fresh raw stage escaped its selected output directory')
        hashes = h.membership(snapshot, tree, algorithm)
        child = validate_raw(raw_report, raw_config, raw, commit, tree, hashes, h)
        require(raw_report.get('tool_paths') == tools and raw_report.get('tool_identity_before') == before and
            raw_report.get('tool_identity_after') == before, 'Raw stage selected a different tool/runtime')
        frozen = {str(raw_out / 'worker' / relative): value for relative, value in
            regular_inventory(raw_out / 'worker').items()}
        for path in (raw_report_path, raw_config_path, raw_out / 'selected-source.tar', raw_out / 'producer-source.tar', staged):
            frozen[str(path)] = digest(path)
        report.update(raw_stage=dict(report=str(raw_report_path), sha256=digest(raw_report_path), partial_input_only=True),
            raw_frozen_sha256=frozen, source_sha256=hashes, selected_git_objects=tree,
            committed_archive_membership_verified_before=True)
        device = {str(depth): {name: str(raw_out / 'worker/actual-wrappers' / ('d' + str(depth)) / filename)
            for name, filename in (('tiny', 'tt.sv'), ('package', 'package.sv'), ('bridge', 'bridge.sv'))} for depth in (2, 4)}
        config = dict(snapshot=str(snapshot), worker_out=str(out / 'worker'), source_commit=commit, producer_commit=commit,
            source_tree=tree, source_sha256=hashes, object_format=algorithm, tool_paths=tools, tool_identity=before,
            library=library, components=component_config(raw_out, child), device=device, raw_frozen_sha256=frozen,
            command_timeout=min(args.timeout_seconds, 3600))
        path = out / 'worker-config.json'; h.write_json(path, config)
        config_hash = digest(path)
        report['worker_config_sha256_before_use'] = config_hash
        h.write_json(out / 'report.json', report)
        run([tools['python'], '-B', snapshot / DRIVER, '--worker-config', path, '--worker-config-sha256', config_hash],
            'fresh-mapped-worker', timeout=args.timeout_seconds)
        require(digest(path) == config_hash, 'Mapped worker configuration changed during use')
        worker_path = out / 'worker/worker-report.json'; result = read_json(worker_path)
        sys.path.insert(0, str(snapshot / 'scripts'))
        import streaming_mapped_campaign as campaign
        from streaming_mapped_simulation import check_uart_cases
        from streaming_mapped_runtime import audit as audit_runtime
        from streaming_mapped_cost import measure
        from streaming_ready_wire_cases import check_i2c_cases
        from streaming_uart_legacy_cases import check_legacy_cases
        cad_membership = audit_runtime(before, manifest, tools)
        validate_worker(result, config, campaign, expected_qnames(raw),
            dict(uart_check=check_uart_cases, i2c_check=check_i2c_cases, legacy_check=check_legacy_cases,
                native_check=lambda result, depth: validate_native(result, depth, tools),
                cost_check=lambda result, depth: validate_cost(result, depth, library['staged'], measure)), cad_membership)
        require(result.get('artifact_sha256') == regular_inventory(out / 'worker', omit=('worker-report.json',)),
            'Mapped retained artifact bytes differ from worker receipt')
        verify_journal(out / 'worker', result['commands'])
        report.update(worker=result, worker_report_sha256=digest(worker_path),
            cad_runtime_archive_membership=cad_membership, passed=True, full_qualification=True)
    except BaseException as error:
        failure = error
        report.update(error=type(error).__name__ + ': ' + str(error), passed=False, full_qualification=False)
    finally:
        try:
            require(h.membership(ROOT, producer_tree, algorithm) == producer_hashes, 'Mapped working producer changed after intake')
            if 'producer_archive_sha256' in report:
                require(digest(out / 'producer-source.tar') == report['producer_archive_sha256'], 'Mapped producer archive changed')
                require(h.membership(out / 'producer', producer_tree, algorithm) == producer_hashes, 'Mapped retained producer changed')
            if snapshot is not None:
                require(h.membership(snapshot, tree, algorithm) == hashes, 'Selected committed mapped inputs changed')
            if frozen: verify_files(frozen)
            if before is not None:
                after = raw.tool_identity(h, report['tool_paths'], manifest)
                require(after == before, 'Mapped native tool/runtime changed after intake')
                report.update(tool_identity_after=after, tool_identity_unchanged=True)
            if 'discovery_lake_proxy' in report:
                selected_proxy = report['discovery_lake_proxy']
                require(digest(selected_proxy['path']) == selected_proxy['sha256'], 'Lake discovery proxy changed after use')
            if library is not None:
                require(all(digest(library[key]) == LIBRARY_SHA256 for key in ('original', 'staged')), 'Liberty changed during validation')
                report['library_unchanged'] = True
            command_inventory(report['commands'])
            report['committed_archive_membership_verified_after'] = True
        except BaseException as error:
            report.update(passed=False, full_qualification=False, closeout_error=type(error).__name__ + ': ' + str(error))
        report['elapsed_seconds'] = round(time.monotonic() - started, 3)
        h.write_json(out / 'report.json', report)
    if failure: raise failure
    require(report['passed'], 'Mapped full closeout refused acceptance')
    print('Streaming mapped full receipt: ' + str(out / 'report.json'), flush=True)


if __name__ == '__main__': main()
