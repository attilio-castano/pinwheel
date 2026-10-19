#!/usr/bin/env python3
"""Export compact streaming receipts after independent immutable-input checks.

No gate is rerun. The accepted full, foundation and Python receipts must share
one source commit. Run only from a commit containing this exporter and tests.
Large RTL, native and proof artifact trees remain at their retained locations.
"""
import argparse
import ast
from datetime import datetime, timezone
import gzip
import hashlib
import importlib.util
import json
from pathlib import Path, PurePosixPath
import re
import subprocess
import sys
import time
import types

ROOT = Path(__file__).resolve().parents[1]
DRIVER = 'scripts/export-streaming-evidence.py'
HELPER = 'scripts/export-rtl-session-evidence.py'
PRODUCER = (DRIVER, HELPER, 'scripts/process_group.py', 'scripts/validation_run.py',
    'test/test_streaming_evidence.py')
BASE = '31816bb86aa5154c2671a8d479650c7b063d93aa'
DESTINATION = 'docs/research/evidence/streaming-continuation-20261017'
DOCS = {
    'docs/protocols/buffered-spi-refinement.md': '805eba24279d4dd798c49f92aaaa146005475f9496cafdf393d9f5140aa66d59',
    'docs/research/status.md': 'c669c35bf690df6c370da43dc6d2cfa6fa96fb3e56be0e9bd2d741a39fb198fe'}
PATCH = 'efb3443f8103705eaeb222847c21750cdeeee5b0bde2ec0c3dea6d6eddef1108'
MIN_JOIN_APIS = ('components_correct', 'physical_step_correct', 'physical_observe_correct',
    'physical_run_correct', 'source_runtime_step_correct', 'source_runtime_run_correct',
    'source_runtime_observe_correct', 'initialized_upload_correct', 'initialized_runtime_correct',
    'physical_warm_reset_correct', 'concrete_spi_initialized', 'concrete_jtag_initialized',
    'concrete_spi_runtime', 'concrete_jtag_runtime', 'concrete_spi_custody', 'concrete_jtag_custody',
    'concrete_spi_progress', 'concrete_jtag_progress')


def require(value, message):
    if not value: raise RuntimeError(message)


def sha(data): return hashlib.sha256(data).hexdigest()


def digest(path):
    value = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b''): value.update(block)
    return value.hexdigest()


def unique_pairs(items):
    result = {}
    for key, value in items:
        require(key not in result, 'Duplicate JSON key: ' + key)
        result[key] = value
    return result


def read_json(data): return json.loads(data, object_pairs_hook=unique_pairs)


def write_json(path, value): path.write_text(json.dumps(value, indent=2, sort_keys=True) + '\n')


def safe_relative(name):
    require(type(name) is str and name and not any(char in name for char in ('\0', '\n', '\r')),
        'Unsafe retained relative path')
    path = PurePosixPath(name)
    require(not path.is_absolute() and '..' not in path.parts and '.' not in path.parts,
        'Unsafe retained relative path')
    return path


def regular(path, root):
    path, root = Path(path), Path(root)
    require(path.is_file() and not path.is_symlink() and path.resolve().is_relative_to(root.resolve()),
        'Missing or redirected retained file: ' + str(path))
    return path


def inventory(root):
    root = Path(root)
    result = {}
    for path in sorted(root.rglob('*')):
        require(not path.is_symlink() and path.resolve().is_relative_to(root.resolve()),
            'Redirected retained artifact')
        if path.is_file(): result[str(path.relative_to(root))] = digest(path)
    return result


def same_source(reports):
    require(set(reports) == {'full', 'foundation', 'python'}, 'All three accepted gates are mandatory')
    require(all(type(value) is dict and type(value.get('source_commit')) is str for value in reports.values()),
        'Missing final source commit identity')
    commits = {value.get('source_commit') for value in reports.values()}
    require(len(commits) == 1, 'Accepted receipts use different final source commits')
    commit = next(iter(commits))
    require(type(commit) is str and re.fullmatch(r'[0-9a-f]{40}|[0-9a-f]{64}', commit),
        'Require one full source commit identity')
    require(all(value.get('passed') is True for value in reports.values()), 'An accepted gate failed')
    return commit


def foundation_parts(source):
    tree, values = ast.parse(source), {}
    for node in tree.body:
        if isinstance(node, ast.Assign):
            for target in node.targets:
                if isinstance(target, ast.Name) and target.id in ('SUITES', 'KERNEL_SUITES'):
                    require(target.id not in values, 'Duplicate foundation suite assignment')
                    values[target.id] = ast.literal_eval(node.value)
                    node.value = ast.Constant('__allowed_' + target.id)
    boundaries = [keyword for node in ast.walk(tree) if isinstance(node, ast.Call) and
        isinstance(node.func, ast.Name) and node.func.id == 'dict' for keyword in node.keywords
        if keyword.arg == 'boundary']
    require(set(values) == {'SUITES', 'KERNEL_SUITES'} and len(boundaries) == 1,
        'Unsupported foundation suites or boundary layout')
    values['boundary'] = ast.literal_eval(boundaries[0].value)
    boundaries[0].value = ast.Constant('__allowed_boundary')
    return values, ast.dump(tree, include_attributes=False)


def additive_foundation(before, after):
    old, old_ast = foundation_parts(before)
    new, new_ast = foundation_parts(after)
    require(old_ast == new_ast, 'Foundation changes exceed suite and boundary additions')
    for name in ('SUITES', 'KERNEL_SUITES'):
        added = new[name][len(old[name]):]
        require(new[name][:len(old[name])] == old[name] and
            len({repr(value) for value in new[name]}) == len(new[name]) and
            all((value[0] if name == 'SUITES' else value).startswith('Streaming') for value in added),
            'Foundation suites are not additive Streaming contracts')
    prefix, marker, tail = old['boundary'].partition('. Does not ')
    require(marker and (new['boundary'] == old['boundary'] or
        new['boundary'].startswith(prefix + '; ') and new['boundary'].endswith(marker + tail) and
        'streaming' in new['boundary'][len(prefix):-len(marker + tail)].lower()),
        'Foundation boundary removed an existing claim or exclusion')
    return dict(added_suites=new['SUITES'][len(old['SUITES']):],
        added_kernel_suites=new['KERNEL_SUITES'][len(old['KERNEL_SUITES']):], boundary_preserved=True)


def additive_imports(before, after):
    old, index, added = before.splitlines(), 0, []
    for line in after.splitlines():
        if index < len(old) and line == old[index]: index += 1
        else:
            require(re.fullmatch(r'import Pinwheel\.(?:Program|Hardware)\.Streaming[A-Za-z0-9_.]*', line),
                'Default imports changed beyond additive Streaming modules')
            added.append(line)
    require(index == len(old) and len(added) == len(set(added)), 'Default imports removed or duplicated')
    return added


def preserve_base(base, current):
    for name, data in base.items():
        if name not in ('Pinwheel.lean', 'scripts/check-foundation.py'):
            require(current.get(name) == data, 'Frozen baseline file changed: ' + name)
    return dict(base=BASE, baseline_files=len(base),
        added_imports=additive_imports(base['Pinwheel.lean'].decode(), current['Pinwheel.lean'].decode()),
        foundation=additive_foundation(base['scripts/check-foundation.py'].decode(),
            current['scripts/check-foundation.py'].decode()))


def foundation_labels(source):
    values, _ = foundation_parts(source)
    expected = [('version', False), ('build', False), ('axioms', False), ('reject-untrusted-axiom', True)]
    expected += [(name + '-kernel', False) for name in values['KERNEL_SUITES']]
    for name, flags in values['SUITES']:
        expected.append((name + (('-' + flags[0].removeprefix('--')) if flags else ''), False))
        if name == 'Binary': expected.append(('independent-binary', False))
        if name == 'UARTRx': expected.append(('independent-uart-rx', False))
    return expected


def check_foundation(report, source):
    expected, actual = foundation_labels(source), report.get('commands', [])
    require([value.get('label') for value in actual] == [label for label, _ in expected],
        'Foundation command inventory/order differs from the selected committed suites')
    for value, (_, rejected) in zip(actual, expected):
        code = value.get('exit_code')
        require(type(code) is int and (code != 0) is rejected, 'Foundation command outcome differs')
    return len(expected)


def check_journal(intents, commands, log_read):
    require(len(intents) == len(commands) and len({row.get('label') for row in commands}) == len(commands),
        'Command journal length or labels differ')
    for index, (intent, record) in enumerate(zip(intents, commands)):
        reject = intent.get('options', {}).get('reject')
        require(type(intent.get('index')) is int and intent['index'] == index and intent.get('argv') == record.get('argv') and
            intent.get('label') == record.get('label') and
            record.get('expected_failure') is bool(reject) and not record.get('error') and
            type(record.get('exit_code')) is int and (record['exit_code'] != 0) == bool(reject),
            'Pre-use command intent differs from its native outcome')
        if reject: require(reject in log_read(record['label']), 'Native control rejected for the wrong reason')


def freeze_journal(entries, expected, actual):
    combined = {}
    for entry in entries:
        require(type(entry) is dict, 'Malformed input-freeze record')
        for path, value in entry.items():
            safe_relative(path)
            require(path not in combined or combined[path] == value, 'Frozen input changed between uses')
            combined[path] = value
    require(combined == expected and all(actual.get(path) == value for path, value in combined.items()),
        'Input-freeze journal, receipt and retained artifacts differ')
    return len(combined)


def bootstrap(out):
    records = []
    def call(argv, label):
        started = time.monotonic()
        value = subprocess.run(argv, cwd=ROOT, capture_output=True, timeout=30)
        (out / (label + '.log')).write_bytes(value.stdout + value.stderr)
        records.append(dict(label=label, argv=list(map(str, argv)), exit_code=value.returncode,
            seconds=round(time.monotonic() - started, 3)))
        require(value.returncode == 0, 'Exporter bootstrap failed: ' + label)
        return value.stdout
    head = call(['git', 'rev-parse', 'HEAD'], 'export-head').decode().strip()
    payloads = {}
    for index, name in enumerate(PRODUCER):
        data = call(['git', 'show', head + ':' + name], 'export-producer-' + str(index))
        require(regular(ROOT / name, ROOT).read_bytes() == data, 'Commit exporter/helper/test first: ' + name)
        payloads[name] = data
    for name in ('process_group', 'validation_run', '_streaming_export_git_helpers'):
        relative = HELPER if name.startswith('_') else 'scripts/' + name + '.py'
        module = types.ModuleType(name)
        module.__file__ = str(ROOT / relative)
        sys.modules[name] = module
        exec(compile(payloads[relative], module.__file__, 'exec'), module.__dict__)
    return head, {name: sha(data) for name, data in payloads.items()}, records


def load_module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def source_objects(run, commit, mapping, reported=None):
    require(type(mapping) is dict and mapping, 'Missing selected input map')
    if commit not in source_objects.cached:
        text = run(['git', 'ls-tree', '-r', '-z', commit], 'objects-' + commit)
        values = {}
        for entry in text.split('\0'):
            if not entry: continue
            metadata, name = entry.split('\t', 1)
            mode, kind, oid = metadata.split()
            safe_relative(name)
            require(name not in values and kind == 'blob' and mode in ('100644', '100755'),
                'Nonregular or ambiguous committed evidence input')
            values[name] = oid
        source_objects.cached[commit] = values
    values = source_objects.cached[commit]
    selected = {name: values[name] for name in mapping if name in values}
    require(set(selected) == set(mapping) and (reported is None or selected == reported),
        'Recorded Git blob inventory differs from selected source')
    return selected


source_objects.cached = {}


def checked_map(root, mapping, frozen):
    require(type(mapping) is dict and mapping, 'Missing retained artifact map')
    for relative, expected in mapping.items():
        path = regular(Path(root) / str(safe_relative(relative)), root)
        require(re.fullmatch(r'[0-9a-f]{64}', expected or '') and digest(path) == expected,
            'Retained artifact changed: ' + str(path))
        frozen[path] = expected


def checked_path(path, roots, frozen, expected):
    path = Path(path)
    require(path.is_absolute() and any(path.resolve().is_relative_to(Path(root).resolve()) for root in roots),
        'Reported input escapes retained source/artifact roots')
    root = next(root for root in roots if path.resolve().is_relative_to(Path(root).resolve()))
    regular(path, root)
    require(digest(path) == expected, 'Reported input differs from retained bytes')
    frozen[path] = expected


def retained_archive(directory, name, expected, frozen):
    path = regular(Path(directory) / name, directory)
    require(digest(path) == expected, 'Retained archive differs from reproduced Git archive')
    frozen[path] = expected


def foundation_evidence(report, files, directory, frozen):
    source = files['scripts/check-foundation.py'].decode()
    count = check_foundation(report, source)
    lists = [node.value.generators[0].iter for node in ast.walk(ast.parse(source))
        if isinstance(node, ast.Assign) and any(isinstance(target, ast.Name) and target.id == 'sources'
            for target in node.targets) and isinstance(node.value, ast.ListComp)]
    require(len(lists) == 1, 'Unsupported foundation source inventory')
    expected = set(ast.literal_eval(lists[0])) | {name for name in files
        if name.startswith('Pinwheel/') and name.endswith('.lean') or
            re.fullmatch(r'test/[^/]+\.lean', name)}
    require(set(report['source_sha256']) == expected, 'Foundation source coverage differs from committed inventory')
    require(report['modules'] == 1 + sum(name.startswith('Pinwheel/') and name.endswith('.lean') for name in files),
        'Foundation module census differs from committed library')
    logs = {}
    for label, rejected in foundation_labels(source):
        path = regular(Path(directory) / (label + '.log'), directory)
        logs[label] = path.read_text()
        frozen[path] = digest(path)
        if rejected: require('Unapproved axioms in Pinwheel.CI.untrusted' in logs[label],
            'Foundation axiom mutation rejected for the wrong reason')
    audit = re.findall(r'Pinwheel audit: (\d+) declarations, (\d+) theorems; standard axioms only\.', logs['axioms'])
    require(audit == [(str(report['audited_declarations']), str(report['audited_theorems']))],
        'Foundation audit counts differ from actual native log')
    return dict(commands_verified=count, source_files=len(expected), native_audit_verified=True)


def check_python_retained(report, directory, frozen, producer_files):
    actual = inventory(directory)
    actual.pop('report.json', None)
    require(actual == report.get('artifact_sha256'), 'Python retained artifact inventory differs')
    checked_map(directory, actual, frozen)
    summary_module = types.ModuleType('_accepted_python_summary')
    # Extract only the committed pure summary function; no producer command is run.
    tree = ast.parse(producer_files['scripts/check-python-snapshot.py'])
    functions = [node for node in tree.body if isinstance(node, ast.FunctionDef) and node.name == 'test_summary']
    require(len(functions) == 1, 'Missing Python native-summary contract')
    summary_module.__dict__['re'] = re
    exec(compile(ast.Module(body=functions, type_ignores=[]), '<committed test_summary>', 'exec'), summary_module.__dict__)
    log = regular(Path(directory) / 'logs/python-unittest-discover.log', directory).read_text()
    require(summary_module.test_summary(log) == report.get('unittest'), 'Python counts/skips differ from actual discovery log')
    return dict(retained_artifacts=len(actual), native_summary_verified=True)


def actual_bindings(worker, artifacts, root):
    wire = worker['stages']['public-wire']['result']
    raw, cost = worker['stages']['raw-components']['result'], worker['stages']['matched-cost']['result']
    expected_cost = {}
    for depth in (2, 4):
        source_paths = [f'raw/core-d{depth}/core.sv', 'raw/frontend/frontend.sv',
            f'actual-wrappers/d{depth}/package.sv', f'actual-wrappers/d{depth}/tt.sv',
            f'actual-wrappers/d{depth}/bridge.sv']
        require(wire.get('source_binding', {}).get(str(depth)) == {name: artifacts[name] for name in source_paths},
            'Raw-certified/wire source binding differs')
        pairs = dict(zip(('core.sv', 'frontend.sv', 'package.sv', 'tt.sv'), source_paths[:4]))
        pairs.update({name: f'emitted/d{depth}/' + name for name in ('core.mlir', 'frontend.mlir')})
        for name, certified in pairs.items():
            path = f'cost/emitted/d{depth}/' + name
            require(artifacts.get(path) == artifacts.get(certified), 'Mapped row changed its raw-certified input')
            expected_cost[path] = artifacts[certified]
    require(cost.get('raw_certified_input_binding') == expected_cost, 'Cost raw binding is incomplete or self-relabelled')
    for name, stem in [('frontend', 'frontend'), ('core-d2', 'core'), ('core-d4', 'core')]:
        component = raw[name]
        require(component.get('proof_input_sha256_before', {}).get(stem + '.sv') ==
            artifacts.get('raw/' + name + '/' + stem + '.sv'), 'Raw proof did not consume the simulated SV')
    return dict(two_depth_wire_inputs=10, raw_cost_equalities=len(expected_cost), independently_verified=True)


def full_contract(report):
    require(report.get('schema') == 'pinwheel.streaming-continuation.v1' and report.get('stage') == 'full' and
        report.get('full_qualification') is True and all(report.get(name) is True for name in
            ('committed_archive_membership_verified_before', 'committed_archive_membership_verified_after',
                'tool_identity_unchanged', 'library_unchanged')) and not report.get('error') and
        not report.get('closeout_error'), 'Full gate did not close its complete immutable-input contract')
    for kind in ('tool', 'library'):
        require(report.get(kind + '_identity_before') and
            report[kind + '_identity_before'] == report.get(kind + '_identity_after'),
            'Full gate identity closeout differs: ' + kind)
    require(report['library_identity_before'].get('sha256') ==
        '34163f3e7de9f854afac57332ba06f1739b78e7ac35660a8a5ddd39c570124ad', 'Wrong matched Liberty pin')


def check_join_apis(names):
    require(type(names) in (list, tuple) and len(names) == len(set(names)) and
        all(type(name) is str and re.fullmatch(r'[a-z_][a-z0-9_]*', name) for name in names) and
        set(MIN_JOIN_APIS) <= set(names), 'Producer omits required initialized source/wire/custody/progress APIs')


def proof_closures(driver, gate, worker, root, selected, committed):
    directories, counts = [], {}
    raw = worker['stages']['raw-components']['result']
    for name, value in raw.items():
        target, positive = root / 'raw' / name, root / 'raw' / name / 'proof'
        require(driver.generated_closure(gate, selected, [positive], [value['compiled_modules'][-1]], committed) ==
            value['positive_proof_closure'], 'Raw positive dependency closure differs')
        for control in value['mutations']:
            directory = Path(control['proof_directory'])
            require(directory.resolve().is_relative_to((target / 'controls').resolve()), 'Raw control path substitution')
            require(driver.generated_closure(gate, selected, [directory, positive], control['modules'], committed) ==
                value['control_proof_closures'][control['name']], 'Raw mutation dependency closure differs')
        require(driver.generated_closure(gate, selected, [positive], value['private_control_modules'], committed) ==
            value['private_control_proof_closure'], 'Raw private-axiom dependency closure differs')
        counts[name] = len(value['positive_proof_closure'])
        directories.append(positive)
    for depth, value in worker['stages']['actual-wrappers']['result'].items():
        target = root / 'wrapper-proofs' / ('d' + depth)
        positive = target / 'unchanged'
        require(Path(value['proof_directory']).resolve() == positive.resolve(), 'Wrapper positive path substitution')
        for label, name in [('package', 'package.sv'), ('tiny', 'tt.sv')]:
            require(digest(positive / (label + '.sv')) == digest(root / 'actual-wrappers' / ('d' + depth) / name),
                'Positive wrapper certificate changed actual source')
        for control in value['mutations']:
            directory = Path(control['proof_directory'])
            require(directory.resolve().is_relative_to(target.resolve()), 'Wrapper control path substitution')
            require(driver.generated_closure(gate, selected, [directory], [control['module']], committed) ==
                value['control_proof_closures'][control['name']], 'Wrapper dependency closure differs')
        directories.append(positive)
    directories.append(root / 'composition')
    join = worker['stages']['composition-and-audit']['result']
    closure = driver.generated_closure(gate, selected, directories, ['StreamingRequiredTargets'], committed)
    require(closure == join['proof_dependency_closure'], 'Final positive proof dependency closure differs')
    return dict(raw_positive_modules=counts, final_modules=len(closure),
        isolated_negative_closures_verified=True)


def wire_operations(worker, config, root):
    expected = []
    definitions = [('spi', 32768, None), ('jtag', 4097, None), ('spi', 0, None),
        ('spi', 8, 'request_close'), ('spi', 8, 'request_crc'), ('spi', 8, 'response_crc'), ('spi', 8, 'partial_read')]
    for depth in (2, 4):
        executable = str(root / 'wire' / ('d' + str(depth)) / 'chip.vvp')
        argv = [config['tool_paths']['vvp'], executable]
        expected += [dict(api='streaming_wire_cases.run_stream', argv=argv, depth=depth,
            protocol=protocol, bits=bits, fault=fault) for protocol, bits, fault in definitions]
        expected += [dict(api=api, argv=argv, depth=depth) for api in ('streaming_wire_cases.run_custody',
            'streaming_adversarial.run_adversarial', 'streaming_staging_race.run_races')]
        sources = [root / ('raw/core-d' + str(depth) + '/core.sv'), root / 'raw/frontend/frontend.sv',
            *(root / 'actual-wrappers' / ('d' + str(depth)) / name for name in ('package.sv', 'tt.sv', 'bridge.sv'))]
        command = next((row for row in worker['commands'] if row.get('label') == 'wire-compile-d' + str(depth)), {})
        require(command.get('argv') == [config['tool_paths']['iverilog'], '-g2012', '-s',
            'streaming_quad_host_bridge', '-o', executable, *map(str, sources)],
            'Wire simulator did not compile the exact certified component/package sources')
    actual = [{key: value for key, value in row.items() if key != 'note'} for row in worker.get('operations', [])]
    require(actual == expected, 'Physical simulator operation inventory or executable differs')
    return len(expected)


def full_retained(report, directory, source_files, frozen):
    root, worker = directory / 'worker', report['worker']
    config_path = regular(directory / 'worker-config.json', directory)
    require(digest(config_path) == report.get('worker_config_sha256_before_use'), 'Worker configuration changed')
    config = read_json(config_path.read_bytes())
    require(config.get('stage') == 'full' and config.get('source_commit') == report['source_commit'] and
        config.get('producer_commit') == report['producer_commit'] and
        config.get('source_sha256') == report['source_sha256'] and
        config.get('producer_sha256') == report['producer_sha256'] and
        config.get('tool_paths') == report.get('tool_paths') and
        config.get('tool_identity') == report.get('tool_identity_before') and
        config.get('library') == report.get('library_identity_before'), 'Configuration identity differs from accepted receipt')
    require(Path(config.get('worker_out', '')).resolve() == root.resolve() and
        Path(config.get('snapshot', '')).resolve() == (directory / 'selected').resolve(), 'Worker path substitution')
    child_path = regular(root / 'worker-report.json', root)
    require(digest(child_path) == report.get('worker_report_sha256') and
        read_json(child_path.read_bytes()) == worker, 'Outer and retained worker receipts differ')
    artifacts = inventory(root)
    artifacts.pop('worker-report.json', None)
    require(artifacts == worker.get('artifact_sha256'), 'Retained worker artifact inventory differs')
    for path, value in artifacts.items(): frozen[root / path] = value
    frozen[child_path], frozen[config_path] = digest(child_path), digest(config_path)
    selected, producer = directory / 'selected', directory / 'producer'
    for base, mapping in ((selected, report['source_sha256']), (producer, report['producer_sha256'])):
        checked_map(base, mapping, frozen)
    require(config.get('source_tree') == source_objects.cached[report['source_commit']] and
        config.get('producer_tree') == {name: source_objects.cached[report['producer_commit']][name]
            for name in report['producer_sha256']}, 'Worker configuration Git membership differs')
    sys.path.insert(0, str(selected / 'scripts'))
    for name in tuple(sys.modules):
        if name.startswith('streaming_'): del sys.modules[name]
    driver = load_module('_accepted_streaming_coordinator', producer / 'scripts/check-streaming-continuation.py')
    driver.validate_worker(worker, config, closeout=True)
    require(set(report['producer_sha256']) == set(driver.PRODUCER), 'Full producer input inventory differs')
    require(config.get('object_format') in ('sha1', 'sha256'), 'Unknown worker Git object format')
    check_join_apis(driver.JOIN_THEOREMS)
    join = worker['stages']['composition-and-audit']['result']
    for depth in (2, 4):
        for name in driver.JOIN_THEOREMS:
            require('Pinwheel.Artifact.StreamingSessionD' + str(depth) + '.' + name in join['target_types'],
                'Missing checked depth-specific theorem type')
    intents = [read_json(line) for line in (root / 'command-intents.jsonl').read_bytes().splitlines()]
    check_journal(intents, worker['commands'], lambda label: (root / 'logs' / (label + '.log')).read_text())
    entries = [read_json(line) for line in (root / 'input-freeze.jsonl').read_bytes().splitlines()]
    count = freeze_journal(entries, worker['input_sha256_before_use'], artifacts)
    bindings = actual_bindings(worker, artifacts, root)
    operations = wire_operations(worker, config, root)
    gate = load_module('_accepted_streaming_proof_helpers', selected / 'scripts/check-buffered-rtl-session.py')
    closures = proof_closures(driver, gate, worker, root, selected, report['source_sha256'])
    factory = load_module('_accepted_streaming_composition', selected / 'scripts/streaming_composition.py')
    for a in (1, 2):
        texts, _ = driver.composition_texts(factory, a)
        for name, source in texts.items():
            require((root / 'composition' / (name + '.lean')).read_text() == source,
                'Final composition text differs from selected committed factory')
    require((root / 'composition/StreamingRequiredTargets.lean').read_text() == driver.join_checks(join['roots']),
        'Required theorem checks differ from the committed producer')
    audit_log = (root / 'logs/final-audit--StreamingFinalAudit.log').read_text()
    require(re.findall(r'Pinwheel audit: (\d+) declarations, (\d+) theorems; standard axioms only\.', audit_log) ==
        [(str(join['audited_declarations']), str(join['audited_theorems']))], 'Final private-declaration audit counts differ')
    require((root / 'logs/composition--StreamingRequiredTargets.log').read_text() == join['target_types'],
        'Checked target types differ from native Lean stdout')
    require('untrustedStreamingContinuation' in
        (root / 'logs/final-audit--StreamingFinalRejectAxiom.log').read_text(), 'Missing exact final private-axiom rejection')
    cost = worker['stages']['matched-cost']['result']
    for path, value in cost['emission_input_sha256'].items(): checked_path(path, (root, selected), frozen, value)
    for row in cost['rows']:
        for path, value in row['input_sha256'].items(): checked_path(path, (root, selected), frozen, value)
        checked_map(root / 'cost' / row['label'], row['artifact_sha256'], frozen)
    library = report['library_identity_before']
    for name in ('original', 'staged'):
        path = Path(library[name])
        require(path.is_file() and digest(path) == library['sha256'], 'Matched Liberty bytes changed')
        frozen[path] = library['sha256']
    require(source_files['scripts/validation_run.py'] == (producer / 'scripts/validation_run.py').read_bytes() and
        source_files['scripts/process_group.py'] == (producer / 'scripts/process_group.py').read_bytes(),
        'Selected source and producer command/runtime helpers differ')
    return dict(retained_artifacts=len(artifacts), frozen_inputs=count, bindings=bindings,
        simulator_operations=operations, proof_closures=closures,
        mandatory_theorems=list(driver.JOIN_THEOREMS), target_types=join['target_types']), root


def deterministic_gzip(data): return gzip.compress(data, compresslevel=9, mtime=0)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--tag', required=True)
    parser.add_argument('--full-tag', required=True)
    parser.add_argument('--foundation-tag', required=True)
    parser.add_argument('--python-tag', required=True)
    parser.add_argument('--failed-full-tag')
    args = parser.parse_args()
    tags = [args.tag, args.full_tag, args.foundation_tag, args.python_tag, *([args.failed_full_tag] if args.failed_full_tag else [])]
    require(all(re.fullmatch(r'[A-Za-z0-9_-]+', tag) for tag in tags) and len(tags) == len(set(tags)),
        'Require distinct safe receipt/export tags')
    destination = ROOT / DESTINATION
    require(not destination.exists(), 'Preserve existing evidence; destination must be fresh')
    out = ROOT / 'build/validation' / args.tag
    out.mkdir(parents=True, exist_ok=False)
    head, producers, bootstrap_records = bootstrap(out)
    helper = sys.modules['_streaming_export_git_helpers']
    commands_helper = sys.modules['validation_run']
    (out / 'logs').mkdir()
    run = commands_helper.Commands(ROOT, out / 'logs', default_timeout=60)
    git = helper.GitEvidence(out, run)
    source_objects.cached = {}
    stage = out / 'export'
    stage.mkdir()
    frozen, receipts, receipt_bytes = {}, {}, {}
    manifest = dict(schema='pinwheel.streaming-evidence.v1', exported_utc=datetime.now(timezone.utc).isoformat(),
        exporter_commit=head, exporter_sha256=producers, receipts=[], compact_files=[],
        boundary='Immutable receipt/source verification only; gates are not rerun. Raw RTL/wrapper equations and '
            'finite public-pin peers are distinct from synthesis cost/ABC combinational Liberty estimates. '
            'No mapped equivalence, guaranteed Fmax, electrical or physical signoff. Large generated artifacts '
            'and tool payloads stay at their recorded retained paths; this is a compact evidence export.')
    try:
        specifications = [('full', args.full_tag), ('foundation', args.foundation_tag), ('python', args.python_tag)]
        for kind, tag in specifications:
            path = regular(ROOT / 'build/validation' / tag / 'report.json', ROOT)
            data = path.read_bytes()
            receipts[kind] = read_json(data)
            receipt_bytes[kind] = data
            frozen[path] = sha(data)
        source_commit = same_source(receipts)
        manifest['source_commit'] = source_commit
        base = git.archive(BASE)['files']
        current = git.archive(head)['files']
        source = git.archive(source_commit)['files']
        manifest['frozen_baseline'] = preserve_base(base, source)
        preserve_base(base, current)
        for name, expected in DOCS.items(): require(digest(regular(ROOT / name, ROOT)) == expected, 'Intake document changed')
        patch = run(['git', 'diff', '--no-ext-diff', '--no-textconv', '--', *DOCS], 'intake-patch').encode()
        require(sha(patch) == PATCH, 'Intake document patch changed')
        (stage / 'intake-documents.patch').write_bytes(patch)
        manifest['intake_documents_sha256'], manifest['intake_patch_sha256'] = DOCS, PATCH
        for kind, tag in specifications:
            report = receipts[kind]
            mapping = report.get('source_sha256')
            objects = source_objects(run, source_commit, mapping, report.get('selected_git_objects'))
            verified = git.verify_map(source_commit, mapping, objects)
            archive_key = 'selected_archive_sha256' if kind == 'full' else 'snapshot_archive_sha256'
            reproduced = git.reproduce(source_commit, mapping, report.get(archive_key))
            require(all(current.get(name) is not None and sha(current[name]) == value for name, value in mapping.items()),
                'Accepted receipt is stale relative to current committed inputs')
            require(all(name in DOCS or digest(regular(ROOT / name, ROOT)) == value for name, value in mapping.items()),
                'Working source changed after the accepted gates')
            for name, value in mapping.items():
                if name not in DOCS: frozen[ROOT / name] = value
            item = dict(kind=kind, tag=tag, source_verification=verified, archive_verification=reproduced)
            if kind == 'full':
                full_contract(report)
                require(set(mapping) == set(source), 'Full gate omitted committed source files')
                retained_archive(ROOT / 'build/validation' / tag, 'selected-source.tar', report[archive_key], frozen)
            else:
                item['contract'] = helper.contract(kind, True, report, source)
            if kind == 'foundation':
                item['retained'] = foundation_evidence(report, source, ROOT / 'build/validation' / tag, frozen)
                require(report.get('driver_sha256') == sha(source['scripts/check-foundation-snapshot.py']), 'Foundation driver mismatch')
            if 'producer_sha256' in report:
                pc, pm = report['producer_commit'], report['producer_sha256']
                pf = git.archive(pc)['files']
                po = source_objects(run, pc, pm, report.get('producer_git_objects'))
                item['producer_verification'] = git.verify_map(pc, pm, po)
                if report.get('producer_archive_sha256'):
                    item['producer_archive_verification'] = git.reproduce(pc, pm, report['producer_archive_sha256'])
                    retained_archive(ROOT / 'build/validation' / tag, 'producer-source.tar', report['producer_archive_sha256'], frozen)
            if kind == 'full':
                item['retained'], full_root = full_retained(report, ROOT / 'build/validation' / tag,
                    source, frozen)
            if kind == 'python':
                require(set(mapping) == set(source), 'Python discovery omitted committed source files')
                item['retained'] = check_python_retained(report, ROOT / 'build/validation' / tag, frozen, pf)
            data = receipt_bytes[kind]
            compressed = deterministic_gzip(data)
            require(gzip.decompress(compressed) == data, 'Receipt compression failed')
            filename = tag + '.json.gz'
            (stage / filename).write_bytes(compressed)
            item.update(file=filename, raw_bytes=len(data), raw_sha256=sha(data),
                compressed_bytes=len(compressed), compressed_sha256=sha(compressed))
            manifest['receipts'].append(item)
        for name in ('StreamingSessionD2.lean', 'StreamingSessionD4.lean', 'StreamingRequiredTargets.lean', 'StreamingFinalAudit.lean'):
            path = regular(full_root / 'composition' / name, full_root)
            data = path.read_bytes()
            (stage / name).write_bytes(data)
            manifest['compact_files'].append(dict(file=name, sha256=sha(data), bytes=len(data)))
        join = receipts['full']['worker']['stages']['composition-and-audit']['result']
        compact = {
            'checked-target-types.txt': join['target_types'].encode(),
            'final-private-audit.log': (full_root / 'logs/final-audit--StreamingFinalAudit.log').read_bytes(),
            'final-private-axiom-rejection.log': (full_root / 'logs/final-audit--StreamingFinalRejectAxiom.log').read_bytes(),
            'foundation-private-audit.log': (ROOT / 'build/validation' / args.foundation_tag / 'axioms.log').read_bytes(),
        }
        controls = dict(raw={name: dict(mutations=value['mutations'],
            private_axiom_rejected=value['private_axiom_rejected'], axiom_audit=value['axiom_audit'])
            for name, value in receipts['full']['worker']['stages']['raw-components']['result'].items()},
            wrappers={name: value['mutations'] for name, value in
                receipts['full']['worker']['stages']['actual-wrappers']['result'].items()},
            final=dict(audited_declarations=join['audited_declarations'], audited_theorems=join['audited_theorems'],
                private_axiom_rejected=join['private_axiom_rejected'], mandatory_theorems=join['mandatory_theorems']))
        compact['proof-control-summary.json'] = (json.dumps(controls, indent=2, sort_keys=True) + '\n').encode()
        for name, data in compact.items():
            (stage / name).write_bytes(data)
            manifest['compact_files'].append(dict(file=name, sha256=sha(data), bytes=len(data)))
        if args.failed_full_tag:
            path = regular(ROOT / 'build/validation' / args.failed_full_tag / 'report.json', ROOT)
            data, report = path.read_bytes(), read_json(path.read_bytes())
            require(report.get('passed') is False and report.get('error'), 'Optional failed receipt must actually fail')
            git.verify_map(report['source_commit'], report['source_sha256'],
                source_objects(run, report['source_commit'], report['source_sha256'], report.get('selected_git_objects')))
            failed_archive = report.get('selected_archive_sha256')
            require(report.get('schema') == 'pinwheel.streaming-continuation.v1', 'Optional failure is not a continuation receipt')
            failed_reproduced = git.reproduce(report['source_commit'], report['source_sha256'], failed_archive)
            filename = args.failed_full_tag + '.failed.json.gz'
            compressed = deterministic_gzip(data)
            require(gzip.decompress(compressed) == data, 'Historical failure compression failed')
            (stage / filename).write_bytes(compressed)
            manifest['failed_receipt'] = dict(tag=args.failed_full_tag, file=filename,
                source_commit=report['source_commit'], raw_sha256=sha(data), compressed_sha256=sha(compressed),
                error=report['error'], archive_verification=failed_reproduced, excluded_from_acceptance=True)
            frozen[path] = sha(data)
        require(run(['git', 'rev-parse', 'HEAD'], 'closeout-head').strip() == head, 'HEAD changed during export')
        for name, expected in producers.items(): require(digest(ROOT / name) == expected, 'Exporter helper changed')
        for path, expected in frozen.items(): require(digest(path) == expected, 'Retained receipt/artifact changed during export')
        require(sha(run(['git', 'diff', '--no-ext-diff', '--no-textconv', '--', *DOCS], 'closeout-intake-patch').encode()) == PATCH,
            'Intake patch changed during export')
        for name, expected in DOCS.items(): require(digest(ROOT / name) == expected, 'Intake document changed during export')
        for item in manifest['receipts']:
            data = (stage / item['file']).read_bytes()
            require(sha(data) == item['compressed_sha256'] and
                gzip.decompress(data) == receipt_bytes[item['kind']], 'Exported receipt changed after compression')
        for item in manifest['compact_files']:
            require(digest(stage / item['file']) == item['sha256'], 'Compact proof/audit export changed')
        if 'failed_receipt' in manifest:
            item = manifest['failed_receipt']
            data = (stage / item['file']).read_bytes()
            require(sha(data) == item['compressed_sha256'] and
                sha(gzip.decompress(data)) == item['raw_sha256'], 'Historical failure export changed')
        manifest['export_files_sha256'] = inventory(stage)
        manifest['bootstrap_commands'], manifest['commands'] = bootstrap_records, run.records
        write_json(stage / 'manifest.json', manifest)
        require(not destination.exists(), 'Evidence destination appeared during export')
        destination.parent.mkdir(parents=True, exist_ok=True)
        stage.rename(destination)
        write_json(out / 'export-summary.json', dict(passed=True, destination=DESTINATION,
            manifest_sha256=digest(destination / 'manifest.json'), exporter_commit=head))
    except BaseException as error:
        write_json(out / 'export-failed.json', dict(passed=False, error=repr(error),
            exporter_commit=head, exporter_sha256=producers, commands=run.records))
        raise
    print('Streaming evidence exported: ' + str(destination), flush=True)


if __name__ == '__main__': main()
