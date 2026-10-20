"""Strict reuse of a completed, source-identical649 foundation for new raw RTL.

The unused foundation negative-control object is retained as evidence but is
never copied into the positive import library. This module executes no Lean.
"""
from contextlib import contextmanager
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import sys
import time

SCHEMA = 'pinwheel.streaming-tt-fresh-foundation-binding.v1'
ADAPTERS = ('scripts/streaming_tt_fresh_foundation.py', 'scripts/check-streaming-ready-fresh.py',
            'scripts/streaming_tt_opt_intake.py', 'scripts/check-streaming-uart.py',
            'scripts/streaming_tt_optimize.py', 'scripts/streaming_tt_opt_proof.py',
            'scripts/streaming_tt_opt_device.py')
CONTROL = 'Pinwheel/CI/FoundationPrivateControl.olean'
FOUNDATION_INPUTS = ('Pinwheel.lean', 'lean-toolchain', 'lakefile.toml', 'lake-manifest.json',
    'scripts/check-foundation.py', 'scripts/process_group.py', 'scripts/binary_v0.py',
    'scripts/check-uart-rx.py', 'scripts/uart_rx_oracle.py', 'scripts/reactive-core-vectors.py',
    'scripts/execution-vectors.py')


def require(ok, message):
    if not ok:
        raise ValueError(message)


def sha(path):
    with Path(path).open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def pairs(items):
    result = {}
    for key, value in items:
        require(key not in result, 'Duplicate JSON key: ' + key)
        result[key] = value
    return result


def read(path):
    return json.loads(Path(path).read_text(), object_pairs_hook=pairs)


def regular(path):
    path = Path(path)
    require(path.is_absolute() and path.is_file() and not path.is_symlink(), 'Expected absolute regular file: ' + str(path))
    return path


def relative(value):
    path = Path(value)
    require(type(value) is str and value and not path.is_absolute() and '..' not in path.parts and path.as_posix() == value,
            'Invalid relative artifact path')
    return path


def manifest(root):
    root = Path(root)
    require(root.is_dir() and not root.is_symlink(), 'Missing or redirected library root')
    result = {}
    for path in sorted(root.rglob('*')):
        require(not path.is_symlink(), 'Symbolic library artifact')
        if path.is_file():
            result[path.relative_to(root).as_posix()] = sha(path)
    return result


def module_order(root):
    root = Path(root)
    modules = {'.'.join(path.relative_to(root).with_suffix('').parts): path
               for path in (root / 'Pinwheel').rglob('*.lean')}
    modules['Pinwheel'] = root / 'Pinwheel.lean'
    active, seen, ordered = set(), set(), []
    def visit(name):
        if name in seen:
            return
        require(name not in active and name in modules, 'Missing or cyclic local source import: ' + name)
        active.add(name)
        for child in re.findall(r'^\s*(?:public\s+)?import\s+(\S+)', modules[name].read_text(), re.M):
            if child.startswith('Pinwheel'):
                visit(child)
            else:
                require(child.split('.')[0] in ('Init', 'Lean', 'Std', 'Lake'), 'Unknown nonlocal source import')
        active.remove(name); seen.add(name); ordered.append(name)
    visit('Pinwheel')
    require(set(modules) == seen, 'Source module outside whole-library default imports')
    return ordered


def partition_library(modules, artifacts, control):
    require(control == CONTROL and control not in {name.replace('.', '/') + '.olean' for name in modules},
            'Foundation control aliases a positive module')
    expected = {name.replace('.', '/') + suffix for name in modules for suffix in ('.olean', '.ilean')}
    require(set(artifacts) == expected | {control}, 'Incomplete/extra positive or negative foundation library membership')
    require(all(re.fullmatch('[0-9a-f]{64}', value) for value in artifacts.values()), 'Malformed artifact digest')
    return {name: artifacts[name] for name in sorted(expected)}, {control: artifacts[control]}


def bound(path):
    path = regular(Path(path).resolve())
    return dict(path=str(path), sha256=sha(path))


def verify_bound(value):
    path = regular(value['path'])
    require(sha(path) == value['sha256'], 'Bound receipt changed')
    return path


def verify_runtime(runtime_path, foundation_path, tools, *, observe_current=True):
    runtime_path = regular(Path(runtime_path).resolve())
    runtime = read(runtime_path)
    require(runtime.get('schema') == 'pinwheel.streaming-tt-fresh-foundation-runtime.v1' and
            runtime.get('passed') is True and runtime.get('status') == 'completed' and
            type(runtime.get('exit_code')) is int and runtime['exit_code'] == 0 and
            runtime.get('timed_out') is False and runtime.get('native_process_group_closed') is True and
            runtime.get('inputs_unchanged') is True and runtime.get('sources_unchanged') is True and
            runtime.get('foundation_complete_649') is True and runtime.get('runtime_unchanged') is True and
            runtime.get('runtime_files') == 14923,
            'Foundation runtime companion did not close')
    require(Path(runtime['foundation_receipt']).resolve() == Path(foundation_path).resolve() and
            runtime['foundation_receipt_sha256'] == sha(foundation_path), 'Runtime companion belongs to another foundation')
    require(runtime.get('input_sha256') and all(sha(regular(name)) == value
            for name, value in runtime['input_sha256'].items()), 'Foundation runtime observer inputs changed')
    before = read(verify_bound(runtime['runtime_before']))
    after = read(verify_bound(runtime['runtime_after']))
    require(before == after and len(before) == 14923, 'Foundation full runtime membership or identity changed')
    for name in ('lean', 'lake'):
        path = regular(tools[name])
        require(str(path) in before and before[str(path)]['sha256'] == sha(path) and
                before[str(path)]['resolved'] == str(path.resolve()), 'Candidate compiler differs from foundation runtime')
    if observe_current:
        for path, value in before.items():
            item = Path(path)
            require(item.is_file() and str(item.resolve()) == value['resolved'] and item.stat().st_size == value['bytes'] and
                    sha(item) == value['sha256'], 'Current installed foundation runtime differs: ' + path)
        prefix = Path(tools['lean']).parent.parent
        current = {str(path) for path in (prefix / 'lib/lean').rglob('*') if path.is_file()}
        require(not any(path.is_symlink() and path.is_dir() for path in (prefix / 'lib/lean').rglob('*')) and
                current == {name for name in before if Path(name).is_relative_to(prefix / 'lib/lean')},
                'Current compiled runtime file membership differs')
    return runtime


def create_binding(foundation_path, runtime_path, candidate_root, candidate_commit, tools):
    candidate_root = Path(candidate_root).resolve()
    foundation_path = regular(Path(foundation_path).resolve())
    foundation = read(foundation_path)
    require(foundation.get('passed') is True and foundation.get('modules') == 649 and
            foundation.get('serial_build') is True and foundation.get('committed_input_membership_verified') is True and
            foundation.get('inherited_override_guard_checked') is True and
            type(foundation.get('exit_code')) is int and foundation['exit_code'] == 0 and
            foundation.get('lean_resource_limits') == ['-M4096', '-j1', '-DElab.async=false'] and
            foundation.get('executable_suites') == 65 and foundation.get('kernel_suites') == 8 and
            foundation.get('untrusted_axiom_rejected') is True and foundation.get('unused_private_axiom_rejected') is True and
            type(foundation.get('audited_declarations')) is int and foundation['audited_declarations'] > 0 and
            type(foundation.get('audited_theorems')) is int and foundation['audited_theorems'] > 0,
            'A complete fresh649 whole-library/private-audit foundation is required')
    require(re.fullmatch('[0-9a-f]{40}', candidate_commit), 'Exact candidate commit required')
    modules = module_order(candidate_root)
    require(len(modules) == 649, 'Candidate is not the649 source wave')
    projection = foundation['source_sha256']
    expected_projection = set(FOUNDATION_INPUTS) | {path.relative_to(candidate_root).as_posix()
        for directory, pattern in (('Pinwheel', '**/*.lean'), ('test', '*.lean'))
        for path in (candidate_root / directory).glob(pattern)}
    require(set(projection) == expected_projection, 'Foundation consumed-source membership is incomplete or unexpected')
    require(type(projection) is dict and projection and all(
        (candidate_root / relative(name)).is_file() and not (candidate_root / name).is_symlink() and
        sha(candidate_root / name) == value for name, value in projection.items()),
        'Candidate source differs from foundation consumed input projection')
    original_source = Path(foundation['retained_snapshot']).resolve()
    require(all((original_source / name).is_file() and not (original_source / name).is_symlink() and
                sha(original_source / name) == value for name, value in projection.items()),
            'Retained foundation consumed source changed')
    require({name for name in projection if name == 'Pinwheel.lean' or name.startswith('Pinwheel/') and name.endswith('.lean')} ==
            {name.replace('.', '/') + '.lean' for name in modules}, 'Foundation source module membership differs')
    commands = foundation['commands']
    builds = [row for row in commands if row['label'].startswith('build-')]
    require([row['label'][6:] for row in builds] == modules and all(type(row.get('exit_code')) is int and row['exit_code'] == 0
            for row in builds), 'Missing/reordered native foundation source compilation')
    expected_rejects = {'reject-untrusted-axiom', 'reject-unused-private-axiom'}
    require(len({row['label'] for row in commands}) == len(commands) and
            {row['label'] for row in commands if type(row.get('exit_code')) is int and row['exit_code'] != 0} == expected_rejects and
            all(type(row.get('exit_code')) is int for row in commands), 'Foundation negative/positive command outcomes differ')
    library = Path(foundation['retained_library']).resolve()
    require(library == Path(foundation['retained_snapshot']).resolve() / '.lake/build/lib/lean',
            'Foundation library does not belong to its retained source snapshot')
    artifacts = manifest(library)
    require(artifacts == foundation['retained_library_artifact_sha256'], 'Complete retained foundation library changed')
    positive, negative = partition_library(modules, artifacts, foundation['retained_private_control_module'])
    logs = {str(regular((foundation_path.parent / (row['label'] + '.log')).resolve())):
            sha(foundation_path.parent / (row['label'] + '.log')) for row in commands}
    audit = (foundation_path.parent / 'axioms.log').read_text()
    require(f"Pinwheel audit: {foundation['audited_declarations']} declarations, {foundation['audited_theorems']} theorems; standard axioms only." in audit,
            'Foundation audit summary differs')
    reject = (foundation_path.parent / 'reject-unused-private-axiom.log').read_text()
    require('Unapproved axioms in _private.Pinwheel.CI.FoundationPrivateControl.' in reject and 'forbiddenUnused' in reject,
            'Foundation unused-private-axiom rejection is unrelated or missing')
    runtime = verify_runtime(runtime_path, foundation_path, tools)
    require(runtime['source_commit'] == foundation['source_commit'], 'Foundation/runtime source commits differ')
    require(runtime.get('committed_input_sha256') and all(
        (candidate_root / relative(name)).is_file() and not (candidate_root / name).is_symlink() and
        sha(candidate_root / name) == value for name, value in runtime['committed_input_sha256'].items()),
        'Candidate differs from complete foundation/runtime producer source projection')
    return dict(schema=SCHEMA, qualified=False, candidate_commit=candidate_commit, candidate_root=str(candidate_root),
        foundation_commit=foundation['source_commit'], foundation_report=bound(foundation_path), runtime_report=bound(runtime_path),
        foundation_library=str(library), foundation_source_projection=projection, modules=modules,
        positive_library_artifact_sha256=positive, excluded_negative_control_artifact_sha256=negative,
        foundation_native_log_sha256=logs, lean=str(regular(tools['lean'])), lake=str(regular(tools['lake'])),
        python=str(regular(tools['python'])),
        adapter_source_sha256={name: sha(candidate_root / name) for name in ADAPTERS},
        boundary='Fresh649 same-consumed-source library reused; unused negative control OLE excluded. Raw/mapped/physical correspondence must be generated anew.')


def verify_binding(binding):
    require(binding.get('schema') == SCHEMA and len(binding.get('modules', [])) == 649,
            'Wrong fresh foundation binding schema/scope')
    root = Path(binding['candidate_root'])
    expected = create_binding(verify_bound(binding['foundation_report']), verify_bound(binding['runtime_report']),
                              root, binding['candidate_commit'], {key: binding[key] for key in ('lean', 'lake', 'python')})
    require(expected == binding, 'Fresh foundation binding changed or does not regenerate exactly')
    return True


def stage_library(binding, snapshot):
    verify_binding(binding)
    snapshot = Path(snapshot).resolve()
    require(snapshot == Path(binding['candidate_root']), 'Library staging targets another source archive')
    require(not (snapshot / '.lake').exists(), 'Refuse an existing staged or workspace proof cache')
    target = snapshot / '.lake/build/lib/lean'
    original = Path(binding['foundation_library'])
    for name, value in binding['positive_library_artifact_sha256'].items():
        source = original / relative(name)
        require(sha(source) == value, 'Original foundation artifact changed during copy')
        destination = target / name
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_bytes(source.read_bytes())
    verify_staged(binding)
    return target


def verify_staged(binding):
    target = Path(binding['candidate_root']) / '.lake/build/lib/lean'
    require(manifest(target) == binding['positive_library_artifact_sha256'], 'Positive staged library membership/bytes changed')
    require(not (target / CONTROL).exists(), 'Unused negative-control OLE entered positive imports')
    return True


def generated_paths_owned(paths, worker_out):
    owners = {}
    for root in paths:
        require(root.is_relative_to(Path(worker_out).resolve()), 'Generated proof path escapes this fresh worker')
        if not root.exists():
            continue  # Current output directories are created before first compilation.
        require(root.is_dir() and not root.is_symlink(), 'Generated import root is redirected')
        for item in root.rglob('*'):
            require(not item.is_symlink(), 'Generated import alias is forbidden')
            if not item.is_file():
                continue
            relative_name = item.relative_to(root).as_posix()
            suffix = next((value for value in ('.olean.private', '.olean.server', '.olean', '.ilean', '.lean')
                           if relative_name.endswith(value)), None)
            if suffix is None:
                continue
            module = relative_name[:-len(suffix)].replace('/', '.')
            require(module.split('.')[0] not in ('Pinwheel', 'Init', 'Lean', 'Std', 'Lake'),
                    'Generated root shadows a pinned foundation or standard-library module')
            require(module not in owners or owners[module] == root, 'Duplicate generated module across import roots')
            owners[module] = root
    return True


def bounded_command(argv, binding, worker_out, entry, binding_path):
    """Translate only known Lake interfaces; preserve every requested proof/control."""
    argv = list(map(str, argv)); requested = list(argv)
    root = Path(binding['candidate_root'])
    library = root / '.lake/build/lib/lean'
    stdlib = Path(binding['lean']).parent.parent / 'lib/lean'
    paths = []
    if argv and argv[0] == 'env':
        require(len(argv) > 2 and argv[1].startswith('LEAN_PATH='), 'Unexpected compiler environment override')
        paths = [Path(path).resolve() for path in argv[1].split('=', 1)[1].split(':') if path]
        argv = argv[2:]
    if argv[:2] == [binding['lake'], 'build']:
        require(not paths and argv[2:] and all(name in binding['modules'] for name in argv[2:]), 'Unbound library build request')
        return [binding['python'], '-B', str(entry), '--verify-stage', str(binding_path)]
    if argv == [binding['lake'], 'env', 'which', 'lean']:
        return [binding['python'], '-B', str(entry), '--compiler-path', str(binding_path)]
    if argv == [binding['lake'], 'env', 'printenv', 'LEAN_PATH']:
        return [binding['python'], '-B', str(entry), '--compiler-search', str(binding_path)]
    if argv[:3] == [binding['lake'], 'env', 'lean']:
        argv = [binding['lean'], *argv[3:]]
    if argv and argv[0] == binding['lean'] and '--version' not in argv:
        require(not any(value.startswith(('-M', '-j', '-DElab.async=')) for value in argv[1:]),
                'Requested compiler resource override conflicts with strict adapter bounds')
        generated_paths_owned(paths, worker_out)
        if '-o' in argv:
            require(argv.count('-o') == 1 and argv.index('-o') + 1 < len(argv) and
                    Path(argv[argv.index('-o') + 1]).resolve().is_relative_to(Path(worker_out).resolve()),
                    'Compiled output escapes the fresh generated worker')
        paths = list(dict.fromkeys([library, stdlib, *paths]))
        return ['env', 'LEAN_PATH=' + ':'.join(map(str, paths)), 'LEAN_SYSROOT=' + str(stdlib.parent.parent),
                argv[0], '-M4096', '-j1', '-DElab.async=false', *argv[1:]]
    require(not paths and not (argv and argv[0] == binding['lake'] and 'build' in argv), 'Untranslated/unbounded Lake command')
    return requested


def validate_raw_binding(report, config, child, interpreter_root):
    marker = config.get('fresh_foundation')
    require(type(marker) is dict and marker == report.get('fresh_foundation') == child.get('fresh_foundation') and
            report.get('fresh_foundation_adapter_closed') is True, 'Fresh foundation marker missing or inconsistent')
    binding = read(verify_bound(marker))
    require(binding['candidate_commit'] == config['source_commit'] == config['producer_commit'] and
            binding['candidate_root'] == str(Path(config['snapshot']).resolve()), 'Fresh binding candidate selection differs')
    require(report.get('fresh_foundation_adapter_source_sha256') == binding['adapter_source_sha256'],
            'Fresh adapter producer inventory differs')
    for name in ADAPTERS:
        require(sha(Path(interpreter_root) / name) == config['source_sha256'].get(name) ==
                binding['adapter_source_sha256'][name], 'Fresh intake interpreter differs from committed candidate producer')
    verify_binding(binding)
    verify_staged(binding)
    closeout = child.get('fresh_foundation_closeout', {})
    require(closeout.get('schema') == 'pinwheel.streaming-tt-fresh-foundation-import-closeout.v1' and
            closeout.get('passed') is True and closeout.get('binding') == marker and closeout.get('positive_modules') == 649 and
            closeout.get('excluded_negative_control_objects') == binding['excluded_negative_control_artifact_sha256'] and
            all(closeout.get(key) is True for key in ('positive_library_unchanged', 'source_projection_unchanged', 'runtime_unchanged')),
            'Fresh649 positive-only import closeout did not complete')
    out = Path(config['worker_out'])
    path = regular(out / 'fresh-foundation-native-journal.jsonl')
    rows = [json.loads(line, object_pairs_hook=pairs) for line in path.read_text().splitlines()]
    intents = [json.loads(line, object_pairs_hook=pairs) for line in
               (out / 'command-intents.jsonl').read_text().splitlines()]
    validate_command_intents(intents, child['commands'], rows, binding, out, marker['path'])
    require(len(rows) == len(child['commands']) > 0, 'Fresh adapter native journal is incomplete')
    for row, command in zip(rows, child['commands']):
        require(row['record'] == command and row['label'] == command['label'] and row['actual_argv'] == command['argv'] and
                row['actual_argv'] == bounded_command(row['requested_argv'], binding, out,
                    Path(binding['candidate_root']) / 'scripts/check-streaming-ready-fresh.py', marker['path']) and
                row['source_sha256_before'] == row['source_sha256_after'] and
                all(sha(regular(name)) == value for name, value in row['source_sha256_before'].items()),
                'Fresh adapter command/source journal changed or differs from exact bounded translation')
        if binding['lean'] in command['argv']:
            require(row['compiler_sha256_before'] == row['compiler_sha256_after'] == sha(binding['lean']),
                    'Fresh native compiler changed')
    return binding


def validate_command_intents(intents, commands, rows, binding, worker_out, binding_path):
    require(len(intents) == len(commands) == len(rows) > 0, 'Pre-use/actual native journal membership differs')
    for index, (intent, command, row) in enumerate(zip(intents, commands, rows)):
        require(type(intent.get('index')) is int and intent['index'] == index and
                intent.get('label') == command['label'] == row['label'] and
                intent.get('argv') == row['requested_argv'] and row['actual_argv'] == command['argv'] and
                row['record'] == command and row['expected_failure'] is bool(intent.get('options', {}).get('reject')) and
                bounded_command(intent['argv'], binding, worker_out,
                    Path(binding['candidate_root']) / 'scripts/check-streaming-ready-fresh.py', binding_path) == command['argv'],
                'Pre-use requested command does not match its exact bounded native translation/result')
    return True


def consumed_imports(source, roots, binding):
    """Bind actual generated/project import closure; stdlib is batch-pinned."""
    source = Path(source)
    queue = [(source, None)]; seen = set(); result = {}
    base = Path(binding['candidate_root'])
    library = base / '.lake/build/lib/lean'
    while queue:
        path, module = queue.pop()
        path = regular(path.resolve())
        if str(path) in seen: continue
        seen.add(str(path)); result[str(path)] = sha(path)
        if module is not None:
            if module.startswith('Pinwheel'):
                relative_name = module.replace('.', '/') + '.olean'
                obj = regular(library / relative_name)
                require(sha(obj) == binding['positive_library_artifact_sha256'].get(relative_name), 'Consumed project object changed')
                require(sha(path) == binding['foundation_source_projection'].get(module.replace('.', '/') + '.lean'),
                        'Consumed project source differs from fresh foundation')
            else:
                obj = regular(path.with_suffix('.olean'))
            result[str(obj)] = sha(obj)
        for child in re.findall(r'^\s*(?:public\s+)?import\s+(\S+)', path.read_text(), re.M):
            if child.split('.')[0] in ('Init', 'Lean', 'Std', 'Lake'):
                continue
            relative_name = child.replace('.', '/') + '.lean'
            if child.startswith('Pinwheel'):
                candidates = [base / relative_name]
            else:
                candidates = [root / relative_name for root in roots if (root / relative_name).is_file()]
            require(len(candidates) == 1, 'Missing or ambiguous consumed generated/project import: ' + child)
            queue.append((candidates[0], child))
    return result


def optimized_inputs(requested, actual, binding, marker, tools):
    inputs = {str(verify_bound(marker)): marker['sha256']}
    inputs.update({str(regular(path)): sha(path) for path in tools.values()})
    roots = [Path(path).resolve() for path in requested[1].split('=', 1)[1].split(':') if path] \
        if requested and requested[0] == 'env' else []
    for value in actual:
        path = Path(value)
        if path.is_absolute() and path.is_file():
            path = regular(path)
            inputs[str(path)] = sha(path)
            if path.suffix == '.lean': inputs.update(consumed_imports(path, roots, binding))
    return inputs


def closed_group(pid):
    try:
        os.killpg(pid, 0)
        return False
    except ProcessLookupError:
        return True


def terminate_group(pid):
    """Bounded cleanup of this executor's own newly created process group."""
    for action, seconds in ((signal.SIGTERM, 1), (signal.SIGKILL, 3)):
        if closed_group(pid): return True
        try: os.killpg(pid, action)
        except ProcessLookupError: return True
        end = time.monotonic() + seconds
        while time.monotonic() < end:
            if closed_group(pid): return True
            time.sleep(.05)
    return closed_group(pid)


def check_native_environment():
    fixed = {'PYTHONPATH', 'PYTHONHOME', 'PYTHONSTARTUP', 'PYTHONPYCACHEPREFIX',
             'LEAN_PATH', 'LEAN_SRC_PATH', 'LEAN_SYSROOT', 'LAKE_HOME', 'LAKE_PACKAGES_DIR',
             'LAKE_CACHE_DIR', 'LD_PRELOAD', 'LD_LIBRARY_PATH'}
    require(not any(value and (key in fixed or key.startswith(('DYLD_', 'YOSYS_', 'ABC_')))
                    for key, value in os.environ.items()), 'Inherited compiler/import/loader/tool override')


class FreshNativeExecutor:
    """One bounded optimized batch, reusing the existing translation contract."""
    def __init__(self, config, out):
        check_native_environment()
        self.out = Path(out).resolve()
        self.marker = config['fresh_foundation']
        self.binding = read(verify_bound(self.marker))
        require(self.binding['candidate_commit'] == config['source_commit'] == config['producer_commit'] and
                self.binding['candidate_root'] == str(Path(config['root']).resolve()), 'Optimized fresh source selection mismatch')
        require(all(config['tools'][name] == self.binding[name] for name in ('lean', 'lake')), 'Optimized compiler differs from fresh raw foundation')
        verify_binding(self.binding); verify_staged(self.binding)
        self.tools = dict(config['tools'])
        self.path = self.out / 'fresh-foundation-optimized-native.jsonl'
        require(not self.path.exists(), 'Preserve an earlier optimized native journal')
        self.rows = []
        self.outputs = {}

    def append(self, value):
        with self.path.open('a') as stream:
            stream.write(json.dumps(value) + '\n')
            stream.flush(); os.fsync(stream.fileno())

    def run(self, requested, log, *, timeout=600):
        check_native_environment()
        require(type(timeout) is int and 1 <= timeout <= 900, 'Bounded optimized native timeout required')
        requested = list(map(str, requested)); log = Path(log).resolve()
        require(log.is_relative_to(self.out) and not log.exists(), 'Fresh owned optimized log required')
        log.parent.mkdir(parents=True, exist_ok=True)
        entry = Path(self.binding['candidate_root']) / 'scripts/check-streaming-ready-fresh.py'
        actual = bounded_command(requested, self.binding, self.out, entry, self.marker['path'])
        inputs = optimized_inputs(requested, actual, self.binding, self.marker, self.tools)
        for name, value in inputs.items():
            if Path(name).suffix == '.olean' and Path(name).is_relative_to(self.out):
                require(self.outputs.get(name) == value, 'Consumed generated object lacks an earlier closed native producer')
        output = None
        if '-o' in actual:
            output = Path(actual[actual.index('-o') + 1]).resolve()
            require(not output.exists(), 'Refuse a cached optimized target OLE')
        intent = dict(event='intent', index=len(self.rows), binding=self.marker, requested_argv=requested,
            actual_argv=actual, input_sha256_before=inputs, log=str(log), timeout_seconds=timeout)
        self.append(intent); start = time.monotonic(); timed_out = False
        child = subprocess.Popen(actual, cwd=self.binding['candidate_root'], stdout=subprocess.PIPE,
                                 stderr=subprocess.STDOUT, text=True, start_new_session=True)
        try:
            text, _ = child.communicate(timeout=timeout); code = child.returncode
        except subprocess.TimeoutExpired:
            timed_out = True
            try: os.killpg(child.pid, signal.SIGTERM)
            except ProcessLookupError: pass
            try: text, _ = child.communicate(timeout=3)
            except subprocess.TimeoutExpired:
                try: os.killpg(child.pid, signal.SIGKILL)
                except ProcessLookupError: pass
                text, _ = child.communicate(timeout=3)
            code = 124
        closed = closed_group(child.pid)
        if not closed: closed = terminate_group(child.pid)
        log.write_text(text)
        result = dict(event='result', **{key: value for key, value in intent.items() if key != 'event'},
            exit_code=code, timed_out=timed_out, native_process_group_closed=closed,
            input_sha256_after={name: sha(name) for name in inputs}, log_sha256=sha(log),
            olean=str(output) if output else None,
            olean_sha256=sha(output) if output and output.is_file() else None,
            olean_nonempty_regular=(output.is_file() and not output.is_symlink() and output.stat().st_size > 0) if output else None,
            elapsed_seconds=time.monotonic()-start)
        self.append(result); self.rows.append(result)
        require(result['input_sha256_before'] == result['input_sha256_after'] and closed and not timed_out,
                'Optimized native source/import/ownership/timeout closeout failed')
        if code == 0 and output is not None:
            require(output.is_file() and not output.is_symlink() and output.stat().st_size > 0,
                    'Successful fresh Lean produced no nonempty owned object')
            self.outputs[str(output)] = sha(output)
        completed = subprocess.CompletedProcess(actual, code, text, '')
        completed.native_journal_index = intent['index']
        completed.native_argv = actual
        return completed

    def closeout(self):
        check_native_environment()
        verify_binding(self.binding); verify_staged(self.binding)
        require(self.rows and all(row['exit_code'] == 0 and row['timed_out'] is False and
            row['native_process_group_closed'] is True and row['input_sha256_before'] == row['input_sha256_after'] and
            (row['olean'] is None or row['olean_nonempty_regular'] is True and sha(regular(row['olean'])) == row['olean_sha256'])
            for row in self.rows), 'Optimized native batch is incomplete')
        return dict(schema='pinwheel.streaming-tt-fresh-optimized-native.v1', passed=True, qualified=False,
                    binding=self.marker, commands=len(self.rows), journal=bound(self.path))


def validate_optimized_native(raw_config, config, worker, out):
    """Independently close requested intents, actual commands and every consumer."""
    check_native_environment()
    marker = raw_config['fresh_foundation']; out = Path(out).resolve()
    require(marker == config.get('fresh_foundation') == worker.get('fresh_foundation'),
            'Optimized batch lost or changed its exact raw foundation binding')
    binding = read(verify_bound(marker)); verify_binding(binding); verify_staged(binding)
    require(binding['candidate_commit'] == config['source_commit'] == config['producer_commit'] and
            binding['candidate_root'] == str(Path(config['root']).resolve()) and
            all(config['tools'][name] == binding[name] for name in ('lean', 'lake')),
            'Optimized native binding source/runtime differs')
    receipt = worker.get('fresh_optimized_native', {})
    require(receipt.get('schema') == 'pinwheel.streaming-tt-fresh-optimized-native.v1' and
            receipt.get('passed') is True and receipt.get('qualified') is False and receipt.get('binding') == marker and
            type(receipt.get('commands')) is int and receipt['commands'] > 0,
            'Optimized native typed closeout missing')
    journal = verify_bound(receipt['journal'])
    require(journal == out / 'fresh-foundation-optimized-native.jsonl', 'Optimized journal is outside its worker')
    events = [json.loads(line, object_pairs_hook=pairs) for line in journal.read_text().splitlines()]
    require(len(events) == 2 * receipt['commands'], 'Optimized pre-use/result journal is incomplete')
    results = []; outputs = {}
    for index in range(receipt['commands']):
        intent, result = events[2*index:2*index+2]
        require(intent.get('event') == 'intent' and result.get('event') == 'result' and
                type(intent.get('index')) is int and intent['index'] == index and
                type(result.get('index')) is int and type(result.get('timeout_seconds')) is int and
                all(result.get(key) == value for key, value in intent.items() if key != 'event') and
                intent.get('binding') == marker and type(intent.get('timeout_seconds')) is int and
                1 <= intent['timeout_seconds'] <= 900, 'Optimized intent/result identity differs')
        actual = bounded_command(intent['requested_argv'], binding, out,
            Path(binding['candidate_root']) / 'scripts/check-streaming-ready-fresh.py', marker['path'])
        require(actual == intent.get('actual_argv') and type(result.get('exit_code')) is int and result['exit_code'] == 0 and
                result.get('timed_out') is False and result.get('native_process_group_closed') is True,
                'Optimized actual native command failed or differs from strict translation')
        expected = optimized_inputs(intent['requested_argv'], actual, binding, marker, config['tools'])
        output = Path(actual[actual.index('-o') + 1]).resolve() if '-o' in actual else None
        # The now-existing target was absent before its own native execution.
        if output is not None: expected.pop(str(output), None)
        require(expected == intent.get('input_sha256_before') == result.get('input_sha256_after'),
                'Optimized actual consumed input/import identity differs')
        for name, value in expected.items():
            if Path(name).suffix == '.olean' and Path(name).is_relative_to(out):
                require(outputs.get(name) == value, 'Generated import lacks an earlier fresh native producer')
        log = regular(result['log'])
        require(log.is_relative_to(out) and sha(log) == result.get('log_sha256'), 'Optimized native log changed')
        require(result.get('olean') == (str(output) if output else None), 'Optimized target object selection differs')
        if output is not None:
            require(output.is_file() and not output.is_symlink() and output.stat().st_size > 0 and
                    result.get('olean_nonempty_regular') is True and
                    sha(output) == result.get('olean_sha256') and str(output) not in outputs,
                    'Missing, repeated or changed fresh native target object')
            outputs[str(output)] = sha(output)
        else: require(result.get('olean_sha256') is None and result.get('olean_nonempty_regular') is None,
                      'Unrequested optimized object claim')
        results.append(result)
    consumers = []
    for command in worker['commands']:
        consumers.append((command, Path(command['log'])))
    for label in ('frontend', 'core-d2'):
        component = worker['components'][label]
        mapping = component['mapping']; consumers.append((mapping, out / label / 'yosys.log'))
        for row in component['proof']['modules']:
            consumers.append((row, out / (label + '-proof') / (row['module'] + '.log')))
    used = []
    for consumer, log in consumers:
        index = consumer.get('native_journal_index')
        require(type(index) is int and 0 <= index < len(results), 'Native operation has no exact journal owner')
        row = results[index]; used.append(index)
        require(consumer.get('argv') == row['actual_argv'] and type(consumer.get('exit_code')) is int and
                consumer['exit_code'] == 0 and
                str(log.resolve()) == row['log'], 'Optimized consumer differs from its native journal')
        if 'log_sha256' in consumer:
            require(consumer['log_sha256'] == row['log_sha256'], 'Consumer native log identity differs')
    require(sorted(used) == list(range(len(results))), 'Duplicate or unaccounted optimized native operation')
    return binding
