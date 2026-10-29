"""Explicit HOST relocation audit of the immutable completed 649 foundation.

Original reports retain their original paths and bytes. This new receipt maps
each consumed authority to recovered bytes, checks the committed source bridge,
and stages only the positive library. It launches no recovered executable or
Lean process and grants no actual final-netlist proof acceptance.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import io
import json
from pathlib import Path
import re
import shutil
import subprocess
import tarfile
import time

import streaming_tt_fresh_foundation as F
import streaming_8x4_final_runtime as R

ROOT = Path(__file__).resolve().parents[1]
OLD = Path('/Users/attiliocastano/.codex/worktrees/1373/pinwheel')
FOUNDATION = 'build/validation/renewal-foundation-649-03'
RUNTIME = 'build/streaming-tt-foundation/renewal-foundation-649-03'
BINDING = 'build/validation/streaming-tt-balanced-raw-02/fresh-foundation-binding.json'
PINS = dict(
    foundation='81fd894827acd13248bc2f1f12851c35fa87ff342176a796781dd9128f288379',
    runtime='e20245ec401769745a17a59beec4170ef058692262c711366bc5cdcea01fdb0e',
    binding='86e11c97941abcebc2185eed4a3bc24253d4fdf28b40a3965716a1208f5cc73f')
SOURCES = ('scripts/streaming_8x4_foundation.py', 'scripts/streaming_tt_fresh_foundation.py',
           'scripts/streaming_8x4_final_runtime.py')


def need(ok, message):
    if not ok:
        raise ValueError(message)


def bound(original, actual, expected=None):
    actual = R.regular(actual).resolve()
    value = R.digest(actual)
    need(expected is None or value == expected, 'Recovered authority bytes differ: ' + str(original))
    return dict(original_path=str(original), path=str(actual), sha256=value)


def check_foundation(record):
    need(record.get('passed') is True and record.get('modules') == 649 and
         record.get('serial_build') is True and record.get('committed_input_membership_verified') is True and
         record.get('inherited_override_guard_checked') is True and
         type(record.get('exit_code')) is int and record['exit_code'] == 0 and
         record.get('lean_resource_limits') == ['-M4096', '-j1', '-DElab.async=false'] and
         record.get('executable_suites') == 65 and record.get('kernel_suites') == 8 and
         record.get('untrusted_axiom_rejected') is True and record.get('unused_private_axiom_rejected') is True and
         type(record.get('audited_declarations')) is int and record['audited_declarations'] > 0 and
         type(record.get('audited_theorems')) is int and record['audited_theorems'] > 0,
         'Historical foundation is incomplete or lacks its original controls')
    need(record.get('retained_snapshot') == str(OLD / FOUNDATION / 'snapshot') and
         record.get('retained_library') == str(OLD / FOUNDATION / 'snapshot/.lake/build/lib/lean'),
         'Historical retained source/library authority changed')


def check_commands(record, modules, logs):
    commands = record['commands']
    builds = [row for row in commands if row['label'].startswith('build-')]
    need([row['label'][6:] for row in builds] == modules and
         all(type(row.get('exit_code')) is int and row['exit_code'] == 0 for row in builds),
         'Historical source compilation is missing, reordered or failed')
    rejects = {'reject-untrusted-axiom', 'reject-unused-private-axiom'}
    need(len({row['label'] for row in commands}) == len(commands) and
         all(type(row.get('exit_code')) is int for row in commands) and
         {row['label'] for row in commands if row['exit_code'] != 0} == rejects,
         'Historical positive/private-control command outcomes differ')
    summary = (f"Pinwheel audit: {record['audited_declarations']} declarations, "
               f"{record['audited_theorems']} theorems; standard axioms only.")
    need(summary in logs['axioms'], 'Historical whole-library audit summary differs')
    need('Unapproved axioms in Pinwheel.CI.untrusted' in logs['reject-untrusted-axiom'],
         'Untrusted-axiom control failed for an unrelated reason')
    private = logs['reject-unused-private-axiom']
    need('Unapproved axioms in _private.Pinwheel.CI.FoundationPrivateControl.' in private and
         'forbiddenUnused' in private, 'Unused-private-axiom control failed for an unrelated reason')


def committed_projection(commit, projection):
    need(re.fullmatch('[0-9a-f]{40}', commit) is not None, 'Exact committed projection required')
    for name, expected in projection.items():
        F.relative(name)
        need(R.digest(ROOT / name) == expected, 'Current foundation/runtime input changed: ' + name)
    result = subprocess.run(['git', 'archive', '--format=tar', commit, *sorted(projection)], cwd=ROOT,
                            capture_output=True, timeout=60, check=True)
    actual = {}
    with tarfile.open(fileobj=io.BytesIO(result.stdout), mode='r:') as archive:
        for item in archive:
            if item.isdir():
                continue
            need(item.isfile() and item.name in projection and item.name not in actual,
                 'Committed projection has an extra, aliased or duplicate member')
            stream = archive.extractfile(item)
            need(stream is not None, 'Unreadable committed source projection')
            with stream:
                actual[item.name] = hashlib.file_digest(stream, 'sha256').hexdigest()
    need(actual == projection, 'Committed foundation/runtime source projection differs')


def verify_runtime(record, runtime_root, foundation_binding, snapshot, recovery, tools):
    need(record.get('schema') == 'pinwheel.streaming-tt-fresh-foundation-runtime.v1' and
         record.get('passed') is True and record.get('status') == 'completed' and
         type(record.get('exit_code')) is int and record['exit_code'] == 0 and
         record.get('timed_out') is False and record.get('native_process_group_closed') is True and
         record.get('inputs_unchanged') is True and record.get('sources_unchanged') is True and
         record.get('foundation_complete_649') is True and record.get('runtime_unchanged') is True and
         record.get('runtime_files') == 14923 and
         record.get('foundation_receipt') == foundation_binding['original_path'] and
         record.get('foundation_receipt_sha256') == foundation_binding['sha256'],
         'Original foundation runtime did not close against the exact foundation')
    relocated = []
    maps = []
    for label in ('runtime_before', 'runtime_after'):
        original = record[label]
        need(original['path'] == str(OLD / RUNTIME / ('runtime-' + label[8:] + '.json')),
             'Unexpected original runtime identity map authority')
        pair = bound(original['path'], runtime_root / Path(original['path']).name, original['sha256'])
        relocated.append(pair)
        maps.append(R.read(pair['path']))
    need(maps[0] == maps[1] and len(maps[0]) == 14923, 'Historical full runtime identity changed')
    before = maps[0]
    for name, value in before.items():
        item = Path(name)
        need(item.is_absolute() and item.is_file() and str(item.resolve()) == value['resolved'] and
             item.stat().st_size == value['bytes'] and F.sha(item) == value['sha256'],
             'Current complete foundation runtime differs: ' + name)
    prefix = Path(tools['lean']).parent.parent
    library = prefix / 'lib/lean'
    need(not any(path.is_symlink() and path.is_dir() for path in library.rglob('*')) and
         {str(path) for path in library.rglob('*') if path.is_file()} ==
         {name for name in before if Path(name).is_relative_to(library)},
         'Current complete compiled Lean runtime membership differs')
    for name in ('lean', 'lake'):
        path = R.regular(tools[name])
        need(str(path) in before and before[str(path)]['sha256'] == R.digest(path),
             'Selected compiler differs from original foundation runtime')
    auxiliary = {
        str(OLD / 'scripts/run-streaming-tt-foundation.py'): snapshot / 'scripts/run-streaming-tt-foundation.py',
        str(OLD / 'build/streaming-tt-recovery/final-runtime-identity-01/report.json'):
            recovery / 'final-foundation-runtime-intake/build/streaming-tt-recovery/final-runtime-identity-01/report.json',
        str(OLD / 'build/streaming-tt-recovery/foundation-runtime-01/before.json'):
            recovery / 'final-foundation-runtime-prior/build/streaming-tt-recovery/foundation-runtime-01/before.json',
        str(OLD / 'build/streaming-physical-development/frozen-formal-f241b39-unqualified-01/toolchain-seal.json'):
            recovery / 'final-foundation-toolchain-seal/build/streaming-physical-development/frozen-formal-f241b39-unqualified-01/toolchain-seal.json',
    }
    need(set(record['input_sha256']) == set(auxiliary), 'Historical runtime observer input membership differs')
    for name, expected in record['input_sha256'].items():
        relocated.append(bound(name, auxiliary[name], expected))
    native = bound(OLD / RUNTIME / 'native.log', runtime_root / 'native.log', record['native_log_sha256'])
    relocated.append(native)
    return relocated


def audit(recovery, runtime_audit, output):
    started = time.monotonic()
    recovery = Path(recovery).resolve(strict=True)
    output = Path(output).absolute()
    need(not output.exists(), 'Preserve earlier relocated foundation audits')
    commit = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True, timeout=30).strip()
    sources = {name: R.digest(ROOT / name) for name in SOURCES}
    committed_projection(commit, sources)
    selected_runtime = R.closed_report(runtime_audit)
    tools = {key: selected_runtime['tools'][key] for key in ('lean', 'lake', 'python')}
    inputs = dict(
        foundation=bound(OLD / FOUNDATION / 'report.json',
            recovery / 'final-foundation-validation' / FOUNDATION / 'report.json', PINS['foundation']),
        runtime=bound(OLD / RUNTIME / 'report.json',
            recovery / 'final-foundation-runtime' / RUNTIME / 'report.json', PINS['runtime']),
        binding=bound(OLD / BINDING, recovery / 'final-foundation-binding' / BINDING, PINS['binding']))
    output.mkdir(parents=True)
    report = dict(schema='pinwheel.streaming-8x4-relocated-foundation.v1', passed=False, qualified=False,
        native_executed=False, historical_foundation_reused=False, candidate_commit=commit,
        producer_sha256=sources, original_foundation_report=inputs['foundation'],
        original_runtime_report=inputs['runtime'], original_binding=inputs['binding'],
        selected_runtime_audit=bound(str(runtime_audit), runtime_audit), tools=tools,
        boundary='Explicit same-source historical foundation reuse, no fresh historical execution. Actual M, whole-M audit, private controls and public-wire acceptance remain separate.')
    try:
        foundation = R.read(inputs['foundation']['path'])
        runtime = R.read(inputs['runtime']['path'])
        binding = R.read(inputs['binding']['path'])
        check_foundation(foundation)
        need(runtime['source_commit'] == foundation['source_commit'], 'Original runtime/source commits differ')
        snapshot = recovery / 'final-foundation-validation' / FOUNDATION / 'snapshot'
        modules = F.module_order(snapshot)
        need(len(modules) == 649 and F.module_order(ROOT) == modules, 'Current/retained whole-library module membership differs')
        projection = foundation['source_sha256']
        expected = set(F.FOUNDATION_INPUTS) | {path.relative_to(snapshot).as_posix()
            for directory, pattern in (('Pinwheel', '**/*.lean'), ('test', '*.lean'))
            for path in (snapshot / directory).glob(pattern)}
        need(set(projection) == expected, 'Historical consumed-source projection is incomplete or unexpected')
        for name, value in projection.items():
            need(R.digest(snapshot / name) == value, 'Retained consumed source changed: ' + name)
        committed_projection(commit, projection)
        need(runtime.get('committed_input_sha256'), 'Missing complete runtime producer projection')
        committed_projection(commit, runtime['committed_input_sha256'])
        logs = {}
        log_bindings = {}
        expected_logs = binding['foundation_native_log_sha256']
        need(set(expected_logs) == {str(OLD / FOUNDATION / (row['label'] + '.log'))
                                   for row in foundation['commands']},
             'Immutable binding omits or adds historical native logs')
        for row in foundation['commands']:
            name = row['label']
            need(re.fullmatch('[A-Za-z0-9_.-]+', name) is not None, 'Unsafe historical command label')
            path = Path(inputs['foundation']['path']).parent / (name + '.log')
            original_log = OLD / FOUNDATION / (name + '.log')
            log_bindings[name] = bound(original_log, path, expected_logs[str(original_log)])
            if name in ('axioms', 'reject-untrusted-axiom', 'reject-unused-private-axiom'):
                logs[name] = path.read_text()
        check_commands(foundation, modules, logs)
        original_library = snapshot / '.lake/build/lib/lean'
        artifacts = F.manifest(original_library)
        need(artifacts == foundation['retained_library_artifact_sha256'], 'Complete historical library bytes changed')
        positive, negative = F.partition_library(modules, artifacts, foundation['retained_private_control_module'])
        need(binding.get('schema') == F.SCHEMA and binding.get('modules') == modules and
             binding.get('foundation_report') == dict(path=inputs['foundation']['original_path'], sha256=PINS['foundation']) and
             binding.get('runtime_report') == dict(path=inputs['runtime']['original_path'], sha256=PINS['runtime']) and
             binding.get('foundation_source_projection') == projection and
             binding.get('positive_library_artifact_sha256') == positive and
             binding.get('excluded_negative_control_artifact_sha256') == negative and
             binding.get('foundation_library') == foundation['retained_library'],
             'Immutable old binding differs from its original source/runtime/library authorities')
        relocated_runtime = verify_runtime(runtime, Path(inputs['runtime']['path']).parent,
                                           inputs['foundation'], snapshot, recovery, tools)
        target = output / 'positive-library'
        for name, value in positive.items():
            destination = target / F.relative(name)
            destination.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(original_library / name, destination)
        need(F.manifest(target) == positive and not (target / F.CONTROL).exists(),
             'Positive library staging changed membership or imported the private negative control')
        need(F.manifest(original_library) == artifacts and
             all(R.digest(row['path']) == row['sha256'] for row in inputs.values()) and
             all(R.digest(row['path']) == row['sha256'] for row in relocated_runtime) and
             all(R.digest(row['path']) == row['sha256'] for row in log_bindings.values()),
             'Original authority changed during relocation audit')
        committed_projection(commit, projection)
        need({name: R.digest(ROOT / name) for name in SOURCES} == sources, 'Relocation audit producer changed')
        need(verify_runtime(runtime, Path(inputs['runtime']['path']).parent,
                            inputs['foundation'], snapshot, recovery, tools) == relocated_runtime,
             'Complete current foundation runtime or auxiliary custody changed during audit')
        report.update(passed=True, historical_foundation_reused=True, module_order=modules, source_projection_sha256=projection,
            runtime_producer_projection_sha256=runtime['committed_input_sha256'],
            positive_library=dict(path=str(target), artifact_sha256=positive),
            excluded_negative_control_artifact_sha256=negative,
            current_projection_identical=True, runtime_identity_unchanged=True,
            runtime_files=14923, historical_native_log_bindings=log_bindings,
            explicit_runtime_relocations=relocated_runtime,
            input_sha256={row['path']: row['sha256'] for row in
                          list(inputs.values()) + relocated_runtime + list(log_bindings.values())})
    except (ValueError, OSError, KeyError, TypeError, subprocess.SubprocessError) as error:
        report['error'] = type(error).__name__ + ': ' + str(error)
    report.update(completed_utc=datetime.now(timezone.utc).isoformat(), elapsed_seconds=round(time.monotonic() - started, 3))
    R.write(output / 'report.json', report)
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--recovery', type=Path, required=True)
    parser.add_argument('--runtime-audit', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    report = audit(args.recovery, args.runtime_audit, args.output)
    print(json.dumps({key: report.get(key) for key in ('schema', 'passed', 'qualified', 'elapsed_seconds', 'error')}))
    return 0 if report['passed'] else 1


if __name__ == '__main__':
    raise SystemExit(main())
