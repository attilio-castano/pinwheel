#!/usr/bin/env python3
"""Freeze this campaign's accepted and failed receipts after independent Git checks.

Run only after the accepted gates close, from a commit containing this producer.
This exports receipts, not their large build trees, and does not rerun any gate.
"""
import argparse
import ast
from datetime import datetime, timezone
import gzip
import hashlib
import io
import json
from pathlib import Path, PurePosixPath
import re
import subprocess
import sys
import tarfile
import time
import types

ROOT = Path(__file__).resolve().parents[1]
DESTINATION = ROOT / 'docs/research/evidence/rtl-session-20261017'
BASE = 'cf8edbb2abc462e5a274a99240d62495f0ad7455'
DOCS = {
    'docs/protocols/buffered-spi-refinement.md':
        '805eba24279d4dd798c49f92aaaa146005475f9496cafdf393d9f5140aa66d59',
    'docs/research/status.md':
        'c669c35bf690df6c370da43dc6d2cfa6fa96fb3e56be0e9bd2d741a39fb198fe',
}
PATCH = 'efb3443f8103705eaeb222847c21750cdeeee5b0bde2ec0c3dea6d6eddef1108'
IMPORTS = {
    'import Pinwheel.Hardware.Buffered.ArtifactSelection',
    'import Pinwheel.Hardware.Buffered.SramArtifactReference',
    'import Pinwheel.Hardware.Buffered.ArtifactI2cTimingSession',
    'import Pinwheel.Hardware.Buffered.ArtifactTinyTapeoutI2cTimingSession',
    'import Pinwheel.Hardware.Buffered.ArtifactMixedSession',
}
FRONT = 'pinwheel.buffered-rtl-session.frontend.v1'
FULL = 'pinwheel.buffered-rtl-session.full.v1'
SIM = 'pinwheel.buffered-rtl-simulator.v1'


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def pairs_unique(items):
    result = {}
    for key, value in items:
        require(key not in result, 'Duplicate JSON key: ' + key)
        result[key] = value
    return result


def json_read(data):
    return json.loads(data, object_pairs_hook=pairs_unique)


def write_json(path, value):
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + '\n')


def flags(value, *keys):
    for key in keys:
        require(value.get(key) is True, 'Required true flag: ' + key)


def positive(value, *keys):
    for key in keys:
        require(type(value.get(key)) is int and value[key] > 0, 'Required positive count: ' + key)


def identity(value, prefix):
    flags(value, prefix + '_unchanged')
    before, after = value.get(prefix + '_before'), value.get(prefix + '_after')
    require(bool(before) and before == after, 'Identity closeout mismatch: ' + prefix)


def literal(source, name, function=False):
    for node in ast.parse(source).body:
        if not function and isinstance(node, ast.Assign):
            if any(isinstance(target, ast.Name) and target.id == name for target in node.targets):
                return ast.literal_eval(node.value)
        if function and isinstance(node, ast.FunctionDef) and node.name == name:
            returns = [item for item in node.body if isinstance(item, ast.Return)]
            require(len(returns) == 1, 'Expected literal return: ' + name)
            return ast.literal_eval(returns[0].value)
    raise RuntimeError('Missing committed literal: ' + name)


def bootstrap(out):
    """Verify all locally executed helper bytes before importing them."""
    records = []
    def call(argv, label):
        started = time.monotonic()
        result = subprocess.run(argv, cwd=ROOT, capture_output=True, timeout=30)
        (out / (label + '.log')).write_bytes(result.stdout + result.stderr)
        records.append(dict(label=label, argv=argv, exit_code=result.returncode,
                            seconds=round(time.monotonic() - started, 3)))
        require(result.returncode == 0, 'Bootstrap command failed: ' + label)
        return result.stdout
    head = call(['git', 'rev-parse', 'HEAD'], 'export-head').decode().strip()
    paths = ['scripts/export-rtl-session-evidence.py',
             'scripts/process_group.py', 'scripts/validation_run.py']
    payloads = {}
    for index, path in enumerate(paths):
        data = call(['git', 'show', head + ':' + path], 'export-producer-' + str(index))
        require(data == (ROOT / path).read_bytes(), 'Commit exporter/helper first: ' + path)
        payloads[path] = data
    for name in ('process_group', 'validation_run'):
        path = 'scripts/' + name + '.py'
        module = types.ModuleType(name)
        module.__file__ = str(ROOT / path)
        sys.modules[name] = module
        exec(compile(payloads[path], module.__file__, 'exec'), module.__dict__)
    return head, {path: sha(data) for path, data in payloads.items()}, records, sys.modules['validation_run']


class GitEvidence:
    def __init__(self, out, run):
        self.out, self.run, self.cache = out, run, {}
        self.algorithm = run(['git', 'rev-parse', '--show-object-format'], 'object-format').strip()
        require(self.algorithm in ('sha1', 'sha256'), 'Unsupported Git object format')
        self.serial = 0

    def archive(self, commit, paths=()):
        require(re.fullmatch(r'[0-9a-f]{40}|[0-9a-f]{64}', commit), 'Require full Git commit')
        key = (commit, tuple(sorted(paths)))
        if key not in self.cache:
            index = self.serial
            self.serial += 1
            actual = self.run(['git', 'rev-parse', '--verify', commit + '^{commit}'],
                              'commit-' + str(index)).strip()
            require(actual == commit, 'Commit does not resolve exactly')
            path = self.out / ('archive-' + str(index) + '.tar')
            argv = ['git', 'archive', '--format=tar', '--output', str(path), commit]
            if paths:
                argv += ['--', *sorted(paths)]
            self.run(argv, 'archive-' + str(index), timeout=180)
            files = {}
            with tarfile.open(path) as bundle:
                for member in bundle.getmembers():
                    if member.isfile():
                        require(member.name not in files, 'Repeated archive member')
                        files[member.name] = bundle.extractfile(member).read()
            self.cache[key] = dict(path=str(path.relative_to(ROOT)), sha256=sha(path.read_bytes()),
                                   files=files)
        return self.cache[key]

    def verify_map(self, commit, mapping, objects=None):
        require(isinstance(mapping, dict) and mapping, 'Missing input SHA256 map')
        archive = self.archive(commit)
        for name, expected in mapping.items():
            p = PurePosixPath(name)
            require(not p.is_absolute() and '..' not in p.parts, 'Unsafe input path')
            require(re.fullmatch(r'[0-9a-f]{64}', expected or ''), 'Malformed input hash: ' + name)
            data = archive['files'].get(name)
            require(data is not None and sha(data) == expected, 'Git archive/input mismatch: ' + name)
            if objects is not None:
                blob = hashlib.new(self.algorithm, b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
                require(objects.get(name) == blob, 'Git blob/input mismatch: ' + name)
        if objects is not None:
            require(set(objects) == set(mapping), 'Git object/input inventory mismatch')
        return dict(commit=commit, files=len(mapping), independently_verified=True,
                    git_blob_ids_verified=objects is not None,
                    full_tree_archive_sha256=archive['sha256'])

    def reproduce(self, commit, mapping, expected):
        require(re.fullmatch(r'[0-9a-f]{64}', expected or ''), 'Missing archive hash')
        full = self.archive(commit)
        if full['sha256'] == expected:
            return dict(scope='full Git tree', sha256=expected, reproduced=True)
        selected = self.archive(commit, mapping)
        require(selected['sha256'] == expected, 'Archive hash cannot be reproduced')
        return dict(scope='selected SHA256-map paths', paths=sorted(mapping),
                    sha256=expected, reproduced=True)


def controls(value, source, function, field, positive_field=None):
    expected = [row[0] for row in literal(source, function, function=True)]
    rows = value.get(field)
    require(isinstance(rows, list) and len(rows) == len(expected), 'Control inventory length: ' + field)
    require([row.get('name') for row in rows] == expected, 'Control names/order: ' + field)
    for row in rows:
        if field == 'wrapper_controls':
            flags(row, 'parsed', 'kernel_rejected')
        else:
            require(row.get('status') == 'passed' if field == 'mutations' else row.get('passed') is True,
                    'Control did not pass: ' + row['name'])
            unchanged = row['name'] == 'unchanged'
            require(row.get('expected_rejection') is (not unchanged), 'Control polarity mismatch')
            require(row.get(positive_field) is unchanged, 'Universal positive control mismatch')
    return len(rows)


def frontend(value, files, injected):
    require([value.get(key) for key in ('frontend_registers', 'frontend_state_bits', 'frontend_outputs')]
            == [13, 389, 19], 'Frontend endpoint census mismatch')
    positive(value, 'audited_declarations', 'audited_theorems')
    require(value.get('injected_axiom_rejections') == injected, 'Private axiom control mismatch')
    flags(value, 'proof_inputs_unchanged')
    require(value.get('proof_dependency_closure'), 'Missing frontend proof closure')
    require(value.get('proof_input_sha256_before') and
            value['proof_input_sha256_before'] == value.get('proof_input_sha256_after'),
            'Frontend proof input closeout mismatch')
    return controls(value, files['scripts/buffered_serial_readback.py'], 'mutation_specs',
                    'mutations', 'all_state_reimport')


def contract(kind, accepted, report, files):
    require(report.get('passed') is accepted, 'Receipt acceptance mismatch: ' + kind)
    if kind in ('full', 'frontend'):
        require(report.get('schema') == (FULL if kind == 'full' else FRONT), 'Receipt schema mismatch')
        require(report.get('mode') == kind, 'Receipt mode mismatch')
        require(report.get('full_session_proved') is (accepted and kind == 'full'), 'Full-session flag mismatch')
    if not accepted:
        require(isinstance(report.get('error'), str) and report['error'], 'Failed receipt needs error')
        return dict(schema=report.get('schema'), accepted=False, failure=report['error'])
    flags(report, 'passed')
    result = dict(schema=report.get('schema'), accepted=True)
    if kind in ('full', 'frontend'):
        flags(report, 'committed_input_membership_verified_before', 'committed_input_membership_verified_after')
        identity(report, 'tool_identity')
        worker = report.get('worker', {})
        flags(worker, 'passed', 'archived_inputs_unchanged', 'tool_identity_unchanged', 'proof_inputs_unchanged')
        require(worker.get('standalone_qualification') is False, 'Standalone worker cannot qualify')
        for key in ('schema', 'source_commit', 'source_sha256', 'required_targets', 'full_session_proved'):
            require(worker.get(key) == report.get(key), 'Coordinator/worker mismatch: ' + key)
        positive(worker, 'audited_declarations', 'audited_theorems')
        require(worker.get('injected_axiom_rejections') == 1, 'Missing one private axiom refusal')
        require(worker.get('proof_input_sha256_before') and
                worker['proof_input_sha256_before'] == worker.get('proof_input_sha256_after'),
                'Worker proof input closeout mismatch')
        path = 'scripts/buffered_rtl_session_full.py' if kind == 'full' else 'scripts/check-buffered-rtl-session.py'
        targets = literal(files[path], 'FULL_TARGETS' if kind == 'full' else 'REQUIRED_TARGETS')
        require(report.get('required_targets') == list(targets), 'Incomplete committed target inventory')
        if kind == 'frontend':
            result['frontend_controls'] = frontend(worker, files, 1)
        else:
            require(worker.get('full_proof_dependency_closure'), 'Missing full proof dependency closure')
            result['frontend_controls'] = frontend(worker.get('frontend', {}), files, 0)
            c = worker.get('controller', {})
            require([c.get(k) for k in ('registers', 'register_bits', 'outputs')] == [117, 3151, 31],
                    'Controller endpoint census mismatch')
            flags(c, 'typed_source_bridge', 'complete_reference_graph_validated')
            result['controller_controls'] = controls(worker, files['scripts/buffered_sram_mutations.py'],
                'mutation_specs', 'controller_controls', 'universal_all_field_reimport')
            result['wrapper_controls'] = controls(worker, files['scripts/artifact_wrapper_readback.py'],
                'corruption_cases', 'wrapper_controls')
        result.update(audited_declarations=worker['audited_declarations'],
                      audited_theorems=worker['audited_theorems'], required_targets=list(targets))
    elif kind == 'foundation':
        require('schema' not in report, 'Unexpected legacy foundation schema')
        flags(report, 'committed_input_membership_verified', 'untrusted_axiom_rejected')
        require(report.get('exit_code') == 0, 'Foundation command failed')
        positive(report, 'modules', 'audited_declarations', 'audited_theorems')
        source = files['scripts/check-foundation.py']
        for key, literal_name in [('executable_suites', 'SUITES'), ('kernel_suites', 'KERNEL_SUITES')]:
            require(report.get(key) == len(literal(source, literal_name)), 'Foundation suite inventory mismatch')
        require('version 4.33.1' in report.get('lean', ''), 'Foundation Lean version mismatch')
        result.update(legacy_contract=True, modules=report['modules'],
                      audited_declarations=report['audited_declarations'], audited_theorems=report['audited_theorems'],
                      executable_suites=report['executable_suites'], kernel_suites=report['kernel_suites'])
    elif kind == 'python':
        require(report.get('schema') == 'pinwheel.python-snapshot.v1', 'Python schema mismatch')
        flags(report, 'producer_membership_verified_before', 'producer_membership_verified_after',
              'committed_archive_membership_verified_before', 'committed_archive_membership_verified_after',
              'python_identity_unchanged')
        require(bool(report.get('python_before')) and report.get('python_before') == report.get('python_after'),
                'Python identity mismatch')
        suite = report.get('unittest', {})
        positive(suite, 'tests_run')
        require(type(suite.get('skipped')) is int and suite['skipped'] == len(suite.get('skips', [])),
                'Python skip inventory mismatch')
        require(re.search(r'^OK(?: \(skipped=\d+\))?$', suite.get('summary', ''), re.M), 'Missing unittest success')
        summary_count = re.search(r'^Ran (\d+) tests? in ', suite['summary'], re.M)
        require(summary_count and int(summary_count[1]) == suite['tests_run'], 'Unittest summary count mismatch')
        summary_skips = re.search(r'^OK \(skipped=(\d+)\)$', suite['summary'], re.M)
        require((int(summary_skips[1]) if summary_skips else 0) == suite['skipped'], 'Unittest summary skips mismatch')
        tail = ['-B', '-m', 'unittest', 'discover', '-s', 'test', '-p', 'test_*.py']
        require(any([arg for arg in row.get('argv', [])[1:] if arg != '-v'] == tail and row.get('exit_code') == 0
                    for row in report.get('commands', [])), 'Missing complete unittest discover command')
        result['unittest'] = suite
    elif kind == 'simulator':
        require(report.get('schema') == SIM, 'Simulator schema mismatch')
        flags(report, 'committed_archive_membership_verified_before', 'committed_archive_membership_verified_after')
        identity(report, 'tool_identity')
        worker = report.get('worker', {})
        for key in ('schema', 'source_commit', 'producer_commit'):
            require(worker.get(key) == report.get(key), 'Simulator worker mismatch: ' + key)
        flags(worker, 'passed', 'archived_inputs_unchanged', 'producer_unchanged',
              'tool_identity_unchanged', 'frozen_artifacts_unchanged')
        replay = worker.get('frontend_replay', {})
        positive(replay, 'cases', 'edges', 'pre_output_checks', 'post_output_checks', 'register_checks')
        peers = worker.get('public_pin_peers', {})
        require([peers.get(k) for k in ('cases', 'spi_cases', 'jtag_cases', 'i2c_cases')] == [3, 1, 1, 1],
                'Protocol peer inventory mismatch')
        positive(peers, 'physical_edges', 'requests', 'responses', 'zero_poll_timeouts')
        require(peers['requests'] == peers['responses'], 'Peer response count mismatch')
        flags(peers, 'results_retained_twice')
        results = peers.get('peer_results', [])
        require(len(results) == 3 and all(row.get('outcome') == 'complete' for row in results),
                'Incomplete protocol peer outcome')
        memory = worker.get('memory_model', {})
        require(memory.get('macro_qualified') is False and len(set(memory.get('initial_bank_q', []))) == 2,
                'Simulator digital memory boundary mismatch')
        require(all(word in memory.get('law', '') for word in ('synchronous', 'write-priority', 'hold Q')),
                'Missing simulator memory law')
        result.update(frontend_replay=replay, public_pin_peers=peers, memory_model=memory)
    else:
        raise RuntimeError('Unknown receipt kind')
    return result


def input_difference(mapping, read):
    different, missing, matches = {}, [], 0
    for name, expected in mapping.items():
        data = read(name)
        if data is None:
            missing.append(name)
        elif sha(data) == expected:
            matches += 1
        else:
            different[name] = dict(receipt_sha256=expected, current_sha256=sha(data))
    return dict(matches=matches, different=different, missing=missing,
                assertion='Differences recorded; historical inputs are not asserted current.')


def workspace_difference(mapping):
    return input_difference(mapping, lambda name: (ROOT / name).read_bytes() if (ROOT / name).is_file() else None)


def sv_correspondence(full_tag, full, sim_tag, simulator):
    records, frozen = [], {}
    for component, full_name, sim_name in (
            ('frontend', 'worker/frontend/emitted/frontend.sv', 'frontend.sv'),
            ('controller', 'worker/controller/emitted/core.sv', 'controller.sv')):
        expected = full.get('artifact_sha256', {}).get(full_name)
        actual = simulator.get('worker', {}).get('artifact_sha256', {}).get(sim_name)
        require(re.fullmatch(r'[0-9a-f]{64}', expected or '') and expected == actual,
                'Final full/simulator SV receipt hash mismatch: ' + component)
        full_path = ROOT / 'build/validation' / full_tag / full_name
        sim_path = ROOT / 'build/validation' / sim_tag / 'worker' / sim_name
        for path in (full_path, sim_path):
            require(path.is_file() and sha(path.read_bytes()) == expected,
                    'Retained component SV bytes mismatch: ' + str(path))
            frozen[path] = expected
        records.append(dict(component=component, sha256=expected, retained_bytes_verified=True,
                            full_artifact=str(full_path.relative_to(ROOT)),
                            simulator_artifact=str(sim_path.relative_to(ROOT))))
    return records, frozen


def intake_and_semantics(git, head, run):
    intake_path = ROOT / 'build/rtl-session-20261017/intake.json'
    intake = json_read(intake_path.read_bytes())
    require(intake.get('base') == BASE and intake.get('preexisting_dirty_sha256') == DOCS and
            intake.get('preexisting_dirty_patch_sha256') == PATCH, 'Intake claims differ')
    for name, expected in DOCS.items():
        require(sha((ROOT / name).read_bytes()) == expected, 'Original dirty document changed: ' + name)
    patch_file = ROOT / 'build/rtl-session-20261017/preexisting-doc-changes.patch'
    require(sha(patch_file.read_bytes()) == PATCH, 'Original intake patch changed')
    # Git's patch bytes are text; there are no non-UTF8 bytes in these two documents.
    patch = run(['git', 'diff', '--', *DOCS], 'intake-current-patch').encode()
    require(sha(patch) == PATCH, 'Current dirty document patch changed')
    base_files, current = git.archive(BASE)['files'], git.archive(head)['files']
    for name, data in base_files.items():
        if name == 'Pinwheel.lean':
            continue
        require(current.get(name) == data, 'Preexisting committed file changed: ' + name)
        if name not in DOCS:
            require((ROOT / name).is_file() and (ROOT / name).read_bytes() == data,
                    'Preexisting workspace file changed: ' + name)
    old, new = base_files['Pinwheel.lean'].decode().splitlines(), current['Pinwheel.lean'].decode().splitlines()
    require([line for line in new if line not in IMPORTS] == old and
            {line for line in new if line in IMPORTS} == IMPORTS, 'Default import change exceeds five proof imports')
    require((ROOT / 'Pinwheel.lean').read_bytes() == current['Pinwheel.lean'], 'Default imports changed in workspace')
    return dict(base=BASE, original_files_verified=len(base_files),
                only_original_committed_change='Pinwheel.lean: five proof imports',
                dirty_docs_sha256=DOCS, dirty_patch_sha256=PATCH,
                intake_sha256=sha(intake_path.read_bytes()))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--tag', required=True, help='Fresh retained exporter log directory tag')
    parser.add_argument('--full-tag', default='buffered-rtl-session-full-20261017-02')
    parser.add_argument('--python-tag', default='rtl-session-python-dc53ceb')
    args = parser.parse_args()
    for tag in (args.tag, args.full_tag, args.python_tag):
        require(re.fullmatch(r'[A-Za-z0-9_-]+', tag), 'Unsafe evidence tag')
    require(not DESTINATION.exists(), 'Preserve existing evidence; destination must be fresh')
    out = ROOT / 'build/validation' / args.tag
    out.mkdir(parents=True, exist_ok=False)
    head, producer_hashes, bootstrap_records, helper = bootstrap(out)
    logs = out / 'logs'
    logs.mkdir()
    run = helper.Commands(ROOT, logs, default_timeout=60)
    git = GitEvidence(out, run)
    specs = [
        ('full', args.full_tag, True),
        ('foundation', 'rtl-session-foundation-20261017-01', True),
        ('python', args.python_tag, True),
        ('simulator', 'buffered-rtl-sim-20261017-01', True),
        ('frontend', 'buffered-rtl-frontend-20261017-02', True),
        ('frontend', 'buffered-rtl-frontend-20261017-01', False),
        ('full', 'buffered-rtl-session-full-20261017-01', False),
    ]
    require(len({tag for _, tag, _ in specs}) == len(specs), 'Accepted and failed receipt tags overlap')
    manifest = dict(schema='pinwheel.rtl-session-evidence.v1',
        exported_utc=datetime.now(timezone.utc).isoformat(), producer_commit=head,
        producer_sha256=producer_hashes, log_directory=str(out.relative_to(ROOT)),
        source_membership='Each receipt checked independently against its own Git commit archive.',
        boundary='Exact receipts and committed inputs verified; gates and artifact trees are not rerun or recopied. '
                 'Receipt tool/closeout assertions are checked, not a fresh installed-tool payload qualification. '
                 'Digital two-state RTL and explicit memory laws; no macro, electrical, mapped/physical or compiler proof.',
        receipts=[], compatibility=[])
    frozen, maps, accepted_reports = {}, [], {}
    staging = out / 'export'
    staging.mkdir()
    try:
        for kind, tag, accepted in specs:
            path = ROOT / 'build/validation' / tag / 'report.json'
            raw = path.read_bytes()
            report = json_read(raw)
            commit = report.get('source_commit')
            source_map = report.get('source_sha256')
            verified = git.verify_map(commit, source_map, report.get('selected_git_objects'))
            files = git.archive(commit)['files']
            base_files = git.archive(BASE)['files']
            for name, data in base_files.items():
                if name != 'Pinwheel.lean':
                    require(files.get(name) == data, 'Receipt source changed original file: ' + name)
            verified['original_files_match_campaign_base'] = len(base_files) - 1
            item = dict(tag=tag, kind=kind, accepted=accepted, source_commit=commit,
                        original_receipt=str(path.relative_to(ROOT)), raw_sha256=sha(raw), raw_bytes=len(raw),
                        source_verification=verified, contract=contract(kind, accepted, report, files),
                        workspace_inputs=workspace_difference(source_map),
                        current_head_inputs=input_difference(source_map, git.archive(head)['files'].get),
                        archive_verification={})
            archive_key = 'selected_archive_sha256' if kind == 'simulator' else 'snapshot_archive_sha256'
            item['archive_verification'][archive_key] = git.reproduce(commit, source_map, report.get(archive_key))
            if 'producer_sha256' in report:
                producer_commit, producer_map = report.get('producer_commit'), report['producer_sha256']
                item['producer_commit'] = producer_commit
                item['producer_verification'] = git.verify_map(producer_commit, producer_map,
                                                               report.get('producer_git_objects'))
                item['workspace_producer_inputs'] = workspace_difference(producer_map)
                item['current_head_producer_inputs'] = input_difference(producer_map, git.archive(head)['files'].get)
                if 'producer_archive_sha256' in report:
                    item['archive_verification']['producer_archive_sha256'] = git.reproduce(
                        producer_commit, producer_map, report['producer_archive_sha256'])
            if kind == 'foundation':
                require(report.get('driver_sha256') == sha(files['scripts/check-foundation-snapshot.py']),
                        'Foundation driver is not its reported committed version')
                item['driver_verified'] = True
            for previous_tag, previous_commit, previous_map in maps:
                overlap = sorted(set(source_map) & set(previous_map))
                differences = [name for name in overlap if source_map[name] != previous_map[name]]
                if commit == previous_commit:
                    require(not differences, 'Same-commit overlapping source hashes conflict')
                manifest['compatibility'].append(dict(left=previous_tag, right=tag,
                    same_source_commit=commit == previous_commit, overlapping_inputs=len(overlap),
                    different_inputs=differences))
            maps.append((tag, commit, source_map))
            stream = io.BytesIO()
            with gzip.GzipFile(fileobj=stream, filename='', mode='wb', mtime=0, compresslevel=9) as zipped:
                zipped.write(raw)
            compressed = stream.getvalue()
            require(gzip.decompress(compressed) == raw, 'Receipt compression round trip failed')
            filename = tag + '.json.gz'
            (staging / filename).write_bytes(compressed)
            item.update(file=filename, compressed_bytes=len(compressed), compressed_sha256=sha(compressed))
            manifest['receipts'].append(item)
            frozen[path] = sha(raw)
            if accepted:
                accepted_reports[kind] = (tag, report)
        full_tag, full_report = accepted_reports['full']
        sim_tag, sim_report = accepted_reports['simulator']
        correspondence, component_files = sv_correspondence(full_tag, full_report, sim_tag, sim_report)
        manifest['full_simulator_sv_correspondence'] = correspondence
        frozen.update(component_files)
        manifest['frozen_semantics'] = intake_and_semantics(git, head, run)
        require(run(['git', 'rev-parse', 'HEAD'], 'closeout-head').strip() == head, 'HEAD changed during export')
        for name, expected in producer_hashes.items():
            require(sha((ROOT / name).read_bytes()) == expected, 'Exporter producer changed')
        for path, expected in frozen.items():
            require(sha(path.read_bytes()) == expected, 'Receipt/component changed during export')
        for item in manifest['receipts']:
            compressed = (staging / item['file']).read_bytes()
            require(len(compressed) == item['compressed_bytes'] and sha(compressed) == item['compressed_sha256'],
                    'Staged gzip changed during export')
            raw = gzip.decompress(compressed)
            require(len(raw) == item['raw_bytes'] and sha(raw) == item['raw_sha256'] and
                    raw == (ROOT / item['original_receipt']).read_bytes(), 'Staged receipt round trip failed')
        manifest['workspace_git_status'] = run(['git', 'status', '--porcelain=v1', '--untracked-files=normal'],
                                               'workspace-status')
        manifest['bootstrap_commands'], manifest['commands'] = bootstrap_records, run.records
        write_json(staging / 'manifest.json', manifest)
        require(not DESTINATION.exists(), 'Evidence destination appeared during export')
        DESTINATION.parent.mkdir(parents=True, exist_ok=True)
        staging.rename(DESTINATION)
        write_json(out / 'export-summary.json', dict(passed=True, destination=str(DESTINATION.relative_to(ROOT)),
            manifest_sha256=sha((DESTINATION / 'manifest.json').read_bytes()), producer_commit=head,
            producer_sha256=producer_hashes, receipt_count=len(specs), log_directory=str(out.relative_to(ROOT))))
    except BaseException as error:
        write_json(out / 'export-failed.json', dict(passed=False, error=type(error).__name__ + ': ' + str(error),
            producer_commit=head, producer_sha256=producer_hashes,
            bootstrap_commands=bootstrap_records, commands=run.records))
        raise
    print('Evidence exported: ' + str(DESTINATION), flush=True)


if __name__ == '__main__':
    main()
