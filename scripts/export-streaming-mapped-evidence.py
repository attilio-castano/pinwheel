#!/usr/bin/env python3
"""Freeze accepted mapped receipts without rerunning a validation gate.

The full mapped, foundation and Python receipts must share one committed source.
Their actual retained artifacts, fresh raw-input stage, native journals, proof
closure and costs are rechecked. Prior qualified evidence is never rewritten.
"""
import argparse
from copy import deepcopy
from datetime import datetime, timezone
import gzip
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import time
import types

ROOT = Path(__file__).resolve().parents[1]
DRIVER = 'scripts/export-streaming-mapped-evidence.py'
SHARED = 'scripts/export-streaming-uart-evidence.py'
GIT_HELPER = 'scripts/export-rtl-session-evidence.py'
PRODUCER = (DRIVER, SHARED, GIT_HELPER, 'scripts/process_group.py',
    'scripts/validation_run.py', 'test/test_streaming_mapped_evidence.py')
BASE = '3dfbc7cbe7f6d0ca64dd7b8b5392f4fa1c02cde2'
DESTINATION = 'docs/research/evidence/streaming-mapped-continuation-20261017'
SCHEMA = 'pinwheel.streaming-mapped-evidence.v1'
FULL_SCHEMA = 'pinwheel.streaming-mapped-full.v1'
LIBRARY = '34163f3e7de9f854afac57332ba06f1739b78e7ac35660a8a5ddd39c570124ad'
DOCS = {'docs/protocols/buffered-spi-refinement.md':
    '805eba24279d4dd798c49f92aaaa146005475f9496cafdf393d9f5140aa66d59',
    'docs/research/status.md': 'c669c35bf690df6c370da43dc6d2cfa6fa96fb3e56be0e9bd2d741a39fb198fe'}
PATCH = 'efb3443f8103705eaeb222847c21750cdeeee5b0bde2ec0c3dea6d6eddef1108'


def require(value, message):
    if not value: raise RuntimeError(message)


def sha(data): return hashlib.sha256(data).hexdigest()


def digest(path):
    value = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b''): value.update(block)
    return value.hexdigest()


def read_json(data):
    def pairs(items):
        result = {}
        for key, value in items:
            require(key not in result, 'Duplicate evidence JSON key: ' + key)
            result[key] = value
        return result
    return json.loads(data, object_pairs_hook=pairs)


def write_json(path, value): Path(path).write_text(json.dumps(value, indent=2, sort_keys=True) + '\n')


def same_source(reports):
    require(set(reports) == {'full', 'foundation', 'python'}, 'All three accepted receipts are mandatory')
    require(all(type(value) is dict and value.get('passed') is True and
        type(value.get('source_commit')) is str for value in reports.values()), 'Missing accepted source identity')
    commits = {value['source_commit'] for value in reports.values()}
    require(len(commits) == 1, 'Receipts use different final source commits')
    commit = next(iter(commits))
    require(re.fullmatch('[0-9a-f]{40}|[0-9a-f]{64}', commit), 'Use one full source commit identity')
    require(all(value.get('producer_commit', commit) == commit for value in reports.values()),
        'Selected source and producer commits differ')
    return commit


def preserve_base(shared, base, current, base_commit):
    require(re.fullmatch('[0-9a-f]{40}|[0-9a-f]{64}', base_commit or ''), 'Explicit full sealed baseline required')
    for name, data in base.items():
        if name not in ('Pinwheel.lean', 'scripts/check-foundation.py'):
            require(current.get(name) == data, 'Sealed baseline file changed: ' + name)
    imports = shared.additive_imports(base['Pinwheel.lean'].decode(), current['Pinwheel.lean'].decode())
    require(all(line.startswith('import Pinwheel.Hardware.StreamingMapped.') or
        line == 'import Pinwheel.Program.StreamingUARTFirstTerminal' for line in imports),
        'Only additive mapped and first-terminal proof imports are allowed')
    foundation = mapped_foundation(shared, base['scripts/check-foundation.py'].decode(),
        current['scripts/check-foundation.py'].decode())
    return dict(base=base_commit, baseline_files=len(base), added_imports=imports, foundation=foundation)


def mapped_foundation(shared, before, after):
    old, old_ast = shared.foundation_parts(before)
    new, new_ast = shared.foundation_parts(after)
    require(old_ast == new_ast and all(old[name] == new[name] for name in ('SUITES', 'KERNEL_SUITES')),
        'Mapped extension must preserve foundation code and every existing suite')
    prefix, marker, tail = old['boundary'].partition('. Does not ')
    require(marker and new['boundary'].startswith(prefix) and new['boundary'].endswith(marker + tail),
        'Foundation prior claims or exclusions changed')
    added = new['boundary'][len(prefix):-len(marker + tail)]
    require(not added or (added.startswith('; ') or added.startswith('. Includes ')) and
        'mapped' in added.lower(), 'Foundation change is not an appended mapped proof boundary')
    return dict(added_suites=[], added_kernel_suites=[], boundary_preserved=True, added_boundary=added)


def full_contract(report):
    require(report.get('schema') == FULL_SCHEMA and report.get('passed') is True and
        report.get('full_qualification') is True and not report.get('error') and not report.get('closeout_error') and
        all(report.get(name) is True for name in ('committed_archive_membership_verified_before',
            'committed_archive_membership_verified_after', 'tool_identity_unchanged', 'library_unchanged')),
        'Mapped full receipt did not close its immutable full-scope contract')
    require(report.get('source_commit') == report.get('producer_commit') and report.get('tool_identity_before') and
        report['tool_identity_before'] == report.get('tool_identity_after') and
        report.get('library', {}).get('sha256') == LIBRARY, 'Mapped tool/source/library identity differs')
    require(report.get('raw_stage', {}).get('partial_input_only') is True,
        'Fresh raw receipt must remain a partial input stage')
    require(report.get('cad_runtime_archive_membership', {}).get('cad_selected_archive_membership_verified') is True and
        report['cad_runtime_archive_membership'].get('installed_payload_archive_membership_proved') is False,
        'Mapped narrow CAD membership boundary is missing or broadened')


def checked_tool_files(identity, frozen):
    require(type(identity) is dict and identity.get('installed_payload_archive_membership_proved') is False and
        identity.get('files') and identity.get('archives'), 'Unsupported tool runtime/archive identity contract')
    for name, value in identity['files'].items():
        path = Path(name)
        require(path.is_absolute() and path.is_file() and
            str(path.resolve()) == value.get('resolved') and digest(path) == value.get('sha256'),
            'Native tool/runtime file changed: ' + name)
        # Installed native libraries contain legitimate pinned aliases. Bind
        # their resolved target as well as rechecking the alias at closeout.
        frozen[path.resolve()] = value['sha256']
    for name, value in identity['archives'].items():
        path = Path(name)
        require(path.is_absolute() and path.is_file() and not path.is_symlink() and digest(path) == value,
            'Pinned native tool archive changed: ' + name)
        frozen[path] = value
    return len(identity['files'])


def fresh_layout(directory, config, raw_stage):
    directory = Path(directory).resolve()
    root, raw_root = directory / 'worker', directory.parent / (directory.name + '-raw')
    snapshot = raw_root / 'selected'
    require(Path(config.get('worker_out', '')).resolve() == root and
        Path(config.get('snapshot', '')).resolve() == snapshot and
        raw_stage.get('report') == str(raw_root / 'report.json') and raw_stage.get('partial_input_only') is True,
        'Mapped gate did not use its own fresh partial raw input stage')
    return root, raw_root, snapshot


def bootstrap(out):
    """Execute shared verification helpers only after checking their Git bytes."""
    records, payloads = [], {}
    def call(argv, label):
        started = time.monotonic()
        result = subprocess.run(argv, cwd=ROOT, capture_output=True, timeout=30)
        (out / (label + '.log')).write_bytes(result.stdout + result.stderr)
        records.append(dict(label=label, argv=argv, exit_code=result.returncode,
            seconds=round(time.monotonic() - started, 3)))
        require(result.returncode == 0, 'Exporter bootstrap failed: ' + label)
        return result.stdout
    head = call(['git', 'rev-parse', 'HEAD'], 'export-head').decode().strip()
    for index, name in enumerate(PRODUCER):
        data = call(['git', 'show', head + ':' + name], 'export-producer-' + str(index))
        require((ROOT / name).is_file() and not (ROOT / name).is_symlink() and
            (ROOT / name).read_bytes() == data, 'Commit exporter/helper/test first: ' + name)
        payloads[name] = data
    for name, relative in (('process_group', 'scripts/process_group.py'),
            ('validation_run', 'scripts/validation_run.py'),
            ('_mapped_export_git', GIT_HELPER), ('_mapped_export_shared', SHARED)):
        module = types.ModuleType(name)
        module.__file__ = str(ROOT / relative)
        sys.modules[name] = module
        exec(compile(payloads[relative], module.__file__, 'exec'), module.__dict__)
    return head, {name: sha(data) for name, data in payloads.items()}, records


def native_commands(shared, driver, report, root):
    """Match every campaign compile intent to a real, closed parent command."""
    records = report['commands']
    driver.command_inventory(records)
    driver.verify_journal(root, records)
    by_label = {record['label']: record for record in records}
    require(len(by_label) == len(records), 'Ambiguous mapped command labels')
    for command in report['campaign']['commands']:
        actual = by_label.get(command.get('label'), {})
        require(command.get('external_runner') is True and command.get('expected_outcome_completed') is True and
            command.get('argv') == actual.get('argv') and
            command.get('expected_failure') is actual.get('expected_failure'),
            'Campaign intent differs from actual native compiler/tool execution')
    for record in records:
        shared.regular(root / 'logs' / (record['label'] + '.log'), root)
    return by_label


def check_audits(shared, campaign, worker, root, by_label):
    child, compact = worker['campaign'], {}
    for label, entry in child['components'].items():
        prefix = 'Mapped' + {'frontend': 'Frontend', 'core-d2': 'CoreD2', 'core-d4': 'CoreD4'}[label]
        proof = root / 'campaign' / label / 'proof'
        source = shared.regular(proof / (prefix + 'Audit.lean'), root)
        require(source.read_text() == campaign.audit_source(entry['compiled_modules']), 'Component audit owner set changed')
        output = (root / 'logs' / (prefix + 'Audit.log')).read_text()
        require(re.findall(r'Mapped audit: (\d+) declarations, (\d+) theorems; standard axioms only\.', output) ==
            [(str(entry['audited_declarations']), str(entry['audited_theorems']))], 'Component audit count differs from native log')
        record = by_label.get(prefix + 'PrivateAuditControl', {})
        require(record.get('expected_failure') is True and
            'Unapproved axioms' in (root / 'logs' / (prefix + 'PrivateAuditControl.log')).read_text(),
            'Component unused-private-axiom control did not fail for the required reason')
    # This reproduces the actual positive module ownership in compilation order,
    # including positive unchanged controls and component audits, excluding fixtures.
    owners = []
    for record in worker['commands']:
        if record['label'] == 'MappedWrapperAudit': break
        argv = record['argv']
        if '-o' in argv and argv[-1].endswith('.lean') and not record['expected_failure']:
            name = Path(argv[-1]).stem
            if not name.endswith('PrivateControl') and name not in owners: owners.append(name)
    audit = root / 'campaign/wrapper/MappedWrapperAudit.lean'
    require(audit.read_text() == campaign.audit_source(owners), 'Final audit omits positive generated module ownership')
    log = (root / 'logs/MappedWrapperAudit.log').read_text()
    counts = re.findall(r'Mapped audit: (\d+) declarations, (\d+) theorems; standard axioms only\.', log)
    require(len(counts) == 1 and min(map(int, counts[0])) > 0, 'Final whole/private audit native counts absent')
    reject = by_label.get('MappedWrapperPrivateAuditControl', {})
    require(reject.get('expected_failure') is True and
        'Unapproved axioms' in (root / 'logs/MappedWrapperPrivateAuditControl.log').read_text(),
        'Final unused-private-axiom control did not reject')
    require((root / 'campaign/wrapper/MappedWrapperPrivateAuditControl.lean').read_text() ==
        campaign.audit_source([*owners, 'MappedWrapperPrivateControl']), 'Private control did not audit the whole positive closure')
    compact.update(final_declarations=int(counts[0][0]), final_theorems=int(counts[0][1]),
        final_owner_modules=len(owners), component_private_controls=3, final_private_control=True)
    return compact


def check_component_controls(shared, campaign, component, worker, config, root, library, by_label):
    summaries = {}
    for label, entry in worker['campaign']['components'].items():
        directory = root / 'campaign' / label
        cfg, mapped = config['components'][label], directory / 'mapped.json'
        original = shared.read_json(mapped.read_bytes())
        top = next(iter(shared.read_json(Path(cfg['raw_json']).read_bytes())['modules']))
        names = ['unchanged', 'broken-carry', 'changed-output', 'wrong-operator', 'dropped-ff', 'top-word-input', 'ff-clock-zero']
        controls = entry.get('mutations', [])
        require([row.get('name') for row in controls] == names and all(row.get('passed') is True and
            row.get('expected_rejection') is (row['name'] != 'unchanged') for row in controls),
            'Missing positive or distinguishing mapped component controls')
        prefix = 'Mapped' + {'frontend': 'Frontend', 'core-d2': 'CoreD2', 'core-d4': 'CoreD4'}[label]
        words = shared.read_json((directory / 'words.json').read_bytes())
        unchanged = directory / 'controls' / (prefix + 'unchangedControl.lean')
        unchanged_json = shared.regular(controls[0]['artifact'], root)
        require(unchanged_json.resolve() == (directory / 'controls/unchanged.json').resolve(),
            'Positive arithmetic control path substitution')
        candidates = []
        for module, description in words.items():
            if description['kind'] != '$add' or description['ports']['Y'] < 2: continue
            source, _ = campaign.generate_arithmetic(unchanged_json, library, module, '$add',
                namespace=entry['namespace'] + '.Controlunchanged', fa_module=prefix + 'FA',
                fa_namespace=entry['namespace'] + '.FA')
            if source == unchanged.read_text(): candidates.append(module)
        require(len(candidates) == 1, 'Positive arithmetic control does not bind one actual mapped word')
        module = candidates[0]
        for row in controls[:4]:
            name = label + '-' + row['name']
            record = by_label.get(name, {})
            require(record.get('expected_failure') is row['expected_rejection'], 'Kernel mutation native outcome differs')
            candidate = shared.regular(row['artifact'], root)
            require(candidate.resolve() == (directory / 'controls' / (row['name'] + '.json')).resolve(),
                'Arithmetic control path substitution')
            expected = deepcopy(original)
            if row['name'] == 'broken-carry': expected['modules'][module]['cells']['bit_1']['connections']['CI'] = ['0']
            elif row['name'] == 'changed-output': expected['modules'][module]['ports']['Y']['bits'][0] = expected['modules'][module]['ports']['Y']['bits'][1]
            require(shared.read_json(candidate.read_bytes()) == expected, 'Arithmetic control changed the wrong actual artifact')
            text, _ = campaign.generate_arithmetic(candidate, library, module,
                '$sub' if row['name'] == 'wrong-operator' else '$add',
                namespace=entry['namespace'] + '.Control' + row['name'].replace('-', ''),
                fa_module=prefix + 'FA', fa_namespace=entry['namespace'] + '.FA')
            require((directory / 'controls' / (prefix + row['name'].replace('-', '') + 'Control.lean')).read_text() == text,
                'Native arithmetic control did not interpret its exact retained mapped candidate')
            if row['expected_rejection']:
                require(row.get('reason') and row['reason'] in (root / 'logs' / (name + '.log')).read_text(),
                    'Kernel mutation failed for an unrelated native reason')
        # Reproduce structural refusals against the exact retained mutants.
        for row in controls[4:]:
            path = shared.regular(row['artifact'], root)
            expected = directory / 'controls' / ({'top-word-input': 'top-word-input', 'ff-clock-zero': 'ff-clock-zero',
                'dropped-ff': 'dropped-ff'}[row['name']] + '.json')
            require(path.resolve() == expected.resolve(), 'Structural mutation path substitution')
            data = shared.read_json(path.read_bytes())
            expected_data = deepcopy(original)
            if row['name'] == 'top-word-input':
                bits = expected_data['modules'][top]['cells'][row['cell']]['connections'][row['pin']]
                require(bits[row['bit']] in ('0','1'), 'Top-input mutation did not select a literal')
                bits[row['bit']] = '1' if bits[row['bit']] == '0' else '0'
            elif row['name'] == 'ff-clock-zero':
                expected_data['modules'][top]['cells'][row['cell']]['connections']['CLK'] = ['0']
            else:
                ff = next(name for name, cell in expected_data['modules'][top]['cells'].items()
                    if cell['type'].endswith('dfrbpq_1'))
                del expected_data['modules'][top]['cells'][ff]
            require(data == expected_data, 'Structural control changed more than its declared actual connection')
            try:
                if row['name'] == 'top-word-input':
                    kind, bits = ('frontend', 1) if label == 'frontend' else ('core', 1 if label == 'core-d2' else 2)
                    rb = campaign.streaming_ready_readback.backend(kind, bits)
                    component.generate_component(rb, Path(cfg['raw_json']), path, library, entry['word_modules'],
                        namespace=entry['namespace'],raw_module=cfg['raw_module'],raw_namespace=cfg['raw_namespace'])
                else: campaign.state_inventory(shared.read_json(Path(cfg['raw_json']).read_bytes()), data, top, library)
            except ValueError as error:
                if row['name'] != 'dropped-ff': require(row['reason'] in str(error), 'Wrong structural refusal reason')
            else: raise RuntimeError('Retained actual structural mutation was accepted')
        # Each proof module must belong to this exact physical body and artifact.
        for name, spec in entry['word_modules'].items():
            body = json.dumps(original['modules'][name], sort_keys=True, separators=(',', ':')).encode()
            require(spec.get('netlist_sha256') == digest(mapped) and spec.get('module_sha256') == sha(body) and
                spec.get('source_sha256') == digest(directory / 'proof' / (spec['module'] + '.lean')),
                'Word certificate has a stale module body/artifact/source binding')
        summaries[label] = dict(positive_native_control=True, kernel_rejections=3, structural_refusals=3,
            exact_word_body_bindings=len(entry['word_modules']))
    return summaries


def check_cut_boundary(cut, boundary, retained_cut, retained_boundary):
    # cut_engine uses endpoint tuples; the retained JSON represents them as
    # arrays. Canonical JSON preserves every field/value while matching that
    # serialization, including primitive types and endpoint order.
    canonical = lambda value: json.dumps(value, sort_keys=True, separators=(',', ':'), allow_nan=False)
    require(canonical(cut) == canonical(retained_cut) and canonical(boundary) == canonical(retained_boundary),
        'Actual package cut differs from retained mapped boundary')


def device_assembly(shared, worker, config, root, library):
    from streaming_mapped_wrapper import (cut_engine, restore_engine, complete_hierarchy,
        wrapper_source, package_source)
    from streaming_mapped_netlist import load_mapped
    from streaming_mapped_simulation import sampler_mutation
    for depth, result in worker['campaign']['wrapper_metadata']['depths'].items():
        a = 1 if depth == '2' else 2
        directory = root / 'campaign/device' / ('d' + depth)
        outer, package = result['outer'], result['package']
        mapped = shared.regular(directory / 'outer/mapped.json', root)
        actual = shared.read_json((directory / 'outer/actual-outer.json').read_bytes())
        top = outer['top']
        cut, boundary = cut_engine({'modules': {top: actual['modules'][top]}}, top, outer['package'])
        check_cut_boundary(cut, boundary, shared.read_json((directory / 'outer/cut.json').read_bytes()),
            shared.read_json((directory / 'outer/boundary.json').read_bytes()))
        restored = restore_engine(shared.read_json(mapped.read_bytes()), boundary)
        require(restored == shared.read_json((directory / 'outer/restored.json').read_bytes()),
            'Mapped outer restoration changed actual engine connections')
        package_path = shared.regular(directory / 'package/package.json', root)
        package_data = shared.read_json(package_path.read_bytes())
        expected_sources = {
            'StreamingMappedTinyD' + depth: wrapper_source(load_mapped(mapped, top, library, combinational=True), a,
                namespace='Pinwheel.Artifact.StreamingMappedTinyD' + depth, netlist_sha256=digest(mapped)),
            'StreamingMappedPackageD' + depth: package_source(package_data, package['top'], a,
                namespace='Pinwheel.Artifact.StreamingMappedPackageD' + depth, netlist_sha256=digest(package_path))}
        for name, source in expected_sources.items():
            require((root / 'campaign/wrapper' / (name + '.lean')).read_text() == source,
                'Final mapped package/pad certificate is not derived from the retained actual graph')
        complete = complete_hierarchy(restored, package_data,
            shared.read_json((root / 'campaign' / ('core-d' + depth) / 'mapped.json').read_bytes()),
            shared.read_json((root / 'campaign/frontend/mapped.json').read_bytes()), addr_bits=a, library=library)
        require(complete == shared.read_json((directory / 'complete.json').read_bytes()),
            'Cost/native complete hierarchy differs from certified component/package/pad bodies')
        mutant, detail = sampler_mutation(complete, 'pinwheel_streaming_ready_core_d' + depth, library)
        require(mutant == shared.read_json((directory / 'sampler-ff-pin.json').read_bytes()) and
            detail == shared.read_json((directory / 'sampler-mutation.json').read_bytes()),
            'Actual sampler FF-pin control differs from its positive complete hierarchy')
        expected_outer = {name: digest(config['device'][depth][name]) for name in ('tiny', 'package')}
        expected_outer['liberty'] = LIBRARY
        expected_package = dict(package=digest(config['device'][depth]['package']),
            frontend=digest(config['components']['frontend']['sv']), core=digest(config['components']['core-d' + depth]['sv']))
        require(outer['source_sha256'] == expected_outer and package['source_sha256'] == expected_package,
            'Mapped wrapper used a different fresh raw-certified source')
        controls = directory / 'controls'
        bad_pad = deepcopy(shared.read_json(mapped.read_bytes()))
        bad_pad['modules'][top]['ports']['uo_out']['bits'][0] = '0'
        bad_status = deepcopy(package_data)
        connections = bad_status['modules'][package['top']]['cells']['frontend']['connections']
        connections['status_generation'] = deepcopy(connections['status_transfer'])
        for name, data, stem, expected_reason in [('changed-pad', bad_pad, 'MappedChangedPadD',
                'Tactic `decide` proved that the proposition'), ('status-wire', bad_status, 'MappedStatusWireD', 'Tactic `rfl` failed')]:
            path = shared.regular(controls / (name + '.json'), root)
            require(shared.read_json(path.read_bytes()) == data, 'Device control did not make its declared actual connection change')
            if name == 'changed-pad':
                text = wrapper_source(load_mapped(path, top, library, combinational=True), a,
                    namespace='Pinwheel.Artifact.StreamingMappedChangedPadD' + depth, netlist_sha256=digest(path))
            else:
                text = package_source(data, package['top'], a,
                    namespace='Pinwheel.Artifact.StreamingMappedStatusWireD' + depth, netlist_sha256=digest(path))
            require((controls / (stem + depth + '.lean')).read_text() == text and
                expected_reason in (root / 'logs' / (stem + depth + '.log')).read_text(),
                'Actual mapped package/pad mutation did not reach its distinguishing native kernel failure')
        bad_clock = {'modules': {top: deepcopy(actual['modules'][top])}}
        bad_clock['modules'][top]['cells']['engine']['connections']['clk'] = bad_clock['modules'][top]['ports']['ena']['bits']
        require(shared.read_json((controls / 'changed-clock.json').read_bytes()) == bad_clock,
            'Actual clock control did not change only the engine clock')
        try: cut_engine(bad_clock, top, outer['package'])
        except ValueError as error: require('clock is not direct' in str(error), 'Wrong actual outer-clock refusal')
        else: raise RuntimeError('Changed actual outer engine clock was accepted')


def raw_proof_closures(shared, raw, gate, child, root, selected, committed):
    counts = {}
    for label, value in child['stages']['raw-components']['result'].items():
        positive = root / 'raw' / label / 'proof'
        require(raw.generated_closure(gate, selected, [positive], [value['compiled_modules'][-1]], committed) ==
            value['positive_proof_closure'], 'Fresh raw component positive dependency closure differs')
        for control in value['mutations']:
            directory = Path(control['proof_directory'])
            require(directory.resolve().is_relative_to((root / 'raw' / label / 'controls').resolve()),
                'Fresh raw control path substitution')
            require(raw.generated_closure(gate, selected, [directory, positive], control['modules'], committed) ==
                value['control_proof_closures'][control['name']], 'Fresh raw negative dependency closure differs')
        require(raw.generated_closure(gate, selected, [positive], value['private_control_modules'], committed) ==
            value['private_control_proof_closure'], 'Fresh raw unused-private-axiom closure differs')
        counts[label] = len(value['positive_proof_closure'])
    for depth, value in child['stages']['actual-wrappers']['result'].items():
        target = root / 'wrapper-proofs' / ('d' + depth)
        for control in value['mutations']:
            directory = Path(control['proof_directory'])
            require(directory.resolve().is_relative_to(target.resolve()), 'Fresh raw wrapper control path substitution')
            require(raw.generated_closure(gate, selected, [directory], [control['module']], committed) ==
                value['control_proof_closures'][control['name']], 'Fresh raw wrapper dependency closure differs')
    return counts


def retained_full(shared, driver, report, directory, frozen):
    """Recheck bytes and selected pure validators; no mapping, Lean or simulator run."""
    config_path = shared.regular(directory / 'worker-config.json', directory)
    require(digest(config_path) == report.get('worker_config_sha256_before_use'), 'Mapped worker configuration changed')
    config = shared.read_json(config_path.read_bytes())
    root, raw_root, snapshot = fresh_layout(directory, config, report['raw_stage'])
    require(config.get('source_commit') == report['source_commit'] and config.get('producer_commit') == report['producer_commit'] and
        config.get('source_sha256') == report['source_sha256'] and config.get('source_tree') == report['selected_git_objects'] and
        config.get('tool_paths') == report['tool_paths'] and config.get('tool_identity') == report['tool_identity_before'] and
        config.get('library') == report['library'] and config.get('raw_frozen_sha256') == report['raw_frozen_sha256'],
        'Mapped worker/source/raw/tool configuration identity differs')
    child_path = shared.regular(root / 'worker-report.json', root)
    require(digest(child_path) == report.get('worker_report_sha256') and
        shared.read_json(child_path.read_bytes()) == report['worker'], 'Mapped outer and retained worker receipts differ')
    artifacts = shared.inventory(root); artifacts.pop('worker-report.json', None)
    require(artifacts == report['worker'].get('artifact_sha256'), 'Mapped retained artifact inventory differs')
    shared.checked_map(root, artifacts, frozen)
    frozen[config_path], frozen[child_path] = digest(config_path), digest(child_path)
    raw_path = shared.regular(raw_root / 'report.json', raw_root)
    require(report['raw_stage'].get('report') == str(raw_path) and
        report['raw_stage'].get('sha256') == digest(raw_path), 'Mapped receipt substituted a historical raw input stage')
    raw_report = shared.read_json(raw_path.read_bytes())
    raw_config = shared.read_json(shared.regular(raw_root / 'worker-config.json', raw_root).read_bytes())
    shared.checked_map(snapshot, report['source_sha256'], frozen)
    shared.checked_map(directory / 'producer', report['producer_sha256'], frozen)
    shared.checked_map(raw_root / 'producer', raw_report['producer_sha256'], frozen)
    for path, value in report['raw_frozen_sha256'].items():
        shared.checked_path(path, [raw_root, directory / 'inputs'], frozen, value)
    sys.path.insert(0, str(snapshot / 'scripts'))
    for name in tuple(sys.modules):
        if name.startswith('streaming_'): del sys.modules[name]
    raw = shared.load_module('_mapped_verified_raw', snapshot / 'scripts/check-streaming-uart.py')
    h = raw.helpers()
    driver.validate_raw(raw_report, raw_config, raw, report['source_commit'], report['selected_git_objects'], report['source_sha256'], h)
    require(config['components'] == driver.component_config(raw_root, raw_report['worker']),
        'Mapped component inputs are not the freshly executed raw-stage proof closure')
    expected_device = {str(depth): {name: str(raw_root / 'worker/actual-wrappers' / ('d' + str(depth)) / filename)
        for name, filename in (('tiny', 'tt.sv'), ('package', 'package.sv'), ('bridge', 'bridge.sv'))} for depth in (2, 4)}
    require(config['device'] == expected_device, 'Mapped device substituted historical wrapper sources')
    campaign_config = shared.read_json(shared.regular(root / 'campaign/config.json', root).read_bytes())
    require(all(campaign_config.get(name) == value for name, value in
        dict(root=str(snapshot), library=config['library']['staged'], tools=config['tool_paths'],
            components=config['components'], device=config['device'], source_commit=report['source_commit'], build=False,
            timeout=config['command_timeout']).items()) and
        set(campaign_config.get('source_files', [])) == {str(snapshot / path) for path in driver.required_inputs(config['source_tree'])},
        'Retained campaign did not consume the exact parent-selected fresh inputs')
    require(raw_report.get('tool_paths') == report['tool_paths'] and raw_report.get('tool_identity_before') ==
        report['tool_identity_before'] == raw_report.get('tool_identity_after'), 'Fresh raw stage used different tools/runtime')
    import streaming_mapped_campaign as campaign
    import streaming_mapped_component as component
    from streaming_mapped_liberty import load_library
    from streaming_mapped_simulation import check_uart_cases
    from streaming_ready_wire_cases import check_i2c_cases
    from streaming_uart_legacy_cases import check_legacy_cases
    from streaming_mapped_cost import measure
    from streaming_mapped_composition import generate
    from streaming_mapped_uart_timing import generate as timing_sources, required_qnames as timing_qnames
    from streaming_mapped_runtime import audit as cad_audit
    library = load_library(config['library']['staged'])
    checks = dict(uart_check=check_uart_cases, i2c_check=check_i2c_cases, legacy_check=check_legacy_cases,
        native_check=lambda result, depth: driver.validate_native(result, depth, config['tool_paths']),
        cost_check=lambda result, depth: driver.validate_cost(result, depth, config['library']['staged'], measure))
    qnames = driver.expected_qnames(raw)
    cad_membership = cad_audit(report['tool_identity_before'],
        shared.read_json((snapshot / 'tools/hardware-toolchain.json').read_bytes()), config['tool_paths'])
    driver.validate_cad_membership(report.get('cad_runtime_archive_membership'), cad_membership)
    driver.validate_worker(report['worker'], config, campaign, qnames, checks, cad_membership)
    device_assembly(shared, report['worker'], config, root, library)
    require(report.get('required_targets') == list(driver.TARGETS), 'Mapped parent requested-scope inventory changed')
    worker = report['worker']
    by_label = native_commands(shared, driver, worker, root)
    audits = check_audits(shared, campaign, worker, root, by_label)
    controls = check_component_controls(shared, campaign, component, worker, config, root, library, by_label)
    required_log = (root / 'logs/StreamingMappedRequiredTargets.log').read_text()
    campaign.verify_qnames(required_log, qnames)
    extra = timing_qnames()
    require(worker['campaign']['wrapper_metadata'].get('extra_qnames') == extra and
        worker['campaign'].get('extra_qnames_checked') is True, 'Mapped first-terminal proof targets did not close')
    campaign.verify_extra_qnames(required_log, extra, qnames)
    expected_required = '\n'.join(['import StreamingMappedSessionD2', 'import StreamingMappedSessionD4',
        'import StreamingMappedUARTTimingD2', 'import StreamingMappedUARTTimingD4'] +
        ['#check ' + name for name in [*qnames, *extra]]) + '\n'
    require((root / 'campaign/wrapper/StreamingMappedRequiredTargets.lean').read_text() == expected_required,
        'Final required theorem checks changed')
    for a in (1, 2):
        for name, source in {**generate(a), **timing_sources(a)}.items():
            require((root / 'campaign/wrapper' / (name + '.lean')).read_text() == source,
                'Mapped source/session proof differs from committed factory')
    gate = shared.load_module('_mapped_verified_closure', snapshot / 'scripts/check-buffered-rtl-session.py')
    raw_closures = raw_proof_closures(shared, raw, gate, raw_report['worker'], raw_root / 'worker',
        snapshot, report['source_sha256'])
    directories = [root / 'campaign' / label / 'proof' for label in campaign.LABELS] + [root / 'campaign/wrapper']
    require(raw.generated_closure(gate, snapshot, directories, ['StreamingMappedRequiredTargets'], report['source_sha256']) ==
        worker['proof_dependency_closure'], 'Final positive dependency closure differs')
    # All frozen selected sources, generated files and native tool products must
    # still match their first pre-use hashes, including private control sources.
    for path, value in worker['campaign']['frozen_sha256'].items():
        selected = Path(path)
        require(selected.is_absolute() and selected.is_file() and not selected.is_symlink() and digest(selected) == value,
            'Mapped first-use input changed: ' + path)
        frozen[selected] = value
    for name in ('original', 'staged'):
        path = Path(report['library'][name])
        require(path.is_file() and not path.is_symlink() and digest(path) == LIBRARY, 'Pinned Liberty bytes changed')
        frozen[path] = LIBRARY
    runtime_files = checked_tool_files(report['tool_identity_before'], frozen)
    return dict(retained_artifacts=len(artifacts), audits=audits, controls=controls, checked_qnames=qnames,
        extra_first_terminal_qnames=extra,
        tool_runtime_files=runtime_files, installed_payload_archive_membership_proved=False,
        cad_runtime_archive_membership=cad_membership,
        raw_dependency_closures=raw_closures,
        final_dependency_modules=len(worker['proof_dependency_closure']), native_processes=28,
        native_journal_events=56, raw_stage=dict(report=str(raw_path), source_commit=raw_report['source_commit'],
            partial_input_only=True, worker_artifacts=len(raw_report['worker']['artifact_sha256'])),
        complete_costs_recomputed=True), root, raw_root, raw_report


def compact_sources(shared, root):
    files = {}
    for name in ('StreamingMappedSessionD2', 'StreamingMappedSessionD4', 'StreamingMappedPackageD2',
            'StreamingMappedPackageD4', 'StreamingMappedTinyD2', 'StreamingMappedTinyD4',
            'StreamingMappedUARTTimingD2', 'StreamingMappedUARTTimingD4',
            'StreamingMappedRequiredTargets', 'MappedWrapperAudit'):
        path = shared.regular(root / 'campaign/wrapper' / (name + '.lean'), root)
        files[name + '.lean'] = path.read_bytes()
    for target, relative in {'checked-target-types.txt': 'logs/StreamingMappedRequiredTargets.log',
            'final-private-audit.log': 'logs/MappedWrapperAudit.log',
            'final-private-axiom-rejection.log': 'logs/MappedWrapperPrivateAuditControl.log'}.items():
        files[target] = shared.regular(root / relative, root).read_bytes()
    for depth in (2, 4):
        for name in ('cost.json', 'native-intent.json', 'native.jsonl'):
            files['d' + str(depth) + '-' + name] = shared.regular(root / 'campaign/device' / ('d' + str(depth)) / name, root).read_bytes()
    return files


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ('tag', 'full-tag', 'foundation-tag', 'python-tag'): parser.add_argument('--' + name, required=True)
    parser.add_argument('--base-commit', default=BASE)
    args = parser.parse_args()
    tags = [args.tag, args.full_tag, args.foundation_tag, args.python_tag]
    require(all(re.fullmatch('[A-Za-z0-9_-]+', tag) for tag in tags) and len(set(tags)) == len(tags), 'Use distinct safe tags')
    require(re.fullmatch('[0-9a-f]{40}|[0-9a-f]{64}', args.base_commit or ''), 'Use explicit sealed --base-commit')
    require(BASE is None or args.base_commit == BASE, 'Preserve the pinned sealed UART baseline')
    destination = ROOT / DESTINATION
    require(not destination.exists(), 'Preserve existing mapped evidence destination')
    out = ROOT / 'build/validation' / args.tag; out.mkdir(parents=True, exist_ok=False)
    head, producers, bootstrap_commands = bootstrap(out)
    shared, helper = sys.modules['_mapped_export_shared'], sys.modules['_mapped_export_git']
    (out / 'logs').mkdir()
    run = sys.modules['validation_run'].Commands(ROOT, out / 'logs', default_timeout=60)
    git = helper.GitEvidence(out, run)
    shared.source_objects.cached = {}
    stage = out / 'export'; stage.mkdir()
    frozen, receipts, raw_bytes = {}, {}, {}
    interpreter = Path(sys.executable).resolve()
    frozen[interpreter] = digest(interpreter)
    manifest = dict(schema=SCHEMA, exported_utc=datetime.now(timezone.utc).isoformat(), exporter_commit=head,
        exporter_sha256=producers, exporter_python=dict(path=str(interpreter), sha256=frozen[interpreter], version=sys.version),
        export_log_directory=str(out), receipts=[], compact_files=[], boundary='Immutable committed-source and retained-artifact '
        'verification; no gate rerun. Kernel mapped Boolean/FF equations, finite native public-pin diagnostics and complete '
        'Liberty cell costs are separate evidence. Restricted interpreters and native Lean/tools remain trust boundaries. '
        'No electrical, delay/Fmax, placement/routing or silicon-signoff claim; large trees remain at recorded retained paths.')
    try:
        specifications = [('full', args.full_tag), ('foundation', args.foundation_tag), ('python', args.python_tag)]
        for kind, tag in specifications:
            path = shared.regular(ROOT / 'build/validation' / tag / 'report.json', ROOT)
            raw_bytes[kind] = path.read_bytes(); receipts[kind] = read_json(raw_bytes[kind]); frozen[path] = sha(raw_bytes[kind])
        commit = same_source(receipts)
        source, current = git.archive(commit)['files'], git.archive(head)['files']
        base = git.archive(args.base_commit)['files']
        manifest.update(source_commit=commit, frozen_baseline=preserve_base(shared, base, source, args.base_commit))
        preserve_base(shared, base, current, args.base_commit)
        for name, value in DOCS.items(): require(digest(shared.regular(ROOT / name, ROOT)) == value, 'Intake document changed')
        patch = run(['git', 'diff', '--no-ext-diff', '--no-textconv', '--', *DOCS], 'intake-patch').encode()
        require(sha(patch) == PATCH, 'Intake dirty-document patch changed')
        (stage / 'intake-documents.patch').write_bytes(patch)
        manifest.update(intake_documents_sha256=DOCS, intake_patch_sha256=PATCH)
        for kind, tag in specifications:
            report, directory = receipts[kind], ROOT / 'build/validation' / tag
            mapping = report.get('source_sha256')
            objects = shared.source_objects(run, commit, mapping, report.get('selected_git_objects'))
            item = dict(kind=kind, tag=tag, retained_directory=str(directory),
                source_verification=git.verify_map(commit, mapping, objects))
            require(all(name in current and sha(current[name]) == value for name, value in mapping.items()),
                'Accepted source is stale relative to current commit')
            for name, value in mapping.items():
                if name not in DOCS:
                    path = shared.regular(ROOT / name, ROOT)
                    require(digest(path) == value, 'Working source changed after qualification')
                    frozen[path] = value
            if kind == 'full':
                full_contract(report)
                require(set(mapping) == set(source), 'Full mapped stage omitted committed source files')
            else:
                item['contract'] = helper.contract(kind, True, report, source)
                expected = report.get('snapshot_archive_sha256')
                item['archive_verification'] = git.reproduce(commit, mapping, expected)
                if kind == 'python': shared.retained_archive(directory, 'selected-source.tar', expected, frozen)
            if kind == 'foundation':
                item['retained'] = shared.foundation_evidence(report, source, directory, frozen)
                require(report.get('driver_sha256') == sha(source['scripts/check-foundation-snapshot.py']), 'Foundation driver mismatch')
            producer_files = source
            if 'producer_sha256' in report:
                pm = report['producer_sha256']; po = shared.source_objects(run, commit, pm, report.get('producer_git_objects'))
                item['producer_verification'] = git.verify_map(commit, pm, po)
                producer_files = git.archive(commit)['files']
                if report.get('producer_archive_sha256'):
                    item['producer_archive_verification'] = git.reproduce(commit, pm, report['producer_archive_sha256'])
                    shared.retained_archive(directory, 'producer-source.tar', report['producer_archive_sha256'], frozen)
            if kind == 'full':
                # Verify the producer tree before executing any validator body.
                shared.checked_map(directory / 'producer', report['producer_sha256'], frozen)
                require((directory / 'producer/scripts/check-streaming-mapped.py').read_bytes() ==
                    source['scripts/check-streaming-mapped.py'], 'Mapped validator bytes differ from independently verified Git source')
                driver = shared.load_module('_mapped_export_driver', directory / 'producer/scripts/check-streaming-mapped.py')
                require(set(report['producer_sha256']) == driver.required_inputs(report['selected_git_objects']),
                    'Mapped producer inventory omits a required committed helper/test/proof')
                retained, full_root, raw_root, raw_report = retained_full(shared, driver, report, directory, frozen)
                item['retained'] = retained
                for scope, nested in [('selected', raw_report['source_sha256']), ('producer', raw_report['producer_sha256'])]:
                    expected = raw_report[scope + '_archive_sha256']
                    item['raw_' + scope + '_archive_verification'] = git.reproduce(commit, nested, expected)
                    shared.retained_archive(raw_root, scope + '-source.tar', expected, frozen)
                require(raw_report['source_sha256'] == mapping, 'Fresh raw stage consumed different committed source files')
                item['raw_producer_verification'] = git.verify_map(commit, raw_report['producer_sha256'],
                    shared.source_objects(run, commit, raw_report['producer_sha256'], raw_report.get('producer_git_objects')))
            if kind == 'python':
                require(set(mapping) == set(source), 'Python discovery omitted committed source files')
                item['retained'] = shared.check_python_retained(report, directory, frozen, producer_files)
            compressed = gzip.compress(raw_bytes[kind], compresslevel=9, mtime=0)
            filename = tag + '.json.gz'; (stage / filename).write_bytes(compressed)
            item.update(file=filename, raw_sha256=sha(raw_bytes[kind]), raw_bytes=len(raw_bytes[kind]),
                compressed_sha256=sha(compressed), compressed_bytes=len(compressed))
            manifest['receipts'].append(item)
        compact = compact_sources(shared, full_root)
        compact['foundation-private-audit.log'] = (ROOT / 'build/validation' / args.foundation_tag / 'axioms.log').read_bytes()
        compact['proof-and-control-summary.json'] = (json.dumps(manifest['receipts'][0]['retained'], indent=2, sort_keys=True) + '\n').encode()
        for name, data in compact.items():
            (stage / name).write_bytes(data); manifest['compact_files'].append(dict(file=name, bytes=len(data), sha256=sha(data)))
        require(run(['git', 'rev-parse', 'HEAD'], 'closeout-head').strip() == head, 'HEAD changed during export')
        checked_tool_files(receipts['full']['tool_identity_before'], frozen)
        for name, value in producers.items(): require(digest(ROOT / name) == value, 'Exporter/helper changed during export')
        for path, value in frozen.items(): require(digest(path) == value, 'Retained input changed during export')
        require(sha(run(['git', 'diff', '--no-ext-diff', '--no-textconv', '--', *DOCS], 'closeout-intake-patch').encode()) == PATCH,
            'Intake document patch changed during export')
        for name, value in DOCS.items(): require(digest(ROOT / name) == value, 'Intake document changed during export')
        for item in manifest['receipts']:
            data = (stage / item['file']).read_bytes()
            require(sha(data) == item['compressed_sha256'] and gzip.decompress(data) == raw_bytes[item['kind']],
                'Exported receipt changed after compression')
        for item in manifest['compact_files']: require(digest(stage / item['file']) == item['sha256'], 'Compact export changed')
        manifest['export_files_sha256'] = shared.inventory(stage)
        manifest['exporter_retained_sha256'] = {name: value for name, value in shared.inventory(out).items()
            if not name.startswith('export/')}
        for name, value in manifest['exporter_retained_sha256'].items():
            require(digest(out / name) == value, 'Exporter command log/archive changed')
        manifest['bootstrap_commands'], manifest['commands'] = bootstrap_commands, run.records
        write_json(stage / 'manifest.json', manifest)
        require(not destination.exists(), 'Evidence destination appeared during export')
        destination.parent.mkdir(parents=True, exist_ok=True); stage.rename(destination)
        write_json(out / 'export-summary.json', dict(passed=True, destination=DESTINATION,
            manifest_sha256=digest(destination / 'manifest.json'), exporter_commit=head))
    except BaseException as error:
        write_json(out / 'export-failed.json', dict(passed=False, error=repr(error), exporter_commit=head,
            exporter_sha256=producers, commands=run.records)); raise
    print('Mapped streaming evidence exported: ' + str(destination), flush=True)


if __name__ == '__main__': main()
