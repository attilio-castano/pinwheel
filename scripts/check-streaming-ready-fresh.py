#!/usr/bin/env python3
"""Run the unchanged UART components gate with an exact completed649 foundation.

The original coordinator still owns emission, raw/wrapper certificates and all
of its negative controls. This adapter owns library provenance and bounded
direct Lean commands; it never calls an unconstrained Lake build.
"""
import argparse
from contextlib import contextmanager
import importlib.util
import json
from pathlib import Path
import sys

import streaming_tt_fresh_foundation as F

ROOT = Path(__file__).resolve().parents[1]
ORIGINAL = 'scripts/check-streaming-uart.py'


def load_gate(root):
    spec = importlib.util.spec_from_file_location('_fresh649_original_uart_gate', Path(root) / ORIGINAL)
    gate = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = gate
    spec.loader.exec_module(gate)
    return gate


def dump(path, value):
    Path(path).write_text(json.dumps(value, indent=2) + '\n')


def artifact_map(root):
    return {path.relative_to(root).as_posix(): F.sha(path) for path in sorted(Path(root).rglob('*'))
            if path.is_file() and path != Path(root) / 'worker-report.json'}


@contextmanager
def master_hooks(gate, foundation_path, runtime_path, state):
    original = gate.helpers
    def helpers():
        helper = original()
        old_write, old_load = helper.write_json, helper.load_helpers
        def write(path, data):
            if Path(path).name == 'worker-config.json':
                F.require(data['stage'] == 'components' and data['source_commit'] == data['producer_commit'],
                          'Fresh adapter requires one exact same-commit components gate')
                binding = F.create_binding(foundation_path, runtime_path, data['snapshot'],
                                           data['source_commit'], data['tool_paths'])
                F.require(all(F.sha(ROOT / name) == value for name, value in binding['adapter_source_sha256'].items()),
                          'Executed adapter/master interpreter differs from selected committed archive')
                binding_path = Path(path).parent / 'fresh-foundation-binding.json'
                F.require(not binding_path.exists(), 'Preserve an earlier binding')
                dump(binding_path, binding)
                data['fresh_foundation'] = F.bound(binding_path)
                state.update(config_path=Path(path), marker=data['fresh_foundation'], binding=binding)
            return old_write(path, data)
        def load(root):
            orchestration = old_load(root)
            base = orchestration.Commands
            class Commands(base):
                def __call__(self, argv, label, **options):
                    if label == 'fresh-continuation-worker':
                        F.require(state and '--worker-config' in list(map(str, argv)), 'Worker invoked before foundation binding')
                        config = F.read(state['config_path'])
                        entry = Path(config['snapshot']) / 'scripts/check-streaming-ready-fresh.py'
                        argv = [config['tool_paths']['python'], '-B', entry, '--worker-config', state['config_path'],
                                '--producer-root', Path(argv[2]).resolve().parents[1]]
                    return super().__call__(argv, label, **options)
            orchestration.Commands = Commands
            return orchestration
        helper.write_json, helper.load_helpers = write, load
        return helper
    gate.helpers = helpers
    try:
        yield
    finally:
        gate.helpers = original


@contextmanager
def worker_hooks(gate, binding, marker, config):
    original = gate.helpers
    worker_out = Path(config['worker_out'])
    entry = Path(binding['candidate_root']) / 'scripts/check-streaming-ready-fresh.py'
    def helpers():
        helper = original()
        old_load = helper.load_helpers
        def load(root):
            orchestration = old_load(root)
            base = orchestration.Commands
            class Commands(base):
                def __call__(self, argv, label, **options):
                    requested = list(map(str, argv))
                    actual = F.bounded_command(requested, binding, worker_out, entry, marker['path'])
                    sources = {}
                    for value in actual:
                        if value.endswith('.lean'):
                            path = Path(value)
                            if not path.is_absolute(): path = Path(binding['candidate_root']) / path
                            path = F.regular(path.resolve())
                            F.require(path.is_relative_to(worker_out) or path.is_relative_to(Path(binding['candidate_root'])),
                                      'Proof source escapes the selected archive/worker')
                            sources[str(path)] = F.sha(path)
                    row = dict(label=label, requested_argv=requested, actual_argv=actual,
                               source_sha256_before=sources, expected_failure=bool(options.get('reject')))
                    if binding['lean'] in actual:
                        row['compiler_sha256_before'] = F.sha(binding['lean'])
                    try:
                        return super().__call__(actual, label, **options)
                    finally:
                        row['source_sha256_after'] = {path: F.sha(path) for path in sources}
                        row['record'] = dict(self.records[-1])
                        if binding['lean'] in actual:
                            row['compiler_sha256_after'] = F.sha(binding['lean'])
                        with (worker_out / 'fresh-foundation-native-journal.jsonl').open('a') as stream:
                            stream.write(json.dumps(row) + '\n')
            orchestration.Commands = Commands
            return orchestration
        helper.load_helpers = load
        return helper
    gate.helpers = helpers
    try:
        yield
    finally:
        gate.helpers = original


def worker(config_path, producer_root):
    config_path = F.regular(Path(config_path).resolve())
    config = F.read(config_path)
    F.require(config.get('stage') == 'components' and config['source_commit'] == config['producer_commit'],
              'Fresh worker requires exact same-commit raw components')
    marker = config['fresh_foundation']
    binding = F.read(F.verify_bound(marker))
    F.require(binding['candidate_commit'] == config['source_commit'] and
              Path(binding['candidate_root']) == Path(config['snapshot']).resolve(), 'Fresh worker source selection mismatch')
    for relative in F.ADAPTERS:
        F.require(F.sha(ROOT / relative) == config['source_sha256'][relative] == binding['adapter_source_sha256'][relative],
                  'Executed fresh adapter differs from committed source archive')
    F.stage_library(binding, config['snapshot'])
    gate = load_gate(producer_root)
    failure = None
    try:
        with worker_hooks(gate, binding, marker, config):
            gate.worker(config_path)
    except BaseException as error:
        failure = error
    report_path = Path(config['worker_out']) / 'worker-report.json'
    if report_path.exists():
        report = F.read(report_path)
        try:
            F.verify_binding(binding)
            F.verify_staged(binding)
            closure = dict(schema='pinwheel.streaming-tt-fresh-foundation-import-closeout.v1',
                passed=failure is None and report.get('passed') is True, qualified=False,
                binding=marker, positive_modules=649, excluded_negative_control_objects=binding['excluded_negative_control_artifact_sha256'],
                positive_library_unchanged=True, source_projection_unchanged=True, runtime_unchanged=True)
            report['fresh_foundation'] = marker
            report['fresh_foundation_closeout'] = closure
        except BaseException as error:
            report.update(passed=False, fresh_foundation_error=str(error))
            failure = error
        report['artifact_sha256'] = artifact_map(Path(config['worker_out']))
        dump(report_path, report)
    if failure:
        raise failure


def main():
    parser = argparse.ArgumentParser(description=__doc__, add_help=False)
    parser.add_argument('--foundation-report', type=Path)
    parser.add_argument('--runtime-companion', type=Path)
    parser.add_argument('--worker-config', type=Path)
    parser.add_argument('--producer-root', type=Path)
    parser.add_argument('--verify-stage', type=Path)
    parser.add_argument('--compiler-path', type=Path)
    parser.add_argument('--compiler-search', type=Path)
    args, remaining = parser.parse_known_args()
    query = args.verify_stage or args.compiler_path or args.compiler_search
    if query:
        F.require(not remaining, 'Unexpected verification arguments')
        binding = F.read(query)
        F.verify_staged(binding)
        if args.compiler_path: print(binding['lean'])
        elif args.compiler_search:
            print(str(Path(binding['candidate_root']) / '.lake/build/lib/lean') + ':' + str(Path(binding['lean']).parent.parent / 'lib/lean'))
        else: print('Exact649 positive library verified; foundation negative-control object excluded.')
        return
    if args.worker_config:
        F.require(args.producer_root is not None and not remaining, 'Worker requires its committed original producer root')
        worker(args.worker_config, args.producer_root)
        return
    F.require(args.foundation_report is not None and args.runtime_companion is not None,
              'Provide the completed649 foundation and its closed runtime companion')
    gate = load_gate(ROOT)
    F.require('--stage' in remaining and remaining[remaining.index('--stage') + 1] == 'components',
              'This adapter runs only the existing complete components stage')
    state = {}
    old_argv = sys.argv
    try:
        sys.argv = [str(ROOT / ORIGINAL), *remaining]
        with master_hooks(gate, args.foundation_report, args.runtime_companion, state):
            gate.main()
        config = F.read(state['config_path'])
        report_path = state['config_path'].parent / 'report.json'
        report = F.read(report_path)
        F.verify_binding(state['binding'])
        F.verify_staged(state['binding'])
        report['fresh_foundation'] = state['marker']
        report['fresh_foundation_adapter_source_sha256'] = state['binding']['adapter_source_sha256']
        report['fresh_foundation_adapter_closed'] = True
        dump(report_path, report)
    except BaseException as error:
        if state and (state['config_path'].parent / 'report.json').is_file():
            report_path = state['config_path'].parent / 'report.json'
            report = F.read(report_path)
            report.update(passed=False, fresh_foundation_adapter_closed=False,
                          fresh_foundation_adapter_error=type(error).__name__ + ': ' + str(error))
            dump(report_path, report)
        raise
    finally:
        sys.argv = old_argv


if __name__ == '__main__':
    main()
