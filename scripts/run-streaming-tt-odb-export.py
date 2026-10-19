#!/usr/bin/env python3
"""Read exact closed physical ODB connectivity in one bounded native process.

This records diagnostic readback, not physical or functional acceptance.
"""
import argparse
from datetime import datetime, timezone
import importlib.util
import json
import os
from pathlib import Path
import shutil
import subprocess
import time
import uuid

import streaming_tt_physical as P
from streaming_tt_intake import dependency_closure

ROOT = P.ROOT


def check_environment(environment=None):
    environment = os.environ if environment is None else environment
    fixed = {'PYTHONPATH', 'PYTHONHOME', 'PYTHONSTARTUP', 'PYTHONPYCACHEPREFIX', 'LD_PRELOAD', 'LD_LIBRARY_PATH',
        'LEAN_PATH', 'LEAN_SRC_PATH', 'LEAN_SYSROOT', 'LAKE_HOME', 'LAKE_PACKAGES_DIR', 'LAKE_CACHE_DIR'}
    prefixes = ('DYLD_', 'YOSYS_', 'ABC_', 'Z3_', 'CIRCT_', 'OPENROAD_', 'KLAYOUT_', 'MAGIC_', 'NETGEN_',
        'VVP_', 'IVERILOG_', 'IVL_', 'VPI_')
    bad = sorted(name for name, value in environment.items() if value and (name in fixed or name.startswith(prefixes)))
    P.require(not bad, 'Refuse inherited compiler/cache/loader overrides: '+', '.join(bad))


def select(report_path, state_path):
    report_path, state_path = P.regular(report_path).resolve(), P.regular(state_path).resolve()
    report, state = P.read(report_path), P.read(state_path)
    closed_exit = type(report.get('exit_code')) is int and ((report.get('status') == 'flow_completed' and
        report['exit_code'] == 0) or (report.get('status') == 'failed' and report['exit_code'] != 0))
    P.require(report.get('schema') in ('pinwheel.streaming-tt-physical-run.v2', 'pinwheel.streaming-tt-final-run.v1') and
        closed_exit and
        report.get('inputs_unchanged_after_run') is True and
        report.get('container_termination', {}).get('status') == 'absent', 'Physical run is not closed')
    root = report_path.parent
    P.require(state_path.is_relative_to(root) and report['artifact_sha256'].get(str(state_path.relative_to(root))) ==
        P.sha(state_path), 'State is not the selected closed physical artifact')
    matches = [row for row in report['states'] if Path(row['state']).resolve() == state_path and
        row['state_sha256'] == P.sha(state_path)]
    P.require(len(matches) == 1 and type(matches[0]['views'].get('odb')) is dict, 'State has no unique actual ODB view')
    binding = matches[0]['views']['odb']; database = P.regular(binding['path']).resolve()
    P.require(database.is_relative_to(root) and binding['sha256'] == P.sha(database) ==
        report['artifact_sha256'].get(str(database.relative_to(root))), 'ODB is not the closed authoritative artifact')
    P.require(state.get('odb') == binding['container'], 'State ODB pointer differs from selected actual view')
    return report, database


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--physical-report', required=True, type=Path)
    parser.add_argument('--state', required=True, type=Path)
    parser.add_argument('--reference', required=True, type=Path)
    parser.add_argument('--top', required=True)
    parser.add_argument('--tag', required=True)
    parser.add_argument('--memory-mb', type=int, default=2048)
    args = parser.parse_args(); P.safe_name(args.tag); check_environment()
    P.require(256 <= args.memory_mb <= 2048, 'Readback memory must be between 256 and 2048 MiB')
    report, database = select(args.physical_report, args.state)
    reference = P.regular(args.reference).resolve()
    source = P.ROOT/'scripts/streaming_tt_export_odb.py'
    closure = dependency_closure(ROOT, ['scripts/run-streaming-tt-odb-export.py',
        'scripts/streaming_tt_export_odb.py', 'tools/physical-toolchain.json'])
    sources = closure['files']
    for name in sources: P.committed(P.ROOT/name)
    consumed = [database, reference, args.physical_report.resolve(), args.state.resolve(),
        *(P.ROOT/name for name in sources)]
    before = {str(path): P.sha(path) for path in consumed}
    out = P.ROOT/'build/streaming-physical-development'/args.tag; out.mkdir(parents=True, exist_ok=False)
    inputs = out/'inputs'; inputs.mkdir()
    for name, path in (('actual.odb', database), ('reference.json', reference), ('export.py', source)):
        shutil.copyfile(path, inputs/name); (inputs/name).chmod(0o444)
    native_argv = ['/inputs/export.py', '--database', '/inputs/actual.odb', '--reference',
        '/inputs/reference.json', '--top', args.top, '--out', '/outputs/export']
    (inputs/'launch.py').write_text('import runpy,sys\nsys.argv='+repr(native_argv)+
        '\nrunpy.run_path("/inputs/export.py",run_name="__main__")\n')
    (inputs/'launch.py').chmod(0o444)
    staged = {str(path.relative_to(inputs)): P.sha(path) for path in inputs.iterdir()}
    outputs = out/'native'; outputs.mkdir()
    owner = str(uuid.uuid4()); runtime = P.inspect_runtime(P.read(P.ROOT/'tools/physical-toolchain.json'))
    command = ['docker', 'run', '--rm', '--pull', 'never', '--name', 'pinwheel-odb-'+args.tag,
        '--label', 'org.pinwheel.streaming_tt_owner='+owner, '--network', 'none', '--cpus', '1', '--memory', str(args.memory_mb)+'m',
        '--memory-swap', str(args.memory_mb)+'m',
        '--read-only', '--cap-drop', 'ALL', '--security-opt', 'no-new-privileges',
        '--env', 'PYTHONDONTWRITEBYTECODE=1',
        '--mount', 'type=bind,source='+str(inputs)+',target=/inputs,readonly',
        '--mount', 'type=bind,source='+str(outputs)+',target=/outputs', runtime['image_id'],
        'openroad', '-no_init', '-exit', '-python', '/inputs/launch.py']
    receipt = dict(schema='pinwheel.streaming-tt-odb-export-run.v1', qualified=False,
        physical_acceptance_claim=False, status='running', started_utc=datetime.now(timezone.utc).isoformat(),
        physical_report=str(args.physical_report.resolve()), source_commit=report.get('candidate_source_commit', report.get('source_commit')),
        physical_producer_status=report['status'], physical_producer_exit_code=report['exit_code'],
        producer_commit=subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=P.ROOT, text=True).strip(),
        actual_odb=str(database), actual_odb_sha256=P.sha(database), reference=str(reference),
        input_sha256=before, staged_input_sha256=staged, producer_dependency_closure=closure,
        command=command, native_exporter_argv=native_argv, runtime=runtime, inherited_override_guard_checked_before_output=True,
        ownership_label=owner, cpus=1, memory=str(args.memory_mb)+'m', memory_swap=str(args.memory_mb)+'m',
        network='none', timeout_seconds=120)
    P.write(out/'report.json', receipt); started = time.monotonic()
    with (out/'native.log').open('w') as log:
        try:
            result = subprocess.run(command, stdout=log, stderr=subprocess.STDOUT, timeout=120)
            receipt.update(exit_code=result.returncode, status='exported' if result.returncode == 0 else 'failed')
        except subprocess.TimeoutExpired:
            receipt.update(exit_code=124, status='timed_out')
        finally:
            spec = importlib.util.spec_from_file_location('_coarse_cleanup', ROOT/'scripts/run-streaming-tt-physical.py')
            module = importlib.util.module_from_spec(spec); spec.loader.exec_module(module)
            receipt['container_termination'] = module.cleanup(owner, log)
            receipt['inputs_unchanged'] = before == {str(path): P.sha(path) for path in consumed}
            receipt['staged_inputs_unchanged'] = staged == {str(path.relative_to(inputs)): P.sha(path) for path in inputs.iterdir()}
            receipt['runtime_unchanged'] = runtime == P.inspect_runtime(P.read(P.ROOT/'tools/physical-toolchain.json'))
            receipt['elapsed_seconds'] = round(time.monotonic()-started, 3)
            receipt['artifact_sha256'] = {str(path.relative_to(out)): P.sha(path) for path in sorted(outputs.rglob('*')) if path.is_file()}
            log.flush(); receipt['native_log_sha256'] = P.sha(out/'native.log')
            exported = outputs/'export/receipt.json'
            receipt['native_export_binding'] = False
            if receipt.get('exit_code') == 0 and exported.is_file():
                native = P.read(exported)
                receipt['native_export_binding'] = (native.get('schema') == 'pinwheel.streaming-tt-odb-export.v1' and
                    native.get('database_sha256') == before[str(database)] and
                    native.get('reference_sha256') == before[str(reference)] and
                    native.get('source_sha256') == before[str(source)] and native.get('top') == args.top and
                    native.get('read_only_database') is True and set(native.get('artifacts_sha256', {})) ==
                    {'connectivity.json', 'inventory.json'} and all(P.sha(P.regular(exported.parent/name)) == value
                    for name, value in native['artifacts_sha256'].items()))
            receipt['passed'] = receipt.get('exit_code') == 0 and receipt['native_export_binding'] and receipt['inputs_unchanged'] and receipt['staged_inputs_unchanged'] and receipt['runtime_unchanged'] and receipt['container_termination']['status'] == 'absent'
            P.write(out/'report.json', receipt)
    print(out/'report.json')
    return 0 if receipt['passed'] else 1


if __name__ == '__main__': raise SystemExit(main())
