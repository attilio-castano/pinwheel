"""Fresh typed six-call R diagnostic with the reviewed narrow physical gate.

The complete original numerical and execution body is retained. Only typed
intake/report authority and the physical byte gate differ; Root alone admits
Native execution. Original failed byte/numeric gates are never relabeled.
"""
import argparse
import copy
import inspect
import json
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import sys
import time

sys.path.insert(0, str(Path(__file__).resolve().parent))
import streaming_8x4_rc_route_semantics as S

N, C = S.N, S.N.C
P, need = C.P, C.need
POLICIES, parse_spef, analyze_values = C.POLICIES, C.parse_spef, C.analyze_values
BASELINE_HASH = 'dd1cad5279255f2f7d793594c0f54d565af2b89a924c9a7701436c406e0f0cb3'
EXPECTED_BEFORE = '9d50fc55eff69c38f634f78b7b8b2ce692f068f9592c594a6d670a91c768245b'
EXPECTED_AFTER = '64bb1f1731e79adbf840d3e861aa7cd6389a6ce5dde4b61356500f5b6a41e608'
SCHEMA = 'pinwheel.streaming-8x4-rc-consumer-route-plan.v1'
NEW = ('streaming_8x4_rc_route_semantics.py', 'streaming_8x4_rc_consumer_semantic.py',
       'streaming_8x4_rc_consumer_semantic_readback.py', 'streaming_8x4_rc_consumer_readback.py')


def write(path, value): N.write(path, value)


def producers(old):
    result = dict(old['producer_sha256'])
    result.update({name: P.sha(Path(__file__).with_name(name)) for name in NEW})
    return dict(sorted(result.items()))


def prepare(baseline, writer_source, failed, output):
    old = N.verify(baseline, BASELINE_HASH)
    need(not output.exists() and output.parent.is_dir(), 'Fresh semantic preparation owner required')
    source = S.source_evidence(writer_source, baseline / 'source-evidence')
    failure = json.loads((failed / 'report.json').read_text())
    inner_failure = json.loads((failed / 'native/report.json').read_text())
    owner = failed / 'native/MIN-retained_rules'
    need(failure['schema'] == 'pinwheel.streaming-8x4-rc-consumer-DEF-NDR-execution.v1'
        and failure['plan_sha256'] == BASELINE_HASH and failure['passed'] is False
        and failure['all_six_native_calls_closed'] is False and failure['inputs_unchanged'] is True
        and inner_failure['schema'] == 'pinwheel.streaming-8x4-rc-consumer-execution.v1'
        and inner_failure['passed'] is False and inner_failure['jobs'] == []
        and inner_failure['error'] == 'ValueError: Extraction changed geometry DEF readback'
        and P.sha(owner / 'before.def') == EXPECTED_BEFORE and P.sha(owner / 'after.def') == EXPECTED_AFTER,
        'Original measured byte-gate failure differs')
    output.mkdir(); shutil.copytree(baseline, output / 'baseline-ndr-preparation')
    shutil.copytree(writer_source, output / 'writer-source')
    shutil.copytree(baseline / 'consumer-inputs', output / 'consumer-inputs')
    (output / 'failed-byte-gate').mkdir()
    for path, name in ((failed / 'report.json', 'report.json'), (failed / 'native/report.json', 'native-report.json'),
        (owner / 'native.log', 'native.log'), (owner / 'before.def', 'before.def'), (owner / 'after.def', 'after.def'),
        (owner / 'result.spef', 'result.spef')): shutil.copyfile(path, output / 'failed-byte-gate' / name)
    plan = dict(schema=SCHEMA, qualified=False, model_qualified=False, native_executed=False, root_go_required=True,
        baseline_NDR_plan_sha256=BASELINE_HASH, consumer_plan_sha256=old['consumer_plan_sha256'],
        expected_native_before_DEF_sha256=EXPECTED_BEFORE, source_evidence=source,
        producer_sha256=producers(old), protocol=old['protocol'], fixture_rows=old['fixture_rows'],
        consumer_numeric_math_unchanged=True, all_six_corner_policy_calls_required=True,
        physical_gate='Exact selected Native import plus complete physical facts and only proven via-exit NEW normalization',
        files_sha256=N.file_inventory(output))
    write(output / 'plan.json', plan); verify(output, P.sha(output / 'plan.json'))
    return dict(plan_sha256=P.sha(output / 'plan.json'), native_executed=False, model_qualified=False)


def verify(base, plan_hash):
    need(P.sha(base / 'plan.json') == plan_hash, 'Semantic plan identity differs')
    plan = json.loads((base / 'plan.json').read_text()); old = N.verify(base / 'baseline-ndr-preparation', BASELINE_HASH)
    actual = N.file_inventory(base); actual.pop('plan.json')
    need(plan['schema'] == SCHEMA and all(plan[k] is False for k in ('qualified', 'model_qualified', 'native_executed'))
        and plan['root_go_required'] is True and plan['baseline_NDR_plan_sha256'] == BASELINE_HASH
        and actual == plan['files_sha256'] and plan['producer_sha256'] == producers(old)
        and plan['consumer_plan_sha256'] == old['consumer_plan_sha256'] and plan['protocol'] == old['protocol']
        and plan['fixture_rows'] == old['fixture_rows'] and plan['expected_native_before_DEF_sha256'] == EXPECTED_BEFORE
        and plan['consumer_numeric_math_unchanged'] is True and plan['all_six_corner_policy_calls_required'] is True
        and plan['physical_gate'] == 'Exact selected Native import plus complete physical facts and only proven via-exit NEW normalization'
        and plan['source_evidence'] == S.source_evidence(base / 'writer-source', base / 'baseline-ndr-preparation/source-evidence'),
        'Semantic typed scope/source/unchanged experiment custody differs')
    need(N.file_inventory(base / 'consumer-inputs') == N.file_inventory(base / 'baseline-ndr-preparation/consumer-inputs'),
        'Semantic consumer input bytes differ from original NDR plan')
    need(P.sha(base / 'failed-byte-gate/before.def') == EXPECTED_BEFORE
        and P.sha(base / 'failed-byte-gate/after.def') == EXPECTED_AFTER, 'Original failed byte evidence differs')
    return plan


def verify_consumer(base, plan_hash):
    outer = verify(base.parent, P.sha(base.parent / 'plan.json'))
    need(outer['consumer_plan_sha256'] == plan_hash, 'Semantic consumer identity differs')
    return C.verify_plan(base, plan_hash)


def geometry_gate(base, directory):
    plan = verify_consumer(base, P.sha(base / 'plan.json'))
    before, after = directory / 'before.def', directory / 'after.def'
    need(all(p.is_file() and not p.is_symlink() for p in (before, after))
        and P.sha(before) == EXPECTED_BEFORE, 'Actual initial Native DEF differs from exact selected import authority')
    witness = json.loads((base.parent / 'baseline-ndr-preparation/NDR-witness.json').read_text())
    return S.compare(before.read_text(), after.read_text(), (base / 'tech.lef').read_text(), witness, plan['fixture_rows'])


def run_native(base, plan_hash, output):
    plan = verify_consumer(base, plan_hash)
    need(not output.exists() and output.parent.is_dir(), 'Consumer output directory must be fresh')
    # Root separately observes image identity, Docker admission and cleanup.
    cg = Path('/sys/fs/cgroup'); memory = (cg / 'memory.max').read_text().strip()
    cpu = (cg / 'cpu.max').read_text().split(); swap = (cg / 'memory.swap.max').read_text().strip()
    pids = (cg / 'pids.max').read_text().strip()
    need(memory.isdigit() and 0 < int(memory) <= 2147483648 and swap == '0', 'Consumer memory/swap ceiling differs')
    need(len(cpu) == 2 and cpu[0].isdigit() and 0 < int(cpu[0]) <= int(cpu[1]), 'Consumer CPU ceiling differs')
    need(pids.isdigit() and 0 < int(pids) <= 256, 'Consumer PID ceiling differs')
    output.mkdir(); started = time.monotonic(); jobs = []
    report = {'schema': 'pinwheel.streaming-8x4-rc-consumer-route-native-execution.v1', 'plan_sha256': plan_hash,
              'passed': False, 'qualified': False, 'model_qualified': False, 'jobs': jobs}
    try:
        for corner in ('MIN', 'TYP', 'MAX'):
            for policy in POLICIES:
                need(time.monotonic() - started < 175, 'Insufficient predeclared consumer work budget')
                directory = output / (corner + '-' + policy); directory.mkdir()
                for name in ('tech.lef', 'widths.lef', 'fixture.def', 'run.tcl'):
                    shutil.copyfile(base / name, directory / name)
                shutil.copyfile(base / (corner + '-' + policy + '.txt'), directory / 'rules.txt')
                before = {p.name: P.sha(p) for p in directory.iterdir()}
                log = directory / 'native.log'; command = ['openroad', '-no_init', '-exit', 'run.tcl']
                child = None
                with log.open('wb') as stream:
                    child = subprocess.Popen(command, cwd=directory, stdout=stream, stderr=subprocess.STDOUT,
                                             start_new_session=True)
                    try:
                        code = child.wait(timeout=30)
                    except subprocess.TimeoutExpired:
                        os.killpg(child.pid, signal.SIGKILL); child.wait()
                        raise ValueError('Consumer OpenROAD timeout')
                need(type(code) is int and code == 0, 'Consumer OpenROAD nonzero exit')
                try:
                    os.killpg(child.pid, 0)
                except ProcessLookupError:
                    pass
                else:
                    os.killpg(child.pid, signal.SIGKILL)
                    raise ValueError('Consumer OpenROAD left a live process group')
                raw = log.read_text()
                need(not re.search(r'(?im)\b(?:warning|warn|error|fatal)\b', raw), 'Consumer native warning/error')
                need(raw.count('PINWHEEL_CONSUMER_TERMINAL') == 1, 'Missing/duplicate terminal marker')
                geometry = geometry_gate(base, directory)
                write(directory / 'semantic-geometry.json', geometry)
                need(all(P.sha(directory / name) == value for name, value in before.items()), 'Copied consumer input changed')
                values = parse_spef((directory / 'result.spef').read_text(), {r['name'] for r in plan['fixture_rows']})
                result = analyze_values(plan, corner, policy, values)
                jobs.append({'corner': corner, 'policy': policy, 'argv': command, 'exit_code': code,
                             'native_log_sha256': P.sha(log), 'SPEF_sha256': P.sha(directory / 'result.spef'),
                             'geometry_unchanged': True, 'semantic_geometry_sha256': P.sha(directory / 'semantic-geometry.json'),
                             'copied_inputs_unchanged': True,
                             'process_tree_reaped': True, 'values': values, 'analysis': result})
                # Record all six measurements without adapting or silently dropping failed numeric controls.
        verify_consumer(base, plan_hash)
        report['inputs_unchanged'] = True
        report['passed'] = len(jobs) == 6 and all(j['analysis']['passed'] for j in jobs)
    except Exception as error:
        report['error'] = type(error).__name__ + ': ' + str(error)
    report['wall_seconds'] = time.monotonic() - started
    (output / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    return report


def run(base, plan_hash, output):
    plan = verify(base, plan_hash); need(not output.exists() and output.parent.is_dir(), 'Fresh semantic execution owner required')
    output.mkdir(); result = dict(schema='pinwheel.streaming-8x4-rc-consumer-route-execution.v1', qualified=False,
        model_qualified=False, plan_sha256=plan_hash, passed=False, all_six_native_calls_closed=False,
        original_numeric_policy_unchanged=True, initial_native_DEF_exact=True)
    try:
        inner = run_native(base / 'consumer-inputs', plan['consumer_plan_sha256'], output / 'native')
        result.update(passed=inner['passed'], all_six_native_calls_closed=len(inner['jobs']) == 6,
            inner_report_sha256=P.sha(output / 'native/report.json'))
    except BaseException as error: result['error'] = type(error).__name__ + ': ' + str(error)
    finally:
        result['inputs_unchanged'] = verify(base, plan_hash) == plan; result['passed'] &= result['inputs_unchanged']
        write(output / 'report.json', result)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__); sub = parser.add_subparsers(dest='mode', required=True)
    p = sub.add_parser('prepare')
    for name in ('baseline', 'writer-source', 'failed', 'output'): p.add_argument('--' + name, type=Path, required=True)
    for mode in ('verify', 'run'):
        p = sub.add_parser(mode); p.add_argument('--inputs', type=Path, required=True); p.add_argument('--plan-sha256', required=True)
        if mode == 'run': p.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    value = prepare(args.baseline, args.writer_source, args.failed, args.output) if args.mode == 'prepare' else \
        verify(args.inputs, args.plan_sha256) if args.mode == 'verify' else run(args.inputs, args.plan_sha256, args.output)
    print(json.dumps(value, indent=2)); return 2 if args.mode == 'run' and not value['passed'] else 0


if __name__ == '__main__': raise SystemExit(main())
