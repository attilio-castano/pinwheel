"""Explicit root-only launch cards for a separately qualified logger observer.

Import and prepare are host-only. Heavy work occurs only after an explicit CLI
subcommand, under the existing campaign owner/lock/deadline runner.
"""
from __future__ import annotations
import argparse
import ast
from dataclasses import replace
import hashlib
import importlib.util
import json
from pathlib import Path
import shutil
import sys
import time

HERE = Path(__file__).resolve().parent
ROOT = Path('/Users/attiliocastano/.codex/worktrees/8259/pinwheel')
CAMPAIGN = ROOT / 'build/physical/tt-overnight-campaign-20261015'
SOURCE = CAMPAIGN / 'runs/p2-route-iter14-01/after'
HEADERS = ROOT / 'build/physical/tt-overnight-taper-tools-01/jobs/build-05'
DEPS = Path('/Users/attiliocastano/.codex/worktrees/c6eb/pinwheel/build/validation/hold-repair-01/headers')
NATIVE_SHA = '6ba87b45c762ee8c9670375c204cd03d801a6da98cd6e056a1c73027aad68a7c'
sys.path.insert(0, str(HERE))
from analyze import analyze


def read(p): return json.loads(Path(p).read_text())
def write(p, value): Path(p).write_text(json.dumps(value, indent=2) + '\n')
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    sys.modules[name] = mod
    spec.loader.exec_module(mod)
    return mod


def verify_files(values):
    for name, expected in values.items(): assert sha(name) == expected, name


def receipt(path, *, passed=True):
    p = Path(path); r = read(p)
    if passed: assert r['status'] == 'passed'
    assert r['inputs_unchanged'] and r['container_termination']['status'] == 'absent'
    assert r['within_absolute_and_job_deadlines']
    verify_files(r['input_sha256'])
    for name, expected in r['artifact_sha256'].items(): assert sha(p.parent / name) == expected, name
    return r


def observer_binary(build):
    r = receipt(build / 'report.json')
    b = read(build / 'build.json'); binary = build / 'libpinwheel_logger_observer.so'
    assert b['status'] == 'passed' and b['DRT_implementation_compiled'] is False
    assert sha(binary) == b['binary_sha256'] == r['artifact_sha256'][binary.name]
    return binary


def observer_native(base, iteration, control):
    source = base(iteration, control, False)
    anchor = "B,BG,BW=inventory('before')"
    assert source.count(anchor) == 1
    install = """import ctypes
_pw_logger_observer_handle=ctypes.CDLL('/work/diagnostic/libpinwheel_logger_observer.so',mode=os.RTLD_NOW|os.RTLD_GLOBAL)
tcl('load /work/diagnostic/libpinwheel_logger_observer.so Pinwheelloggerobserver')
tcl('pinwheel_logger_observer_install /work/diagnostic/observer.jsonl engine.memory.storage1 {A_BM[31]}')
B,BG,BW=inventory('before')"""
    source = source.replace(anchor, install)
    route = f'detailed_route -droute_end_iter {iteration} '
    assert source.count(route) == 1
    source = source.replace(route, route + '-verbose 2 ')
    error = 'error=tcl(cmd,allow_error=True)'
    assert source.count(error) == 1
    source = source.replace(error, error + "\ntcl('pinwheel_logger_observer_remove')")
    ast.parse(source)
    return source


def core(bundle):
    # Load the retained host runner/stage, never a moving maintained helper.
    sys.path.insert(0, str(bundle / 'host-base'))
    runner = module('runner', bundle / 'host-base/runner.py')
    module('drc', bundle / 'host-base/drc.py')
    stage = module('observer_base_stage', bundle / 'host-base/stage.py')
    stage.ROOT, stage.ORIGINAL = ROOT, ROOT / 'build/physical/tt-p2-drt-onepass-route-01'
    return runner, stage


def inputs(bundle, prepared, manifest):
    verify_files(prepared['bound_files_sha256'])
    values = dict(manifest['protected_sources_sha256'])
    values.update(manifest['reference_files_sha256'])
    values.update(prepared['bound_files_sha256'])
    values[str(bundle / 'prepared.json')] = sha(bundle / 'prepared.json')
    return values


def simple_job(args, bundle, prepared, manifest, runner):
    began = time.time()
    out = CAMPAIGN / 'runs' / args.name
    assert not (CAMPAIGN / 'heavy.lock').exists(), 'Root heavy slot occupied'
    out.mkdir(exist_ok=False)
    values = inputs(bundle, prepared, manifest)
    if args.mode == 'build':
        for name in ['observer.cc', 'native_build.py']: shutil.copyfile(bundle / name, out / name)
        cmd = ['python3', '-B', '/work/diagnostic/native_build.py']
        mounts = [(HEADERS, '/headers'), (DEPS, '/deps')]
        seconds, total = 300, 360
    else:
        binary = observer_binary(args.build_root)
        shutil.copyfile(binary, out / binary.name)
        shutil.copyfile(bundle / 'native_threads.py', out / 'native_threads.py')
        write(out / 'bindings.json', {'native_binary_sha256': NATIVE_SHA, 'observer_sha256': sha(binary)})
        cmd = ['openroad', '-python', '-exit', '-threads', '4', '-no_splash', '/work/diagnostic/native_threads.py']
        mounts = []; seconds, total = 60, 120
        values[str(args.build_root / 'report.json')] = sha(args.build_root / 'report.json')
        values[str(binary)] = sha(binary)
    values.update({str(p): sha(p) for p in out.rglob('*') if p.is_file()})
    spec = runner.JobSpec(out, CAMPAIGN / 'heavy.lock', manifest['image_id'], cmd,
        'tt-overnight-20261015-000717', min(manifest['hard_stop_epoch'] - 3600, began + total), values, seconds,
        max_job_seconds=total, closeout_reserve_seconds=45, minimum_native_seconds=15,
        cpus=4, memory='6g', readonly_mounts=mounts,
        scope='Separate logger-only observer qualification; no DRT implementation or physical edits.')
    result = runner.run_owned_job(spec)
    if args.mode == 'threads' and result['status'] == 'passed':
        check = analyze(out / 'observer.jsonl', 'threads')
        f = read(out / 'fixture.json'); assert f['original_exception_preserved']
        assert f['actual_native_binary_sha256'] == NATIVE_SHA and f['observer_sha256'] == sha(out / binary.name)
        write(out / 'observer-review.json', check)
    print(json.dumps({k: result.get(k) for k in ['status', 'exit_code', 'inputs_unchanged', 'container_termination']}, indent=2))
    return 0 if result['status'] == 'passed' else 1


def route_job(args, bundle, prepared, manifest, runner, stage):
    binary = observer_binary(args.build_root)
    assert sha(SOURCE / 'checkpoint.odb') == prepared['saved_C14_odb_sha256']
    receipt(args.thread_root / 'report.json')
    assert read(args.thread_root / 'observer-review.json')['status'] == 'logger_observation_complete'
    assert sha(args.thread_root / binary.name) == sha(binary)
    assert analyze(args.thread_root / 'observer.jsonl', 'threads')['status'] == 'logger_observation_complete'
    fixture = read(args.thread_root / 'fixture.json')
    assert fixture['original_exception_preserved'] and fixture['actual_native_binary_sha256'] == NATIVE_SHA
    assert fixture['observer_sha256'] == sha(binary)
    baseline = CAMPAIGN / 'runs/c14-control-01'
    receipt(baseline / 'report.json')
    assert read(baseline / 'stage-plan.json')['source_odb_sha256'] == prepared['saved_C14_odb_sha256']
    original_control = stage.parse_native_log((baseline / 'native.log').read_text(), producer_status='passed')
    assert original_control['completed_native_final_count'] == 1731
    if args.mode == 'probe':
        receipt(args.control_root / 'report.json')
        proof = read(args.control_root / 'observer-review.json')
        assert proof['mode'] == 'control' and proof['control_native_table_parity'] is True
        assert proof['observer_sha256'] == sha(binary)
        assert sha(args.control_root / binary.name) == sha(binary)
        analyze(args.control_root / 'observer.jsonl', 'control')
        actual = stage.parse_native_log((args.control_root / 'native.log').read_text(), producer_status='passed')
        assert actual['completed_native_final_count'] == 1731 and not actual['native_error_lines']
        assert actual['completed_native_final_table']['rows'] == original_control['completed_native_final_table']['rows']
    base_native, base_run = stage.native_program, stage.run_owned_job
    stage.native_program = lambda i, c, s: observer_native(base_native, i, c)

    def augment(spec):
        started = time.monotonic()
        out = spec.output_dir
        shutil.copyfile(binary, out / binary.name)
        write(out / 'observer-binding.json', {'observer_sha256': sha(binary),
            'build_receipt_sha256': sha(args.build_root / 'report.json'),
            'thread_fixture_receipt_sha256': sha(args.thread_root / 'report.json'),
            'baseline_control_receipt_sha256': sha(baseline / 'report.json'),
            'scope': 'fresh frDesign AP reads only during original native DRT1231; original sinks and exception retained'})
        phase = read(out / 'phase-inputs.json')
        for name in [binary.name, 'observer-binding.json']:
            phase['/work/diagnostic/' + name] = sha(out / name)
        write(out / 'phase-inputs.json', phase)
        values = dict(spec.input_sha256); values.update(inputs(bundle, prepared, manifest))
        for p in [binary, args.build_root / 'report.json', args.thread_root / 'report.json',
                  args.thread_root / 'observer-review.json', baseline / 'report.json', baseline / 'native-observations.json']:
            values[str(p)] = sha(p)
        if args.mode == 'probe': values[str(args.control_root / 'observer-review.json')] = sha(args.control_root / 'observer-review.json')
        values.update({str(p.resolve()): sha(p) for p in out.rglob('*') if p.is_file()})
        remaining = spec.max_job_seconds - (time.monotonic() - started)
        assert remaining > spec.closeout_reserve_seconds + spec.minimum_native_seconds
        return base_run(replace(spec, input_sha256=values, max_job_seconds=remaining,
            native_seconds=min(spec.native_seconds, remaining - spec.closeout_reserve_seconds)))

    stage.run_owned_job = augment
    card = prepared['base_adapter_argv']
    sys.argv = ['stage.py', '--manifest', str(CAMPAIGN / 'manifest.json'), '--name', args.name, *card,
        '--source-root', str(SOURCE), '--end-iter', '0' if args.mode == 'control' else '4',
        '--native-seconds', '600' if args.mode == 'control' else '900']
    if args.mode == 'control': sys.argv.append('--control')
    else: sys.argv += ['--control-root', str(args.control_root)]
    result = stage.main()
    out = CAMPAIGN / 'runs' / args.name
    producer = receipt(out / 'report.json', passed=args.mode == 'control')
    assert read(out / 'independent-scope-audit.json')['status'] == 'scope_verified'
    parsed = stage.parse_native_log((out / 'native.log').read_text(), producer_status=producer['status'])
    review = analyze(out / 'observer.jsonl', args.mode)
    review['observer_sha256'] = sha(binary)
    if args.mode == 'control':
        assert result == 0
        assert parsed['completed_native_final_table']['rows'] == original_control['completed_native_final_table']['rows']
        assert parsed['completed_native_final_count'] == 1731
        review['control_native_table_parity'] = True
    else:
        assert result == 1 and producer['status'] == 'failed' and producer['exit_code'] == 1
        old = stage.parse_native_log((CAMPAIGN / 'runs/c14-route-iter20-01/native.log').read_text(), producer_status='failed')
        assert [x['iteration'] for x in parsed['iteration_starts']] == [0, 1, 2, 3, 4]
        assert [(t['iteration'], t['rows']) for t in parsed['native_table_observations']] == [(t['iteration'], t['rows']) for t in old['native_table_observations']]
        assert len(parsed['native_error_lines']) == 1 and 'DRT-1231' in str(parsed['native_error_lines'])
        assert parsed['completed_native_final_count'] is None
        assert read(out / 'adjudication.json')['stage_execution_and_scope_gate_passed'] is False
        review.update({'expected_original_fatal_error_preserved': True, 'producer_status_retained': 'failed',
                       'prefix0_3_native_table_parity': True, 'candidate_accepted': False})
    write(out / 'observer-review.json', review)
    return result # Expected diagnostic failure remains exit1; never promote it.


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('mode', choices=['build', 'threads', 'control', 'probe'])
    parser.add_argument('--bundle', required=True, type=Path)
    parser.add_argument('--name', required=True)
    parser.add_argument('--build-root', type=Path)
    parser.add_argument('--thread-root', type=Path)
    parser.add_argument('--control-root', type=Path)
    args = parser.parse_args()
    assert args.name and all(c.isalnum() or c in '-_' for c in args.name)
    bundle = args.bundle.resolve(); prepared = read(bundle / 'prepared.json')
    verify_files(prepared['bound_files_sha256'])
    manifest = read(CAMPAIGN / 'manifest.json'); runner, stage = core(bundle)
    if args.mode in ('build', 'threads'): return simple_job(args, bundle, prepared, manifest, runner)
    return route_job(args, bundle, prepared, manifest, runner, stage)


if __name__ == '__main__': raise SystemExit(main())
