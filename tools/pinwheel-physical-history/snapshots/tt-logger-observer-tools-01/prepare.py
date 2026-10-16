"""Prepare a NEW immutable package and cards. No native execution."""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import shutil

ROOT = Path(__file__).resolve().parents[2]
TOOLS = Path(__file__).resolve().parent
CAMPAIGN = ROOT / 'build/physical/tt-overnight-campaign-20261015'
HEADERS = ROOT / 'build/physical/tt-overnight-taper-tools-01/jobs/build-05'
DEPS = Path('/Users/attiliocastano/.codex/worktrees/c6eb/pinwheel/build/validation/hold-repair-01/headers')


def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args(); out = args.output.resolve(); out.mkdir(parents=True, exist_ok=False)
    for name in ['observer.cc', 'launch.py', 'analyze.py', 'native_build.py', 'native_threads.py', 'prepare.py', 'README.md']:
        shutil.copyfile(TOOLS / name, out / name)
    shutil.copytree(TOOLS / 'tests', out / 'tests', ignore=shutil.ignore_patterns('__pycache__'))
    shutil.copytree(TOOLS / 'source-evidence', out / 'source-evidence')
    (out / 'host-base').mkdir()
    for name in ['stage.py', 'runner.py', 'drc.py']:
        shutil.copyfile(ROOT / 'tools/pinwheel-physical-campaign' / name, out / 'host-base' / name)
    files = {str(p): sha(p) for p in out.rglob('*') if p.is_file()}
    # Bind the complete header/dependency content actually read by this build.
    for top in [HEADERS / 'source', HEADERS / 'source-extra-01', HEADERS / 'source-extra-02', HEADERS / 'generated-03/include', DEPS]:
        for p in top.rglob('*'):
            if p.is_file(): files[str(p)] = sha(p)
    reference = HEADERS / 'native-05/build.json'; files[str(reference)] = sha(reference)
    files[str(CAMPAIGN / 'manifest.json')] = sha(CAMPAIGN / 'manifest.json')
    adapter = HEADERS / 'native-05/patched/libpinwheel_drt_preservation.so'
    fixture = ROOT / 'build/physical/tt-overnight-taper-tools-01/jobs/regression-06'
    base = ['--adapter', str(adapter), '--adapter-build-receipt', str(reference),
        '--adapter-build-job-receipt', str(HEADERS / 'report.json'),
        '--adapter-fixture-receipt', str(fixture / 'results/regression.json'),
        '--adapter-fixture-job-receipt', str(fixture / 'report.json')]
    saved_c14 = CAMPAIGN / 'runs/p2-route-iter14-01/after'
    for name in ['checkpoint.odb', 'checkpoint.def', 'native-inventory.json', 'master-OBS-signature.json', 'via-definitions.json']:
        files[str(saved_c14 / name)] = sha(saved_c14 / name)
    for name in ['report.json', 'native.log']:
        p = CAMPAIGN / 'runs/c14-route-iter20-01' / name
        files[str(p)] = sha(p)
    prepared = {'schema': 'pinwheel-standalone-logger-observer-prepared-v1',
        'status': 'host_prepared_native_uncompiled_unqualified', 'bound_files_sha256': files,
        'base_adapter_argv': base, 'qualified_adapter_is_unchanged': True,
        'saved_C14_odb_sha256': sha(saved_c14 / 'checkpoint.odb'),
        'native_source_revision': 'dcf36133a369abc8f3c5e5738cd4d82e4903c0e0',
        'mandatory_order': ['build', 'threads', 'control', 'probe'], 'physical_acceptance_claim': False}
    (out / 'prepared.json').write_text(json.dumps(prepared, indent=2) + '\n')
    build, threads, control = [CAMPAIGN / 'runs' / n for n in ['logger-observer-build-01', 'logger-observer-threads-01', 'logger-observer-C14-control-01']]
    cards = {}
    for mode, name in [('build', build.name), ('threads', threads.name), ('control', control.name), ('probe', 'logger-observer-C14-error-probe-01')]:
        argv = ['python3', '-B', str(out / 'launch.py'), mode, '--bundle', str(out), '--name', name]
        if mode != 'build': argv += ['--build-root', str(build)]
        if mode in ('control', 'probe'): argv += ['--thread-root', str(threads)]
        if mode == 'probe': argv += ['--control-root', str(control)]
        cards[mode] = {'argv': argv, 'only_root_may_launch': True, 'requires_all_previous_gates': True,
            'native_all_in_seconds': {'build': [300, 360], 'threads': [60, 120], 'control': [600, 660], 'probe': [900, 960]}[mode]}
    cards.update({'schema': 'pinwheel-logger-observer-execution-cards-v1',
        'prepared_sha256': sha(out / 'prepared.json'), 'status': 'native_execution_not_performed',
        'campaign_native_cutoff_UTC': '2026-10-16T07:07:17Z',
        'campaign_hard_end_UTC': '2026-10-16T08:07:17Z',
        'probe_expected_producer_exit': 1, 'probe_is_never_an_accepted_routing_candidate': True})
    (out / 'cards.json').write_text(json.dumps(cards, indent=2) + '\n')
    print(json.dumps({'prepared': str(out / 'prepared.json'), 'sha256': sha(out / 'prepared.json'), 'cards': str(out / 'cards.json')}, indent=2))


if __name__ == '__main__': main()
