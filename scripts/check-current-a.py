#!/usr/bin/env python3
"""Preflight, recover and replay the explicitly current-v2 retained Design A.

No CAD is run. Physical evidence is reused by hash. Exit 2 is an assessed but
unaccepted A; exit 1 means invalid/unavailable evidence or an unsuccessful replay.
"""
import argparse
import importlib.util
import json
import os
from pathlib import Path
import shutil
import sys

from retained_evidence import (BUNDLE_MANIFEST, POLICY, SELECTION, compare_current_design,
    create_bundle, digest, load_bundle, load_seed, preflight, read_json,
    relocated_evidence_class, relocations, require)
from validation_run import Commands, fresh_directory


ROOT = Path(__file__).resolve().parents[1]


def emit(value):
    print(json.dumps(value, indent=2), flush=True)


def frozen_assessment(bundle, tag):
    bundle = Path(bundle).absolute()
    manifest = load_bundle(bundle, ROOT)
    snapshot = bundle / 'root'
    # The worker is a separate process, so no current mutable checker module is
    # already imported when the preserved historical modules are loaded.
    sys.path.insert(0, str(snapshot / 'scripts'))
    for name in ('validation_run', 'process_group'):
        sys.modules.pop(name, None)
    spec = importlib.util.spec_from_file_location('retained_acceptance_cli',
                                                  snapshot / 'scripts/check-design-acceptance.py')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    module.Evidence = relocated_evidence_class(module.Evidence, bundle, manifest,
                                             Path('build/validation') / tag)
    sys.argv = [str(spec.origin), '--tag', tag, '--selection', SELECTION, '--require-accepted']
    return module.main()


def replay(bundle, tag, lean_bin=None):
    bundle = Path(bundle).absolute()
    manifest = load_bundle(bundle, ROOT)
    current = compare_current_design(bundle, manifest, ROOT)
    if lean_bin:
        directory = Path(lean_bin).absolute()
        require((directory / 'lean').is_file() and (directory / 'lake').is_file(),
                'Lean runtime directory must contain lean and lake')
        os.environ['PATH'] = str(directory) + os.pathsep + os.environ.get('PATH', '')
    lean, lake = shutil.which('lean'), shutil.which('lake')
    require(lean and lake, 'Install the pinned Lean toolchain or pass --lean-bin')
    out = fresh_directory(ROOT / 'build/validation', tag)
    snapshot = bundle / 'root'
    report = dict(schema=1, policy=POLICY, status='running', A_accepted=False,
                  B_admitted=False, complete_design_iteration=False, cad_seconds=0,
                  bundle=str(bundle), inventory_sha256=digest(bundle / BUNDLE_MANIFEST),
                  original_assessment_root=manifest['original_root'],
                  current_design=current, commands=[],
                  wrapper_sources={str(Path(__file__).relative_to(ROOT)): digest(__file__),
                                   **{name: digest(ROOT / name) for name in
                                      ('scripts/retained_evidence.py', 'scripts/validation_run.py',
                                       'scripts/process_group.py')}},
                  physical_evidence=dict(replayed_now=False, mode='hash-bound retained reuse'),
                  boundary='Fresh historical-source library build and eight kernel image checks. '
                           'Original formal and physical receipts are retained observations; '
                           'no CAD, host simulation, physical repeatability or accepted-A claim.')
    run = Commands(snapshot, out, records=report['commands'], default_timeout=600)
    historical_tag = 'current-a-' + tag
    try:
        version = run([lean, '--version'], 'lean-version')
        pin = (snapshot / 'lean-toolchain').read_text().strip().split(':v')[-1]
        require(('Lean (version ' + pin + ',') in version or ('Lean (version ' + pin + ')') in version,
                'Lean runtime does not match snapshot pin')
        report['runtime'] = {Path(path).name: dict(path=path, sha256=digest(Path(path).resolve()))
                             for path in (lean, lake)}
        run([lake, 'build', 'Pinwheel'], 'retained-library-build')
        # Exit 2 is expected only with the exact three physical blockers; do not
        # pass it to Commands as a generic successful subprocess.
        run([sys.executable, '-B', __file__, '__assess', str(bundle), historical_tag],
            'current-v2-assessment', reject='"status": "assessed"')
        require(report['commands'][-1].get('exit_code') == 2,
                'Current-v2 assessment must return exactly the blocked exit code 2')
        assessment_path = snapshot / 'build/validation' / historical_tag / 'report.json'
        assessment = read_json(assessment_path)
        require(assessment.get('status') == 'assessed' and assessment.get('policy') == POLICY and
                assessment.get('A_accepted') is False and set(assessment.get('blockers', [])) ==
                {'sram_qualification', 'timing_conditions', 'package_power'},
                'Expected assessed current-v2 A with exactly three physical blockers')
        require(len(assessment.get('certificates', [])) == 8 and
                all(item.get('kernel_rechecked') is True for item in assessment['certificates']),
                'Missing fresh kernel certificate checks')
        for name in ('report.json', 'report.md'):
            shutil.copyfile(assessment_path.parent / name, out / ('assessment-' + name))
        load_bundle(bundle, ROOT)
        compare_current_design(bundle, manifest, ROOT)
        for name, sha in report['wrapper_sources'].items():
            require(digest(ROOT / name) == sha, 'Replay wrapper source changed during run')
        report.update(status='assessed', blockers=assessment['blockers'],
                      fresh_kernel_certificates=8, snapshot_inputs_unchanged=True,
                      assessment=dict(path=str(out / 'assessment-report.json'),
                                      sha256=digest(out / 'assessment-report.json')))
    except (ValueError, OSError, RuntimeError, KeyError, TypeError) as error:
        report.update(status='invalid_evidence', error=f'{type(error).__name__}: {error}')
    with (out / 'report.json').open('x') as stream:
        stream.write(json.dumps(report, indent=2) + '\n')
    text = ['# Current Design A replay', '', '**A accepted: no.** Status: ' + report['status'] + '.', '',
            report['boundary'], '', 'Bundle: `' + str(bundle) + '`.', '']
    if report['status'] == 'assessed':
        text += ['Eight captured image certificates were freshly kernel checked. '
                 'The current Lean design matches the preserved source snapshot.', '',
                 'Open requirements: SRAM qualification, compatible fast timing conditions, package power.', '',
                 '[Detailed assessment](assessment-report.md)', '']
    else:
        text += [report.get('error', 'Replay failed'), '']
    (out / 'report.md').write_text('\n'.join(text))
    emit({k: report.get(k) for k in ('status', 'A_accepted', 'blockers', 'fresh_kernel_certificates', 'error')})
    print(out / 'report.md')
    return 2 if report['status'] == 'assessed' else 1


def main():
    if len(sys.argv) > 1 and sys.argv[1] == '__assess':
        require(len(sys.argv) == 4, 'Invalid internal worker arguments')
        return frozen_assessment(sys.argv[2], sys.argv[3])
    parser = argparse.ArgumentParser(description=__doc__)
    actions = parser.add_subparsers(dest='action', required=True)
    for name in ('inventory', 'bundle'):
        item = actions.add_parser(name)
        item.add_argument('--source-root', type=Path, required=True)
        item.add_argument('--relocate', action='append', default=[], metavar='OLD=NEW')
        if name == 'bundle':
            item.add_argument('--bundle', type=Path, required=True)
    item = actions.add_parser('replay')
    item.add_argument('--bundle', type=Path, required=True)
    item.add_argument('--tag', required=True)
    item.add_argument('--lean-bin', type=Path)
    args = parser.parse_args()
    if args.action == 'replay':
        return replay(args.bundle, args.tag, args.lean_bin)
    seed = load_seed(args.source_root, ROOT)
    prepared = preflight(seed, args.source_root, relocations(args.relocate))
    if args.action == 'inventory':
        emit({k: v for k, v in prepared.items() if k != 'files'})
        return 0 if prepared['status'] == 'ready' else 1
    require(prepared['status'] == 'ready', 'Bundle preflight failed: ' + json.dumps(prepared['issues']))
    manifest = create_bundle(args.bundle, seed, prepared)
    emit(dict(status='recovered', bundle=str(args.bundle.absolute()), policy=POLICY,
              files=len(manifest['files']), physical_evidence=manifest['physical_evidence']))
    return 0


if __name__ == '__main__':
    try:
        raise SystemExit(main())
    except (ValueError, OSError, KeyError, TypeError, RuntimeError) as error:
        emit(dict(status='invalid_evidence', A_accepted=False,
                  error=f'{type(error).__name__}: {error}'))
        raise SystemExit(1)
