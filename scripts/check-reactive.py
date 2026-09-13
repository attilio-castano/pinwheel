#!/usr/bin/env python3
"""Reproduce the candidate reactive engine's Lean proofs and execution checks."""
import hashlib
import json
import re
import shutil
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'build/reactive'


def run(args, log):
    result = subprocess.run(args, cwd=ROOT, text=True, capture_output=True)
    output = result.stdout + result.stderr
    (OUT / log).write_text(output)
    if result.returncode:
        raise RuntimeError(f'Command failed: {args}\n{output}')
    return output


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    (OUT / 'report.json').unlink(missing_ok=True)
    lake = shutil.which('lake')
    if not lake:
        raise SystemExit('Install the pinned Lean toolchain; see docs/development.md')
    run([lake, 'build'], 'build.log')
    lean = [lake, 'env', 'lean', '-DwarningAsError=true']
    version = run([lake, 'env', 'lean', '--version'], 'version.log').strip()
    expected = re.findall(r'^#print axioms (\S+)$', (ROOT / 'test/ReactiveAxioms.lean').read_text(), re.M)
    audit = run([*lean, 'test/ReactiveAxioms.lean'], 'axioms.log')
    entries = re.findall(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)", audit)
    if not expected or sorted(name for name, _ in entries) != sorted(expected):
        raise RuntimeError('Incomplete theorem dependency audit')
    for name, group in entries:
        if set(filter(None, map(str.strip, group.split(',')))) - {'propext', 'Classical.choice', 'Quot.sound'}:
            raise RuntimeError(f'Nonstandard assumptions in {name}')
    print(run([*lean, '--run', 'test/Reactive.lean'], 'checks.log').strip(), flush=True)
    print(run([*lean, '--run', 'test/Control.lean'], 'control-checks.log').strip(), flush=True)
    coverage = dict((key, int(value)) for key, value in
                    (line.split('=') for line in (OUT / 'coverage.txt').read_text().splitlines()))
    artifacts = sorted(ROOT.glob('Pinwheel/**/*.lean')) + [ROOT / p for p in [
        'Pinwheel.lean', 'lean-toolchain', 'lakefile.toml', 'lake-manifest.json',
        'test/Reactive.lean', 'test/ReactiveAxioms.lean', 'scripts/check-reactive.py',
        'test/Control.lean', 'build/reactive/control-checks.log',
        'build/reactive/stretched-pulse.csv', 'build/reactive/coverage.txt',
        'build/reactive/axioms.log', 'build/reactive/checks.log']]
    report = dict(lean=version, coverage=coverage, audited_theorems=len(expected),
                  standard_axioms_only=True,
                  negative_variants_rejected=['ignored readiness', 'short post-wait duration', 'lost capture'],
                  sha256={str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in artifacts},
                  boundary='Typed candidate engine: universal legacy embedding and wait/timing proofs; '
                           'sampled stretched-pulse, guard/branch/qualification, and legacy checks. '
                           'I2C compiler checks have a separate receipt. No new binary encoding, '
                           'structural circuit refinement, or RTL validation.')
    (OUT / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    print(f'Audited {len(expected)} theorems. See build/reactive/report.json.')


if __name__ == '__main__':
    main()
