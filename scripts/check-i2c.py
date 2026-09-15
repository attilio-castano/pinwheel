#!/usr/bin/env python3
"""Reproduce the pure Lean I2C experiment; no hardware tools required."""
import hashlib
import json
import re
import shutil
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'build/i2c'


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
    audit_source = ROOT / 'test/I2CAxioms.lean'
    expected = re.findall(r'^#print axioms (\S+)$', audit_source.read_text(), re.M)
    audit = run([*lean, str(audit_source)], 'axioms.log')
    entries = re.findall(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)", audit)
    allowed = {'propext', 'Classical.choice', 'Quot.sound'}
    if not expected or sorted(name for name, _ in entries) != sorted(expected):
        raise RuntimeError('Incomplete theorem dependency audit')
    for name, group in entries:
        if set(filter(None, map(str.strip, group.split(',')))) - allowed:
            raise RuntimeError(f'Nonstandard assumptions in {name}')
    print(run([*lean, '--run', 'test/I2C.lean'], 'checks.log').strip(), flush=True)
    coverage = dict((key, int(value)) for key, value in
                    (line.split('=') for line in (OUT / 'coverage.txt').read_text().splitlines()))
    artifacts = sorted(ROOT.glob('Pinwheel/**/*.lean')) + [
        ROOT / p for p in ['Pinwheel.lean', 'lean-toolchain', 'lakefile.toml', 'lake-manifest.json',
                          'test/I2C.lean', 'test/I2CAxioms.lean', 'scripts/check-i2c.py',
                          'build/i2c/write-0x53-0xa6-stretched.csv', 'build/i2c/coverage.txt',
                          'build/i2c/axioms.log', 'build/i2c/checks.log']]
    report = dict(lean=version, coverage=coverage, audited_theorems=len(expected),
                  standard_axioms_only=True,
                  negative_variants_rejected=['wrong payload', 'short high period', 'ignored stretching'],
                  sha256={str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                          for p in artifacts},
                  boundary='Local universal bus/controller proofs and sampled closed-loop protocol checks. '
                           'No full-transaction theorem, shared-engine I2C compiler, RTL, or physical timing claim.')
    (OUT / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    print(f'Audited {len(expected)} theorems. See build/i2c/report.json.')


if __name__ == '__main__':
    main()
