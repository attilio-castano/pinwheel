#!/usr/bin/env python3
"""Check the bounded combined read, its complete public theorem audit, and wire evidence."""
import hashlib
import json
import re
import shutil
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'build/i2c-read'


def run(args, log):
    result = subprocess.run(args, cwd=ROOT, text=True, capture_output=True)
    output = result.stdout + result.stderr
    (OUT / log).write_text(output)
    if result.returncode:
        raise RuntimeError(f'{args}:\n{output}')
    return output


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    (OUT / 'report.json').unlink(missing_ok=True)
    lake = shutil.which('lake')
    if not lake:
        raise SystemExit('The pinned Lean toolchain is required')
    run([lake, 'build'], 'build.log')
    lean = [lake, 'env', 'lean', '-DwarningAsError=true']
    declared = re.findall(r'^theorem (\w+)', (ROOT / 'Pinwheel/Compile/I2CReadProofs.lean').read_text(), re.M)
    expected = ['Pinwheel.Compile.I2CRead.' + n for n in declared]
    audit_source = (ROOT / 'test/I2CReadAxioms.lean').read_text()
    if sorted(re.findall(r'^#print axioms (\S+)', audit_source, re.M)) != sorted(expected):
        raise RuntimeError('The audit must name every public read-compiler theorem')
    audit = run([*lean, 'test/I2CReadAxioms.lean'], 'axioms.log')
    entries = re.findall(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)", audit)
    if sorted(n for n, _ in entries) != sorted(expected):
        raise RuntimeError('Incomplete audit')
    for name, axioms in entries:
        if set(filter(None, map(str.strip, axioms.split(',')))) - {'propext', 'Classical.choice', 'Quot.sound'}:
            raise RuntimeError(f'Unapproved proof assumptions: {name}')
    print(run([*lean, '--run', 'test/I2CRead.lean'], 'wire.log').strip(), flush=True)
    coverage = dict((k, int(v)) for k, v in (line.split('=') for line in (OUT / 'coverage.txt').read_text().splitlines()))
    sources = sorted(ROOT.glob('Pinwheel/**/*.lean')) + [ROOT / p for p in [
        'Pinwheel.lean', 'test/I2CRead.lean', 'test/I2CReadAxioms.lean', 'scripts/check-i2c-read.py',
        'lean-toolchain', 'lakefile.toml', 'lake-manifest.json']]
    artifacts = sorted(p for p in OUT.iterdir() if p.is_file() and p.name != 'report.json')
    report = dict(audited_theorems=len(expected), standard_axioms_only=True, coverage=coverage,
                  negative_variants=6, execution_addresses=155, sample_bits_used=11,
                  configured_addresses=256, configured_samples=16,
                  sha256={str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in sources + artifacts},
                  boundary='Universal compiler/reference correspondence for uninterrupted runs. '
                           'Independent target/monitor and fault/reset/reload checks are executable evidence. '
                           'No universal closed-loop liveness, physical timing, or electrical compliance claim.')
    (OUT / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    print(f'Audited {len(expected)} theorems. See build/i2c-read/report.json.')


if __name__ == '__main__':
    main()
