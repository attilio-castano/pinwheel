#!/usr/bin/env python3
"""Reproduce PWL v0 proofs, image validation, independent lookup, and decoded I2C execution."""
import csv
import hashlib
import json
import re
import shutil
import subprocess
from pathlib import Path

from binary_v0 import verify

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'build/binary'


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
    audit_source = ROOT / 'test/BinaryAxioms.lean'
    expected = re.findall(r'^#print axioms (\S+)$', audit_source.read_text(), re.M)
    declared = ['Pinwheel.Binary.' + name for path in sorted((ROOT / 'Pinwheel/Binary').glob('*.lean'))
                for name in re.findall(r'^theorem (\w+)', path.read_text(), re.M)]
    if sorted(declared) != sorted(expected):
        raise RuntimeError('The binary audit must cover every public binary theorem')
    audit = run([*lean, str(audit_source)], 'axioms.log')
    entries = re.findall(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)", audit)
    allowed = {'propext', 'Classical.choice', 'Quot.sound'}
    if not expected or sorted(name for name, _ in entries) != sorted(expected):
        raise RuntimeError('Incomplete theorem dependency audit')
    for name, group in entries:
        if set(filter(None, map(str.strip, group.split(',')))) - allowed:
            raise RuntimeError(f'Nonstandard assumptions in {name}')
    print(run([*lean, '--run', 'test/Binary.lean'], 'images.log').strip(), flush=True)
    oracle = verify(OUT)
    (OUT / 'independent-lookup.json').write_text(json.dumps(oracle, indent=2) + '\n')
    print(f'Independent Python lookup passed: {oracle}', flush=True)
    coverage = {}
    for mode in ['binary-explicit', 'binary-looped']:
        print(f'Running {mode} wire suite...', flush=True)
        print(run([*lean, '--run', 'test/CompiledI2C.lean', '--' + mode], mode + '.log').strip(), flush=True)
        coverage[mode] = dict((key, int(value)) for key, value in
                             (line.split('=') for line in (ROOT / 'build' / mode / 'coverage.txt').read_text().splitlines()))
    if coverage['binary-explicit'] != coverage['binary-looped']:
        raise RuntimeError('Decoded execution coverage or timing differs')
    with (OUT / 'storage.csv').open() as stream:
        storage = [{key: value if key == 'image' else int(value) for key, value in row.items()}
                   for row in csv.DictReader(stream)]
    sources = sorted(ROOT.glob('Pinwheel/**/*.lean')) + [ROOT / name for name in [
        'Pinwheel.lean', 'lean-toolchain', 'lakefile.toml', 'lake-manifest.json',
        'test/Binary.lean', 'test/BinaryAxioms.lean', 'test/CompiledI2C.lean',
        'scripts/check-binary.py', 'scripts/binary_v0.py']]
    artifacts = sorted(path for path in OUT.iterdir() if path.is_file() and path.name != 'report.json')
    artifacts += [ROOT / 'build' / mode / name for mode in coverage
                  for name in ['coverage.txt', 'write-0x53-0xa6-stretched.csv']]
    report = dict(format='PWL', version=0, lean=version, audited_theorems=len(expected),
                  standard_axioms_only=True, round_trip_images=1280, truncated_images_rejected=920,
                  independent_lookup=oracle, storage=storage, wire_coverage=coverage,
                  sha256={str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest()
                          for path in sources + artifacts},
                  boundary='Canonical byte-image round trips, decoded execution equality, and image-loading semantics '
                           'are proved in Lean. File IO, Python lookup, malformed-input checks, and wire suites '
                           'are executable evidence. Storage counts describe V0 serialized images, including '
                           'explicit bank padding; they are not allocated chip memory or synthesized area. '
                           'No binary circuit decoder, raw-byte cycle interpreter, physical loading interface, '
                           'RTL, or synthesis result is part of this milestone. Reference runs exclude reset/reload.')
    (OUT / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    print(f'Audited {len(expected)} theorems. See build/binary/report.json.')


if __name__ == '__main__':
    main()
