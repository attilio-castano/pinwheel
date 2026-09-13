#!/usr/bin/env python3
"""Reproduce explicit or counted-loop I2C evidence; no hardware tools required."""
import argparse
import hashlib
import json
import re
import shutil
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'build/compiled-i2c'


def run(args, log):
    result = subprocess.run(args, cwd=ROOT, text=True, capture_output=True)
    output = result.stdout + result.stderr
    (OUT / log).write_text(output)
    if result.returncode:
        raise RuntimeError(f'Command failed: {args}\n{output}')
    return output


def main():
    global OUT
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--looped', action='store_true', help='validate the counted-loop instruction store')
    args = parser.parse_args()
    mode = 'looped-i2c' if args.looped else 'compiled-i2c'
    OUT = ROOT / 'build' / mode
    OUT.mkdir(parents=True, exist_ok=True)
    (OUT / 'report.json').unlink(missing_ok=True)
    lake = shutil.which('lake')
    if not lake:
        raise SystemExit('Install the pinned Lean toolchain; see docs/development.md')
    run([lake, 'build'], 'build.log')
    lean = [lake, 'env', 'lean', '-DwarningAsError=true']
    version = run([lake, 'env', 'lean', '--version'], 'version.log').strip()
    audit_source = ROOT / ('test/LoopedI2CAxioms.lean' if args.looped else 'test/CompiledI2CAxioms.lean')
    expected = re.findall(r'^#print axioms (\S+)$', audit_source.read_text(), re.M)
    audit = run([*lean, str(audit_source)], 'axioms.log')
    entries = re.findall(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)", audit)
    allowed = {'propext', 'Classical.choice', 'Quot.sound'}
    if not expected or sorted(name for name, _ in entries) != sorted(expected):
        raise RuntimeError('Incomplete theorem dependency audit')
    for name, group in entries:
        if set(filter(None, map(str.strip, group.split(',')))) - allowed:
            raise RuntimeError(f'Nonstandard assumptions in {name}')
    if args.looped:
        print(run([*lean, '--run', 'test/Counted.lean'], 'counted.log').strip(), flush=True)
    print(run([*lean, '--run', 'test/CompiledI2C.lean', *(['--looped'] if args.looped else [])],
              'checks.log').strip(), flush=True)
    coverage = dict((key, int(value)) for key, value in
                    (line.split('=') for line in (OUT / 'coverage.txt').read_text().splitlines()))
    artifacts = sorted(ROOT.glob('Pinwheel/**/*.lean')) + [
        ROOT / p for p in ['Pinwheel.lean', 'lean-toolchain', 'lakefile.toml', 'lake-manifest.json',
                          'test/CompiledI2C.lean', 'test/CompiledI2CAxioms.lean', 'test/Counted.lean',
                          'test/LoopedI2CAxioms.lean', 'scripts/check-compiled-i2c.py',
                          f'build/{mode}/write-0x53-0xa6-stretched.csv', f'build/{mode}/coverage.txt',
                          f'build/{mode}/axioms.log', f'build/{mode}/checks.log']]
    if args.looped:
        artifacts.append(OUT / 'counted.log')
    report = dict(mode=mode, lean=version, coverage=coverage, audited_theorems=len(expected),
                  standard_axioms_only=True,
                  negative_variants_rejected=['missing ACK capture', 'ignored NACK branch', 'early ACK capture'],
                  sha256={str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                          for p in artifacts},
                  boundary='Universal compiled-engine correspondence to the finite I2C reference, without reset during a run. '
                           'Wire-monitor, error-path, and mixed-reload checks are sampled evidence. '
                           'Reset clears engine status; it differs from reference resetAbort. '
                           'No new encoding, circuit refinement, RTL, electrical timing, or unconditional liveness claim.')
    if args.looped:
        report.update(
            storage=dict(explicit_instructions=79, stored_templates=15, loop_descriptors=2,
                         sequence_nodes=14, total_syntax_nodes=31, data_bits=16,
                         execution_pc_bits=7, maximum_execution_slots=128,
                         maximum_syntax_nodes=64, maximum_loop_nesting=2),
            generic_serial_loops=6144,
            loop_negative_variants_rejected=['wrong byte selection', 'wrong bit order', 'skipped final bit',
                                             'wrong ACK destination', 'ignored NACK branch'],
            boundary='Universal fetched-instruction and complete-state equality with the explicit image; '
                     'one-step equality includes reset/start. Reference trace corollaries exclude reset/reload. '
                     'Generic and wire-monitor/fault/reload tests are sampled evidence. '
                     '15 templates exclude descriptors, operand metadata, and data. '
                     'No binary encoding, synthesis area, physical timing, or unconditional liveness claim.')
    (OUT / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    print(f'Audited {len(expected)} theorems. See build/{mode}/report.json.')


if __name__ == '__main__':
    main()
