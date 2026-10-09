#!/usr/bin/env python3
"""Freeze and check bounded buffered source/decoded-image execution proofs.

Runs the default Lean build and whole-library axiom audit, then compares fresh
typed constructor exports to the independent Python canonical SRAM lowerer.
No CAD tools or retained physical artifacts are required. The source interpreter
to packed circuit state relation is outside this gate.
"""
import argparse
import copy
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import time

from buffered_counted_hardware import compact_spi
from buffered_reactive_hardware import compact_i2c_read
from buffered_sram_hardware import lower_sram

ROOT = Path(__file__).resolve().parents[1]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def fields(image):
    return dict(words=list(image.words), controls=list(image.controls),
        branch_indices=list(image.branch_indices), branch_table=list(image.branch_table),
        virtual_span=image.virtual_span, idle_levels=image.idle_levels,
        idle_enabled=image.idle_enabled, tx_bits=image.tx_bits,
        rx_reservation_bits=image.rx_bits)


def compare(exported, expected):
    for key, value in expected.items():
        if exported.get(key) != value:
            raise ValueError('Typed/Python canonical image mismatch: ' + key)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--tag', required=True, help='Fresh local receipt directory under build/validation')
    args = parser.parse_args()
    if not re.fullmatch(r'[A-Za-z0-9_-]+', args.tag):
        parser.error('Use letters, numbers, hyphens or underscores in tags')
    out = ROOT / 'build/validation' / args.tag
    if out.exists():
        raise RuntimeError('Choose a fresh tag to preserve earlier evidence')
    lake = shutil.which('lake')
    if not lake:
        raise RuntimeError('The pinned Lean toolchain must be on PATH')
    sources = [ROOT / name for name in ('Pinwheel.lean', 'lakefile.toml', 'lake-manifest.json', 'lean-toolchain')]
    sources += sorted((ROOT / 'Pinwheel').rglob('*.lean'))
    sources += [ROOT / 'test' / name for name in ('ProofAudit.lean', 'BufferedSpiSource.lean',
        'BufferedSpiExecution.lean', 'BufferedI2cSource.lean')]
    sources += sorted((ROOT / 'scripts').glob('buffered_*.py'))
    sources += [Path(__file__).resolve()]
    hashes = {str(p.relative_to(ROOT)): sha(p) for p in sources}
    out.mkdir(parents=True)
    (out / 'intake.json').write_text(json.dumps(dict(source_sha256=hashes), indent=2) + '\n')
    commands, cases, mutations = [], [], []
    started = time.monotonic()

    def run(command, label, rejected=False):
        result = subprocess.run(command, cwd=ROOT, text=True, capture_output=True)
        log = result.stdout + result.stderr
        (out / (label + '.log')).write_text(log)
        commands.append(dict(label=label, command=command, exit_code=result.returncode))
        if rejected:
            if result.returncode == 0 or 'Unapproved axioms in Pinwheel.CI.untrusted' not in log:
                raise RuntimeError('Custom axiom did not fail the audit for the expected reason')
        elif result.returncode:
            raise RuntimeError(label + ' failed:\n' + log)
        print(label + ': ' + ('expected rejection' if rejected else 'passed'), flush=True)
        return result.stdout

    run([lake, 'build'], 'build')
    lean = [lake, 'env', 'lean', '-DwarningAsError=true']
    audit = run([*lean, 'test/ProofAudit.lean'], 'axioms')
    counts = re.search(r'Pinwheel audit: (\d+) declarations, (\d+) theorems;', audit)
    if counts is None:
        raise RuntimeError('Missing whole-library audit summary')
    mutant = out / 'RejectAxiom.lean'
    mutant.write_text((ROOT / 'test/ProofAudit.lean').read_text().removesuffix('#audit_pinwheel\n') +
        'axiom Pinwheel.CI.untrusted : False\n#audit_pinwheel\n')
    run([*lean, str(mutant)], 'reject-untrusted-axiom', rejected=True)
    run([*lean, '--run', 'test/BufferedSpiExecution.lean'], 'spi-execution-controls')
    for count in range(1, 5):
        for half in (3, 4, 6, 256):
            label = f'spi-{count}-{half}'
            exported = json.loads(run([*lean, '--run', 'test/BufferedSpiSource.lean',
                str(count), str(half)], label))
            if exported.get('schema') != 'pinwheel-buffered-spi-source-v1':
                raise RuntimeError('Wrong SPI constructor schema')
            image = lower_sram(compact_spi(count, half))
            compare(exported, fields(image))
            cases.append(dict(id=label, image_key=image.key, fields=9, passed=True))
    exported = json.loads(run([*lean, '--run', 'test/BufferedI2cSource.lean'], 'i2c-4-4-32'))
    if exported.get('schema') != 'pinwheel-buffered-i2c-source-v1':
        raise RuntimeError('Wrong I2C constructor schema')
    image = lower_sram(compact_i2c_read(4, 4, 32))
    expected = fields(image)
    compare(exported, expected)
    cases.append(dict(id='i2c-4-4-32', image_key=image.key, fields=9, passed=True))
    for field in ('words', 'controls', 'branch_indices', 'branch_table'):
        changed = copy.deepcopy(exported)
        changed[field][0] ^= 1
        try:
            compare(changed, expected)
        except ValueError:
            mutations.append(dict(field=field, rejected=True))
        else:
            raise RuntimeError('Image comparison accepted changed ' + field)
    for path in sources:
        if sha(path) != hashes[str(path.relative_to(ROOT))]:
            raise RuntimeError('A frozen source changed during validation: ' + str(path))
    report = dict(passed=True, audited_declarations=int(counts[1]), audited_theorems=int(counts[2]),
        untrusted_axiom_rejected=True, constructor_cases=cases, image_mutations=mutations,
        commands=commands, source_sha256=hashes, elapsed_seconds=round(time.monotonic()-started, 3),
        boundary='Kernel source versus independently decoded image Buffered semantics for parametric mode-0 SPI '
            'and one fixed reactive I2C constructor, arbitrary capacities/states/raw inputs/prefixes. '
            'Typed/Python byte identity is finite evidence. Packed-register source refinement, serial, '
            'native/emitter/RTL equivalence and physical timing remain separate.')
    (out / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    print('Source execution receipt: ' + str(out / 'report.json'), flush=True)


if __name__ == '__main__':
    main()
