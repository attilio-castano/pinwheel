#!/usr/bin/env python3
"""Portable merge gate: pinned Lean, whole-library axiom audit, executable contracts.

Needs Python 3.12+ and the pinned Lean toolchain; no CAD tools or prior build/
fixtures. Use a fresh tag to retain the previous gate's receipt and logs.
"""
import argparse
import hashlib
import json
import re
import shutil
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SUITES = [
    ('UART', []), ('UARTRx', []), ('UARTLink', []), ('UARTStream', []), ('UARTStreamClocks', []),
    ('SPI', []), ('SPITransactions', []),
    ('Engine', []), ('I2C', []), ('I2CWriteTransactions', []), ('I2CReadTransactions', []),
    ('I2CRecovery', []), ('Reactive', []),
    ('Control', []), ('CompiledI2C', []), ('Counted', []),
    ('CompiledI2C', ['--looped']), ('Binary', []),
    ('CompiledI2C', ['--binary-explicit']), ('CompiledI2C', ['--binary-looped']),
    ('I2CRead', []), ('Encoding', []), ('Hardware', []),
    ('TimedContracts', []), ('FetchChoice', []), ('FetchContract', []), ('Interfaces', []),
    ('StorageCapacity', []), ('StorageRepetition', []), ('PinSampler', []),
    ('StructuralTiming', []), ('Enables', []), ('Latency', []), ('Memory', []),
    ('SerialUpload', []),
    ('HostResult', []),
    ('UARTBufferedSupervisor', []), ('UARTBufferedSupervisorPhase', []),
    ('PairedStream', []), ('PairedStreamSession', []),
    ('ResidentEffects', []),
    ('ProgramExport', []), ('ResidentProgram', []),
    ('Transfer', []),
    ('Buffered', []),
    ('BufferedHardware', []),
    ('BufferedCountedHardware', []),
    ('BufferedReactiveHardware', []),
    ('BufferedSharedBranches', []),
    ('BufferedSharedBranchesMemo', []),
    ('BufferedFetchDeadline', []),
    ('BufferedSramHardware', []),
    ('BufferedSramCandidates', []),
    ('BufferedSramMemoBind', []),
    ('BufferedSramMemoEval', []),
    ('BufferedSramSerial', []),
]
KERNEL_SUITES = ['ChipPinMap']


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check_imports():
    modules = {'.'.join(p.relative_to(ROOT).with_suffix('').parts): p
               for p in (ROOT / 'Pinwheel').rglob('*.lean')}
    modules['Pinwheel'] = ROOT / 'Pinwheel.lean'
    seen = set()
    def visit(name):
        if name in seen or name not in modules:
            return
        seen.add(name)
        for child in re.findall(r'^import (\S+)', modules[name].read_text(), re.M):
            visit(child)
    visit('Pinwheel')
    missing = sorted(modules.keys() - seen)
    if missing:
        raise RuntimeError(f'Library files outside the default build: {missing}')
    return len(seen)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--tag', default='local')
    args = parser.parse_args()
    if not args.tag.replace('-', '').replace('_', '').isalnum():
        parser.error('Use letters, numbers, hyphens or underscores in tags')
    if sys.version_info < (3, 12):
        raise RuntimeError('Python 3.12+ is required')
    out = ROOT / 'build/validation' / args.tag
    if out.exists():
        raise RuntimeError('Choose a fresh tag to preserve earlier validation evidence')
    lake = shutil.which('lake')
    if not lake:
        raise RuntimeError('Install the pinned Lean toolchain and put lake on PATH')
    modules = check_imports()
    sources = [ROOT / p for p in ['Pinwheel.lean', 'lean-toolchain', 'lakefile.toml',
                                 'lake-manifest.json', 'scripts/check-foundation.py',
                                 'scripts/binary_v0.py',
                                 'scripts/check-uart-rx.py', 'scripts/uart_rx_oracle.py',
                                 'scripts/reactive-core-vectors.py', 'scripts/execution-vectors.py']]
    sources += sorted((ROOT / 'Pinwheel').rglob('*.lean')) + sorted((ROOT / 'test').glob('*.lean'))
    hashes = {str(p.relative_to(ROOT)): sha(p) for p in sources}
    out.mkdir(parents=True)
    commands = []
    started = time.monotonic()
    def run(command, label, reject=False):
        result = subprocess.run(list(map(str, command)), cwd=ROOT, capture_output=True, text=True)
        log = result.stdout + result.stderr
        (out / f'{label}.log').write_text(log)
        commands.append(dict(label=label, command=list(map(str, command)), exit_code=result.returncode))
        if reject:
            if result.returncode == 0 or 'Unapproved axioms in Pinwheel.CI.untrusted' not in log:
                raise RuntimeError(f'Audit mutation was not rejected for the expected reason: {log}')
        elif result.returncode:
            raise RuntimeError(f'{label} failed:\n{log}')
        print(f'{label}: ' + ('expected rejection' if reject else log.strip()[-1200:]), flush=True)
        return log
    lean = [lake, 'env', 'lean', '-DwarningAsError=true']
    version = run([lake, 'env', 'lean', '--version'], 'version').strip()
    expected = (ROOT / 'lean-toolchain').read_text().strip().split(':v')[-1]
    if not re.search(r'Lean \(version ' + re.escape(expected) + r'(?:,|\s)', version):
        raise RuntimeError(f'Expected repository toolchain {expected}, got {version}')
    run([lake, 'build'], 'build')
    audit = run([*lean, 'test/ProofAudit.lean'], 'axioms')
    counts = re.search(r'Pinwheel audit: (\d+) declarations, (\d+) theorems;', audit)
    if not counts:
        raise RuntimeError('Missing whole-library audit summary')
    audit_text = (ROOT / 'test/ProofAudit.lean').read_text()
    mutant = out / 'RejectAxiom.lean'
    mutant.write_text(audit_text.removesuffix('#audit_pinwheel\n') +
                      'axiom Pinwheel.CI.untrusted : False\n#audit_pinwheel\n')
    run([*lean, mutant], 'reject-untrusted-axiom', reject=True)
    for name in KERNEL_SUITES:
        run([*lean, f'test/{name}.lean'], name + '-kernel')
    for name, flags in SUITES:
        label = name + (('-' + flags[0].removeprefix('--')) if flags else '')
        run([*lean, '--run', f'test/{name}.lean', *flags], label)
        if name == 'Binary':
            run([sys.executable, 'scripts/binary_v0.py'], 'independent-binary')
        if name == 'UARTRx':
            run([sys.executable, 'scripts/check-uart-rx.py'], 'independent-uart-rx')
    for path in sources:
        if sha(path) != hashes[str(path.relative_to(ROOT))]:
            raise RuntimeError(f'Source changed during validation: {path}')
    report = dict(lean=version, modules=modules, audited_declarations=int(counts[1]),
                  audited_theorems=int(counts[2]), executable_suites=len(SUITES),
                  kernel_suites=len(KERNEL_SUITES),
                  untrusted_axiom_rejected=True, commands=commands, source_sha256=hashes,
                  elapsed_seconds=round(time.monotonic()-started, 3),
                  boundary='Fresh-source-capable Lean/model gate, initialized finite UART package/lifecycle and owned receipts, '
                           'compiled UART link/stream timing, independent PWL lookup and UART RX/E64 oracle, '
                           'retained-result ownership and stream-control circuitry; '
                           'parametric finite-transfer ownership and shared reactive/counted buffered '
                           'execution models, local buffered circuit equations and directed typed circuit tests. '
                           'Does not run RTL simulation, technology mapping, physical tools, '
                           'or prove emitter/CIRCT equivalence.')
    (out / 'report.json').write_text(json.dumps(report, indent=2)+'\n')
    print(f'Foundation gate passed: {out / "report.json"}', flush=True)


if __name__ == '__main__':
    main()
