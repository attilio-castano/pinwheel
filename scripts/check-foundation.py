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

import process_group

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
    ('BufferedSramLoading', []),
    ('BufferedSpiSource', []),
    ('BufferedSpiExecution', []),
    ('BufferedSpiRefinement', []),
    ('BufferedI2cSource', []),
    ('GenericStartBoundary', []),
    ('GenericExecution', []),
    ('SerialSourceBoundary', []),
    ('StreamingParity', []),
]
KERNEL_SUITES = ['ChipPinMap', 'StreamingCompile', 'StreamingReadySource', 'StreamingReadyCompile', 'StreamingReadyBoot', 'StreamingUARTSource', 'StreamingUARTCompile', 'StreamingUARTBoot']


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


def serial_modules(root=ROOT):
    """Compile each local dependency before its importer, once per process."""
    modules = {'.'.join(p.relative_to(root).with_suffix('').parts): p
               for p in (root / 'Pinwheel').rglob('*.lean')}
    modules['Pinwheel'] = root / 'Pinwheel.lean'
    ordered, active, seen = [], set(), set()
    def visit(name):
        if name in seen or name not in modules:
            return
        if name in active:
            raise RuntimeError('Cyclic local Lean imports: ' + name)
        active.add(name)
        for child in re.findall(r'^\s*(?:public\s+)?import\s+(\S+)', modules[name].read_text(), re.M):
            visit(child)
        active.remove(name); seen.add(name); ordered.append((name, modules[name]))
    visit('Pinwheel')
    if set(modules) != seen:
        raise RuntimeError('Serial build does not cover the complete default library')
    return ordered


def serial_limits(memory_mib=4096):
    if type(memory_mib) is not int or not 256 <= memory_mib <= 6144:
        raise RuntimeError('Serial Lean memory must be between 256 and 6144 MiB')
    return [f'-M{memory_mib}', '-j1', '-DElab.async=false']


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--tag', default='local')
    parser.add_argument('--serial-build', action='store_true',
                        help='One bounded Lean process per module; no concurrent Lake build')
    parser.add_argument('--timeout-seconds', type=int, default=7200)
    parser.add_argument('--lean-memory-mib', type=int, default=4096,
                        help='Serial Lean memory ceiling, 256..6144 MiB (default4096)')
    args = parser.parse_args()
    if not 1 <= args.timeout_seconds <= 43200:
        parser.error('Timeout must be between 1 and 43200 seconds')
    limits = serial_limits(args.lean_memory_mib) if args.serial_build else []
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
                                 'scripts/process_group.py',
                                 'scripts/binary_v0.py',
                                 'scripts/check-uart-rx.py', 'scripts/uart_rx_oracle.py',
                                 'scripts/reactive-core-vectors.py', 'scripts/execution-vectors.py']]
    sources += sorted((ROOT / 'Pinwheel').rglob('*.lean')) + sorted((ROOT / 'test').glob('*.lean'))
    hashes = {str(p.relative_to(ROOT)): sha(p) for p in sources}
    out.mkdir(parents=True)
    commands = []
    started = time.monotonic()
    def run(command, label, reject=False, reject_marker='Unapproved axioms in Pinwheel.CI.untrusted'):
        argv = list(map(str, command))
        if args.serial_build:
            remaining = args.timeout_seconds - (time.monotonic() - started)
            if remaining <= 0:
                raise TimeoutError('Serial foundation wall-time limit reached')
            result = process_group.run_captured(argv, cwd=ROOT, timeout=min(900, remaining),
                                               log_path=out / f'{label}.log')
        else:
            result = subprocess.run(argv, cwd=ROOT, capture_output=True, text=True)
        log = result.stdout + result.stderr
        (out / f'{label}.log').write_text(log)
        commands.append(dict(label=label, command=list(map(str, command)), exit_code=result.returncode))
        if reject:
            if result.returncode == 0 or reject_marker not in log:
                raise RuntimeError(f'Audit mutation was not rejected for the expected reason: {log}')
        elif result.returncode:
            raise RuntimeError(f'{label} failed:\n{log}')
        print(f'{label}: ' + ('expected rejection' if reject else log.strip()[-1200:]), flush=True)
        return log
    lean = [lake, 'env', 'lean', *limits, '-DwarningAsError=true']
    version = run([lake, 'env', 'lean', '--version'], 'version').strip()
    expected = (ROOT / 'lean-toolchain').read_text().strip().split(':v')[-1]
    if not re.search(r'Lean \(version ' + re.escape(expected) + r'(?:,|\s)', version):
        raise RuntimeError(f'Expected repository toolchain {expected}, got {version}')
    if args.serial_build:
        for name, source in serial_modules():
            relative = source.relative_to(ROOT)
            artifacts = ROOT / '.lake/build/lib/lean' / relative.with_suffix('')
            generated = ROOT / '.lake/build/ir' / relative.with_suffix('.c')
            artifacts.parent.mkdir(parents=True, exist_ok=True)
            generated.parent.mkdir(parents=True, exist_ok=True)
            run([*lean, '-o', str(artifacts)+'.olean', '-i', str(artifacts)+'.ilean',
                 '-c', generated, relative], 'build-' + name)
    else:
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
    if args.serial_build:
        control = out / 'Pinwheel/CI/FoundationPrivateControl.lean'
        control.parent.mkdir(parents=True, exist_ok=True)
        control.write_text('namespace Pinwheel.CI\nprivate axiom forbiddenUnused : False\nend Pinwheel.CI\n')
        control_olean = ROOT / '.lake/build/lib/lean/Pinwheel/CI/FoundationPrivateControl.olean'
        if control_olean.exists():
            raise RuntimeError('Private axiom control must use a fresh module')
        control_olean.parent.mkdir(parents=True, exist_ok=True)
        run([*lean, '-R', out, '-o', control_olean, control], 'compile-unused-private-axiom')
        private_audit = out / 'AuditPrivateControl.lean'
        private_audit.write_text('import Pinwheel.CI.FoundationPrivateControl\n' + audit_text)
        rejected = run([*lean, '-R', out, private_audit], 'reject-unused-private-axiom', reject=True,
                       reject_marker='Unapproved axioms in _private.Pinwheel.CI.FoundationPrivateControl.')
        if 'forbiddenUnused' not in rejected:
            raise RuntimeError('Private control rejection did not identify the unused axiom')
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
                  serial_build=args.serial_build, lean_resource_limits=limits,
                  timeout_seconds=args.timeout_seconds if args.serial_build else None,
                  audited_theorems=int(counts[2]), executable_suites=len(SUITES),
                  kernel_suites=len(KERNEL_SUITES),
                  untrusted_axiom_rejected=True, commands=commands, source_sha256=hashes,
                  unused_private_axiom_rejected=True if args.serial_build else None,
                  elapsed_seconds=round(time.monotonic()-started, 3),
                  boundary='Fresh-source-capable Lean/model gate, initialized finite UART package/lifecycle and owned receipts, '
                           'compiled UART link/stream timing, independent PWL lookup and UART RX/E64 oracle, '
                           'retained-result ownership and stream-control circuitry; '
                           'parametric finite-transfer ownership and shared reactive/counted buffered '
                           'execution models, initialized one-transfer SPI source-to-packed-digital-SRAM '
                           'execution refinement, all-eight-operation certified digital refinement, '
                           'initialized I2C and timing-parameterized source execution, finite reuse/reset and '
                           'carried logical allocation, sampled-frame interior abort/reload, '
                           'sampled-serial frozen receipt contracts, local buffered circuit equations and '
                           'independent source/circuit executable controls; bounded streaming queues, '
                           'ordered bit conservation, natural nonwrapping counters, serviced termination, '
                           'sampled HIGH timing, physical frontend/source sessions and compiler-bound '
                           'cold/upload/COMMIT initialization; sampled-ready streaming guards, bounded timeout prefixes, '
                           'guarded capture, reactive I2C cold boot and actual runtime/custody/fair-service composition; '
                           'autonomous streaming UART8N1 source timing, physical cold/upload/START arming, '
                           'public idle-host command derivation and retained good/fault frame custody. '
                           'Includes generic mapped-cell certificate infrastructure and universal first-terminal '
                           'UART source/public-BUSY timing; actual mapped artifact qualification is a separate gate. '
                           'Does not run RTL simulation, technology mapping, physical tools, '
                           'or prove emitter/CIRCT equivalence.')
    (out / 'report.json').write_text(json.dumps(report, indent=2)+'\n')
    print(f'Foundation gate passed: {out / "report.json"}', flush=True)


if __name__ == '__main__':
    main()
