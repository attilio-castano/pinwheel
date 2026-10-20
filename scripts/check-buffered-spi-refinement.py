#!/usr/bin/env python3
"""Freeze and validate the bounded SPI source-to-packed-circuit proof gate.

The kernel checks the theorem signatures and complete-library axiom audit.
Independent finite execution checks exercise the source interpreter and actual
packed Reactive equations. This gate does not run CAD or qualify serial,
native compiler, emitter, RTL, or physical timing equivalence.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import time


ROOT = Path(__file__).resolve().parents[1]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def sources():
    paths = [ROOT / name for name in (
        'Pinwheel.lean', 'lakefile.toml', 'lake-manifest.json', 'lean-toolchain')]
    paths += sorted((ROOT / 'Pinwheel').rglob('*.lean'))
    paths += [ROOT / 'test' / name for name in (
        'ProofAudit.lean', 'BufferedSpiRefinement.lean')]
    paths.append(Path(__file__).resolve())
    return paths


def parse_checks(log):
    cases = re.findall(
        r'^([a-z0-9-]+): (\d+) independent source/circuit prefixes passed$',
        log, re.MULTILINE)
    summary = re.search(
        r'SPI source/circuit semantic probes: (\d+) cases, (\d+) compared prefixes; '
        r'START sampler and stopped sampler counterexamples witnessed', log)
    controls = re.search(
        r'Controls: (\d+) ordinary actual-state parity boundaries, '
        r'(\d+) rejected independent state mutations, and a short-TX high-bit counterexample passed', log)
    if not cases or not summary or not controls:
        raise RuntimeError('Missing independent execution/control summaries')
    count, prefixes = map(int, summary.groups())
    if len(cases) != count or len({name for name, _ in cases}) != count:
        raise RuntimeError('Execution case names/count do not match the summary')
    if sum(int(n) for _, n in cases) != prefixes:
        raise RuntimeError('Execution prefix total does not match the case records')
    return dict(cases=[dict(id=name, prefixes=int(n), passed=True) for name, n in cases],
        case_count=count, compared_prefixes=prefixes,
        ordinary_actual_boundaries=int(controls[1]),
        rejected_state_mutations=int(controls[2]),
        unused_high_tx_bits_witnessed=True,
        start_sampler_offset_witnessed=True,
        stopped_sampler_abstraction_witnessed=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--tag', required=True,
        help='Fresh receipt directory under build/validation; previous tags are preserved')
    args = parser.parse_args()
    if not re.fullmatch(r'[A-Za-z0-9_-]+', args.tag):
        parser.error('Use letters, numbers, hyphens or underscores in tags')
    out = ROOT / 'build/validation' / args.tag
    if out.exists():
        raise RuntimeError('Choose a fresh tag to preserve earlier evidence')
    lake = shutil.which('lake')
    if not lake:
        raise RuntimeError('The pinned Lean toolchain must be on PATH')

    hashes = {str(path.relative_to(ROOT)): sha(path) for path in sources()}
    out.mkdir(parents=True)
    (out / 'intake.json').write_text(json.dumps(dict(source_sha256=hashes), indent=2) + '\n')
    commands = []
    report = dict(passed=False, source_sha256=hashes, commands=commands,
        boundary='Kernel SPI source/packed-state refinement for one admitted transfer; '
            'independent finite source versus actual Reactive execution checks. '
            'Stopped sampler values are abstracted. Serial delivery, native compiler, '
            'emitter/RTL equivalence and physical timing remain separate boundaries.')
    started = time.monotonic()

    def run(command, label, rejected=False):
        command = list(map(str, command))
        result = subprocess.run(command, cwd=ROOT, text=True, capture_output=True)
        log = result.stdout + result.stderr
        (out / (label + '.log')).write_text(log)
        commands.append(dict(label=label, command=command, exit_code=result.returncode))
        if rejected:
            if result.returncode == 0 or 'Unapproved axioms in Pinwheel.CI.untrusted' not in log:
                raise RuntimeError('Injected custom axiom was not rejected for the expected reason')
        elif result.returncode:
            raise RuntimeError(label + ' failed:\n' + log)
        print(label + ': ' + ('expected rejection' if rejected else 'passed'), flush=True)
        return log

    try:
        version = run([lake, 'env', 'lean', '--version'], 'version').strip()
        expected = (ROOT / 'lean-toolchain').read_text().strip().split(':v')[-1]
        if not re.search(r'Lean \(version ' + re.escape(expected) + r'(?:,|\s)', version):
            raise RuntimeError('Toolchain does not match lean-toolchain: ' + version)
        report['lean'] = version
        run([lake, 'build'], 'build')
        lean = [lake, 'env', 'lean', '-DwarningAsError=true']
        audit_text = ('import Pinwheel.Hardware.Buffered.SpiSimulation\n' +
            (ROOT / 'test/ProofAudit.lean').read_text())
        audit_source = out / 'AuditSpiRefinement.lean'
        audit_source.write_text(audit_text)
        audit = run([*lean, audit_source], 'axioms')
        counts = re.search(r'Pinwheel audit: (\d+) declarations, (\d+) theorems;', audit)
        if not counts:
            raise RuntimeError('Missing whole-library audit summary')
        report['audited_declarations'] = int(counts[1])
        report['audited_theorems'] = int(counts[2])
        mutant = out / 'RejectAxiom.lean'
        mutant.write_text(audit_text.removesuffix('#audit_pinwheel\n') +
            'axiom Pinwheel.CI.untrusted : False\n#audit_pinwheel\n')
        run([*lean, mutant], 'reject-untrusted-axiom', rejected=True)
        report['untrusted_axiom_rejected'] = True
        checks = run([*lean, '--run', 'test/BufferedSpiRefinement.lean'], 'spi-refinement-checks')
        report['independent_checks'] = parse_checks(checks)
        current = {str(path.relative_to(ROOT)): sha(path) for path in sources()}
        if current != hashes:
            changed = sorted(key for key in hashes.keys() | current.keys()
                if hashes.get(key) != current.get(key))
            raise RuntimeError('Frozen source set changed during validation: ' + ', '.join(changed))
        report['inputs_unchanged'] = True
        report['passed'] = True
    except Exception as error:
        report['error'] = str(error)
        raise
    finally:
        report['elapsed_seconds'] = round(time.monotonic() - started, 3)
        report['artifact_sha256'] = {str(path.relative_to(out)): sha(path)
            for path in sorted(out.rglob('*')) if path.is_file() and path.name != 'report.json'}
        (out / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    print('SPI refinement receipt: ' + str(out / 'report.json'), flush=True)


if __name__ == '__main__':
    main()
