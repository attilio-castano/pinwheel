#!/usr/bin/env python3
"""Build and audit the witness library outside the default Lean build.

`PinwheelWitness` holds proofs that conditional theorems are not vacuous. They
replay long executions in the kernel (minutes, several GB), so `lake build`
skips them. This check builds them, requires every file under
`PinwheelWitness/` to be imported from `PinwheelWitness.lean`, and runs the
whole-library axiom audit with the witness modules loaded.

    python3 -B scripts/check-witness.py --tag NAME

Results go to `build/witness/NAME/report.json`; exit status 1 means a build,
coverage or audit failure.
"""
import argparse
import json
import re
import shutil
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LIBRARY = 'PinwheelWitness'


def witness_modules(root=ROOT):
    """Witness modules reachable from the library root; reject unreachable files."""
    modules = {'.'.join(p.relative_to(root).with_suffix('').parts): p
               for p in (root / LIBRARY).rglob('*.lean')}
    modules[LIBRARY] = root / (LIBRARY + '.lean')
    seen = set()
    def visit(name):
        if name in seen or name not in modules:
            return
        seen.add(name)
        for child in re.findall(r'^\s*(?:public\s+)?import\s+(\S+)', modules[name].read_text(), re.M):
            visit(child)
    visit(LIBRARY)
    missing = sorted(modules.keys() - seen)
    if missing:
        raise RuntimeError(f'Witness files not imported from {LIBRARY}.lean: {missing}')
    return sorted(seen)


def audit_source(root=ROOT):
    """The whole-library audit with the witness library also imported."""
    text = (root / 'test/ProofAudit.lean').read_text()
    if '\nimport Pinwheel\n' not in '\n' + text:
        raise RuntimeError('test/ProofAudit.lean no longer imports Pinwheel')
    return ('\n' + text).replace('\nimport Pinwheel\n', f'\nimport Pinwheel\nimport {LIBRARY}\n', 1)[1:]


def main():
    parser = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    parser.add_argument('--tag', required=True)
    args = parser.parse_args()
    if not args.tag.replace('-', '').replace('_', '').isalnum():
        parser.error('Use letters, numbers, hyphens or underscores in tags')
    out = ROOT / 'build/witness' / args.tag
    if out.exists():
        parser.error('Choose a fresh tag to preserve earlier witness evidence')
    lake = shutil.which('lake')
    if not lake:
        raise RuntimeError('Install the pinned Lean toolchain and put lake on PATH')
    modules = witness_modules()
    out.mkdir(parents=True)
    commands = []

    def run(command, label):
        started = time.monotonic()
        result = subprocess.run(command, cwd=ROOT, capture_output=True, text=True)
        log = result.stdout + result.stderr
        (out / f'{label}.log').write_text(log)
        commands.append(dict(label=label, command=[str(c) for c in command], exit_code=result.returncode,
                             seconds=round(time.monotonic() - started, 1)))
        print(f'{label}: exit {result.returncode} in {commands[-1]["seconds"]} s', flush=True)
        if result.returncode:
            raise RuntimeError(f'{label} failed:\n{log[-4000:]}')
        return log

    run([lake, 'build', LIBRARY], 'build')
    audit = out / 'WitnessAudit.lean'
    audit.write_text(audit_source())
    log = run([lake, 'env', 'lean', audit], 'axioms')
    counts = re.search(r'Pinwheel audit: (\d+) declarations, (\d+) theorems;', log)
    if not counts:
        raise RuntimeError('Missing witness audit summary')
    report = dict(modules=modules, audited_declarations=int(counts[1]), audited_theorems=int(counts[2]),
                  commands=commands)
    (out / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    print(f'Witness check passed: {out / "report.json"}', flush=True)


if __name__ == '__main__':
    try:
        main()
    except RuntimeError as error:
        print(f'FAILED: {error}', file=sys.stderr)
        sys.exit(1)
