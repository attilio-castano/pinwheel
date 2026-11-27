"""Regenerate the release RTL from the current tree and compare it with the pins.

The entry's four RTL files (core.sv, frontend.sv, package.sv, tt.sv) are
pinned by SHA-256 in the release workflow. A change in Lean, the emitter,
CIRCT lowering or the Python wrapper that alters the chip shows up here as a
hash difference, so refactors that should preserve the chip can be checked in
one command. Hash equality is the claim; nothing is re-signed or rebuilt
physically.

With `--simulate`, the regenerated RTL is also compiled into the public-pin
bridge and the bring-up simulation runs in every I2C fixture mode.

Outputs go to a fresh build/release-rtl/TAG directory with report.json. Exit
status 1 means a hash differed or a simulation failed.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))

RELEASE_WORKFLOW = ROOT / 'physical/streaming_8x4/ttihp27a-custom-gds.yml'
RTL_FILES = ('core.sv', 'frontend.sv', 'package.sv', 'tt.sv')
DEPTH_ADDR_BITS = 1  # depth two, the release configuration
CIRCT_RELEASE = 'firtool-1.159.0'
# Pinned tool installs; PINWHEEL_TOOLS points elsewhere, e.g. at the main checkout's build/tools.
DEFAULT_TOOLS = Path(os.environ.get('PINWHEEL_TOOLS', ROOT / 'build/tools'))


def sha(path):
    with Path(path).open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def pinned_hashes(workflow=RELEASE_WORKFLOW):
    """The src/*.sv hashes that the release workflow's sha256sum step checks."""
    found = {name: digest for digest, name in
             re.findall(r'^\s*([0-9a-f]{64})\s+src/(\S+)\s*$', Path(workflow).read_text(), re.M)}
    if set(found) != set(RTL_FILES):
        raise ValueError(f'Release workflow pins {sorted(found)}, expected {list(RTL_FILES)}')
    return found


def compare(pins, generated):
    """Rows of (file, pinned, generated, equal) for each release RTL file."""
    return [dict(file=name, pinned=pins[name], generated=generated.get(name), equal=pins[name] == generated.get(name))
            for name in RTL_FILES]


def default_tool(name):
    paths = {'circt': DEFAULT_TOOLS / CIRCT_RELEASE / 'bin/circt-opt',
             'iverilog': DEFAULT_TOOLS / 'oss-cad-suite/bin/iverilog',
             'vvp': DEFAULT_TOOLS / 'oss-cad-suite/bin/vvp'}
    return paths[name]


def run(argv, out, label, **kwargs):
    log = out / (label + '.log')
    with log.open('xb') as stream:
        result = subprocess.run([str(arg) for arg in argv], cwd=ROOT, stdout=kwargs.pop('stdout', stream),
                                stderr=stream, timeout=kwargs.pop('timeout', 1800), **kwargs)
    if result.returncode != 0:
        raise RuntimeError(f'{label} failed with exit {result.returncode}; see {log}')
    return log


def regenerate(out, circt):
    """Emit, wrap and lower the release RTL into out/src, as the source replay does."""
    from streaming_ready_artifacts import LOWERING_PASSES, lowering_copy
    from streaming_ready_wrapper import bridge_source, package_source, tt_source

    version = subprocess.run([str(circt), '--version'], capture_output=True, text=True, check=True).stdout
    if CIRCT_RELEASE not in version:
        raise RuntimeError(f'Expected CIRCT {CIRCT_RELEASE}, found: {version.strip()}')
    emitted, src = out / 'emitted', out / 'src'
    src.mkdir(parents=True)
    run(['lake', 'build', 'Pinwheel.Hardware.StreamingReady.CoreEmit', 'Pinwheel.Hardware.Streaming.FrontendEmit'],
        out, 'lean-build')
    run(['lake', 'env', 'lean', '-DwarningAsError=true', '--run', 'test/StreamingReadyArtifactEmit.lean',
         emitted, str(DEPTH_ADDR_BITS)], out, 'lean-emit')
    for name in ('core', 'frontend'):
        lowering_copy(emitted / (name + '.mlir'), emitted / (name + '-lowering.mlir'))
        with (src / (name + '.sv')).open('xb') as target:
            run([circt, emitted / (name + '-lowering.mlir'), *LOWERING_PASSES], out, name + '-lower', stdout=target)
    core = json.loads((emitted / 'assembly.json').read_text())
    frontend = json.loads((emitted / 'frontend-assembly.json').read_text())
    (src / 'package.sv').write_text(package_source(core, frontend))
    (src / 'tt.sv').write_text(tt_source(2))
    (out / 'bridge.sv').write_text(bridge_source(2))
    return {name: sha(src / name) for name in RTL_FILES}, version.strip()


def simulate(out, iverilog, vvp):
    """Compile the public-pin bridge and run the bring-up simulation in every I2C mode."""
    import streaming_8x4_bringup as bringup

    model = out / 'bridge.vvp'
    run([iverilog, '-g2012', '-s', 'streaming_quad_host_bridge', '-o', model,
         *(out / 'src' / name for name in RTL_FILES), out / 'bridge.sv'], out, 'bridge-compile')
    digest = sha(model)
    results = {}
    for mode in bringup.I2C_MODES:
        target = out / f'simulate-{mode}.json'
        with target.open('xb') as stream:
            run([sys.executable, '-B', 'scripts/streaming_8x4_bringup.py', 'simulate', '--vvp', vvp,
                 '--executable', model, '--executable-sha256', digest, '--i2c-mode', mode],
                out, f'simulate-{mode}', stdout=stream)
        report = json.loads(target.read_text())
        results[mode] = dict(passed=report.get('passed') is True, cases=sorted(report['cases']))
    return dict(model_sha256=digest, modes=results)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument('--tag', required=True, help='name of the fresh build/release-rtl/TAG directory')
    parser.add_argument('--circt', type=Path, default=None, help=f'circt-opt from {CIRCT_RELEASE}')
    parser.add_argument('--simulate', action='store_true', help='also run the bring-up simulation in every I2C mode')
    parser.add_argument('--iverilog', type=Path, default=None)
    parser.add_argument('--vvp', type=Path, default=None)
    args = parser.parse_args(argv)
    if not re.fullmatch(r'[A-Za-z0-9][A-Za-z0-9._-]*', args.tag):
        parser.error('Use a plain tag name')
    out = ROOT / 'build/release-rtl' / args.tag
    if out.exists():
        parser.error(f'{out} exists; choose a fresh tag')
    tools = {name: (getattr(args, name) or default_tool(name)) for name in ('circt', 'iverilog', 'vvp')}
    needed = ['circt'] + (['iverilog', 'vvp'] if args.simulate else [])
    missing = [name for name in needed if not Path(tools[name]).is_file()]
    if missing or shutil.which('lake') is None:
        parser.error(f'Missing tools: {", ".join(missing) or "lake"}; pass their paths explicitly')
    pins = pinned_hashes()
    out.mkdir(parents=True)

    report = dict(schema='pinwheel.release-rtl-check.v1', tag=args.tag,
                  source_commit=subprocess.run(['git', 'rev-parse', 'HEAD'], cwd=ROOT, capture_output=True,
                                               text=True).stdout.strip(),
                  worktree_clean=subprocess.run(['git', 'status', '--porcelain'], cwd=ROOT, capture_output=True,
                                                text=True).stdout == '',
                  pins_from=RELEASE_WORKFLOW.relative_to(ROOT).as_posix(),
                  tools={name: str(path) for name, path in tools.items() if name in needed})
    try:
        generated, report['circt_version'] = regenerate(out, tools['circt'])
        report['rtl'] = compare(pins, generated)
        identical = all(row['equal'] for row in report['rtl'])
        report['rtl_identical'] = identical
        if args.simulate:
            report['simulation'] = simulate(out, tools['iverilog'], tools['vvp'])
        passed = identical and (not args.simulate or all(m['passed'] for m in report['simulation']['modes'].values()))
    except (OSError, RuntimeError, ValueError, subprocess.SubprocessError) as error:
        report['error'] = str(error)
        passed = False
    report['passed'] = passed
    (out / 'report.json').write_text(json.dumps(report, indent=1) + '\n')

    for row in report.get('rtl', []):
        print(f"{'same' if row['equal'] else 'DIFFERENT':9} src/{row['file']}")
    for mode, result in report.get('simulation', {}).get('modes', {}).items():
        print(f"{'pass' if result['passed'] else 'FAIL':9} bring-up simulation, I2C mode {mode}")
    if 'error' in report:
        print('error:', report['error'])
    print(('PASSED' if passed else 'FAILED') + f': {out.relative_to(ROOT)}/report.json')
    return 0 if passed else 1


if __name__ == '__main__':
    sys.exit(main())
