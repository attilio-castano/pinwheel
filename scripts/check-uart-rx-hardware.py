#!/usr/bin/env python3
"""Fresh-source RX integration: structural components and four emitted RTL backends.

Runs the existing mixed-protocol vectors with RX additions. No synthesis, mapping,
physical run, or replacement of frozen timed-contract fixtures is performed.
"""
import argparse
import hashlib
import json
import re
import runpy
import shutil
import subprocess
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--tag', required=True)
    parser.add_argument('--tools', type=Path, default=ROOT / 'build/tools')
    args = parser.parse_args()
    if not args.tag.replace('-', '').replace('_', '').isalnum():
        parser.error('Use letters, numbers, hyphens or underscores in tags')
    out = ROOT / 'build/uart-rx/hardware' / args.tag
    if out.exists():
        raise RuntimeError('Choose a fresh tag to retain earlier evidence')
    manifest = json.loads((ROOT / 'tools/hardware-toolchain.json').read_text())
    circt = args.tools / manifest['packages']['circt']['directory'] / 'bin/circt-opt'
    suite = args.tools / manifest['packages']['oss-cad-suite']['directory'] / 'bin'
    lake = shutil.which('lake')
    if not lake or not all(p.is_file() for p in [circt, suite / 'iverilog', suite / 'vvp']):
        raise RuntimeError('Install the pinned Lean/CAD tools; see docs/development.md')
    sources = sorted((ROOT / 'Pinwheel').rglob('*.lean')) + [ROOT / p for p in [
        'Pinwheel.lean', 'lean-toolchain', 'lakefile.toml', 'lake-manifest.json',
        'tools/hardware-toolchain.json', 'test/ReactiveCore.lean', 'test/Loader.lean',
        'test/Storage.lean', 'test/reactive_core_tb.sv', 'test/loader_tb.sv',
        'scripts/check-uart-rx-hardware.py', 'scripts/reactive-core-vectors.py',
        'scripts/loader-vectors.py', 'scripts/execution-vectors.py', 'scripts/uart_rx_oracle.py']]
    hashes = {str(p.relative_to(ROOT)): sha(p) for p in sources}
    out.mkdir(parents=True)
    started = time.monotonic()
    commands = []

    def run(command, label, reject=False):
        command = list(map(str, command))
        result = subprocess.run(command, cwd=ROOT, text=True, capture_output=True)
        log = result.stdout + result.stderr
        (out / f'{label}.log').write_text(log)
        commands.append(dict(label=label, command=command, exit_code=result.returncode))
        if reject:
            if result.returncode == 0 or 'FATAL:' not in log or 'LOADER edge' not in log:
                raise RuntimeError(f'{label} did not fail the loader oracle: {log}')
        elif result.returncode:
            raise RuntimeError(f'{label} failed: {log}')
        return log

    run([lake, 'build'], 'build')
    lean = [lake, 'env', 'lean', '-DwarningAsError=true', '--run']
    for name in ['ReactiveCore', 'Loader', 'Storage']:
        print(run([*lean, f'test/{name}.lean'], f'emit-{name}').strip(), flush=True)
    coverage = {}
    for name in ['reactive-core', 'loader']:
        coverage[name] = runpy.run_path(str(ROOT / f'scripts/{name}-vectors.py'))['generate']()
    for name in ['ReactiveCore', 'Loader']:
        print(run([*lean, f'test/{name}.lean', 'check'], f'structural-{name}').strip(), flush=True)

    designs = dict(direct=ROOT / 'build/reactive-core/direct.mlir',
                   indexed=ROOT / 'build/reactive-core/indexed.mlir',
                   atomic=ROOT / 'build/loader/atomic.mlir',
                   default=ROOT / 'build/storage/small-dense-cached.mlir')
    for name, mlir in designs.items():
        (out / f'{name}.mlir').write_bytes(mlir.read_bytes())
        rtl = run([circt, mlir, '--canonicalize', '--lower-seq-to-sv', '--lower-hw-to-sv',
                   '--hw-legalize-modules', '--export-verilog', '-o', '/dev/null'], f'export-{name}')
        (out / f'{name}.sv').write_text(rtl)

    # Copy vectors into the tagged receipt, so another experiment cannot alter this evidence.
    for name in ['direct', 'indexed']:
        (out / f'{name}-vectors.txt').write_bytes((ROOT / f'build/reactive-core/{name}-vectors.txt').read_bytes())
    (out / 'loader-vectors.txt').write_bytes((ROOT / 'build/loader/vectors.txt').read_bytes())
    core_tb = (ROOT / 'test/reactive_core_tb.sv').read_text()
    for name in ['direct', 'indexed']:
        core_tb = core_tb.replace(f'build/reactive-core/{name}-vectors.txt', str(out / f'{name}-vectors.txt'))
    (out / 'core_tb.sv').write_text(core_tb)
    loader_tb = (ROOT / 'test/loader_tb.sv').read_text().replace('build/loader/vectors.txt', str(out / 'loader-vectors.txt'))
    observe = (ROOT / 'build/loader/memory-observe.svh').read_text()
    (out / 'atomic-observe.svh').write_text(observe)
    (out / 'atomic_tb.sv').write_text(loader_tb.replace('build/loader/memory-observe.svh', str(out / 'atomic-observe.svh')))

    # Same physical 55-bit overlay and cache observation as measure-storage-variant.py.
    for bank in range(2):
        for k in range(32, 64):
            observe = observe.replace(f'dut.r_bank{bank}_word{k};', "64'd4;")
    observe = re.sub(r'(dut\.r_bank[01]_word\d+)', r'expand55(\1)', observe)
    (out / 'default-observe.svh').write_text(observe)
    default_tb = loader_tb.replace('pinwheel_atomic_indexed', 'pinwheel_atomic_small_dense_cached')
    default_tb = default_tb.replace('build/loader/memory-observe.svh', str(out / 'default-observe.svh'))
    default_tb = default_tb.replace('  reg [63:0] expected', '''  function [63:0] expand55(input [54:0] w);
    expand55 = w[2:0] == 3 ? {35'd0,w[28:17],w[16:0]} : {1'b0,w[54:17],8'd0,w[16:0]};
  endfunction
  reg [63:0] expected''')
    default_tb = default_tb.replace('      for (k = 0;', '''      if (busy && dut.r_cached_word !== observed[(loader_active ? 322 : 0) + observed[(loader_active ? 322 : 0) + 64 + pc]])
        $fatal(1, "LOADER edge %0d cached word invariant", count);
      for (k = 0;''')
    (out / 'default_tb.sv').write_text(default_tb)

    def simulate(name, rtl, reject=False):
        core = name in ['direct', 'indexed']
        top = 'reactive_core_tb' if core else 'loader_tb'
        tb = out / ('core_tb.sv' if core else 'atomic_tb.sv' if name == 'atomic' else 'default_tb.sv')
        flags = ['-DINDEXED'] if name == 'indexed' else []
        run([suite / 'iverilog', '-g2012', *flags, '-s', top, '-o', out / f'{name}.vvp', rtl, tb], f'compile-{name}')
        return run([suite / 'vvp', out / f'{name}.vvp'], f'simulate-{name}', reject)

    simulations = {}
    for name in designs:
        simulations[name] = simulate(name, out / f'{name}.sv').strip()
        print(name + ': ' + simulations[name], flush=True)
    rtl = (out / 'default.sv').read_text()
    mutated = re.sub(r'(r_cached_word\s*<=)[^;]+;', lambda m: m[1] + " 64'd4;", rtl)
    if mutated == rtl:
        raise RuntimeError('Cache mutation anchor changed')
    (out / 'cache-mutant.sv').write_text(mutated)
    simulate('cache-mutant', out / 'cache-mutant.sv', True)
    print('Default cache mutation rejected.', flush=True)
    versions = {name: run([binary, flag], f'version-{name}').strip() for name, binary, flag in [
        ('circt', circt, '--version'), ('iverilog', suite / 'iverilog', '-V')]}
    for path in sources:
        if sha(path) != hashes[str(path.relative_to(ROOT))]:
            raise RuntimeError(f'Source changed during validation: {path}')
    report = dict(coverage=coverage, simulations=simulations, mutations_rejected=['default-cache-held-at-halt'],
                  source_sha256=hashes, artifact_sha256={p.name: sha(p) for p in sorted(out.iterdir())
                      if p.suffix in {'.sv', '.svh', '.mlir', '.txt'}},
                  tool_sha256={str(p): sha(p) for p in [circt, suite / 'iverilog', suite / 'vvp']},
                  versions=versions, commands=commands, elapsed_seconds=round(time.monotonic() - started, 3),
                  boundary='Structural components and independent RTL regression on four existing backends. '
                           'No translation proof, synthesis, timing closure, physical RX synchronizer or analog claim.')
    (out / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    print(f'UART RX hardware integration passed: {out / "report.json"}', flush=True)


if __name__ == '__main__':
    main()
