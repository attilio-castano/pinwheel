#!/usr/bin/env python3
"""Check timed refinement and unchanged RTL against the completed storage study.

Requires the existing storage oracle fixtures and pinned hardware tools. This
runner does not regenerate or overwrite physical/mapping receipts.
"""
import hashlib
import json
import re
import shutil
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'build/contracts'
STORAGE = ROOT / 'build/storage'
ORACLE = STORAGE / 'small-dense-cached'


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run(args, label, reject=False):
    result = subprocess.run(list(map(str, args)), cwd=ROOT, text=True, capture_output=True)
    log = result.stdout + result.stderr
    (OUT / label).write_text(log)
    if reject:
        if not result.returncode or 'LOADER edge' not in log:
            raise RuntimeError(f'Mutation was not rejected as expected: {log}')
    elif result.returncode:
        raise RuntimeError(f'{args}\n{log}')
    return result.stdout


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    (OUT / 'report.json').unlink(missing_ok=True)
    baseline_path = ROOT / 'test/timed-contracts-baseline.json'
    baseline = json.loads(baseline_path.read_text())
    lake = shutil.which('lake')
    if not lake:
        raise RuntimeError('Put the pinned Lean toolchain on PATH before running this check.')
    for name, expected in baseline['oracle_sha256'].items():
        path = ORACLE / name
        if not path.exists() or digest(path) != expected:
            raise RuntimeError(f'Missing or changed storage-study fixture: {path}')
    run([lake, 'build'], 'build.log')
    paths = [ROOT / 'Pinwheel/Hardware/Timed.lean', ROOT / 'Pinwheel/Hardware/Reactive/Fetch.lean',
             ROOT / 'Pinwheel/Hardware/Reactive/FetchChoice.lean',
             ROOT / 'Pinwheel/Hardware/Interface.lean', ROOT / 'Pinwheel/Hardware/Reactive/Interface.lean']
    paths += sorted((ROOT / 'Pinwheel/Hardware/Storage').glob('*.lean'))
    expected = []
    for path in paths:
        source = path.read_text()
        namespace = re.search(r'^namespace (\S+)', source, re.M)[1]
        if path == ROOT / 'Pinwheel/Hardware/Interface.lean':
            namespace += '.Interface'
        expected += [namespace + '.' + n for n in re.findall(r'^theorem ([\w.]+)', source, re.M)]
    expected += ['Pinwheel.Hardware.Timed.Refinement.' + n for n in ['refl', 'trans']]
    expected += ['Pinwheel.Hardware.Storage.Cache.' + n for n in
                 ['refinement', 'structuralRefinement', 'completeRefinement']]
    expected += ['Pinwheel.Hardware.Storage.FetchChoice.' + n for n in
                 ['refinement', 'completeRefinement']]
    expected += ['Pinwheel.Hardware.Interface.namedRefinement']
    expected += ['Pinwheel.Hardware.Reactive.' + n for n in
                 ['inputInterface', 'registerInterface', 'outputInterface']]
    audit_file = OUT / 'Axioms.lean'
    audit_file.write_text('import Pinwheel\n' + ''.join(f'#print axioms {n}\n' for n in expected))
    audit = run([lake, 'env', 'lean', '-DwarningAsError=true', audit_file], 'axioms.log')
    entries = re.findall(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)", audit)
    if sorted(n for n, _ in entries) != sorted(expected):
        raise RuntimeError('Axiom audit did not cover every requested declaration.')
    for name, axioms in entries:
        extra = set(filter(None, map(str.strip, axioms.split(',')))) - {'propext', 'Classical.choice', 'Quot.sound'}
        if extra:
            raise RuntimeError(f'Unexpected axioms for {name}: {extra}')
    print(f'Audited {len(entries)} declarations.', flush=True)
    for name in ['TimedContracts', 'FetchChoice', 'Interfaces', 'StorageCache', 'StorageDense']:
        print(run([lake, 'env', 'lean', '-DwarningAsError=true', '--run', f'test/{name}.lean'],
                  f'{name}.log').strip(), flush=True)
    run([lake, 'env', 'lean', '--run', 'test/Storage.lean'], 'emit.log')
    mlir = {name: digest(STORAGE / f'{name}.mlir') for name in baseline['mlir_sha256']}
    if mlir != baseline['mlir_sha256']:
        raise RuntimeError(f'Emitted MLIR changed: {mlir}')
    circt = ROOT / 'build/tools/firtool-1.159.0/bin/circt-opt'
    rtl = run([circt, STORAGE / 'small-dense-cached.mlir', '--canonicalize', '--lower-seq-to-sv',
               '--lower-hw-to-sv', '--hw-legalize-modules', '--export-verilog', '-o', '/dev/null'], 'export.log')
    design = OUT / 'design.sv'
    design.write_text(rtl)
    if digest(design) != baseline['rtl_sha256']:
        raise RuntimeError('General candidate RTL changed.')
    suite = ROOT / 'build/tools/oss-cad-suite/bin'
    run([suite / 'iverilog', '-g2012', '-s', 'loader_tb', '-o', OUT / 'sim.vvp', design,
         ORACLE / 'tb.sv'], 'compile.log')
    simulation = run([suite / 'vvp', OUT / 'sim.vvp'], 'simulation.log')
    print(simulation.strip(), flush=True)
    bad, count = re.subn(r'(r_cached_word\s*<=)[^;]+;', lambda m: m[1] + " 64'd4;", rtl)
    if count != 1:
        raise RuntimeError(f'Expected one cache mutation anchor, found {count}.')
    mutant = OUT / 'mutant.sv'
    mutant.write_text(bad)
    run([suite / 'iverilog', '-g2012', '-s', 'loader_tb', '-o', OUT / 'mutant.vvp', mutant,
         ORACLE / 'tb.sv'], 'mutant-compile.log')
    run([suite / 'vvp', OUT / 'mutant.vvp'], 'mutant.log', reject=True)
    sources = sorted((ROOT / 'Pinwheel').rglob('*.lean'))
    sources += [Path(__file__).resolve(), baseline_path, ROOT / 'test/TimedContracts.lean', ROOT / 'test/Interfaces.lean',
                ROOT / 'test/FetchChoice.lean',
                ROOT / 'test/FetchChoiceEmit.lean', ROOT / 'test/CommandSplitEmit.lean',
                ROOT / 'test/Storage.lean', ROOT / 'test/StorageCache.lean', ROOT / 'test/StorageDense.lean',
                ROOT / 'lean-toolchain', ROOT / 'lakefile.toml', ROOT / 'tools/hardware-toolchain.json']
    fixtures = [ORACLE / n for n in baseline['oracle_sha256']]
    fixtures += [STORAGE / 'cached/vectors.txt', STORAGE / 'codec-vectors.txt']
    report = dict(audited_declarations=expected, mlir_sha256=mlir, rtl_sha256=digest(design),
                  simulation=simulation, held_cache_mutant_rejected=True,
                  source_sha256={str(p.relative_to(ROOT)): digest(p) for p in sources},
                  fixture_sha256={str(p.relative_to(ROOT)): digest(p) for p in fixtures},
                  baseline_commit=baseline['source_commit'],
                  boundary='Same-edge Lean refinement plus unchanged generated RTL and regression evidence. '
                           'No proof of emitter/CIRCT translation, new physical measurement, or timing closure.')
    (OUT / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    print('Five MLIR modules and general candidate RTL unchanged; held-cache mutant rejected.', flush=True)


if __name__ == '__main__':
    main()
