#!/usr/bin/env python3
"""Proof audit, independent oracle, component evaluation, RTL, mutations, generic synthesis."""
import collections
import hashlib
import json
import re
import runpy
import shutil
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT/'build/reactive-core'


def run(args, name, reject=False):
    result = subprocess.run(list(map(str, args)), cwd=ROOT, text=True, capture_output=True)
    output = result.stdout+result.stderr
    (OUT/name).write_text(output)
    if reject:
        if result.returncode == 0 or 'FATAL:' not in output or 'CORE edge' not in output:
            raise RuntimeError(f'Mutant escaped the oracle: {args}\n{output}')
    elif result.returncode:
        raise RuntimeError(f'Failed: {args}\n{output}')
    return output


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    (OUT/'report.json').unlink(missing_ok=True)
    manifest = json.loads((ROOT/'tools/hardware-toolchain.json').read_text())
    circt = ROOT/'build/tools'/manifest['packages']['circt']['directory']/'bin/circt-opt'
    suite = ROOT/'build/tools'/manifest['packages']['oss-cad-suite']['directory']/'bin'
    lake = shutil.which('lake')
    if not lake or not all(p.is_file() for p in [circt, suite/'iverilog', suite/'vvp', suite/'yosys']):
        raise RuntimeError('Install pinned Lean and hardware tools; see docs/development.md')
    run([lake, 'build'], 'build.log')
    lean = [lake, 'env', 'lean', '-DwarningAsError=true']
    expected = []
    for p in sorted((ROOT/'Pinwheel/Hardware/Reactive').glob('*.lean')):
        ns = 'Pinwheel.Hardware.Reactive.Core.' if p.name == 'CoreProofs.lean' else 'Pinwheel.Hardware.Reactive.'
        expected += [ns+n for n in re.findall(r'^theorem (\w+)', p.read_text(), re.M)]
    expected.sort()
    audit_source = (ROOT/'test/ReactiveCoreAxioms.lean').read_text()
    if sorted(re.findall(r'^#print axioms (\S+)', audit_source, re.M)) != expected:
        raise RuntimeError('Audit must cover every public reactive hardware theorem')
    audit = run([*lean, 'test/ReactiveCoreAxioms.lean'], 'axioms.log')
    entries = re.findall(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)", audit)
    if sorted(n for n, _ in entries) != expected:
        raise RuntimeError('Incomplete proof audit')
    for name, axioms in entries:
        if set(filter(None, map(str.strip, axioms.split(',')))) - {'propext', 'Classical.choice', 'Quot.sound'}:
            raise RuntimeError(f'Unapproved assumptions in {name}')
    print(f'Audited {len(expected)} public hardware theorems.', flush=True)
    print(run([*lean, '--run', 'test/ReactiveCore.lean'], 'emit.log').strip(), flush=True)
    coverage = runpy.run_path(str(ROOT/'scripts/reactive-core-vectors.py'))['generate']()
    for kind in ['direct', 'indexed']:
        rtl = run([circt, OUT/f'{kind}.mlir', '--canonicalize', '--lower-seq-to-sv',
                   '--lower-hw-to-sv', '--hw-legalize-modules', '--export-verilog', '-o', '/dev/null'], f'{kind}-export.log')
        (OUT/f'{kind}.sv').write_text(rtl)

    def simulate(kind, name, source, reject=False):
        flags = ['-DINDEXED'] if kind == 'indexed' else []
        run([suite/'iverilog', '-g2012', *flags, '-s', 'reactive_core_tb', '-o', OUT/f'{name}.vvp',
             source, ROOT/'test/reactive_core_tb.sv'], f'{name}-compile.log')
        return run([suite/'vvp', OUT/f'{name}.vvp'], f'{name}.log', reject)

    for kind in ['direct', 'indexed']:
        print(simulate(kind, kind, OUT/f'{kind}.sv').strip(), flush=True)
    print(run([*lean, '--run', 'test/ReactiveCore.lean', 'check'], 'lean-check.log').strip(), flush=True)
    mutations = []
    for kind in ['direct', 'indexed']:
        rtl = (OUT/f'{kind}.sv').read_text()
        # Mutate only the body, keeping interface names identical.
        header, body = rtl.split(');', 1)
        variants = {
            'input-pins-swapped': header+');\nwire [1:0] bad_inputs = {incoming[0], incoming[1]};\n'+re.sub(r'\bincoming\b', 'bad_inputs', body),
            'start-ignored': header+');'+re.sub(r'\bstart\b', "1'b0", body),
            'setup-address-bit': header+');\nwire [7:0] bad_address = address ^ 8\'h01;\n'+re.sub(r'\baddress\b', 'bad_address', body),
        }
        for fault, source in variants.items():
            name = f'{kind}-{fault}'
            (OUT/f'{name}.sv').write_text(source)
            simulate(kind, name, OUT/f'{name}.sv', True)
            mutations.append(name)
    print(f'Rejected {len(mutations)} RTL mutations.', flush=True)
    metrics = {}
    for kind in ['direct', 'indexed']:
        top = f'pinwheel_reactive_{kind}'
        script = '\n'.join([f'read_verilog -sv {OUT}/{kind}.sv', f'hierarchy -check -top {top}',
                            f'synth -top {top}', 'check -assert', 'stat', 'ltp -noff',
                            f'write_json {OUT}/{kind}-netlist.json', ''])
        (OUT/f'{kind}-synthesis.ys').write_text(script)
        log = run([suite/'yosys', '-Q', '-T', '-s', OUT/f'{kind}-synthesis.ys'], f'{kind}-synthesis.log')
        cells = json.loads((OUT/f'{kind}-netlist.json').read_text())['modules'][top]['cells']
        histogram = dict(sorted(collections.Counter(c['type'] for c in cells.values()).items()))
        ff = sum(n for cell, n in histogram.items() if 'DFF' in cell)
        if ff != {'direct': 16384+49+14, 'indexed': 5632+49+14}[kind]:
            raise RuntimeError(f'Storage unexpectedly optimized away: {kind} {ff}')
        path = re.search(r'longest topological path.*?length[ =]+(\d+)', log, re.I)
        if not path:
            raise RuntimeError('No topological path measurement')
        metrics[kind] = dict(total_generic_cells=len(cells), flip_flop_bits=ff,
                             combinational_cells=len(cells)-ff, longest_topological_path_cells=int(path[1]),
                             generic_cells=histogram)
        print(f'{kind}: {len(cells)} generic cells, {ff} FF bits, path {path[1]}.', flush=True)
    paths = sorted((ROOT/'Pinwheel').rglob('*.lean')) + [ROOT/p for p in [
        'Pinwheel.lean', 'test/ReactiveCore.lean', 'test/ReactiveCoreAxioms.lean', 'test/reactive_core_tb.sv',
        'scripts/check-reactive-core.py', 'scripts/reactive-core-vectors.py', 'scripts/execution-vectors.py',
        'lean-toolchain', 'tools/hardware-toolchain.json']]
    hashes = {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}
    artifacts = {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(OUT.iterdir())
                 if p.suffix in {'.sv', '.mlir', '.txt'}}
    versions = {name: run([binary, flag], f'{name}-version.log').strip() for name, binary, flag in [
        ('circt', circt, '--version'), ('yosys', suite/'yosys', '-V'), ('iverilog', suite/'iverilog', '-V')]}
    report = dict(proof_theorems=len(expected), coverage=coverage, mutations_rejected=mutations,
                  synthesis=metrics, source_sha256=hashes, artifact_sha256=artifacts, versions=versions,
                  boundary='Fixed loaded program; raw stopped setup is non-atomic. Generic cells/path are not ASIC area/frequency.')
    (OUT/'report.json').write_text(json.dumps(report, indent=2)+'\n')
    print('Wrote build/reactive-core/report.json', flush=True)


if __name__ == '__main__':
    main()
