#!/usr/bin/env python3
"""Atomic-loader proof audit, independent traces, RTL mutations and generic synthesis."""
import collections
import hashlib
import json
import re
import runpy
import shutil
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT/'build/loader'


def run(args, name, reject=False):
    result = subprocess.run(list(map(str, args)), cwd=ROOT, text=True, capture_output=True)
    output = result.stdout+result.stderr
    (OUT/name).write_text(output)
    if reject:
        if result.returncode == 0 or 'FATAL:' not in output or 'LOADER edge' not in output:
            raise RuntimeError(f'Mutant escaped oracle: {args}\n{output}')
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
    run([lake, 'build', 'Pinwheel.Hardware.Loader.Emit'], 'emitter-build.log')
    lean = [lake, 'env', 'lean', '-DwarningAsError=true']
    expected = []
    for path in sorted((ROOT/'Pinwheel/Hardware/Loader').glob('*.lean')):
        ns = re.search(r'^namespace (\S+)', path.read_text(), re.M)[1]
        expected += [ns+'.'+n for n in re.findall(r'^theorem (\w+)', path.read_text(), re.M)]
    expected.sort()
    if sorted(re.findall(r'^#print axioms (\S+)', (ROOT/'test/LoaderAxioms.lean').read_text(), re.M)) != expected:
        raise RuntimeError('Every public loader theorem must be audited')
    audit = run([*lean, 'test/LoaderAxioms.lean'], 'axioms.log')
    entries = re.findall(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)", audit)
    if sorted(n for n, _ in entries) != expected: raise RuntimeError('Incomplete proof audit')
    for name, axioms in entries:
        if set(filter(None, map(str.strip, axioms.split(',')))) - {'propext', 'Classical.choice', 'Quot.sound'}:
            raise RuntimeError(f'Unapproved assumptions in {name}')
    print(f'Audited {len(expected)} public loader theorems.', flush=True)
    print(run([*lean, '--run', 'test/Loader.lean'], 'emit.log').strip(), flush=True)
    coverage = runpy.run_path(str(ROOT/'scripts/loader-vectors.py'))['generate']()
    rtl = run([circt, OUT/'atomic.mlir', '--canonicalize', '--lower-seq-to-sv', '--lower-hw-to-sv',
               '--hw-legalize-modules', '--export-verilog', '-o', '/dev/null'], 'export.log')
    (OUT/'atomic.sv').write_text(rtl)

    def simulate(name, source, reject=False):
        run([suite/'iverilog', '-g2012', '-s', 'loader_tb', '-o', OUT/f'{name}.vvp',
             source, ROOT/'test/loader_tb.sv'], f'{name}-compile.log')
        return run([suite/'vvp', OUT/f'{name}.vvp'], f'{name}.log', reject)

    print(simulate('atomic', OUT/'atomic.sv').strip(), flush=True)
    print(run([*lean, '--run', 'test/Loader.lean', 'check'], 'lean-check.log').strip(), flush=True)
    header, body = rtl.split(');', 1)
    variants = {}
    for name, port, replacement in [('init-ignored', 'init', "1'b0"), ('reset-ignored', 'reset', "1'b0")]:
        variants[name] = header+');'+re.sub(r'\b'+port+r'\b', replacement, body)
    variants['start-ignored'] = header+");\nwire [2:0] bad_command = command == 3'd5 ? 3'd0 : command;\n"+re.sub(r'\bcommand\b', 'bad_command', body)
    variants['upload-bit-corrupted'] = header+");\nwire [63:0] bad_data = data ^ 64'h1;\n"+re.sub(r'\bdata\b', 'bad_data', body)
    target = "r_loader_cursor == 9'h142"
    if rtl.count(target) != 1: raise RuntimeError('Commit mutation anchor changed')
    variants['commit-one-word-early'] = rtl.replace(target, "r_loader_cursor == 9'h141")
    for name, source in variants.items():
        (OUT/f'{name}.sv').write_text(source)
        simulate(name, OUT/f'{name}.sv', True)
    print(f'Rejected {len(variants)} RTL mutations.', flush=True)
    top = 'pinwheel_atomic_indexed'
    script = '\n'.join([f'read_verilog -sv {OUT}/atomic.sv', f'hierarchy -check -top {top}',
                        f'synth -top {top}', 'check -assert', 'stat', 'ltp -noff',
                        f'write_json {OUT}/netlist.json', ''])
    (OUT/'synthesis.ys').write_text(script)
    log = run([suite/'yosys', '-Q', '-T', '-s', OUT/'synthesis.ys'], 'synthesis.log')
    cells = json.loads((OUT/'netlist.json').read_text())['modules'][top]['cells']
    histogram = dict(sorted(collections.Counter(c['type'] for c in cells.values()).items()))
    ff = sum(n for cell, n in histogram.items() if 'DFF' in cell)
    if ff != 2*5646+49+12: raise RuntimeError(f'Unexpected storage: {ff}')
    path = re.search(r'longest topological path.*?length[ =]+(\d+)', log, re.I)
    if not path: raise RuntimeError('No path measurement')
    metrics = dict(total_generic_cells=len(cells), flip_flop_bits=ff, combinational_cells=len(cells)-ff,
                   longest_topological_path_cells=int(path[1]), generic_cells=histogram)
    print(f'Atomic indexed: {len(cells)} generic cells, {ff} FF bits, path {path[1]}.', flush=True)
    paths = sorted((ROOT/'Pinwheel').rglob('*.lean')) + [ROOT/p for p in [
        'Pinwheel.lean', 'test/Loader.lean', 'test/LoaderAxioms.lean', 'test/loader_tb.sv',
        'scripts/check-loader.py', 'scripts/loader-vectors.py', 'scripts/reactive-core-vectors.py',
        'scripts/execution-vectors.py', 'lean-toolchain', 'tools/hardware-toolchain.json']]
    hashes = {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}
    artifacts = {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(OUT.iterdir())
                 if p.suffix in {'.sv', '.svh', '.mlir', '.txt'}}
    versions = {name: run([binary, flag], f'{name}-version.log').strip() for name, binary, flag in [
        ('circt', circt, '--version'), ('yosys', suite/'yosys', '-V'), ('iverilog', suite/'iverilog', '-V')]}
    report = dict(proof_theorems=len(expected), coverage=coverage, mutations_rejected=list(variants),
                  synthesis=metrics, source_sha256=hashes, artifact_sha256=artifacts, versions=versions,
                  boundary='Atomic synchronous host-word interface; no serial transport, CDC, routed area/timing or translation proof.')
    (OUT/'report.json').write_text(json.dumps(report, indent=2)+'\n')
    print('Wrote build/loader/report.json', flush=True)


if __name__ == '__main__': main()
