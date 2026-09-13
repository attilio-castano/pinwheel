#!/usr/bin/env python3
"""Reproduce structural-core proofs, independent traces, RTL mutations, and generic synthesis."""
import collections
import hashlib
import json
import platform
import re
import runpy
import shutil
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'build/core'


def run(args, log, reject=None):
    result = subprocess.run([str(x) for x in args], cwd=ROOT, text=True, capture_output=True)
    output = result.stdout + result.stderr
    (OUT / log).write_text(output)
    if reject:
        if result.returncode == 0 or 'FATAL:' not in output or reject not in output:
            raise RuntimeError(f'Fixture was not rejected for {reject}:\n{output}')
    elif result.returncode:
        raise RuntimeError(f'Command failed: {args}\n{output}')
    return output


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    (OUT / 'report.json').unlink(missing_ok=True)
    manifest = json.loads((ROOT / 'tools/hardware-toolchain.json').read_text())
    circt = ROOT / 'build/tools' / manifest['packages']['circt']['directory'] / 'bin/circt-opt'
    suite = ROOT / 'build/tools' / manifest['packages']['oss-cad-suite']['directory'] / 'bin'
    lake = shutil.which('lake')
    if not lake or not all(p.is_file() for p in [circt, suite/'iverilog', suite/'vvp', suite/'yosys']):
        raise SystemExit('Install the pinned Lean and hardware tools first; see docs/development.md')
    run([lake, 'build'], 'lean-build.log')
    lean = [lake, 'env', 'lean', '-DwarningAsError=true']
    audit = run([*lean, 'test/CoreAxioms.lean'], 'axioms.log')
    groups = re.findall(r'depends on axioms: \[([^]]*)\]', audit)
    count = (ROOT / 'test/CoreAxioms.lean').read_text().count('#print axioms')
    if len(groups) != count or any(set(filter(None, map(str.strip, g.split(',')))) -
                                  {'propext', 'Classical.choice', 'Quot.sound'} for g in groups):
        raise RuntimeError('Incomplete axiom audit or nonstandard assumptions')
    print(run([*lean, '--run', 'test/Core.lean'], 'lean-emit.log').strip(), flush=True)
    coverage = runpy.run_path(str(ROOT/'scripts/core-vectors.py'))['generate']()
    print(f"Checking {coverage['edges']} edges against independent deadlines and protocol contracts", flush=True)
    print(run([*lean, '--run', 'test/Core.lean', 'check'], 'lean-check.log').strip(), flush=True)
    for name in ['decoder', 'core']:
        # HW legalization is required to honor unsupported packed-array lowering options.
        rtl = run([circt, f'build/core/{name}.mlir', '--canonicalize', '--lower-seq-to-sv',
                   '--lower-hw-to-sv', '--hw-legalize-modules', '--export-verilog', '-o', '/dev/null'],
                  f'{name}-export.log')
        (OUT / f'{name}.sv').write_text(rtl)

    def simulate(name, source, top, reject=None):
        run([suite/'iverilog', '-g2012', f"-DIMAGE_COUNT={coverage['images']}", '-s', f'{top}_tb',
             '-o', f'build/core/{name}.vvp', source, f'test/{top}_tb.sv'], f'{name}-compile.log')
        return run([suite/'vvp', f'build/core/{name}.vvp', f'+trace=build/core/{name}.csv'], f'{name}.log', reject)

    print(simulate('decoder', 'build/core/decoder.sv', 'decoder').strip(), flush=True)
    print(simulate('rtl', 'build/core/core.sv', 'core').strip(), flush=True)
    if (OUT/'lean.csv').read_bytes() != (OUT/'rtl.csv').read_bytes():
        raise RuntimeError('Lean/RTL trace mismatch')
    rtl = (OUT/'core.sv').read_text()
    header, body = rtl.split(');', 1)
    delayed = header + ');\n  reg sample_delayed;\n  always @(posedge clk) sample_delayed <= sample;\n' + re.sub(r'\bsample\b', 'sample_delayed', body)
    if rtl.count("r_pc + 5'h1") != 1:
        raise RuntimeError('Review address fixture after CIRCT output change')
    wrap, substitutions = re.subn(r'(wire\s+\w+\s*=\s*)&r_pc;', r"\g<1>1'b0;", rtl)
    if substitutions != 1:
        raise RuntimeError('Review wrap fixture after CIRCT output change')
    mutants = {
        'late-capture': (delayed, 'CAPTURE cycle'),
        'skip-address': (rtl.replace("r_pc + 5'h1", "r_pc + 5'h2"), 'ADDRESS cycle'),
        'wrap-at-31': (wrap, 'STATE cycle'),
    }
    for name, (text, failure) in mutants.items():
        (OUT/f'{name}.sv').write_text(text)
        simulate(name, f'build/core/{name}.sv', 'core', reject=failure)
    print('Rejected late capture, skipped address, and slot-31 wrap RTL fixtures', flush=True)

    script = '\n'.join([
        'read_verilog -sv build/core/core.sv', 'hierarchy -check -top pinwheel_core',
        'synth -top pinwheel_core', 'check -assert', 'stat',
        'write_json build/core/netlist.json', 'write_verilog -noattr build/core/netlist.v', ''])
    (OUT/'synthesis.ys').write_text(script)
    run([suite/'yosys', '-Q', '-T', '-s', 'build/core/synthesis.ys'], 'synthesis.log')
    cells = json.loads((OUT/'netlist.json').read_text())['modules']['pinwheel_core']['cells']
    histogram = dict(sorted(collections.Counter(c['type'] for c in cells.values()).items()))
    versions = {name: run([binary, flag], f'{name}-version.log').strip() for name, binary, flag in [
        ('circt', circt, '--version'), ('yosys', suite/'yosys', '-V'), ('iverilog', suite/'iverilog', '-V')]}
    artifacts = sorted([str(p.relative_to(ROOT)) for p in (ROOT/'Pinwheel').rglob('*.lean')]) + [
        'Pinwheel.lean', 'test/Core.lean', 'test/CoreAxioms.lean', 'test/core_tb.sv', 'test/decoder_tb.sv',
        'scripts/check-core.py', 'scripts/core-vectors.py', 'tools/hardware-toolchain.json', 'lean-toolchain',
        'build/core/core.mlir', 'build/core/decoder.mlir', 'build/core/core.sv', 'build/core/decoder.sv',
        'build/core/images.txt', 'build/core/images.hex', 'build/core/stimuli.txt', 'build/core/lean.csv',
        'build/core/rtl.csv', 'build/core/netlist.json', 'build/core/netlist.v', 'build/core/axioms.log',
        'build/core/coverage.json', 'build/core/synthesis.ys']
    report = dict(host=f'{platform.system()} {platform.machine()}', versions=versions, toolchain=manifest,
                  coverage=coverage, standard_axioms_only=True, audited_theorems=count, traces_identical=True,
                  negative_fixtures_rejected=list(mutants), generic_cells=histogram,
                  total_generic_cells=sum(histogram.values()),
                  flip_flop_bits=sum(n for kind,n in histogram.items() if 'DFF' in kind),
                  sha256={p: hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in artifacts},
                  boundary='Exact Lean circuit refinement; sampled RTL validation; generic synthesis. No emitter proof, gate equivalence, physical loading transport, technology area, or timing result.')
    (OUT/'report.json').write_text(json.dumps(report, indent=2)+'\n')
    print(f"Synthesized {report['total_generic_cells']} generic cells, including {report['flip_flop_bits']} flip-flop bits. See build/core/report.json.")


if __name__ == '__main__':
    main()
