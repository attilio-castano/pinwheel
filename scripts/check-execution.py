#!/usr/bin/env python3
"""Audit E64 proofs, compare independent Lean/RTL traces, and synthesize equal-interface stores."""
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
OUT = ROOT / 'build/execution'


def run(args, log, reject=None):
    result = subprocess.run([str(x) for x in args], cwd=ROOT, text=True, capture_output=True)
    output = result.stdout + result.stderr
    (OUT / log).write_text(output)
    if reject:
        if result.returncode == 0 or 'FATAL:' not in output or reject not in output:
            raise RuntimeError(f'Mutation was not rejected for {reject}:\n{output}')
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
        raise SystemExit('Install the pinned Lean and hardware tools; see docs/development.md')
    if not all((ROOT / f'build/binary/i2c-{kind}.pwl').is_file() for kind in ['explicit', 'counted']):
        raise SystemExit('Run scripts/check-binary.py first to produce native V0 image fixtures')
    run([lake, 'build'], 'lean-build.log')
    lean = [lake, 'env', 'lean', '-DwarningAsError=true']
    expected = sorted('Pinwheel.Hardware.Execution.' + name
                      for p in (ROOT / 'Pinwheel/Hardware/Execution').glob('*.lean')
                      for name in re.findall(r'^theorem (\w+)', p.read_text(), re.M))
    audit_source = (ROOT / 'test/ExecutionAxioms.lean').read_text()
    if sorted(re.findall(r'^#print axioms (\S+)', audit_source, re.M)) != expected:
        raise RuntimeError('Audit must cover every public execution theorem')
    audit = run([*lean, 'test/ExecutionAxioms.lean'], 'axioms.log')
    entries = re.findall(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)", audit)
    if sorted(n for n, _ in entries) != expected:
        raise RuntimeError('Incomplete audit')
    for name, axioms in entries:
        if set(filter(None, map(str.strip, axioms.split(',')))) - {'propext', 'Classical.choice', 'Quot.sound'}:
            raise RuntimeError(f'Unapproved proof assumptions: {name}')
    print(run([*lean, '--run', 'test/Execution.lean'], 'lean-emit.log').strip(), flush=True)
    coverage = runpy.run_path(str(ROOT / 'scripts/execution-vectors.py'))['generate']()
    print(run([*lean, '--run', 'test/Execution.lean', 'check'], 'lean-check.log').strip(), flush=True)
    for name in ['decoder', 'direct', 'indexed']:
        rtl = run([circt, f'build/execution/{name}.mlir', '--canonicalize', '--lower-seq-to-sv',
                   '--lower-hw-to-sv', '--hw-legalize-modules', '--export-verilog', '-o', '/dev/null'],
                  f'{name}-export.log')
        (OUT / f'{name}.sv').write_text(rtl)

    def simulate(name, source, kind, reject=None):
        top = 'execution_decoder_tb' if kind == 'decoder' else 'execution_store_tb'
        flags = ['-DINDEXED'] if kind == 'indexed' else []
        run([suite/'iverilog', '-g2012', *flags, '-s', top, '-o', f'build/execution/{name}.vvp',
             source, f'test/{top}.sv'], f'{name}-compile.log')
        return run([suite/'vvp', f'build/execution/{name}.vvp', f'+trace=build/execution/{name}.csv'],
                   f'{name}.log', reject)

    for name in ['decoder', 'direct', 'indexed']:
        print(simulate(name + '-rtl', f'build/execution/{name}.sv', name).strip(), flush=True)
        if name != 'decoder' and (OUT/f'{name}-lean.csv').read_bytes() != (OUT/f'{name}-rtl.csv').read_bytes():
            raise RuntimeError(f'{name} Lean/RTL trace mismatch')
    mutants = []
    for kind in ['direct', 'indexed']:
        source = (OUT/f'{kind}.sv').read_text()
        if source.count('~busy') != 1:
            raise RuntimeError('Review busy mutation after CIRCT output change')
        bad_address, count = re.subn(r'\bread_a\[0\]', '~read_a[0]', source)
        if not count:
            raise RuntimeError('Review address mutation after CIRCT output change')
        for fault, text in [('busy-write', source.replace('~busy', "1'b1")), ('address-bit', bad_address)]:
            name = f'{kind}-{fault}'
            (OUT/f'{name}.sv').write_text(text)
            simulate(name, f'build/execution/{name}.sv', kind, 'STORE edge')
            mutants.append(name)
    source = (OUT/'decoder.sv').read_text()
    header, body = source.split(');', 1)
    source = header + ");\nwire [63:0] unreserved = {1'b0, word[62:0]};\n" + re.sub(r'\bword\b', 'unreserved', body)
    (OUT/'decoder-reserved.sv').write_text(source)
    simulate('decoder-reserved', 'build/execution/decoder-reserved.sv', 'decoder', 'DECODE vector')
    mutants.append('decoder-reserved')
    print(f'Rejected {len(mutants)} RTL mutations for decoder, addressing, and busy writes.', flush=True)

    metrics = {}
    for name in ['decoder', 'direct', 'indexed']:
        top = 'pinwheel_e64_' + name
        script = '\n'.join([
            f'read_verilog -sv build/execution/{name}.sv', f'hierarchy -check -top {top}',
            f'synth -top {top}', 'check -assert', 'stat', 'ltp -noff',
            f'write_json build/execution/{name}-netlist.json',
            f'write_verilog -noattr build/execution/{name}-netlist.v', ''])
        (OUT/f'{name}-synthesis.ys').write_text(script)
        log = run([suite/'yosys', '-Q', '-T', '-s', f'build/execution/{name}-synthesis.ys'], f'{name}-synthesis.log')
        cells = json.loads((OUT/f'{name}-netlist.json').read_text())['modules'][top]['cells']
        histogram = dict(sorted(collections.Counter(c['type'] for c in cells.values()).items()))
        path = re.search(r'longest topological path.*?length[ =]+(\d+)', log, re.I)
        if not path:
            raise RuntimeError('Missing topological path measurement')
        ff = sum(n for kind, n in histogram.items() if 'DFF' in kind)
        if ff != {'decoder': 0, 'direct': 16384, 'indexed': 5632}[name]:
            raise RuntimeError(f'{name} lost writable storage: {ff}')
        metrics[name] = dict(total_generic_cells=sum(histogram.values()), flip_flop_bits=ff,
                             combinational_cells=sum(histogram.values())-ff,
                             longest_topological_path_cells=int(path[1]), generic_cells=histogram)
        print(f'{name}: {metrics[name]}', flush=True)

    packed_reads = {}
    for name in ['direct', 'indexed']:
        print(run([*lean, '--run', 'test/I2CRead.lean', name], f'{name}-read.log').strip(), flush=True)
        packed_reads[name] = dict((k, int(v)) for k, v in
                                 (line.split('=') for line in (OUT/f'{name}-read-coverage.txt').read_text().splitlines()))
    versions = {name: run([binary, flag], f'{name}-version.log').strip() for name, binary, flag in [
        ('circt', circt, '--version'), ('yosys', suite/'yosys', '-V'), ('iverilog', suite/'iverilog', '-V')]}
    sources = sorted((ROOT/'Pinwheel').rglob('*.lean')) + [ROOT / p for p in [
        'Pinwheel.lean', 'test/Execution.lean', 'test/ExecutionAxioms.lean', 'test/I2CRead.lean',
        'test/execution_decoder_tb.sv', 'test/execution_store_tb.sv', 'scripts/check-execution.py',
        'scripts/execution-vectors.py', 'tools/hardware-toolchain.json', 'lean-toolchain',
        'lakefile.toml', 'lake-manifest.json']]
    artifacts = sorted(p for p in OUT.iterdir() if p.is_file() and p.name != 'report.json') + [
        ROOT/'build/binary/i2c-explicit.pwl', ROOT/'build/binary/i2c-counted.pwl']
    report = dict(host=f'{platform.system()} {platform.machine()}', versions=versions, toolchain=manifest,
                  audited_theorems=len(expected), standard_axioms_only=True, coverage=coverage,
                  traces_identical=True, negative_fixtures_rejected=mutants, synthesis=metrics,
                  packed_read_coverage=packed_reads,
                  sha256={str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in sources+artifacts},
                  boundary='Universal Lean record/lookup/write/refinement proofs; sampled generated-RTL validation; '
                           'generic register-store synthesis with two combinational read ports. No emitter proof, '
                           'gate equivalence, technology area/delay, full reactive RTL scheduler, atomic physical '
                           'loader, or electrical compliance. Indexed capacity is at most 64 distinct records.')
    (OUT/'report.json').write_text(json.dumps(report, indent=2)+'\n')
    print(f'Audited {len(expected)} execution theorems. See build/execution/report.json.')


if __name__ == '__main__':
    main()
