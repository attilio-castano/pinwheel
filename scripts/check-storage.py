#!/usr/bin/env python3
"""Isolated storage candidates: independent host traces, axiom audit, CMOS5L mapping."""
import hashlib
import json
import re
import runpy
import shutil
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT/'build/storage'

def run(args, name):
    r = subprocess.run(list(map(str, args)), cwd=ROOT, text=True, capture_output=True)
    (OUT/name).write_text(r.stdout+r.stderr)
    if r.returncode: raise RuntimeError(f'{args}\n{r.stdout}{r.stderr}')
    return r.stdout+r.stderr

def main():
    OUT.mkdir(parents=True, exist_ok=True)
    (OUT/'report.json').unlink(missing_ok=True)
    lake = shutil.which('lake')
    suite = ROOT/'build/tools/oss-cad-suite/bin'
    circt = ROOT/'build/tools/firtool-1.159.0/bin/circt-opt'
    run([lake, 'build', 'Pinwheel.Hardware.Storage.DenseEmit'], 'build.log')
    paths = sorted((ROOT/'Pinwheel/Hardware/Storage').glob('*.lean'))
    expected = []
    for p in paths:
        ns = re.search(r'^namespace (\S+)', p.read_text(), re.M)[1]
        expected += [ns+'.'+n for n in re.findall(r'^theorem (\w+)', p.read_text(), re.M)]
    audit_file = OUT/'Axioms.lean'
    audit_file.write_text('import Pinwheel.Hardware.Storage.DenseEmit\n'+''.join(f'#print axioms {n}\n' for n in expected))
    audit = run([lake, 'env', 'lean', '-DwarningAsError=true', audit_file], 'axioms.log')
    entries = re.findall(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)", audit)
    assert sorted(n for n, _ in entries) == sorted(expected)
    assert all(not set(filter(None, map(str.strip, a.split(',')))) - {'propext', 'Classical.choice', 'Quot.sound'} for _, a in entries)
    run([lake, 'env', 'lean', '--run', 'test/Storage.lean'], 'emit.log')
    # Reuse the independent oracle, preserving its protocol and interruption suite.
    ns = runpy.run_path(str(ROOT/'scripts/loader-vectors.py'))
    class Small(ns['Atomic']):
        def __init__(self):
            super().__init__()
            for image in self.images: image[32:64] = [4]*32
        def edge(self, init=0, reset=0, command=0, data=0, incoming=0):
            fits = self.cursor < 32 or (data == 4 if self.cursor < 64 else data < 32 if self.cursor < 320 else True)
            super().edge(init, reset, 6 if command == 2 and not fits else command, data, incoming)
            self.rows[-1][2] = command
    env = ns['generate'].__globals__
    env['Atomic'], env['OUT'] = Small, OUT
    shutil.copyfile(ROOT/'build/loader/images.txt', OUT/'images.txt')
    coverage = ns['generate']()
    # Deliberately valid E64 records exceeding the physical capacity must be rejected.
    m = Small()
    m.edge(init=1); m.edge(command=1)
    for _ in range(32): m.edge(command=2, data=4)
    m.edge(command=2, data=0); assert m.gates == [0, 0, 0, 1] and m.cursor == 32
    for _ in range(32): m.edge(command=2, data=4)
    m.edge(command=2, data=32); assert m.gates == [0, 0, 0, 1] and m.cursor == 64
    # Begin this extension with a full overwrite, so the physical observation scoreboard agrees.
    # Existing bank data are intentionally retained across init; no zero-initialization assumption.
    with (OUT/'vectors.txt').open('a') as f:
        f.write(''.join(' '.join(map(str, row))+'\n' for row in m.rows))
    coverage['edges'] += len(m.rows)
    coverage['capacity_rejections'] = 2
    observe = (OUT/'memory-observe.svh').read_text()
    for b in range(2):
        for k in range(32, 64): observe = observe.replace(f'dut.r_bank{b}_word{k};', "64'd4;")
    (OUT/'memory-observe.svh').write_text(observe)
    tb = (ROOT/'test/loader_tb.sv').read_text().replace('pinwheel_atomic_indexed', 'pinwheel_atomic_small').replace('build/loader/', 'build/storage/')
    (OUT/'tb.sv').write_text(tb)
    rtl = run([circt, OUT/'small.mlir', '--canonicalize', '--lower-seq-to-sv', '--lower-hw-to-sv', '--hw-legalize-modules', '--export-verilog', '-o', '/dev/null'], 'export.log')
    (OUT/'small.sv').write_text(rtl)
    run([suite/'iverilog', '-g2012', '-s', 'loader_tb', '-o', OUT/'small.vvp', OUT/'small.sv', OUT/'tb.sv'], 'compile.log')
    print(run([suite/'vvp', OUT/'small.vvp'], 'simulation.log').strip(), flush=True)
    lm = json.loads((ROOT/'tools/technology-library.json').read_text())
    for item in lm['files']:
        assert hashlib.sha256((ROOT/'build/tools/ihp-cmos5l'/item['name']).read_bytes()).hexdigest() == item['sha256']
    (OUT/'abc.constr').write_text('set_driving_cell sg13cmos5l_buf_2\nset_load 10\n')
    metrics = {}
    for corner, libname in [('typical', 'sg13cmos5l_stdcell_typ_1p20V_25C.lib'), ('slow', 'sg13cmos5l_stdcell_slow_1p08V_125C.lib')]:
        lib = ROOT/'build/tools/ihp-cmos5l'/libname
        top = 'pinwheel_atomic_small'
        ys = '\n'.join([f'read_verilog -sv {OUT}/small.sv', f'hierarchy -check -top {top}', f'synth -top {top} -noabc', f'dfflibmap -liberty {lib}', f'abc -liberty {lib} -constr {OUT}/abc.constr -D 10000', f'read_liberty -lib {lib}', 'clean', 'check -assert', f'stat -liberty {lib}', f'write_json {OUT}/{corner}-netlist.json', ''])
        (OUT/f'{corner}.ys').write_text(ys)
        log = run([suite/'yosys', '-Q', '-T', '-s', OUT/f'{corner}.ys'], f'{corner}.log')
        cells = json.loads((OUT/f'{corner}-netlist.json').read_text())['modules'][top]['cells']
        ff = sum(c['type'].startswith('sg13cmos5l_df') for c in cells.values())
        assert ff == 6745, ff
        metrics[corner] = dict(standard_cell_area_um2=float(re.findall(r'Chip area for module.*?:\s*([\d.]+)', log)[-1]), sequential_area_um2=float(re.findall(r'of which used for sequential elements:\s*([\d.]+)', log)[-1]), abc_combinational_delay_ps=float(re.findall(r'ABC(?: RESULTS)?:.*?Delay\s*=\s*([\d.]+)', log)[-1]), flip_flops=ff, cells=len(cells))
        print(corner, metrics[corner], flush=True)
    sources = sorted((ROOT/'Pinwheel').rglob('*.lean')) + [ROOT/'scripts/check-storage.py', ROOT/'test/Storage.lean', ROOT/'test/StorageCapacity.lean', ROOT/'scripts/loader-vectors.py', ROOT/'scripts/reactive-core-vectors.py', ROOT/'test/loader_tb.sv', ROOT/'tools/technology-library.json', ROOT/'tools/hardware-toolchain.json', ROOT/'lean-toolchain']
    report = dict(metrics=metrics, coverage=coverage, audited_theorems=expected, source_sha256={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sources}, rtl_sha256=hashlib.sha256(rtl.encode()).hexdigest(), boundary='32-entry experimental capacity; same 256 addresses and 322-word host transfer. Mapped cell area and ABC combinational delay only; no routed fit or STA claim.')
    (OUT/'report.json').write_text(json.dumps(report, indent=2)+'\n')

if __name__ == '__main__': main()
