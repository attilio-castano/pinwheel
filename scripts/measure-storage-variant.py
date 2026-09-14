#!/usr/bin/env python3
"""Map a previously emitted storage candidate and check it against atomic traces."""
import argparse
import hashlib
import json
import re
import runpy
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT/'build/storage'

def main():
    p = argparse.ArgumentParser()
    p.add_argument('name', choices=['cached', 'dense', 'small-dense', 'small-cached', 'small-dense-cached', 'repetition'])
    p.add_argument('--ff', type=int, required=True)
    a = p.parse_args()
    out = BASE/a.name
    out.mkdir(parents=True, exist_ok=True)
    (out/'report.json').unlink(missing_ok=True)
    def run(args, label):
        r = subprocess.run(list(map(str,args)), cwd=ROOT, text=True, capture_output=True)
        (out/label).write_text(r.stdout+r.stderr)
        if r.returncode: raise RuntimeError(f'{args}\n{r.stdout}{r.stderr}')
        return r.stdout+r.stderr
    top = 'pinwheel_atomic_'+a.name.replace('-', '_')
    circt = ROOT/'build/tools/firtool-1.159.0/bin/circt-opt'
    suite = ROOT/'build/tools/oss-cad-suite/bin'
    rtl = run([circt, BASE/(a.name+'.mlir'), '--canonicalize', '--lower-seq-to-sv', '--lower-hw-to-sv', '--hw-legalize-modules', '--export-verilog', '-o', '/dev/null'], 'export.log')
    (out/'design.sv').write_text(rtl)
    if a.name == 'repetition':
        tb=(out/'runtime_tb.sv').read_text()
        vectors=(out/'vectors.txt').read_text()
    else:
        ns = runpy.run_path(str(ROOT/'scripts/loader-vectors.py'))
        class Small(ns['Atomic']):
            def __init__(self):
                super().__init__()
                for image in self.images: image[32:64] = [4]*32
            def edge(self, init=0, reset=0, command=0, data=0, incoming=0):
                fits = self.cursor < 32 or (data == 4 if self.cursor < 64 else data < 32 if self.cursor < 320 else True)
                super().edge(init, reset, 6 if command == 2 and not fits else command, data, incoming)
                self.rows[-1][2] = command
        m, pack = (Small() if 'small' in a.name else ns['Atomic']()), ns['pack']
        m.edge(init=1)
        m.load('consecutive-one-cycle', [pack(dict(kind=0,levels=k,enabled=7)) for k in range(6)]+[4], 6)
        m.edge(command=5)
        for _ in range(7): m.edge()
        m.load('self-branch', [pack(dict(kind=2,finish=1,yes=0))], 0)
        m.edge(command=5)
        for _ in range(8):
            m.edge(incoming=3)
            assert m.s[0] == 3 and m.s[1] == 0
        m.edge(reset=1)
        words = [pack(dict(kind=2,terminal=63,finish=2,sample=15,yes=1,no=2)), pack(dict(kind=0,levels=5,enabled=7,entry=61)), 4]
        m.load('terminal-capture-branch-overwrite', words, 2)
        for incoming in [0,2]:
            m.edge(command=5); m.edge(incoming=incoming)
            if incoming: assert m.s[1] == 1 and m.s[6] == 0 and m.s[4] == 5
            else: assert m.s[0] == 5
            m.edge(); m.edge(reset=1)
        if 'small' in a.name:
            m.edge(command=1)
            for _ in range(32): m.edge(command=2, data=4)
            m.edge(command=2, data=0); assert m.gates == [0,0,0,1] and m.cursor == 32
            for _ in range(32): m.edge(command=2, data=4)
            m.edge(command=2, data=32); assert m.gates == [0,0,0,1] and m.cursor == 64
        else:
            m.load('full-capacity-retained', [pack(dict(kind=0,duration=k)) for k in range(33)]+[4], 33)
        vectors = (ROOT/'build/loader/vectors.txt').read_text()+''.join(' '.join(map(str,row))+'\n' for row in m.rows)
        (out/'vectors.txt').write_text(vectors)
        tb = (ROOT/'test/loader_tb.sv').read_text().replace('pinwheel_atomic_indexed', top)
        tb = tb.replace('build/loader/vectors.txt', str((out/'vectors.txt').relative_to(ROOT)))
        # These vectors only load <=32 distinct words, with canonical halt padding.
        # Capacity rejection coverage remains a separate test of the small-store gate.
        observe = (ROOT/'build/loader/memory-observe.svh').read_text()
        if 'small' in a.name:
            for b in range(2):
                for k in range(32,64): observe = observe.replace(f'dut.r_bank{b}_word{k};', "64'd4;")
        if 'dense' in a.name:
            # Independent inverse of the physical field overlay for storage observations.
            tb = tb.replace('  reg [63:0] expected', '''  function [63:0] expand55(input [54:0] w);
        expand55 = w[2:0] == 3 ? {35'd0,w[28:17],w[16:0]} : {1'b0,w[54:17],8'd0,w[16:0]};
      endfunction
      reg [63:0] expected''')
            observe = re.sub(r'(dut\.r_bank[01]_word\d+)', r'expand55(\1)', observe)
        if 'cached' in a.name:
            tb = tb.replace('      for (k = 0;', '''      if (busy && dut.r_cached_word !== observed[(loader_active ? 322 : 0) + observed[(loader_active ? 322 : 0) + 64 + pc]])
            $fatal(1, "LOADER edge %0d cached word invariant", count);
          for (k = 0;''')
        (out/'observe.svh').write_text(observe)
        tb = tb.replace('build/loader/memory-observe.svh', str((out/'observe.svh').relative_to(ROOT)))
    (out/'tb.sv').write_text(tb)
    run([suite/'iverilog', '-g2012', '-s', 'loader_tb', '-o', out/'sim.vvp', out/'design.sv', out/'tb.sv'], 'compile.log')
    simulation = run([suite/'vvp', out/'sim.vvp'], 'simulation.log')
    print(a.name, simulation.strip(), flush=True)
    # A held cache must be distinguishable from the correct update on these traces.
    if 'cached' in a.name or a.name == 'repetition':
        bad = re.sub(r'(r_cached_word\s*<=)[^;]+;', lambda m: m[1]+" 64'd4;", rtl)
        if bad == rtl: raise RuntimeError('Cache mutation anchor changed')
        (out/'mutant.sv').write_text(bad)
        run([suite/'iverilog', '-g2012', '-s', 'loader_tb', '-o', out/'mutant.vvp', out/'mutant.sv', out/'tb.sv'], 'mutant-compile.log')
        r = subprocess.run([str(suite/'vvp'), str(out/'mutant.vvp')], cwd=ROOT, text=True, capture_output=True)
        (out/'mutant.log').write_text(r.stdout+r.stderr)
        assert r.returncode and 'LOADER edge' in r.stdout, r.stdout+r.stderr
    lm = json.loads((ROOT/'tools/technology-library.json').read_text())
    for item in lm['files']:
        assert hashlib.sha256((ROOT/'build/tools/ihp-cmos5l'/item['name']).read_bytes()).hexdigest() == item['sha256']
    (out/'abc.constr').write_text('set_driving_cell sg13cmos5l_buf_2\nset_load 10\n')
    metrics = {}
    for corner, libname in [('typical','sg13cmos5l_stdcell_typ_1p20V_25C.lib'), ('slow','sg13cmos5l_stdcell_slow_1p08V_125C.lib')]:
        lib = ROOT/'build/tools/ihp-cmos5l'/libname
        script = '\n'.join([f'read_verilog -sv {out}/design.sv', f'hierarchy -check -top {top}', f'synth -top {top} -noabc', f'dfflibmap -liberty {lib}', f'abc -liberty {lib} -constr {out}/abc.constr -D 10000', f'read_liberty -lib {lib}', 'clean', 'check -assert', f'stat -liberty {lib}', f'write_json {out}/{corner}.json', ''])
        (out/f'{corner}.ys').write_text(script)
        log = run([suite/'yosys','-Q','-T','-s',out/f'{corner}.ys'], f'{corner}.log')
        cells = json.loads((out/f'{corner}.json').read_text())['modules'][top]['cells']
        ff = sum(c['type'].startswith('sg13cmos5l_df') for c in cells.values())
        assert ff == a.ff, ff
        metrics[corner] = dict(standard_cell_area_um2=float(re.findall(r'Chip area for module.*?:\s*([\d.]+)', log)[-1]), abc_combinational_delay_ps=float(re.findall(r'ABC(?: RESULTS)?:.*?Delay\s*=\s*([\d.]+)', log)[-1]), flip_flops=ff, cells=len(cells))
        print(a.name, corner, metrics[corner], flush=True)
    sources = sorted((ROOT/'Pinwheel').rglob('*.lean')) + [Path(__file__).resolve(), ROOT/'test/loader_tb.sv', ROOT/'test/Storage.lean', ROOT/'test/StorageCache.lean', ROOT/'test/StorageCacheAxioms.lean', ROOT/'test/StorageRepetition.lean', ROOT/'test/StorageRepetitionEmit.lean', ROOT/'scripts/repetition-vectors.py', ROOT/'scripts/loader-vectors.py', ROOT/'scripts/reactive-core-vectors.py', ROOT/'tools/technology-library.json', ROOT/'tools/hardware-toolchain.json', ROOT/'lean-toolchain']
    report = dict(metrics=metrics, simulation=simulation, rtl_sha256=hashlib.sha256(rtl.encode()).hexdigest(), vectors_sha256=hashlib.sha256(vectors.encode()).hexdigest(), source_sha256={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sources}, boundary='Independent RTL traces and separately mapped CMOS5L corners. No full STA or physical fit claim. Proof audit is separate.')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')

if __name__ == '__main__': main()
