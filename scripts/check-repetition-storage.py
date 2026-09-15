#!/usr/bin/env python3
"""Bounded repetition prototype: certified images, structural Lean/RTL traces and mapped cost."""
import hashlib
import json
import re
import shutil
import subprocess
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
OUT=ROOT/'build/storage/repetition'

def main():
    OUT.mkdir(parents=True,exist_ok=True)
    (OUT/'checked-report.json').unlink(missing_ok=True)
    def run(args,name,reject=False):
        r=subprocess.run(list(map(str,args)),cwd=ROOT,text=True,capture_output=True)
        (OUT/name).write_text(r.stdout+r.stderr)
        if reject: assert r.returncode and 'LOADER edge' in r.stdout,r.stdout+r.stderr
        elif r.returncode: raise RuntimeError(r.stdout+r.stderr)
        return r.stdout+r.stderr
    lake=shutil.which('lake'); suite=ROOT/'build/tools/oss-cad-suite/bin'
    run([lake,'build','Pinwheel.Hardware.Storage.RepetitionEmit'],'build.log')
    expected=[]
    for p in sorted((ROOT/'Pinwheel/Hardware/Storage').glob('*.lean')):
        s=p.read_text(); ns=re.search(r'^namespace (\S+)',s,re.M)[1]
        expected += [ns+'.'+n for n in re.findall(r'^theorem (\w+)',s,re.M)]
    (OUT/'Axioms.lean').write_text('import Pinwheel.Hardware.Storage.RepetitionEmit\n'+''.join('#print axioms '+n+'\n' for n in expected))
    audit=run([lake,'env','lean','-DwarningAsError=true',OUT/'Axioms.lean'],'axioms.log')
    entries=re.findall(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)",audit)
    assert sorted(n for n,_ in entries)==sorted(expected)
    for n,a in entries: assert not set(filter(None,map(str.strip,a.split(','))))-{'propext','Classical.choice','Quot.sound'},(n,a)
    print('Audited',len(entries),'storage theorems.',flush=True)
    print(run([lake,'env','lean','-DwarningAsError=true','--run','test/StorageRepetition.lean'],'matrix.log').strip(),flush=True)
    run([lake,'env','lean','-DwarningAsError=true','--run','test/StorageRepetitionEmit.lean'],'emit.log')
    print(run(['python3','scripts/repetition-vectors.py'],'vectors.log').strip(),flush=True)
    print(run([lake,'env','lean','-DwarningAsError=true','--run','test/StorageRepetitionCheck.lean'],'lean-check.log').strip(),flush=True)
    print(run(['python3','scripts/measure-storage-variant.py','repetition','--ff','2163'],'measure.log').strip(),flush=True)
    rtl=(OUT/'design.sv').read_text(); mutants={}
    for idx in [1,2,3]:
        pattern=rf'(wire \[7:0\]\s+chosen_descriptor{idx}\s*=)([^;]+);'
        mutated,n=re.subn(pattern,lambda m:m[1]+' ('+m[2]+") ^ 8'h01;",rtl)
        assert n==1,n; mutants[f'descriptor{idx}']=mutated
    a,b=rtl.split('  always_ff @(posedge clk)',1)
    mutants['byte-selection']=a.replace('r_bank1_byte1 : r_bank0_byte1','r_bank1_byte0 : r_bank0_byte0')+'  always_ff @(posedge clk)'+b
    assert mutants['byte-selection']!=rtl
    for name,source in mutants.items():
        (OUT/(name+'.sv')).write_text(source)
        run([suite/'iverilog','-g2012','-s','loader_tb','-o',OUT/(name+'.vvp'),OUT/(name+'.sv'),OUT/'tb.sv'],name+'-compile.log')
        run([suite/'vvp',OUT/(name+'.vvp')],name+'.log',True)
    print('Rejected the held-cache mutant and four repetition-specific mutants.',flush=True)
    sources=sorted((ROOT/'Pinwheel').rglob('*.lean'))+[ROOT/p for p in ['scripts/check-repetition-storage.py','scripts/repetition-vectors.py','scripts/measure-storage-variant.py','test/StorageRepetition.lean','test/StorageRepetitionEmit.lean','test/StorageRepetitionCheck.lean','test/loader_tb.sv','scripts/loader-vectors.py','scripts/reactive-core-vectors.py','tools/hardware-toolchain.json','tools/technology-library.json','lean-toolchain']]
    report=dict(audited_theorems=expected,certified=json.loads((OUT/'capacity.json').read_text()),coverage=json.loads((OUT/'coverage.json').read_text()),metrics=json.loads((OUT/'report.json').read_text())['metrics'],mutants_rejected=5,source_sha256={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sources},rtl_sha256=hashlib.sha256(rtl.encode()).hexdigest(),boundary='Bounded two-byte I2C-write backend. Kernel-proved structural reader/store and certified lookup/run equality; independent checks cover complete emitted atomic host/core integration. Not a general counted compiler or proof of RTL translation/physical timing.')
    (OUT/'checked-report.json').write_text(json.dumps(report,indent=2)+'\n')
if __name__=='__main__':main()
