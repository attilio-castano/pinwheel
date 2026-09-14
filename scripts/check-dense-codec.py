#!/usr/bin/env python3
"""Independent bit-position oracle for the 55-bit codec, including raw invalid inputs."""
import hashlib
import json
import random
import re
import shutil
import subprocess
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
OUT=ROOT/'build/storage'

def main():
    def run(args,name,reject=False):
        r=subprocess.run(list(map(str,args)),cwd=ROOT,text=True,capture_output=True)
        (OUT/name).write_text(r.stdout+r.stderr)
        if reject: assert r.returncode and 'CODEC' in r.stdout, r.stdout+r.stderr
        elif r.returncode: raise RuntimeError(r.stdout+r.stderr)
        return r.stdout+r.stderr
    def compress(w): return ((w>>17 & 4095) if w & 7 == 3 else (w>>25 & ((1<<38)-1)))<<17 | (w & ((1<<17)-1))
    def expand(w): return ((w & ((1<<29)-1)) if w & 7 == 3 else ((w>>17)<<25 | (w & ((1<<17)-1))))
    rng=random.Random(550064)
    vectors=[]; valid=0
    for line in (ROOT/'build/execution/decoder-vectors.txt').read_text().splitlines():
        w,v,_=map(int,line.split()); d=compress(w)
        if v: assert expand(d)==w; valid+=1
        vectors.append([w,d,d,expand(d)])
    for _ in range(4096):
        w,d=rng.getrandbits(64),rng.getrandbits(55)
        vectors.append([w,d,compress(w),expand(d)])
    (OUT/'codec-vectors.txt').write_text(''.join(' '.join(map(str,row))+'\n' for row in vectors))
    lake=shutil.which('lake')
    run([lake,'build','Pinwheel.Hardware.Storage.DenseEmit'],'dense-build.log')
    print(run([lake,'env','lean','-DwarningAsError=true','--run','test/StorageDense.lean'],'dense-lean.log').strip(),flush=True)
    suite=ROOT/'build/tools/oss-cad-suite/bin'
    rtl=run([ROOT/'build/tools/firtool-1.159.0/bin/circt-opt',OUT/'codec.mlir','--canonicalize','--lower-seq-to-sv','--lower-hw-to-sv','--hw-legalize-modules','--export-verilog','-o','/dev/null'],'codec-export.log')
    (OUT/'codec.sv').write_text(rtl)
    tb='''module codec_tb;
reg clk=0; reg[63:0] word; reg[54:0] dense; wire[54:0] compressed; wire[63:0] expanded;
reg[54:0] ep; reg[63:0] ee; integer file,status,count=0;
pinwheel_dense_codec dut(.*);
initial begin
file=$fopen("build/storage/codec-vectors.txt","r");
if(!file) $fatal(1,"missing CODEC vectors");
while(!$feof(file)) begin
status=$fscanf(file,"%d %d %d %d\\n",word,dense,ep,ee); #1;
if(status!=4 || compressed!==ep || expanded!==ee) $fatal(1,"CODEC vector %0d",count);
count=count+1;
end
$display("Passed %0d dense codec vectors",count); $finish;
end
endmodule
'''
    (OUT/'codec_tb.sv').write_text(tb)
    def sim(rtlfile,name,reject=False):
        run([suite/'iverilog','-g2012','-s','codec_tb','-o',OUT/(name+'.vvp'),rtlfile,OUT/'codec_tb.sv'],name+'-compile.log')
        return run([suite/'vvp',OUT/(name+'.vvp')],name+'.log',reject)
    print(sim(OUT/'codec.sv','codec').strip(),flush=True)
    header,body=rtl.split(');',1)
    mutant=header+');\nwire [54:0] bad_dense = dense ^ 55\'h20000;\n'+re.sub(r'\bdense\b','bad_dense',body)
    (OUT/'codec-mutant.sv').write_text(mutant); sim(OUT/'codec-mutant.sv','codec-mutant',True)
    (OUT/'codec-report.json').write_text(json.dumps(dict(vectors=len(vectors),valid_e64_roundtrips=valid,mutants_rejected=1,source_sha256={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in [Path(__file__).resolve(),ROOT/'test/StorageDense.lean',*sorted((ROOT/'Pinwheel/Hardware/Storage').glob('Dense*.lean'))]},rtl_sha256=hashlib.sha256(rtl.encode()).hexdigest()),indent=2)+'\n')
if __name__=='__main__':main()
