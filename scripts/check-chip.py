#!/usr/bin/env python3
"""Check the emitted chip at its external ports, including retained host results."""
import argparse
import json
from pathlib import Path
import re
import time

from chip_oracle import generate
from hardware_targets import TARGETS
from validation_run import Commands, fresh_directory, sha

ROOT=Path(__file__).resolve().parents[1]


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--tag',required=True)
    p.add_argument('--variant',choices=['oneport','twoport'],default='twoport')
    args=p.parse_args()
    target=TARGETS[f'chip-{args.variant}-result']
    out=fresh_directory(ROOT/'build/chip',args.tag)
    started=time.monotonic()
    source_paths=[*sorted((ROOT/'Pinwheel').rglob('*.lean')),ROOT/'Pinwheel.lean',ROOT/'lakefile.toml',
        ROOT/'lean-toolchain',ROOT/'test/ChipEmit.lean',ROOT/'test/HostResult.lean',ROOT/'test/Loader.lean',
        ROOT/'test/chip_tb.sv',Path(__file__),*[ROOT/'scripts'/name for name in
        ['chip_oracle.py','host_demo.py','pinwheel_host.py','hardware_targets.py','validation_run.py','process_group.py','loader-vectors.py',
         'reactive-core-vectors.py','execution-vectors.py','uart_rx_oracle.py']],ROOT/'tools/hardware-toolchain.json']
    sources={str(path.relative_to(ROOT)):sha(path) for path in source_paths}
    run=Commands(ROOT,out,default_timeout=600)
    run(['lake','build','Pinwheel',target.emitter],'build')
    run(['lake','env','lean','-DwarningAsError=true','--run','test/HostResult.lean'],'host-contract')
    run(['lake','env','lean','-DwarningAsError=true','--run','test/Loader.lean'],'compiler-images')
    run([ROOT/'.lake/build/bin'/target.emitter,out],'emit')
    coverage=generate(out,target.readiness)
    circt=ROOT/'build/tools/firtool-1.159.0/bin/circt-opt'
    cad=ROOT/'build/tools/oss-cad-suite/bin'
    versions={name:run(command,name+'-version').strip() for name,command in
              [('circt',[circt,'--version']),('yosys',[cad/'yosys','-V'])]}
    mlir=out/(target.name+'.mlir')
    rtl=run([circt,mlir,'--canonicalize','--lower-seq-to-sv','--lower-hw-to-sv',
             '--hw-legalize-modules','--export-verilog','-o','/dev/null'],'export')
    (out/'design.sv').write_text(rtl)
    tb=ROOT/'test/chip_tb.sv'
    def simulate(file,label,reject=None):
        run([cad/'iverilog','-g2012','-s','chip_tb','-o',out/(label+'.vvp'),file,tb],label+'-compile')
        return run([cad/'vvp',out/(label+'.vvp'),'+vectors='+str(out/'vectors.txt')],label,reject=reject)
    sim=simulate(out/'design.sv','rtl')
    if f'Passed {coverage["edges"]} independent whole-chip edges' not in sim:
        raise RuntimeError('Missing complete RTL trace')
    script=out/'synth.ys'
    script.write_text(f'read_verilog -sv {out}/design.sv\nsynth -top {target.top}\ncheck -assert\n'
                      f'write_verilog -noattr {out}/gates.v\n')
    run([cad/'yosys','-Q','-T','-s',script],'synthesis')
    # Preserve the complete width of matched fetched/start registers. Their
    # constant high bit otherwise causes the entire register to miss matching.
    gates=(out/'gates.v').read_text()
    narrowed=re.findall(r'^\s*reg \[62:0\] (r_\w+);',gates,re.M)
    for register in narrowed:
        gates=re.sub(rf'\b{register}\b',register+'_narrow',gates)
        gates=gates.replace(f'reg [62:0] {register}_narrow;',
            f'reg [62:0] {register}_narrow;\n  wire [63:0] {register};\n'
            f"  assign {register} = {{1'h0, {register}_narrow}};",1)
    (out/'gates-matched.v').write_text(gates)
    eq=out/'equivalence.ys'
    eq.write_text(f'read_verilog -sv {out}/design.sv\nproc\nrename -hide w:_GEN*\nrename {target.top} gold\n'
        f'read_verilog -sv {out}/gates-matched.v\nproc\nrename -hide w:_GEN*\nrename {target.top} gate\n'
        'equiv_make gold gate equiv\nhierarchy -check -top equiv\nequiv_simple -seq 3\n'
        'equiv_induct -seq 3\nequiv_status -assert\n')
    log=run([cad/'yosys','-Q','-T','-s',eq],'gate-equivalence')
    matched=re.search(r'Of those cells (\d+) are proven and 0 are unproven',log)
    if not matched or int(matched[1])<6000: raise RuntimeError('Incomplete whole-chip comparison')
    simulate(out/'gates.v','gates')
    # Corrupt a real result bit while preserving valid syntax and all drivers.
    header=rtl.index(');')+2
    if not re.search(r'output\s+\[7:0\]\s+uo_out',rtl[:header]):
        raise RuntimeError('Unrecognized chip output declaration')
    body,count=re.subn(r'\buo_out\b','uncorrupted_uo_out',rtl[header:])
    if not count or 'r_result_page_second' not in body: raise RuntimeError('Missing result mutation anchor')
    broken=rtl[:header]+'\nwire [7:0] uncorrupted_uo_out;\n'+body
    end=broken.rfind('endmodule')
    broken=broken[:end]+"assign uo_out=uncorrupted_uo_out ^ (r_result_page_second==1 ? 8'h01 : 8'h00);\n"+broken[end:]
    (out/'corrupt-result.sv').write_text(broken)
    simulate(out/'corrupt-result.sv','corrupt-result',reject='CHIP after edge')
    for path in source_paths:
        if sha(path)!=sources[str(path.relative_to(ROOT))]: raise RuntimeError(f'Source changed during check: {path}')
    report=dict(target=target.name,top=target.top,readiness_enforced=target.readiness,
                source_sha256=sources,mlir_sha256=sha(mlir),rtl_sha256=sha(out/'design.sv'),
                generic_gates_sha256=sha(out/'gates.v'),vectors_sha256=sha(out/'vectors.txt'),
                coverage=coverage,equivalence_points=int(matched[1]),rewidened_registers=narrowed,
                tools=versions,commands=run.records,elapsed_seconds=round(time.monotonic()-started,3),
                boundary='External pin RTL and generic-gate simulation from unknown registers, '
                         'after explicit reset; all reachable storage uploaded before execution. '
                         'RTL/generic-gate equivalence, result corruption rejection. '
                         'No emitted-RTL-to-Lean read-back, technology mapping or physical closure.')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print(out/'report.json')


if __name__=='__main__': main()
