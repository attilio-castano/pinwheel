#!/usr/bin/env python3
"""Bounded functional test of the experimental hybrid upload stage; no routing."""
import argparse
import json
from pathlib import Path
import re
import time

from chip_oracle import generate as chip_vectors
from upload_pipeline_vectors import generate as core_vectors
from validation_run import Commands, fresh_directory, sha

ROOT=Path(__file__).resolve().parents[1]


def write_priority_mutant(source):
    """Remove the shared grant so data/address/read users stay consistent."""
    gate=re.search(r'\bassign mem_write = (\w+);',source)
    if gate is None:
        raise ValueError('Cannot identify the emitted write-priority expression')
    mutant,count=re.subn(r'(\bwire\s+'+re.escape(gate[1])+r'\s*=\s*)[^;]+;',
                         r'\g<1>r_upload_pending;',source)
    if count!=1 or mutant==source:
        raise ValueError('Ambiguous emitted write-priority expression')
    return mutant


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--tag',required=True)
    args=p.parse_args()
    out=fresh_directory(ROOT/'build/storage/upload-pipeline',args.tag)
    run=Commands(ROOT,out,default_timeout=120)
    started=time.monotonic()
    cad=ROOT/'build/tools/oss-cad-suite/bin'
    circt=ROOT/'build/tools/firtool-1.159.0/bin/circt-opt'
    macro_dir=ROOT/'build/storage/macros'
    models=[macro_dir/'RM_IHPSG13_1P_64x64_c2_bm_bist.v',
            macro_dir/'RM_IHPSG13_1P_core_behavioral_bm_bist.v']
    lock=json.loads((ROOT/'tools/storage-macros.json').read_text())
    expected={Path(k).name:v for k,v in lock['files_sha256'].items()}
    for model in models:
        if sha(model)!=expected[model.name]:
            raise ValueError('Changed macro model: '+model.name)
    files=[*sorted((ROOT/'Pinwheel').rglob('*.lean')),ROOT/'Pinwheel.lean',ROOT/'lakefile.toml',
        ROOT/'lean-toolchain',*models,ROOT/'tools/storage-macros.json',circt,
        *[cad/n for n in ['iverilog','vvp']],ROOT/'build/loader/images.txt',
        *[ROOT/'test'/n for n in ['UploadPipelineEmit.lean','sram_chip.sv','sram_core_tb.sv','chip_tb.sv']],
        *[ROOT/'scripts'/n for n in ['check-upload-pipeline.py','upload_pipeline_vectors.py','sram_core_vectors.py',
            'chip_oracle.py','loader-vectors.py','reactive-core-vectors.py','execution-vectors.py',
            'host_demo.py','pinwheel_host.py','validation_run.py','process_group.py']]]
    report=dict(schema=1,status='running',commands=run.records,inputs_sha256={str(f):sha(f) for f in files},
                bounds=dict(per_command_seconds=120),added_register_bits=71)
    try:
        run(['lake','build','Pinwheel.Hardware.Storage.UploadPipeline'],'lean-build')
        run(['lake','env','lean','-DwarningAsError=true','--run','test/UploadPipelineEmit.lean',out],'emit')
        report['coverage']=dict(core=core_vectors(out),chip=chip_vectors(out))
        for kind in ('core','chip'):
            rtl=run([circt,out/(kind+'.mlir'),'--canonicalize','--lower-seq-to-sv','--lower-hw-to-sv',
                '--hw-legalize-modules','--export-verilog','-o','/dev/null'],kind+'-export')
            (out/(kind+'.sv')).write_text(rtl)
            top='sram_core_tb' if kind=='core' else 'chip_tb'
            tb=ROOT/'test'/(top+'.sv')
            run([cad/'iverilog','-g2012','-DFUNCTIONAL','-DSRAM_HYBRID','-s',top,'-o',out/(kind+'.vvp'),
                out/(kind+'.sv'),ROOT/'test/sram_chip.sv',tb,*models],kind+'-compile')
            vectors=out/('core-vectors.txt' if kind=='core' else 'vectors.txt')
            result=run([cad/'vvp',out/(kind+'.vvp'),'+vectors='+str(vectors)],kind+'-oracle')
            expected_line=f'Passed {report["coverage"][kind]["edges"]} independent '+('SRAM core' if kind=='core' else 'whole-chip')+' edges'
            if expected_line not in result:
                raise ValueError('Incomplete oracle run: '+kind)
        # Bypass the read-priority gate in a compiled mutant. The independent
        # immediate-start cases must reject it for an actual state mismatch.
        source=(out/'core.sv').read_text()
        # Change the shared predicate, including its address/read mux users,
        # so this mutant still writes the queued inactive address correctly.
        (out/'unconditional-write.sv').write_text(write_priority_mutant(source))
        run([cad/'iverilog','-g2012','-DFUNCTIONAL','-DSRAM_HYBRID','-s','sram_core_tb','-o',out/'mutant.vvp',
            out/'unconditional-write.sv',ROOT/'test/sram_chip.sv',ROOT/'test/sram_core_tb.sv',*models],'mutant-compile')
        run([cad/'vvp',out/'mutant.vvp','+vectors='+str(out/'core-vectors.txt')],
            'mutant-oracle',reject='SRAM core state')
        report.update(status='passed',boundary='Experimental emitted hybrid RTL plus digital macro models. Queue lemmas are not a composed whole-chip refinement; no mapped area, clock/hold repair, wire timing or routing benefit is established.')
    except BaseException as error:
        report.update(status='failed',error=str(error))
        raise
    finally:
        report['seconds']=round(time.monotonic()-started,3)
        report['source_unchanged']=all(sha(f)==h for f,h in report['inputs_sha256'].items())
        if not report['source_unchanged']:
            report['status']='failed'
        report['artifacts_sha256']={str(f.relative_to(out)):sha(f) for f in out.rglob('*')
            if f.is_file() and f.name!='report.json'}
        with (out/'report.json').open('x') as f:
            json.dump(report,f,indent=2);f.write('\n')
        print(report['status'],report['seconds'],out/'report.json',flush=True)
    if report['status']!='passed':
        raise RuntimeError('Upload pipeline validation failed')


if __name__=='__main__':
    main()
