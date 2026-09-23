#!/usr/bin/env python3
"""Emit, check, map and time the opt-in paired controller; no placement/routing.

Create-only receipts, 120-second subprocess caps and installed pinned tools.
STA containers use two CPUs/2 GiB, no network and independent cleanup checks.
"""
import argparse
from datetime import datetime, timezone
import json
from pathlib import Path
import re
import sys
import time

from paired_vectors import core_vectors,chip_vectors
from paired_mapping import mapping,timing,write,MACRO
from tiled_chip import chip_metrics
from validation_run import Commands,fresh_directory,sha

ROOT=Path(__file__).resolve().parents[1]


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--tag',required=True)
    args=parser.parse_args()
    out=fresh_directory(ROOT/'build/validation',args.tag)
    run=Commands(ROOT,out,default_timeout=120);started=time.monotonic()
    report=dict(schema=1,status='running',date=datetime.now(timezone.utc).isoformat(),commands=run.records,
                per_command_seconds=120,placement_or_routing=False)
    cad=ROOT/'build/tools/oss-cad-suite/bin';circt=ROOT/'build/tools/firtool-1.159.0/bin/circt-opt'
    views=ROOT/'build/storage/macros'
    models=[views/(MACRO+'.v'),views/'RM_IHPSG13_1P_core_behavioral_bm_bist.v']
    try:
        sources=[ROOT/'Pinwheel.lean',*sorted((ROOT/'Pinwheel').rglob('*.lean')),
            *[ROOT/p for p in ['scripts/check-paired-controller.py','scripts/paired_mapping.py','scripts/paired_vectors.py',
                'scripts/paired_execution.py','scripts/check-sram-timing.py','scripts/check-map-tile.py',
                'scripts/tiled_chip.py','scripts/map_distribution.py','scripts/chip_oracle.py','scripts/loader-vectors.py',
                'scripts/reactive-core-vectors.py','scripts/execution-vectors.py','scripts/uart_rx_oracle.py',
                'scripts/host_demo.py','scripts/pinwheel_host.py','scripts/validation_run.py','scripts/process_group.py',
                'test/PairedChipEmit.lean','test/paired_chip.sv','test/sram_core_tb.sv','test/chip_tb.sv',
                'lean-toolchain','lakefile.toml','tools/storage-macros.json','tools/technology-library.json',
                'tools/hardware-toolchain.json','tools/physical-toolchain.json','build/loader/images.txt']],
            circt,*[cad/n for n in ['yosys','yosys-abc','iverilog','vvp']]]
        lock=json.loads((ROOT/'tools/storage-macros.json').read_text())
        for rel,digest in lock['files_sha256'].items():
            path=views/Path(rel).name
            if sha(path)!=digest:raise ValueError('changed pinned macro view: '+rel)
            sources.append(path)
        sources+=list((ROOT/'build/tools/ihp-cmos5l').glob('*.lib'))
        preserved={}
        for name in ['paired-execution','local-load']:
            manifest_path=ROOT/f'physical/experiments/{name}-results.json'
            manifest=json.loads(manifest_path.read_text());path=ROOT/manifest['report']
            if sha(path)!=manifest['report_sha256']:raise ValueError('changed retained '+name)
            sources += [manifest_path,path]
            previous=json.loads(path.read_text())
            if name=='paired-execution':
                for group in ['source_sha256','artifact_sha256']:
                    for rel,digest in previous[group].items():
                        if sha(ROOT/rel)!=digest:raise ValueError('changed prior paired evidence: '+rel)
                report['declared_bits']=previous['resources']['declared_register_bits']
            else:
                report['baseline']={}
                for corner in ['typical','slow']:
                    saved=path.parent/f'tiled-{corner}.json'
                    if sha(saved)!=previous['artifacts_sha256'][saved.name]:raise ValueError('changed baseline netlist')
                    measured=chip_metrics(json.loads(saved.read_text()))
                    if measured!=previous['variants'][corner]['tiled']:raise ValueError('baseline census mismatch')
                    report['baseline'][corner]=measured;sources.append(saved)
                cell_models=[Path(p) for p in previous['pin_oracle_source']['cell_models_sha256']]
                for p in cell_models:
                    if sha(p)!=previous['pin_oracle_source']['cell_models_sha256'][str(p)]:raise ValueError('changed cell model')
                sources+=cell_models
            preserved[name]=dict(report=manifest['report'],sha256=sha(path))
        report['preserved_receipts']=preserved
        frozen={str(p.relative_to(ROOT)) if p.is_relative_to(ROOT) else str(p):sha(p) for p in sources}
        report['source_sha256']=frozen;write(out/'inputs.json',frozen)
        run(['lake','build','Pinwheel.Hardware.Storage.PairedController'],'lean-build')
        emit=run(['lake','env','lean','-DwarningAsError=true','--run','test/PairedChipEmit.lean',out],'emit')
        if 'standard axioms only' not in emit:raise ValueError('missing controller audit')
        emitted=json.loads((out/'assembly.json').read_text())
        if sum(p['width'] for p in emitted['chip']['registers'])!=report['declared_bits']:
            raise ValueError('full emitted state differs from the studied budget')
        text=(ROOT/'test/PairedChipEmit.lean').read_text()
        mutant=text.replace('\n#audit_paired_controller\n',
            '\nnamespace Pinwheel.Hardware.Storage.PairedController\naxiom forbidden : False\nend Pinwheel.Hardware.Storage.PairedController\n#audit_paired_controller\n')
        if mutant==text:raise ValueError('missing audit mutation anchor')
        (out/'AuditNegative.lean').write_text(mutant)
        run(['lake','env','lean',out/'AuditNegative.lean'],'axiom-negative',reject='Unapproved paired controller axioms')
        report['coverage']=dict(core=core_vectors(out),chip=chip_vectors(out))
        for kind in ['core','chip']:
            rtl=run([circt,out/(kind+'.mlir'),'--canonicalize','--lower-seq-to-sv','--lower-hw-to-sv',
                '--hw-legalize-modules','--export-verilog','-o','/dev/null'],kind+'-export')
            (out/(kind+'.sv')).write_text(rtl)
        (out/'core-tb.sv').write_text((ROOT/'test/sram_core_tb.sv').read_text().replace(
            'pinwheel_sram_core dut','pinwheel_paired_core dut'))
        for kind in ['core','chip']:
            tb=out/'core-tb.sv' if kind=='core' else ROOT/'test/chip_tb.sv'
            top='sram_core_tb' if kind=='core' else 'chip_tb'
            run([cad/'iverilog','-g2012','-DFUNCTIONAL','-s',top,'-o',out/(kind+'.vvp'),
                 out/(kind+'.sv'),ROOT/'test/paired_chip.sv',tb,*models],kind+'-compile')
            vector=out/('core-vectors.txt' if kind=='core' else 'vectors.txt')
            log=run([cad/'vvp',out/(kind+'.vvp'),'+vectors='+str(vector)],kind+'-oracle')
            expected=f'Passed {report["coverage"][kind]["edges"]} independent '+('SRAM core' if kind=='core' else 'whole-chip')+' edges'
            if expected not in log:raise ValueError('incomplete paired '+kind+' oracle')
        # Route the actual SRAM request from old stored row bits in this mutant.
        # It must fail for a concrete state mismatch, not a parser error.
        wrapper=(ROOT/'test/paired_chip.sv').read_text()
        core_start=wrapper.index('module pinwheel_paired_core')
        before,body=wrapper[:core_start],wrapper[core_start:]
        body=body.replace('pinwheel_paired_memory memory (.*);',
            'pinwheel_paired_memory memory (.clk(clk), .mem_addr0({mem_addr0[8],controller.r_current[29:22]}), .mem_data(mem_data), .mem_q0(mem_q0), .mem_write(mem_write), .mem_read(mem_read));')
        if before+body==wrapper:raise ValueError('missing SRAM-request mutation')
        (out/'stale-row.sv').write_text(before+body)
        run([cad/'iverilog','-g2012','-DFUNCTIONAL','-s','sram_core_tb','-o',out/'stale-row.vvp',
             out/'core.sv',out/'stale-row.sv',out/'core-tb.sv',*models],'stale-row-compile')
        run([cad/'vvp',out/'stale-row.vvp','+vectors='+str(out/'core-vectors.txt')],
            'stale-row-negative',reject='SRAM core state')
        mapping(run,out,emitted['chip'],report)
        # Read back the saved mapped chip with the pinned physical cell models.
        run([cad/'iverilog','-g2012','-DFUNCTIONAL','-s','chip_tb','-o',out/'mapped.vvp',
             out/'typical/design.v',ROOT/'test/chip_tb.sv',*models,*cell_models],'mapped-compile')
        log=run([cad/'vvp',out/'mapped.vvp','+vectors='+str(out/'vectors.txt')],'mapped-oracle')
        if f'Passed {report["coverage"]["chip"]["edges"]} independent whole-chip edges' not in log:
            raise ValueError('incomplete mapped pin oracle')
        timing(run,out,emitted['chip'],report)
        report['comparison']={}
        for corner,v in report['variants'].items():
            base=report['baseline'][corner]['total_cell_and_macro_area_um2']
            area=v['metrics']['total_cell_and_macro_area_um2']
            report['comparison'][corner]=dict(mapped_area_delta_um2=round(area-base,4),
                mapped_area_delta_percent=round(100*(area/base-1),4),
                signal_electrical_pass=not any(v['cell_timing']['electrical_violations'].values()),
                setup_pass=v['cell_timing']['setup_slack_ns']>=0,hold_pass=v['cell_timing']['hold_slack_ns']>=0)
        report['boundary']=[
            'Typed Lean controller and existing sampler/serial/mailbox composition; emitter is not formally proved.',
            'Independent Python/E64/peer RTL traces, arbitrary-state saved-mapped equivalence and mapped pin replay.',
            'Exact one-macro terminal and exhaustive physical-FF ownership intake; no hidden parameter read port.',
            'Complete mapped area includes SRAM, admission, payload, wrappers and signal fanout repair.',
            '20 ns ideal-clock cell/macro STA with 4/0.2 ns max/min I/O delays, .010 pF output load and .2 ns uncertainty.',
            'No clock-tree, wire-parasitic, placed hold-repair, congestion, routing, antenna or silicon closure.',
            '290-word experimental upload format differs from E64 wire uploads; current production chip unchanged.']
        report['status']='passed'
    except BaseException as error:
        report.update(status='failed',error=f'{type(error).__name__}: {error}')
        raise
    finally:
        report['seconds']=round(time.monotonic()-started,3)
        report['inputs_unchanged']=all(sha(ROOT/name if not Path(name).is_absolute() else name)==digest
            for name,digest in report.get('source_sha256',{}).items())
        if not report['inputs_unchanged']:report['status']='failed'
        report['artifact_sha256']={str(p.relative_to(ROOT)):sha(p) for p in sorted(out.rglob('*')) if p.is_file()}
        with (out/'report.json').open('x') as stream:stream.write(json.dumps(report,indent=2)+'\n')
        print(json.dumps({k:report.get(k) for k in ['status','seconds','comparison','error']}),flush=True)
    if report['status']!='passed':raise RuntimeError('paired controller check failed')


if __name__=='__main__':main()
