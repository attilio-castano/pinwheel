#!/usr/bin/env python3
"""Bounded full-operation model and matched lookup cost follow-up.

Preserves the first compact study. No production emitter, placement or routing.
Each subprocess is capped at 120 seconds; STA uses the installed pinned image,
two CPUs and 2 GiB, with no network and independent termination checks.
"""
import argparse
from datetime import datetime, timezone
import json
from pathlib import Path
import re
import runpy
import shutil
import sys
import time

from paired_execution import Machine, compile_e64, resource_budget, uart_image, spi_image
from paired_cost import screen
from validation_run import Commands, fresh_directory, sha

ROOT = Path(__file__).resolve().parents[1]


def write_json(path, value):
    with path.open('x') as stream:
        stream.write(json.dumps(value, indent=2)+'\n')


def protocol_checks():
    legacy = runpy.run_path(str(ROOT/'scripts/reactive-core-vectors.py'))
    images, budgets = {}, {}
    for line in (ROOT/'build/loader/images.txt').read_text().splitlines():
        name, *numbers = line.split()
        last, levels, enables, *words = map(int,numbers)
        images[name] = (words,last,(levels,enables))
        candidate = compile_e64(words,(levels,enables),last)
        budgets[name] = dict(logical_positions=last+1, distinct_e64_records=len(set(words)),
                             parameter_entries=candidate.used_parameters)

    class Adapter:
        def __init__(self):
            self.m, self.count = Machine(), 0
        @property
        def s(self): return self.m.s
        def load(self, name, words, last, idle):
            self.m.edge(reset=True)
            self.m.load(compile_e64(words,idle,last))
        def edge(self, incoming=0, start=0, write=0, **ignored):
            # The package's command 7 resets; use only rejectable busy commands.
            command = self.count%6+1 if write else 5 if start else 0
            self.count += 1
            self.m.edge(command=command,data=(1<<64)-1,incoming=incoming)
            if write and self.m.gates != (False,False,False,True):
                raise ValueError('busy protocol command accepted')

    m = Adapter()
    m.load('i2c-write',*images['i2c-write'])
    i2c_edges = [legacy['i2c'](m,False,stretched=True)]
    m.load('i2c-read',*images['i2c-read'])
    for byte in [0,1,0x55,0x80,0x96,0xaa,0xfe,0xff]:
        for stretch in [False,True]:
            i2c_edges.append(legacy['i2c'](m,True,byte,stretched=stretch))
    for bits in range(7):
        i2c_edges.append(legacy['i2c'](m,True,acks=tuple(bits>>k&1 for k in range(3)),stretched=True))
    rx_frames = legacy['uart_rx']['exercise'](m,images)
    # Recheck the actual saved TX/SPI fixtures edge-by-edge against E64.
    tx_edges = {}
    for name, edges in [('uart',40),('spi',68)]:
        words,last,idle = images[name]
        m.load(name,*images[name])
        reference = legacy['Machine'](False)
        reference.load(name,words,last,idle)
        m.edge(start=1); reference.edge(start=1)
        if m.s != reference.s: raise ValueError('compiled entry mismatch')
        for k in range(edges):
            incoming = k%4
            m.edge(incoming=incoming); reference.edge(incoming=incoming)
            if m.s != reference.s: raise ValueError('compiled trace mismatch')
        if m.s[0]!=5: raise ValueError('compiled TX did not finish')
        tx_edges[name] = edges
    return dict(images=budgets,i2c_cases=len(i2c_edges),i2c_edges=sum(i2c_edges),
                uart_rx_frames=rx_frames,compiled_tx_edges=tx_edges,
                input_boundary='already sampled inputs; no package serial replay')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--tag',required=True)
    args = parser.parse_args()
    out = fresh_directory(ROOT/'build/validation',args.tag)
    started = time.monotonic()
    run = Commands(ROOT,out,default_timeout=120)
    report = dict(status='running',date=datetime.now(timezone.utc).isoformat(),
                  scope='execution models, conditional schedule proof and standalone lookup mapping/STA',
                  commands=run.records,per_command_timeout_seconds=120)
    try:
        inputs = [ROOT/p for p in [
            'scripts/paired_execution.py','scripts/paired_cost.py','scripts/check-paired-execution.py',
            'test/test_paired_execution.py','test/PairedSchedule.lean',
            'scripts/compact_execution.py','test/test_compact_execution.py',
            'scripts/execution-vectors.py','scripts/reactive-core-vectors.py','scripts/uart_rx_oracle.py',
            'scripts/check-map-tile.py','scripts/check-sram-timing.py',
            'scripts/tiled_chip.py','scripts/map_distribution.py',
            'scripts/validation_run.py','scripts/process_group.py',
            'lean-toolchain','lakefile.toml','tools/hardware-toolchain.json',
            'tools/storage-macros.json','tools/technology-library.json','tools/physical-toolchain.json',
            'build/loader/images.txt',
            'build/storage/macros/RM_IHPSG13_1P_64x64_c2_bm_bist.lef',
            'build/storage/macros/RM_IHPSG13_1P_512x64_c2_bm_bist.lef',
            'build/tools/oss-cad-suite/bin/yosys']]
        inputs += sorted((ROOT/'build/tools/ihp-cmos5l').glob('*.lib'))
        hardware = [ROOT/'Pinwheel.lean',*sorted((ROOT/'Pinwheel').rglob('*.lean'))]
        retained = {}
        for name in ['compact-execution','chip-architecture','local-slew']:
            path = ROOT/f'physical/experiments/{name}-results.json'
            manifest = json.loads(path.read_text())
            receipt = ROOT/manifest['report']
            if sha(receipt)!=manifest['report_sha256']:
                raise ValueError('changed retained receipt: '+name)
            if name=='compact-execution':
                previous = json.loads(receipt.read_text())
                for rel,digest in previous['source_sha256'].items():
                    if sha(ROOT/rel)!=digest:
                        raise ValueError('first study input changed: '+rel)
                for rel,digest in previous['artifact_sha256'].items():
                    if sha(ROOT/rel)!=digest:
                        raise ValueError('first study artifact changed: '+rel)
            retained[name] = dict(report=manifest['report'],sha256=sha(receipt))
            inputs += [path,receipt]
        hashes = {str(p.relative_to(ROOT)):sha(p) for p in inputs+hardware}
        report.update(source_sha256=hashes,preserved_receipts=retained)
        write_json(out/'inputs.json',hashes)
        log = run([sys.executable,'-B','-m','unittest','discover','-s','test',
                   '-p','test_paired_execution.py','-v'],'models')
        match = re.search(r'Ran (\d+) tests in ([0-9.]+)s\s+OK',log)
        if not match: raise ValueError('missing successful model summary')
        report.update(focused_tests=int(match[1]),model_test_seconds=float(match[2]),
                      behavioral_mutants_rejected=6)
        report['compiled_protocols'] = protocol_checks()
        write_json(out/'compiled-protocols.json',report['compiled_protocols'])
        lake = shutil.which('lake')
        if not lake: raise ValueError('missing pinned Lean toolchain')
        proof = run([lake,'env','lean','test/PairedSchedule.lean'],'schedule')
        if 'standard axioms only' not in proof: raise ValueError('missing axiom audit')
        text = (ROOT/'test/PairedSchedule.lean').read_text()
        mutant = text.replace('end PairedSchedule',
            'axiom forbidden : False\ntheorem bad : False := forbidden\nend PairedSchedule')
        if mutant==text: raise ValueError('missing mutation anchor')
        mutation = out/'ScheduleMutant.lean'
        mutation.write_text(mutant)
        run([lake,'env','lean',mutation],'axiom-negative',reject='Unapproved paired schedule axioms')
        report.update(schedule_theorems=['PairedSchedule.step_related','PairedSchedule.trace_related'],
                      axiom_negative_rejected=True)
        for name,image in [('resident-uart',uart_image()),('resident-spi',spi_image())]:
            write_json(out/(name+'.json'),dict(parameters=image.parameters,rows=image.rows,
                boot=image.boot,idle=image.idle,used_parameters=image.used_parameters,
                logical_positions=image.logical_positions,upload_words=len(image.upload())))
        report['resources'] = resource_budget()
        macro_areas = {}
        for rows in [64,512]:
            lef = ROOT/f'build/storage/macros/RM_IHPSG13_1P_{rows}x64_c2_bm_bist.lef'
            found = re.findall(r'\bSIZE\s+([\d.]+)\s+BY\s+([\d.]+)\s*;',lef.read_text())
            if len(found)!=1: raise ValueError('ambiguous macro geometry')
            w,h = map(float,found[0])
            macro_areas[str(rows)] = dict(width_um=w,height_um=h,area_um2=round(w*h,4))
        report['macro_geometry'] = macro_areas
        run([ROOT/'build/tools/oss-cad-suite/bin/yosys','-V'],'yosys-version')
        report['lookup_screen'] = screen(run,out)
        premium = macro_areas['512']['area_um2']-2*macro_areas['64']['area_um2']
        report['lookup_plus_macro_delta_um2'] = {
            corner:round(result['area_um2']-
                         report['lookup_screen']['variants']['index'][corner]['area_um2']+premium,4)
            for corner,result in report['lookup_screen']['variants']['parameter'].items()}
        report['decision'] = 'keep-paired-direction-open; next exact controller emission and composed timing'
        report['evidence_boundary'] = [
            'Canonical E64-operation model with full 256-address/32-record capacity; no universal compiler theorem.',
            'Independent sampled-pin and E64 oracles, including compiled I2C/RX; no package-wrapper RTL composition.',
            'Conditional Lean dispatch schedule includes the cached parameter; not compiler/loader refinement.',
            'Mapped lookup SAT covers arbitrary two-valued state/inputs and every output/next-state bit.',
            'Lookup RTL uses identical generic topology for both sizes; neither is the actual full chip.',
            'Standalone cell timing excludes SRAM clock-to-Q/setup, branch/entry logic and wires.',
            'Lookup-plus-macro delta excludes other controller logic, clocks, hold repair and placement.',
            'The new 290-word program format requires host translation and new admission integration.',
            'No new production hardware, placement, detailed routing, extracted timing or silicon claim.']
        changed = [name for name,digest in hashes.items() if sha(ROOT/name)!=digest]
        if changed: raise ValueError('inputs changed during check: '+', '.join(changed))
        report.update(status='passed',unchanged_hardware_sources=len(hardware))
    except BaseException as error:
        report.update(status='failed',error=f'{type(error).__name__}: {error}')
        raise
    finally:
        report['seconds'] = round(time.monotonic()-started,3)
        report['artifact_sha256'] = {str(p.relative_to(ROOT)):sha(p)
            for p in sorted(out.rglob('*')) if p.is_file()}
        write_json(out/'report.json',report)
    print(json.dumps({k:report[k] for k in ['status','focused_tests','seconds',
                                           'lookup_plus_macro_delta_um2','unchanged_hardware_sources']}))


if __name__=='__main__':
    main()
