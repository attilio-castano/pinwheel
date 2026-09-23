#!/usr/bin/env python3
"""Bounded schedule experiment and explicit area scenarios, not an SRAM backend.

Requires the public views fetched by inspect-storage-macros.py and local Icarus.
No physical tools, downloads, or full-chip implementation are invoked here.
"""
import argparse
import json
from pathlib import Path
import re

from validation_run import Commands, fresh_directory, sha

ROOT = Path(__file__).resolve().parents[1]


def area_scenarios(macros):
    # Pinned CMOS5L typical cells, docs/storage-primitives.md. A write-enabled
    # bit is budgeted as one FF plus one mux; these are arithmetic estimates.
    ff, mux, nand = 48.9888, 18.144, 7.2576
    enabled_bit = ff + mux
    # Current result chips have 468/469 non-storage state bits. Macro Q replaces
    # two fetched words with two ports, or one with one port (retain the other
    # response). Add one commit/start bypass flag; the larger scenario reserves
    # another 64 control bits. No synthesis optimization is assumed here.
    state_bits = {1: 469-64+1, 2: 468-128+1}
    common = {ports: [bits*enabled_bit + 400*mux + 1500*nand,
                      (bits+64)*enabled_bit + 800*mux + 3000*nand]
              for ports,bits in state_bits.items()}
    # One staging dictionary, no staging map: expand as each index is uploaded.
    scratch = [32*w*enabled_bit + 31*w*mux + 64*nand for w in (55, 64)]
    # Two atomic 256x5 maps, a flat mux tree per port, shared write decoding.
    def maps(ports):
        return 512*5*enabled_bit + ports*511*5*mux + 1024*nand
    d = macros['RM_IHPSG13_1P_64x64_c2_bm_bist']['footprint_um2']
    a = macros['RM_IHPSG13_1P_512x8_c3_bm_bist']['footprint_um2']
    full = macros['RM_IHPSG13_1P_512x64_c2_bm_bist']['footprint_um2']
    results = {}
    for name, area, logic, ports, rule in [
        ('hybrid-oneport', d, [maps(1)]*2, 1, 'SinglePort.Ready; combinational maps'),
        ('hybrid-twoport', 2*d, [maps(2)]*2, 2, 'No duration rule; combinational maps'),
        ('direct-oneport', full, scratch, 1, 'SinglePort.Ready plus response retention'),
        ('direct-twoport', 2*full, scratch, 2, 'No duration rule; broadcast expanded uploads'),
        ('indexed-two-stage', d+a, [0, 0], 1, 'Incompatible with latency-one policy; not costed'),
    ]:
        complete = name != 'indexed-two-stage'
        # Reserve 10/20% of standard-cell subtotal for clocking, buffering and
        # repair. Routing whitespace/halos are deliberately separate geometry.
        totals = [area + (logic[k]+common[ports][k])*(1.1 if k==0 else 1.2)
                  for k in range(2)] if complete else None
        results[name] = dict(macro_um2=area, storage_logic_um2=logic if complete else None,
                             whole_chip_scenarios_um2=totals, execution_rule=rule)
    return dict(cells_um2=dict(ff=ff,mux2=mux,nand2=nand), state_bits=state_bits,
                common_logic_scenarios_um2=common, options=results,
                boundary='Explicit gate-budget scenarios, not synthesized or routed area bounds. '
                         'Both atomic banks, scratch/maps, fetch/control/serial/result state, '
                         'decode logic, and 10/20 percent standard-cell repair allowance included. '
                         'Excludes routing whitespace, macro halos, power integration and signoff.')


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--tag', required=True)
    args = p.parse_args()
    out = fresh_directory(ROOT/'build/storage/feasibility', args.tag)
    manifest = json.loads((ROOT/'tools/storage-macros.json').read_text())
    views = ROOT/'build/storage/macros'
    identities = {}
    for rel, expected in manifest['files_sha256'].items():
        file = views/Path(rel).name
        if sha(file) != expected:
            raise RuntimeError(f'Mismatched pinned view: {file}')
        identities[rel] = expected
    names = [Path(p).stem for p in identities if p.startswith('lef/')]
    macros = {}
    for name in names:
        size = re.findall(r'\bSIZE\s+([\d.]+)\s+BY\s+([\d.]+)',
                          (views/(name+'.lef')).read_text())
        if len(size) != 1: raise RuntimeError('Ambiguous macro dimensions')
        w,h = map(float,size[0])
        macros[name] = dict(width_um=w,height_um=h,footprint_um2=w*h)
    commands = Commands(ROOT,out,default_timeout=60)
    iverilog = ROOT/'build/tools/oss-cad-suite/bin/iverilog'
    vvp = ROOT/'build/tools/oss-cad-suite/bin/vvp'
    sources = [ROOT/'test/sram_feasibility_tb.sv',
               views/'RM_IHPSG13_1P_512x64_c2_bm_bist.v',
               views/'RM_IHPSG13_1P_core_behavioral_bm_bist.v']
    commands([iverilog,'-g2012','-DFUNCTIONAL','-s','tb','-o',out/'schedule.vvp',*sources], 'compile')
    log = commands([vvp,out/'schedule.vvp'], 'schedule')
    match = re.search(r'SRAM feasibility passed: (\d+) edges, (\d+) consecutive branch dispatches',log)
    if not match: raise RuntimeError('Missing schedule evidence')
    # A single read response cannot stand in for two distinct successors.
    mutant = out/'single-response.sv'
    mutant.write_text(sources[0].read_text().replace('wire [63:0] q0,q1;',
        'wire [63:0] q0,unused; wire [63:0] q1=q0;').replace('ren,a0,a1,q0,q1);','ren,a0,a1,q0,unused);'))
    commands([iverilog,'-g2012','-DFUNCTIONAL','-s','tb','-o',out/'mutant.vvp',mutant,*sources[1:]],'mutant-compile')
    commands([vvp,out/'mutant.vvp'],'single-response-rejected',reject='SRAM lookup mismatch')
    report = dict(library_revision=manifest['library_revision'],files_sha256=identities,
                  source_sha256={str(f.relative_to(ROOT)):sha(f) for f in
                    [sources[0],Path(__file__),ROOT/'scripts/validation_run.py',ROOT/'scripts/process_group.py',
                     ROOT/'tools/storage-macros.json',ROOT/'tools/technology-library.json']},
                  tools_sha256={str(f.relative_to(ROOT)):sha(f.resolve()) for f in [iverilog,vvp]},
                  macros=macros,area=area_scenarios(macros),
                  edges=int(match[1]),branch_dispatches=int(match[2]),commands=commands.records,
                  boundary='Actual functional macro models; accepted small-image upload expansion, '
                           'two banks, immediate commit/start, consecutive terminal-capture branch fetches, '
                           'disabled reads, partial inactive writes and replacement. '
                           'Not a complete loader/engine, Lean refinement, timing proof or physical run.')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print(out/'report.json')


if __name__ == '__main__':
    main()
