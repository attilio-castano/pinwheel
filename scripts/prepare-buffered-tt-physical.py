#!/usr/bin/env python3
"""Freeze one independently validated buffered Tiny Tapeout physical candidate.

Uses exact accepted generated RTL and the pinned 6x4 template/PDK inventory.
No shared runtime or PDK is changed. --fetch retrieves only missing macro views
and checks Git blob identities; missing views otherwise remain explicit blockers.
"""
import argparse
from copy import deepcopy
import json
from pathlib import Path
import shutil
import urllib.request

from buffered_tt_physical import ROOT, MASTER, TOP, PLACEMENTS, blob, column_plan, read, sha, supply_geometry, template_signal_columns, validate_flow_config, write
from validation_run import fresh_directory


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--validation', required=True, type=Path)
    p.add_argument('--design', required=True)
    p.add_argument('--macro-root', required=True, type=Path)
    p.add_argument('--fetch', action='store_true')
    args = p.parse_args()
    validation = args.validation.resolve()
    gate = read(validation)
    if gate.get('schema') != 'pinwheel-tt-buffered-digital-v1' or gate.get('status') != 'passed' or not gate.get('inputs_unchanged'):
        raise ValueError('A passed, source-bound Tiny Tapeout wrapper gate is required')
    for name, digest in gate['source_sha256'].items():
        if sha(ROOT/name) != digest:
            raise ValueError('Changed validated source: '+name)
    rtl = []
    for name in ['frontend', 'controller']:
        source = ROOT/gate['inputs'][name]['path']
        if sha(source) != gate['inputs'][name]['sha256']:
            raise ValueError('Changed validated generated RTL: '+name)
        rtl.append(source)
    rtl += [ROOT/'physical'/name for name in ['buffered_sram_memory.sv', 'buffered_sram_serial_wrapper.sv', 'tt_um_pinwheel_buffered.sv']]
    lock = read(ROOT/'tools/physical-toolchain.json')
    upstream = ROOT/'build/physical/upstream'
    inventory = upstream/'pdk-tree.json'
    if sha(inventory) != lock['pdk_tree_sha256']:
        raise ValueError('Wrong pinned PDK tree inventory')
    tree = read(inventory)
    if tree['truncated'] or tree['sha'] != lock['pdk_revision']:
        raise ValueError('Incomplete or wrong PDK inventory')
    entries = {e['path']:e for e in tree['tree']}
    template = upstream/'tt_block_6x4_pgvdd.def'
    if sha(template) != lock['allocation']['tt_def_template_sha256']:
        raise ValueError('Wrong official 6x4 template')
    views = [f'{sub}/{MASTER}.{suffix}' for sub, suffix in [('lef','lef'),('gds','gds'),('cdl','cdl'),('verilog','v')]]
    views += [f'lib/{MASTER}_{corner}.lib' for corner in ['typ_1p20V_25C','slow_1p08V_125C','fast_1p32V_m55C']]
    loaded, missing = {}, []
    for relative in views:
        name = Path(relative).name
        source = 'ihp-sg13g2/libs.ref/sg13g2_sram/'+relative
        expected = entries[source]['sha']
        local = args.macro_root/name
        cached = upstream/'buffered-macro'/name
        path = local if local.is_file() else cached
        if not path.is_file() and args.fetch:
            url = f"https://raw.githubusercontent.com/IHP-GmbH/IHP-Open-PDK/{lock['pdk_revision']}/{source}"
            with urllib.request.urlopen(url, timeout=90) as response:
                data = response.read()
            if blob(data) != expected:
                raise ValueError('Unpinned macro download: '+name)
            cached.parent.mkdir(parents=True, exist_ok=True)
            cached.write_bytes(data)
        if not path.is_file():
            missing.append(name)
        elif blob(path.read_bytes()) != expected:
            raise ValueError('Changed pinned macro view: '+name)
        else:
            loaded[name] = path
    if MASTER+'.lef' not in loaded or MASTER+'.v' not in loaded:
        raise ValueError('Need pinned macro LEF/model even for incomplete preparation')
    geometry = supply_geometry(loaded[MASTER+'.lef'])
    plan = column_plan(geometry, template_signal_columns(template))
    out = fresh_directory(ROOT/'build/physical', args.design)
    (out/'macro').mkdir()
    for name, path in loaded.items():
        shutil.copyfile(path, out/'macro'/name)
    model = loaded[MASTER+'.v'].read_text()
    header, separator, _ = model.partition('// ---- Simulation-only check:')
    if not separator or header.count('module '+MASTER+' (') != 1:
        raise ValueError('Unrecognized pinned SRAM model header')
    (out/'macro'/(MASTER+'.bb.v')).write_text(header.replace('module '+MASTER, '(* blackbox *) module '+MASTER, 1)+'endmodule\n`endcelldefine\n')
    (out/'design.sv').write_text('\n'.join(source.read_text() for source in rtl))
    shutil.copyfile(template, out/template.name)
    shutil.copyfile(ROOT/'physical/chip.sdc', out/'core.sdc')
    helpers = ['pdn.tcl','librelane_plugin_buffered_tt.py','connect_sram_power.py']
    for name in helpers:
        shutil.copyfile(ROOT/'physical/buffered_tt'/name, out/name)
    write(out/'power-columns.json', plan)
    write(out/'macro-geometry.json', geometry)
    config = deepcopy(read(ROOT/'physical/chip.json'))
    config.update(DESIGN_NAME=TOP, VERILOG_FILES=['dir::design.sv'],
        PDN_MULTILAYER=False, PDN_CONNECT_MACROS_TO_GRID=True, PDN_CFG='dir::pdn.tcl',
        PDN_VWIDTH=2.1, PDN_VSPACING=3.52, PDN_VPITCH=44.96, PDN_VOFFSET=6.15,
        PDN_VERTICAL_LAYER='Metal4', PDN_EXTEND_TO='boundary', RUN_KLAYOUT_DRC=True,
        KLAYOUT_DRC_RUNSET='pdk_dir::libs.tech/klayout/tech/drc/ihp-sg13cmos5l.drc',
        RUN_MAGIC_DRC=True, ERROR_ON_ILLEGAL_OVERLAPS=True,
        meta={'flow':'Classic','substituting_steps':{'+OpenROAD.GeneratePDN':'Project.BufferedSramPower'}})
    config.pop('VERILOG_DEFINES', None)
    config['MACROS'] = {MASTER:config['MACROS'][MASTER]}
    config['PDN_MACRO_CONNECTIONS'] = [f'engine\\.memory\\.storage[01] VPWR VGND {pin} VSS!' for pin in ['VDD!', 'VDDARRAY!']]
    config['MACROS'][MASTER]['instances'] = deepcopy(PLACEMENTS)
    validate_flow_config(config)
    write(out/'core.json', config)
    sources = rtl+[Path(__file__).resolve(),ROOT/'scripts/buffered_tt_physical.py',ROOT/'scripts/run-buffered-tt-physical.py',
                   ROOT/'physical/chip.json',ROOT/'physical/chip.sdc',ROOT/'tools/physical-toolchain.json',
                   ROOT/'scripts/install-physical-pdk.py',ROOT/'scripts/run-physical.py']
    sources += [ROOT/'physical/buffered_tt'/name for name in helpers]
    inputs = dict(schema='pinwheel-buffered-tt-physical-input-v1', profile='buffered-tt',
        variant='two64x64-buffered-sram-serial', status='ready' if not missing else 'missing_macro_views',
        missing_macro_views=missing, validation_receipt=str(validation), validation_receipt_sha256=sha(validation),
        source_sha256={str(path.relative_to(ROOT)):sha(path) for path in sources},
        files_sha256={str(path.relative_to(out)):sha(path) for path in sorted(out.rglob('*')) if path.is_file()},
        template_sha256=sha(template), pdk_tree_sha256=sha(inventory), macro_view_git_blobs={Path(v).name:entries['ihp-sg13g2/libs.ref/sg13g2_sram/'+v]['sha'] for v in views},
        disabled_checks=['RUN_KLAYOUT_XOR'], pdn_status='designed_unvalidated',
        boundary='One 6x4 Tiny Tapeout wrapper baseline at 20 ns with 4/0.2 ns I/O budgets, two exact 64x64 macros and explicit Metal4 column extension. '
                 'No TopMetal power grid, false timing paths or Magic illegal-overlap waiver. KLayout DRC is enabled. '
                 'Fast screening combines -40 C logic and -55 C SRAM; it is not a matched-temperature signoff corner. '
                 'Physical success does not establish universal correctness, analog CDC, internal SRAM qualification or the separate official Tiny Tapeout precheck.')
    write(out/'inputs.json', inputs)
    print(out/'inputs.json')


if __name__ == '__main__':
    main()
