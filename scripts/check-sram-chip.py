#!/usr/bin/env python3
"""Compare complete SRAM chips with the FF chip; no place/route or timing claim.

Requires the pinned macro views and an installed physical PDK/tree inventory.
All input files are verified locally. This command does not download or install
PDK files, alter the physical flow, or promote an experimental backend.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import time

from chip_oracle import generate as chip_vectors
from sram_core_vectors import generate as core_vectors
from validation_run import Commands, fresh_directory, sha

ROOT = Path(__file__).resolve().parents[1]
VIEWS = ROOT/'build/storage/macros'
MACROS = dict(direct='RM_IHPSG13_1P_512x64_c2_bm_bist', hybrid='RM_IHPSG13_1P_64x64_c2_bm_bist')


def blob(data):
    return hashlib.sha1(f'blob {len(data)}\0'.encode()+data).hexdigest()


def compatibility(pdk, inventory, out):
    lock = json.loads((ROOT/'tools/physical-toolchain.json').read_text())
    if sha(inventory) != lock['pdk_tree_sha256']:
        raise RuntimeError('Unpinned physical PDK inventory')
    tree = json.loads(inventory.read_text())
    if tree['truncated'] or tree['sha'] != lock['pdk_revision']:
        raise RuntimeError('Incomplete or mismatched physical PDK inventory')
    entries = {e['path']: e for e in tree['tree']}
    manifest = json.loads((ROOT/'tools/storage-macros.json').read_text())
    verified = {}
    for rel, expected in manifest['files_sha256'].items():
        path = VIEWS/Path(rel).name
        key = 'ihp-sg13g2/libs.ref/sg13g2_sram/'+rel
        if sha(path) != expected or blob(path.read_bytes()) != entries[key]['sha']:
            raise RuntimeError(f'Macro view differs from pinned physical PDK: {rel}')
        verified[rel] = dict(sha256=expected, physical_pdk_blob=entries[key]['sha'])

    def installed(relative):
        path = pdk/relative
        # Resolve and verify symlinks as well as the final file against the tree.
        while path.is_symlink():
            target = str(path.readlink())
            if blob(target.encode()) != entries[str(path.relative_to(pdk))]['sha']:
                raise RuntimeError(f'Unpinned PDK symlink: {path}')
            path = (path.parent/target).resolve()
        if blob(path.read_bytes()) != entries[str(path.relative_to(pdk))]['sha']:
            raise RuntimeError(f'Unpinned installed PDK view: {path}')
        return path

    cell_prefix = 'ihp-sg13cmos5l/libs.ref/sg13cmos5l_stdcell/'
    cell_models = [installed(cell_prefix+'verilog/'+name) for name in
                   ['sg13cmos5l_stdcell.v', 'sg13cmos5l_udp.v']]
    technology = installed(cell_prefix+'lef/sg13cmos5l_tech.lef')
    tech_layers = set(re.findall(r'^LAYER\s+(\S+)', technology.read_text(), re.M))
    macros = {}
    for name in MACROS.values():
        lef = (VIEWS/(name+'.lef')).read_text()
        width, height = map(float, re.findall(r'\bSIZE\s+([\d.]+)\s+BY\s+([\d.]+)', lef)[0])
        layers = set(re.findall(r'\bLAYER\s+(\S+)', lef))
        routing_layers = {v for v in layers if v.startswith('Metal')}
        if not routing_layers <= tech_layers:
            raise RuntimeError(f'Macro uses unsupported routing layers: {name}')
        pins = re.findall(r'PIN (\S+)\s+DIRECTION INOUT\s*;\s+USE (POWER|GROUND)', lef)
        required = {}
        for rel in [f'gds/{name}.gds', f'cdl/{name}.cdl', f'lib/{name}_fast_1p32V_m55C.lib']:
            key = 'ihp-sg13g2/libs.ref/sg13g2_sram/'+rel
            required[rel] = dict(git_blob=entries[key]['sha'], bytes=entries[key]['size'],
                                 installed=(pdk/key).is_file())
        macros[name] = dict(width_um=width, height_um=height, footprint_um2=width*height,
                            lef_layers=sorted(layers), lef_power_pins=pins, additional_views=required)
    cell_lock = json.loads((ROOT/'tools/technology-library.json').read_text())
    cell_files = {}
    for item in cell_lock['files']:
        file = ROOT/'build/tools/ihp-cmos5l'/item['name']
        if sha(file) != item['sha256']: raise RuntimeError(f'Unpinned mapping library: {file}')
        if file.suffix == '.lib':
            physical = installed(cell_prefix+'lib/'+item['name'])
            if sha(physical) != item['sha256']: raise RuntimeError('Physical/mapping cell library mismatch')
            cell_files[item['name']] = item['sha256']
    result = dict(physical_pdk_revision=lock['pdk_revision'], inventory_sha256=sha(inventory),
                  study_library_revision=manifest['library_revision'], macro_views=verified,
                  mapping_libraries_identical_to_physical_pdk=cell_files, macros=macros,
                  cell_models_sha256={str(p.relative_to(pdk)):sha(p) for p in cell_models},
                  technology_lef_sha256=sha(technology),
                  boundary='Pinned source/view compatibility only. LEF power pins use ! suffixes; '
                           'Liberty power groups do not. Explicit VDD!/VDDARRAY!/VSS! connections, '
                           'macro halos/placement, GDS/CDL integration, full STA, DRC and LVS remain untested.')
    (out/'compatibility.json').write_text(json.dumps(result, indent=2)+'\n')
    return result, cell_models


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--tag', required=True)
    p.add_argument('--pdk-root', required=True, type=Path)
    p.add_argument('--pdk-tree', required=True, type=Path)
    args = p.parse_args()
    out = fresh_directory(ROOT/'build/storage/sram-chip', args.tag)
    started = time.monotonic()
    files = [*sorted((ROOT/'Pinwheel').rglob('*.lean')), ROOT/'Pinwheel.lean', ROOT/'lakefile.toml',
             ROOT/'lean-toolchain', *[ROOT/'test'/n for n in
             ['SramChipEmit.lean', 'ChipEmit.lean', 'Loader.lean', 'sram_chip.sv', 'sram_core_tb.sv', 'chip_tb.sv']],
             Path(__file__), *[ROOT/'scripts'/n for n in ['sram_core_vectors.py', 'chip_oracle.py', 'host_demo.py', 'pinwheel_host.py',
             'validation_run.py', 'process_group.py', 'loader-vectors.py', 'reactive-core-vectors.py',
             'execution-vectors.py', 'uart_rx_oracle.py']], *[ROOT/'tools'/n for n in
             ['physical-toolchain.json', 'technology-library.json', 'storage-macros.json', 'hardware-toolchain.json']]]
    sources = {str(f.relative_to(ROOT)): sha(f) for f in files}
    compatible, cell_models = compatibility(args.pdk_root.resolve(), args.pdk_tree, out)
    run = Commands(ROOT, out, default_timeout=600)
    run(['lake', 'build', 'Pinwheel', 'sram_chip_emit', 'chip_emit'], 'build')
    run(['lake', 'env', 'lean', '-DwarningAsError=true', '--run', 'test/Loader.lean'], 'compiler-images')
    run([ROOT/'.lake/build/bin/sram_chip_emit', out], 'emit-sram')
    run([ROOT/'.lake/build/bin/chip_emit', out/'baseline'], 'emit-baseline')
    coverage = dict(chip=chip_vectors(out), core=core_vectors(out))
    circt = ROOT/'build/tools/firtool-1.159.0/bin/circt-opt'
    cad = ROOT/'build/tools/oss-cad-suite/bin'
    versions = {name:run(argv, name+'-version').strip() for name, argv in
                [('circt', [circt, '--version']), ('yosys', [cad/'yosys', '-V'])]}
    tool_hashes = {str(f.relative_to(ROOT)):sha(f.resolve()) for f in
                   [circt, cad/'yosys', cad/'yosys-abc', cad/'iverilog', cad/'vvp']}
    wrapper = ROOT/'test/sram_chip.sv'
    results = {}
    for variant in ['direct', 'hybrid', 'ff']:
        target = out/variant
        target.mkdir()
        defines = ['-DSRAM_HYBRID'] if variant == 'hybrid' else []
        model = [VIEWS/(MACROS[variant]+'.v'), VIEWS/'RM_IHPSG13_1P_core_behavioral_bm_bist.v'] if variant != 'ff' else []
        artifacts = {}
        for kind in (['chip', 'core'] if variant != 'ff' else ['chip']):
            mlir = out/f'{variant}-{kind}.mlir' if variant != 'ff' else out/'baseline/chip-twoport-result.mlir'
            rtl = run([circt, mlir, '--canonicalize', '--lower-seq-to-sv', '--lower-hw-to-sv',
                       '--hw-legalize-modules', '--export-verilog', '-o', '/dev/null'], f'{variant}-{kind}-export')
            file = target/(kind+'.sv')
            file.write_text(rtl)
            artifacts[kind] = dict(mlir_sha256=sha(mlir), rtl_sha256=sha(file))

        def simulate(file, kind, label, binding=wrapper, cells=(), reject=None):
            tb = ROOT/'test'/('chip_tb.sv' if kind == 'chip' else 'sram_core_tb.sv')
            top = 'chip_tb' if kind == 'chip' else 'sram_core_tb'
            # Technology netlists already include the flattened macro binding.
            bindings = [binding] if variant != 'ff' and not cells else []
            run([cad/'iverilog', '-g2012', '-DFUNCTIONAL', *defines, '-s', top, '-o', target/(label+'.vvp'),
                 file, *bindings, tb, *model, *cells], f'{variant}-{label}-compile')
            vectors = out/('vectors.txt' if kind == 'chip' else 'core-vectors.txt')
            log = run([cad/'vvp', target/(label+'.vvp'), '+vectors='+str(vectors)],
                      f'{variant}-{label}', reject=reject)
            expected = f'Passed {coverage[kind]["edges"]} independent '+('whole-chip' if kind == 'chip' else 'SRAM core')+' edges'
            if not reject and expected not in log: raise RuntimeError('Incomplete simulation trace')

        simulate(target/'chip.sv', 'chip', 'rtl')
        if variant != 'ff':
            simulate(target/'core.sv', 'core', 'core-rtl')
            # These faults compile successfully and must fail the core oracle.
            mutant = target/'single-response.sv'
            mutant.write_text(wrapper.read_text().replace('.A_ADDR(mem_addr1[', '.A_ADDR(mem_addr0['))
            simulate(target/'core.sv', 'core', 'single-response', binding=mutant, reject='SRAM core state')
            mutant = target/'no-broadcast.sv'
            body = wrapper.read_text()
            before, after = body.split('`PINWHEEL_SRAM storage1 (', 1)
            mutant.write_text(before+'`PINWHEEL_SRAM storage1 ('+after.replace('.A_WEN(mem_write)', ".A_WEN(1'b0)", 1))
            simulate(target/'core.sv', 'core', 'no-broadcast', binding=mutant, reject='SRAM core state')
        (target/'abc.constr').write_text('set_driving_cell sg13cmos5l_buf_2\nset_load 10\n')
        metrics = {}
        for corner, suffix in [('typical', 'typ_1p20V_25C'), ('slow', 'slow_1p08V_125C')]:
            lib = ROOT/'build/tools/ihp-cmos5l'/f'sg13cmos5l_stdcell_{suffix}.lib'
            macro = VIEWS/f'{MACROS[variant]}_{suffix}.lib' if variant != 'ff' else None
            lines = [f'read_liberty -lib {lib}']
            if macro: lines += [f'read_liberty -lib {macro}']
            lines += [f'read_verilog -sv {" ".join(defines)} {target}/chip.sv'+(f' {wrapper}' if macro else ''),
                      'hierarchy -check -top tt_um_pinwheel', 'synth -top tt_um_pinwheel -flatten -noabc',
                      f'dfflibmap -liberty {lib}',
                      f'abc -liberty {lib} -constr {target}/abc.constr -D 10000', 'clean', 'check -assert',
                      f'stat -liberty {lib}'+(f' -liberty {macro}' if macro else ''),
                      f'write_json {target}/{corner}.json', f'write_verilog -noattr -noexpr {target}/{corner}.v']
            script = target/(corner+'.ys')
            script.write_text('\n'.join(lines)+'\n')
            log = run([cad/'yosys', '-Q', '-T', '-s', script], f'{variant}-{corner}-map')
            cells = json.loads((target/(corner+'.json')).read_text())['modules']['tt_um_pinwheel']['cells']
            macro_count = sum(c['type'].startswith('RM_IHPSG13_') for c in cells.values())
            if macro_count != (2 if macro else 0): raise RuntimeError('Wrong macro count after mapping')
            total = float(re.findall(r'Chip area for module.*?:\s*([\d.]+)', log)[-1])
            footprint = 2*compatible['macros'][MACROS[variant]]['footprint_um2'] if macro else 0
            metrics[corner] = dict(total_cell_and_macro_area_um2=total, macro_area_um2=footprint,
                                   standard_cell_area_um2=total-footprint, macros=macro_count,
                                   flip_flops=sum(c['type'].startswith('sg13cmos5l_df') for c in cells.values()),
                                   cells=len(cells), abc_combinational_delay_ps=float(re.findall(
                                       r'ABC(?: RESULTS)?:.*?Delay\s*=\s*([\d.]+)', log)[-1]),
                                   netlist_sha256=sha(target/(corner+'.v')))
            simulate(target/(corner+'.v'), 'chip', corner+'-gates', cells=cell_models)
        results[variant] = dict(artifacts=artifacts, metrics=metrics)
        print(variant, json.dumps(metrics), flush=True)
    for path in files:
        if sha(path) != sources[str(path.relative_to(ROOT))]: raise RuntimeError(f'Source changed during check: {path}')
    report = dict(variants=results, compatibility=compatible, source_sha256=sources, tools=versions,
                  tools_sha256=tool_hashes, coverage=coverage, commands=run.records,
                  vectors_sha256={name:sha(out/name) for name in ['vectors.txt', 'core-vectors.txt']},
                  elapsed_seconds=round(time.monotonic()-started, 3),
                  boundary='Independent full-chip RTL and both mapped-corner functional simulations; '
                           'separate core-edge stress and two negative controls for both SRAM organizations. '
                           'Full controller plus two physical macro footprints; no clock tree, placement '
                           'repair, routing whitespace or macro halos. ABC delay excludes synchronous '
                           'macro arcs and is not whole-chip timing. No new Lean SRAM refinement or physical closure.')
    (out/'report.json').write_text(json.dumps(report, indent=2)+'\n')
    print(out/'report.json')


if __name__ == '__main__':
    main()
