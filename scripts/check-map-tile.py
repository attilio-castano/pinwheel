#!/usr/bin/env python3
"""Prove and cost a local-decoding map tile and complete map-only composition.

Uses installed tools and pinned libraries. Each command is capped; no physical
flow or whole-chip implementation is launched. SAT checks expose every stored
bit as an arbitrary input and compare both outputs and every next-state bit.
"""
import argparse
from collections import Counter
from copy import deepcopy
import json
import math
from pathlib import Path
import re
import time

from validation_run import Commands, fresh_directory, sha
from map_distribution import BUFFER, boundary_loads, distribute

ROOT = Path(__file__).resolve().parents[1]
CAD = ROOT / 'build/tools/oss-cad-suite/bin'
CIRCT = ROOT / 'build/tools/firtool-1.159.0/bin/circt-opt'
FF = 'sg13cmos5l_dfrbpq_1'
TOPS = {'tile': 'pinwheel_map_tile', 'flat': 'pinwheel_map_flat', 'tiled': 'pinwheel_map_tiled'}
MAP_INPUTS = {'write_enable': 1, 'write_bank': 1, 'cursor': 9, 'write_data': 5,
              'read_bank': 1, 'pc0': 8, 'pc1': 8}
TILE_INPUTS = {'write_enable': 1, 'write_hi': 4, 'write_data': 5, 'read_hi0': 4, 'read_hi1': 4}


def validate_manifest(manifest):
    for key, expected in [('inputs', MAP_INPUTS), ('tile_inputs', TILE_INPUTS),
                          ('outputs', {'index0': 5, 'index1': 5})]:
        items = manifest[key]
        if len(items) != len(expected) or {x['name']: x['width'] for x in items} != expected:
            raise ValueError('Unexpected typed interface: ' + key)
    tiles = manifest['tiles']
    if len(tiles) != 32 or {(t['bank'], t['low']) for t in tiles} != {
            (b, k) for b in range(2) for k in range(16)}:
        raise ValueError('Incomplete or duplicate tile coordinates')
    for tile in tiles:
        b, low = tile['bank'], tile['low']
        if tile['name'] != f'tile_b{b}_l{low}' or tile['words'] != list(range(low, 256, 16)):
            raise ValueError('Tile coordinate/name mismatch')


def wrapper(manifest):
    """Only wire emitted interfaces; all decoder/mux logic comes from Lean."""
    def declaration(direction, item):
        return f"{direction} [{item['width'] - 1}:0] {item['name']}"
    ports = ['input clk'] + [declaration('input', p) for p in manifest['inputs']]
    ports += [declaration('output', p) for p in manifest['outputs']]
    lines = ['module pinwheel_map_tiled(' + ', '.join(ports) + ');']
    external = {p['name'] for p in manifest['inputs'] + manifest['outputs']}
    wires = {p['name']: p['width'] for p in manifest['glue_inputs'] + manifest['glue_outputs']}
    lines += [f'wire [{w-1}:0] {n};' for n, w in wires.items() if n not in external]
    glue_ports = manifest['glue_inputs'] + manifest['glue_outputs']
    lines.append('pinwheel_map_glue glue(' + ', '.join(f".{p['name']}({p['name']})" for p in glue_ports) + ');')
    for tile in manifest['tiles']:
        name = tile['name']
        connections = {'clk': 'clk', 'write_enable': name + '_enable',
                       'write_hi': 'write_hi', 'write_data': 'write_data',
                       'read_hi0': 'read_hi0', 'read_hi1': 'read_hi1',
                       'index0': name + '_index0', 'index1': name + '_index1'}
        lines.append(f'pinwheel_map_tile {name}(' + ', '.join(f'.{p}({n})' for p, n in connections.items()) + ');')
    return '\n'.join(lines + ['endmodule', ''])


def state_names(variant, manifest):
    """Canonical order is bank, logical word, bit; names come from typed emission."""
    if variant == 'tile':
        return [f'r_word{k}' for k in range(16)]
    if variant == 'flat':
        return [f'r_bank{b}_word{k}' for b in range(2) for k in range(256)]
    locations = {(t['bank'], word): f"{t['name']}.r_word{high}"
                 for t in manifest['tiles'] for high, word in enumerate(t['words'])}
    return [locations[b, k] for b in range(2) for k in range(256)]


def cut_state(module, variant, manifest):
    """Remove only validated positive-edge FFs, expose their exact Q and D pins."""
    cut = deepcopy(module)
    cut['attributes'] = {}
    expected = TILE_INPUTS if variant == 'tile' else MAP_INPUTS
    for name, width in {**expected, 'clk': 1, 'index0': 5, 'index1': 5}.items():
        port = cut['ports'].get(name, {})
        direction = 'output' if name.startswith('index') else 'input'
        if len(port.get('bits', [])) != width or port.get('direction') != direction:
            raise ValueError('Mapped interface mismatch: ' + name)
    if set(cut['ports']) != set(expected) | {'clk', 'index0', 'index1'}:
        raise ValueError('Unexpected port in state cut')
    clock = cut['ports']['clk']['bits']
    flops = {}
    for name, cell in list(cut['cells'].items()):
        kind, pins = cell['type'], cell['connections']
        if kind == '$scopeinfo':
            del cut['cells'][name]
            continue
        if kind not in ('$_DFF_P_', FF):
            if kind.startswith(('$_DFF', '$dff', 'sg13cmos5l_df')):
                raise ValueError('Unsupported state cell: ' + kind)
            continue
        required = {'D', 'Q', 'C'} if kind == '$_DFF_P_' else {'D', 'Q', 'CLK', 'RESET_B'}
        if set(pins) != required or any(len(bits) != 1 for bits in pins.values()):
            raise ValueError('Unsupported flop pins')
        if pins['C' if kind == '$_DFF_P_' else 'CLK'] != clock:
            raise ValueError('Unexpected state clock')
        if kind == FF and pins['RESET_B'] != ['1']:
            raise ValueError('Unexpected state reset')
        q, d = pins['Q'][0], pins['D'][0]
        if type(q) is not int or q in flops:
            raise ValueError('Duplicate or constant state')
        flops[q] = d
        del cut['cells'][name]
    state = []
    for name in state_names(variant, manifest):
        bits = cut['netnames'].get(name, {}).get('bits', [])
        if len(bits) != 5:
            raise ValueError('Missing typed state word: ' + name)
        state.extend(bits)
    if len(set(state)) != len(state) or set(state) != set(flops):
        raise ValueError('State projection is not an exact FF bijection')
    del cut['ports']['clk']
    cut['ports']['state'] = {'direction': 'input', 'bits': state}
    cut['ports']['next_state'] = {'direction': 'output', 'bits': [flops[q] for q in state]}
    return cut


def metrics(module, modules, variant, manifest):
    cut = cut_state(module, variant, manifest)
    cells = [c for c in module['cells'].values() if c['type'] != '$scopeinfo']
    areas = {}
    for cell in cells:
        kind = cell['type']
        area = float(modules[kind]['attributes']['area'])
        if not math.isfinite(area) or area <= 0:
            raise ValueError('Invalid library cell area')
        areas[kind] = area
    roots = {b for p in cut['ports'].values() if p['direction'] == 'input' for b in p['bits']}
    drivers, loads = {}, Counter()
    for name, cell in cut['cells'].items():
        if set(cell['connections']) != set(cell['port_directions']):
            raise ValueError('Missing cell directions')
        ins = [b for p, bits in cell['connections'].items() if cell['port_directions'][p] == 'input' for b in bits]
        loads.update(ins)
        for p, bits in cell['connections'].items():
            if cell['port_directions'][p] == 'output':
                for b in bits:
                    if b in roots or b in drivers or type(b) is not int:
                        raise ValueError('Multiple or invalid mapped drivers')
                    drivers[b] = ins
    depths, visiting = {}, set()
    def depth(bit):
        if bit in depths:
            return depths[bit]
        if bit in roots or bit in ('0', '1'):
            return 0
        if bit not in drivers or bit in visiting:
            raise ValueError('Undriven signal or combinational cycle')
        visiting.add(bit)
        value = 1 + max(map(depth, drivers[bit]), default=0)
        visiting.remove(bit)
        depths[bit] = value
        return value
    for b in drivers:
        depth(b)
    for p in cut['ports'].values():
        if p['direction'] == 'output':
            loads.update(p['bits'])
    counts = Counter(c['type'] for c in cells)
    return {'state_bits': len(cut['ports']['state']['bits']), 'cells': len(cells),
            'combinational_cells': len(cut['cells']), 'cell_types': dict(sorted(counts.items())),
            'area_um2': round(sum(areas[k] * n for k, n in counts.items()), 4),
            'logic_depth': {name: max(map(depth, cut['ports'][name]['bits']))
                            for name in ('index0', 'index1', 'next_state')},
            'maximum_signal_fanout': max((n for b, n in loads.items() if type(b) is int), default=0),
            'input_maximum_fanout': {p: max(loads[b] for b in port['bits'])
                                   for p, port in cut['ports'].items() if port['direction'] == 'input' and p != 'state'},
            'scope': 'Mapped cell area and conservative gate depth/pin fanout; clock excluded. No wire or timing model.'}


def write_json(path, value):
    path.write_text(json.dumps(value, indent=2) + '\n')


def yosys_command(run, out, label, lines, reject=None):
    script = out / (label + '.ys')
    script.write_text('\n'.join(map(str, lines)) + '\n')
    return run([CAD / 'yosys', '-Q', '-T', '-s', script], label, reject=reject)


def prove(run, out, manifest, path, variant, label, library=None, mutant=False, invert_buffer=None):
    data = json.loads(path.read_text())
    cut = cut_state(data['modules'][TOPS[variant]], variant, manifest)
    if mutant:
        cut['ports']['index1']['bits'] = cut['ports']['index0']['bits']
        cut['netnames']['index1']['bits'] = cut['ports']['index0']['bits']
    if invert_buffer is not None:
        cell = cut['cells'][invert_buffer]
        if cell['type'] != BUFFER or set(cell['connections']) != {'A', 'X'}:
            raise ValueError('Negative control must change an actual distribution buffer')
        cell['type'] = 'sg13cmos5l_inv_1'
        cell['connections']['Y'] = cell['connections'].pop('X')
        cell['port_directions']['Y'] = cell['port_directions'].pop('X')
    negative = mutant or invert_buffer is not None
    cut_path = out / (label + '-cut.json')
    write_json(cut_path, {'modules': {'dut': cut}})
    oracle = 'tile_oracle' if variant == 'tile' else 'map_oracle'
    lines = ([f'read_liberty -ignore_miss_func {library}'] if library else []) + [
        f'read_json {cut_path}', f'read_verilog -sv {ROOT}/test/map_tile_oracle.sv',
        'proc', f'miter -equiv -flatten -make_outputs {oracle} dut miter',
        'hierarchy -check -top miter', 'flatten', 'opt_clean',
        'sat -verify -prove trigger 0 -set-def-inputs miter']
    log = yosys_command(run, out, label, lines, reject='proof did fail' if negative else None)
    if not negative and 'SAT proof finished - no model found: SUCCESS!' not in log:
        raise ValueError('Incomplete SAT check')


def pinned_libraries():
    libraries = {}
    for item in json.loads((ROOT / 'tools/technology-library.json').read_text())['files']:
        path = ROOT / 'build/tools/ihp-cmos5l' / item['name']
        if sha(path) != item['sha256']:
            raise ValueError('Unpinned mapping library: ' + str(path))
        if path.suffix == '.lib':
            libraries['slow' if 'slow_' in path.name else 'typical'] = path
    if set(libraries) != {'typical', 'slow'}:
        raise ValueError('Missing mapped corner')
    return libraries


def load_baseline(selected_path):
    """Check the retained receipt and all artifacts before reusing mapped cells."""
    selected = json.loads(selected_path.read_text())
    path = ROOT / selected['report']
    if sha(path) != selected['report_sha256']:
        raise ValueError('Baseline report hash mismatch')
    report = json.loads(path.read_text())
    if report['status'] != 'passed' or report['variants'] != selected['variants']:
        raise ValueError('Baseline is not the selected passing comparison')
    # Only this checker is being extended. Hardware, emission, oracle, library
    # lock and every other original input must still match the proved baseline.
    for name, digest in report['inputs_sha256'].items():
        if name != 'scripts/check-map-tile.py' and sha(ROOT / name) != digest:
            raise ValueError('Changed baseline input: ' + name)
    for name, digest in report['artifacts_sha256'].items():
        if sha(path.parent / name) != digest:
            raise ValueError('Changed baseline artifact: ' + name)
    for name, digest in report['tools_sha256'].items():
        if sha(ROOT / name) != digest:
            raise ValueError('Changed baseline tool: ' + name)
    return path, report


def distribution_study(args):
    out = fresh_directory(ROOT / 'build/storage/map-tile', args.tag)
    started = time.monotonic()
    run = Commands(ROOT, out, default_timeout=180)
    report = {'schema': 1, 'status': 'running', 'commands': run.records}
    try:
        selected = args.distribute_from.resolve()
        baseline_path, baseline = load_baseline(selected)
        source = baseline_path.parent
        manifest = json.loads((source / 'manifest.json').read_text())
        validate_manifest(manifest)
        write_json(out / 'manifest.json', manifest)
        sources = set(baseline['inputs_sha256']) | {
            'scripts/map_distribution.py', 'test/test_map_distribution.py',
            str(selected.relative_to(ROOT)), str(baseline_path.relative_to(ROOT))}
        frozen = {p: sha(ROOT / p) for p in sorted(sources)}
        report.update(inputs_sha256=frozen, tools_sha256=baseline['tools_sha256'],
                      baseline={'selected': str(selected.relative_to(ROOT)), 'selected_sha256': sha(selected),
                                'report': str(baseline_path.relative_to(ROOT)), 'report_sha256': sha(baseline_path),
                                'verified_artifacts': len(baseline['artifacts_sha256']),
                                'source_exception': 'scripts/check-map-tile.py extended for distribution; current hash frozen'},
                      variants={})
        libraries = pinned_libraries()
        report['libraries_sha256'] = {k: sha(v) for k, v in libraries.items()}
        if report['libraries_sha256'] != baseline['libraries_sha256']:
            raise ValueError('Baseline library mismatch')
        banks = {t['name']: (t['bank'], t['low']) for t in manifest['tiles']}
        top = TOPS['tiled']
        for corner, library in libraries.items():
            original = json.loads((source / f'tiled-{corner}.json').read_text())
            instances = original['modules'][top]['cells']
            if {name: c['type'] for name, c in instances.items()} != {
                    **{name: TOPS['tile'] for name in banks}, 'glue': 'pinwheel_map_glue'}:
                raise ValueError('Unexpected baseline hierarchy')
            comparisons = {}
            for variant in ('flat', 'tiled'):
                saved = json.loads((source / f'{variant}-{corner}-readback.json').read_text())
                value = metrics(saved['modules'][TOPS[variant]], saved['modules'], variant, manifest)
                if any(value[k] != baseline['variants'][variant][corner][k] for k in value):
                    raise ValueError('Baseline metrics do not reproduce')
                comparisons[variant] = value
            candidate, distribution = distribute(original, top, banks, args.fanout_limit)
            if not distribution['added_buffers']:
                raise ValueError('No distribution change to measure')
            for name, module in original['modules'].items():
                if name != top and candidate['modules'][name] != module:
                    raise ValueError('Distribution changed a child or library')
            if any(net['loads'] > args.fanout_limit for net in boundary_loads(candidate['modules'], top)):
                raise ValueError('Distribution boundary still exceeds budget')
            prefix = 'distributed-' + corner
            mapped, flat = out / (prefix + '.json'), out / (prefix + '-flat.json')
            write_json(mapped, candidate)
            write_json(out / (prefix + '-trees.json'), distribution)
            yosys_command(run, out, prefix + '-export', [f'read_json {mapped}',
                f'hierarchy -check -top {top}', 'check -assert',
                f'write_verilog -noattr -noexpr {out}/{prefix}.v', 'flatten', 'clean', f'write_json {flat}'])
            data = json.loads(flat.read_text())
            value = metrics(data['modules'][top], data['modules'], 'tiled', manifest)
            back_path = out / (prefix + '-readback.json')
            yosys_command(run, out, prefix + '-readback', [f'read_liberty -lib {library}',
                f'read_verilog {out}/{prefix}.v', f'hierarchy -check -top {top}',
                'flatten', 'check -assert', f'write_json {back_path}'])
            back = json.loads(back_path.read_text())
            if metrics(back['modules'][top], back['modules'], 'tiled', manifest) != value:
                raise ValueError('Distributed Verilog read-back metrics disagree')
            count = distribution['added_buffers']
            expected_cells = Counter(comparisons['tiled']['cell_types']) + Counter({BUFFER: count})
            if value['cell_types'] != expected_cells or value['maximum_signal_fanout'] > args.fanout_limit:
                raise ValueError('Flattened cell census or fanout mismatch')
            if abs(value['area_um2'] - comparisons['tiled']['area_um2'] - distribution['added_area_um2']) > .001:
                raise ValueError('Added buffer area does not reconcile')
            prove(run, out, manifest, back_path, 'tiled', prefix + '-proof', library)
            if corner == 'typical':
                buffer = distribution['trees'][0]['buffers'][0]['cell']
                prove(run, out, manifest, back_path, 'tiled', 'inverted-buffer-negative', library, invert_buffer=buffer)
            report['variants'][corner] = {
                'baseline_flat': comparisons['flat'], 'baseline_tiled': comparisons['tiled'],
                'distributed': value, 'distribution': distribution,
                'remaining_area_advantage_um2': round(comparisons['flat']['area_um2'] - value['area_um2'], 4),
                'remaining_area_advantage_percent': round(100 * (1 - value['area_um2'] / comparisons['flat']['area_um2']), 6),
                'child_modules_unchanged': True, 'mapped_sha256': sha(mapped)}
        if any(sha(ROOT / p) != digest for p, digest in frozen.items()):
            raise ValueError('Source changed during distribution experiment')
        load_baseline(selected)
        report.update(status='passed', scope=(
            'Map-only buffer insertion into retained mapped hierarchy; all child modules unchanged. '
            'Independent arbitrary-state output/next-state SAT at both library corners and inverted-buffer rejection. '
            'Exact cell area, conservative gate depth and sink-pin budget. No new synthesis, whole-chip replacement, '
            'electrical timing, wire, power, placement or routing claim.'))
    except BaseException as error:
        report.update(status='failed', error=f'{type(error).__name__}: {error}')
        raise
    finally:
        report['elapsed_seconds'] = round(time.monotonic() - started, 3)
        report['artifacts_sha256'] = {p.name: sha(p) for p in sorted(out.iterdir())
                                     if p.is_file() and p.name != 'report.json'}
        write_json(out / 'report.json', report)
        print(out / 'report.json', flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--tag', required=True)
    parser.add_argument('--distribute-from', type=Path, help='Reuse a selected map-tile receipt; insert and check buffer distribution')
    parser.add_argument('--fanout-limit', type=int, default=10, help='Signal sink-pin budget for --distribute-from (default: 10)')
    args = parser.parse_args()
    if args.distribute_from:
        return distribution_study(args)
    if args.fanout_limit != 10:
        parser.error('--fanout-limit requires --distribute-from')
    out = fresh_directory(ROOT / 'build/storage/map-tile', args.tag)
    started = time.monotonic()
    sources = [*sorted((ROOT / 'Pinwheel').rglob('*.lean')), ROOT / 'Pinwheel.lean',
               ROOT / 'lakefile.toml', ROOT / 'lean-toolchain', ROOT / 'test/MapTileEmit.lean',
               ROOT / 'test/map_tile_oracle.sv', ROOT / 'test/test_map_tile.py', ROOT / 'tools/technology-library.json',
               Path(__file__), ROOT / 'scripts/map_distribution.py', ROOT / 'test/test_map_distribution.py',
               ROOT / 'scripts/validation_run.py', ROOT / 'scripts/process_group.py']
    frozen = {str(p.relative_to(ROOT)): sha(p) for p in sources}
    run = Commands(ROOT, out, default_timeout=180)
    report = {'schema': 1, 'inputs_sha256': frozen, 'commands': run.records, 'status': 'running'}
    def yosys(label, lines):
        return yosys_command(run, out, label, lines)
    try:
        run(['lake', 'build', 'Pinwheel', 'map_tile_emit'], 'build')
        run(['lake', 'env', 'lean', '-DwarningAsError=true', 'test/ProofAudit.lean'], 'axioms')
        run([ROOT / '.lake/build/bin/map_tile_emit', out], 'emit')
        manifest = json.loads((out / 'manifest.json').read_text())
        validate_manifest(manifest)
        for part in ('tile', 'flat', 'glue'):
            rtl = run([CIRCT, out / (part + '.mlir'), '--canonicalize', '--lower-seq-to-sv',
                       '--lower-hw-to-sv', '--hw-legalize-modules', '--export-verilog', '-o', '/dev/null'], part + '-export')
            (out / (part + '.sv')).write_text(rtl)
        (out / 'tiled.sv').write_text(wrapper(manifest))
        (out / 'abc.constr').write_text('set_driving_cell sg13cmos5l_buf_2\nset_load 10\n')
        report['tools_sha256'] = {str(p.relative_to(ROOT)): sha(p.resolve())
                                  for p in [CIRCT, CAD / 'yosys', CAD / 'yosys-abc']}
        libraries = pinned_libraries()
        report['libraries_sha256'] = {k: sha(v) for k, v in libraries.items()}
        report['variants'] = {}

        for variant, top in TOPS.items():
            files = [out / (variant + '.sv')] if variant != 'tiled' else [out / (p + '.sv') for p in ('tiled', 'tile', 'glue')]
            read = 'read_verilog -sv ' + ' '.join(map(str, files))
            generic = out / (variant + '-generic.json')
            yosys(variant + '-generic', [read, f'synth -top {top} -flatten -noabc',
                                         'dffunmap', 'clean', 'check -assert', f'write_json {generic}'])
            prove(run, out, manifest, generic, variant, variant + '-rtl-proof')
            if variant == 'tile':
                prove(run, out, manifest, generic, variant, 'swapped-reader-negative', mutant=True)
            corners = {}
            for corner, lib in libraries.items():
                prefix = variant + '-' + corner
                mapped, flat = out / (prefix + '.json'), out / (prefix + '-flat.json')
                log = yosys(prefix + '-map', [f'read_liberty -lib {lib}', read,
                    f'synth -top {top} -noabc', f'dfflibmap -liberty {lib}',
                    f'abc -liberty {lib} -constr {out}/abc.constr -D 10000',
                    'clean', 'check -assert', f'stat -liberty {lib}',
                    f'write_json {mapped}', f'write_verilog -noattr -noexpr {out}/{prefix}.v',
                    'flatten', 'clean', f'write_json {flat}'])
                data = json.loads(flat.read_text())
                result = metrics(data['modules'][top], data['modules'], variant, manifest)
                readback = out / (prefix + '-readback.json')
                yosys(prefix + '-readback', [f'read_liberty -lib {lib}',
                    f'read_verilog {out}/{prefix}.v', f'hierarchy -check -top {top}',
                    'flatten', 'check -assert', f'write_json {readback}'])
                back = json.loads(readback.read_text())
                if metrics(back['modules'][top], back['modules'], variant, manifest) != result:
                    raise ValueError('Mapped Verilog read-back metrics disagree')
                result['abc_module_delays_ps'] = list(map(float, re.findall(r'ABC(?: RESULTS)?:.*?Delay\s*=\s*([\d.]+)', log)))
                result['mapped_sha256'] = sha(mapped)
                if variant == 'tiled':
                    hierarchy = json.loads(mapped.read_text())['modules']
                    instances = hierarchy[top]['cells']
                    tile_instances = [c for c in instances.values() if c['type'] == TOPS['tile']]
                    if len(tile_instances) != 32 or Counter(c['type'] for c in instances.values()) != {
                            TOPS['tile']: 32, 'pinwheel_map_glue': 1}:
                        raise ValueError('Tile hierarchy did not survive mapping')
                    boundary = {b for c in tile_instances for p, bits in c['connections'].items() if p != 'clk' for b in bits}
                    if any(type(b) is not int for b in boundary):
                        raise ValueError('Constant on intended tile boundary')
                    areas = {name: round(sum(float(hierarchy[c['type']]['attributes']['area'])
                                             for c in hierarchy[name]['cells'].values()), 4)
                             for name in (TOPS['tile'], 'pinwheel_map_glue')}
                    if abs(result['area_um2'] - (32 * areas[TOPS['tile']] + areas['pinwheel_map_glue'])) > .01:
                        raise ValueError('Hierarchy area does not reconcile')
                    result['composition'] = {'tiles': 32, 'tile_area_um2': areas[TOPS['tile']],
                                              'glue_area_um2': areas['pinwheel_map_glue'],
                                              'unique_tile_boundary_nets': len(boundary)}
                prove(run, out, manifest, readback, variant, prefix + '-mapped-proof', lib)
                corners[corner] = result
            report['variants'][variant] = corners
        if any(sha(ROOT / p) != value for p, value in frozen.items()):
            raise ValueError('Source changed during experiment')
        report['status'] = 'passed'
        report['scope'] = ('Lean tile/controller correspondence; independent arbitrary-state two-valued RTL and mapped-cell '
                           'next-state/output SAT checks; map-only hierarchy and area/depth/fanout comparison. '
                           'No chip replacement, extracted timing, placement, routing or silicon claim.')
    except BaseException as error:
        report.update(status='failed', error=f'{type(error).__name__}: {error}')
        raise
    finally:
        report['elapsed_seconds'] = round(time.monotonic() - started, 3)
        report['artifacts_sha256'] = {p.name: sha(p) for p in sorted(out.iterdir())
                                     if p.is_file() and p.name != 'report.json'}
        write_json(out / 'report.json', report)
        print(out / 'report.json', flush=True)


if __name__ == '__main__':
    main()
