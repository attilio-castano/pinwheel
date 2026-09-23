"""Typed wrappers, state projections and cost checks for the tiled chip study."""
from collections import Counter
from copy import deepcopy
import math

FF = 'sg13cmos5l_dfrbpq_1'
MACRO = 'RM_IHPSG13_1P_64x64_c2_bm_bist'


def controller_wrapper(part, description, map_manifest):
    def port(direction, p):
        return f"{direction} [{p['width']-1}:0] {p['name']}"
    name = 'pinwheel_sram_controller' if part == 'chip' else 'pinwheel_sram_core_controller'
    ports = ['input clk'] + [port('input', p) for p in description['inputs']]
    ports += [port('output', p) for p in description['outputs']]
    lines = [f'module {name}(' + ', '.join(ports) + ');']
    for p in map_manifest['inputs'] + map_manifest['outputs']:
        lines.append(f"wire [{p['width']-1}:0] map_{p['name']};")
    lines.append(f'pinwheel_tiled_{part}_logic engine (.*);')
    pins = ['.clk(clk)'] + [f".{p['name']}(map_{p['name']})" for p in map_manifest['inputs'] + map_manifest['outputs']]
    lines.append('pinwheel_map_tiled map (' + ', '.join(pins) + ');')
    return '\n'.join(lines + ['endmodule', ''])


def signal(module, name, width):
    bits = module.get('netnames', {}).get(name, {}).get('bits')
    if bits is None or len(bits) != width:
        raise ValueError('Missing or wrong-width named signal: ' + name)
    return bits


def macro_binding(module):
    """Check every functional/control terminal against the unchanged binding."""
    macros = {n: c for n, c in module['cells'].items() if c['type'].startswith('RM_IHPSG13_')}
    if set(macros) != {'memory.storage0', 'memory.storage1'}:
        raise ValueError('Expected exactly the two retained SRAM copies')
    for b in range(2):
        cell = macros[f'memory.storage{b}']
        address = signal(module, f'controller.mem_addr{b}', 9)
        if address[6:] != ['0'] * 3 or cell['type'] != MACRO:
            raise ValueError('Changed SRAM type or address truncation')
        expected = {'A_CLK': module['ports']['clk']['bits'], 'A_MEN': ['1'], 'A_DLY': ['1'],
                    'A_ADDR': address[:6], 'A_DIN': signal(module, 'controller.mem_data', 64),
                    'A_DOUT': signal(module, f'controller.mem_q{b}', 64),
                    'A_WEN': signal(module, 'controller.mem_write', 1),
                    'A_REN': signal(module, 'controller.mem_read', 1), 'A_BM': ['1'] * 64,
                    'A_BIST_CLK': ['0'], 'A_BIST_EN': ['0'], 'A_BIST_MEN': ['0'],
                    'A_BIST_WEN': ['0'], 'A_BIST_REN': ['0'], 'A_BIST_ADDR': ['0'] * 6,
                    'A_BIST_DIN': ['0'] * 64, 'A_BIST_BM': ['0'] * 64}
        if cell['connections'] != expected or cell['port_directions'] != {
                p: 'output' if p == 'A_DOUT' else 'input' for p in expected}:
            raise ValueError('Changed macro terminal: ' + f'memory.storage{b}')
    return macros


def state_cut(module, description, candidate, package=False):
    """Expose all named logical state, including bits derived from stored bits.

    Named bits with no driver, pin use or external port are explicitly recorded
    as pruned state. Derived bits must be functions solely of FF Q/constants;
    clone that function with D substituted for Q to observe its next value.
    Every physical FF has exactly one named position. No initial-state assumptions.
    """
    cut = deepcopy(module)
    cut['attributes'] = {}
    prefix = 'controller.' if package else ''
    macros = macro_binding(module) if package else {}
    clock = module['ports']['clk']['bits']
    flops = {}
    for name, cell in list(cut['cells'].items()):
        kind, pins = cell['type'], cell['connections']
        if name in macros or kind == '$scopeinfo':
            del cut['cells'][name]
            continue
        if kind not in (FF, '$_DFF_P_'):
            if kind.startswith(('sg13cmos5l_df', '$_DFF', '$dff')):
                raise ValueError('Unsupported state cell: ' + kind)
            continue
        required = {'CLK', 'D', 'Q', 'RESET_B'} if kind == FF else {'C', 'D', 'Q'}
        if set(pins) != required or any(len(bs) != 1 for bs in pins.values()):
            raise ValueError('Unexpected FF ports')
        if pins['CLK' if kind == FF else 'C'] != clock or (kind == FF and pins['RESET_B'] != ['1']):
            raise ValueError('Changed state clock/reset')
        q = pins['Q'][0]
        if type(q) is not int or q in flops:
            raise ValueError('Aliased or constant FF Q')
        flops[q] = pins['D'][0]
        del cut['cells'][name]
    ports = {}
    for direction, group in [('input', 'inputs'), ('output', 'outputs')]:
        for p in description[group]:
            if p['name'] in ports:
                raise ValueError('Duplicate controller port')
            ports[p['name']] = {'direction': direction,
                               'bits': signal(module, prefix + p['name'], p['width'])}
    macro_ports = {'mem_q0', 'mem_q1', 'mem_addr0', 'mem_addr1', 'mem_data', 'mem_write', 'mem_read'}
    external = set(ports) - (macro_ports if package else set())
    if set(module['ports']) != external | {'clk'} or any(
            module['ports'][p] != ports[p] for p in external):
        raise ValueError('Controller interface does not match actual external ports')
    cut['ports'] = ports
    slots = description['registers']
    names = [s['name' if candidate else 'reference'] for s in slots]
    if len(set(names)) != len(names) or any(type(s['width']) is not int or s['width'] <= 0 for s in slots):
        raise ValueError('Duplicate or invalid state projection')
    bits = [b for slot, name in zip(slots, names)
            for b in signal(module, prefix + name, slot['width'])]
    named_q = [b for b in bits if b in flops]
    if len(named_q) != len(set(named_q)) or set(named_q) != set(flops):
        raise ValueError('State projection is not an exact physical FF bijection')
    connected = {b for c in module['cells'].values() for bs in c['connections'].values() for b in bs}
    connected.update(b for p in module['ports'].values() for b in p['bits'])
    dead = {b for b in bits if type(b) is int and b not in connected}
    drivers = {}
    for name, cell in cut['cells'].items():
        for p, bs in cell['connections'].items():
            if cell['port_directions'][p] == 'output':
                for bit in bs:
                    if type(bit) is not int or bit in drivers or bit in flops:
                        raise ValueError('Invalid combinational state driver')
                    drivers[bit] = (name, cell)
    all_bits = [b for n in module['netnames'].values() for b in n['bits'] if type(b) is int]
    all_bits += [b for c in module['cells'].values() for bs in c['connections'].values() for b in bs if type(b) is int]
    next_free = max(all_bits, default=1) + 1
    cloned, visiting = {}, set()

    def after(bit):
        nonlocal next_free
        if bit in flops:
            return flops[bit]
        if bit in dead:
            return '0'
        if bit in ('0', '1'):
            return bit
        if bit in cloned:
            return cloned[bit]
        if bit in visiting or bit not in drivers:
            raise ValueError('Derived state depends on an input, unknown value or cycle')
        visiting.add(bit)
        name, original = drivers[bit]
        cell = deepcopy(original)
        if any(len(bs) != 1 for p, bs in cell['connections'].items() if cell['port_directions'][p] == 'output'):
            raise ValueError('Unsupported multi-bit derived-state gate')
        for p, bs in original['connections'].items():
            if cell['port_directions'][p] == 'input':
                cell['connections'][p] = [after(b) for b in bs]
        for p, bs in original['connections'].items():
            if cell['port_directions'][p] == 'output':
                cloned[bs[0]] = next_free
                cell['connections'][p] = [next_free]
                next_free += 1
        clone_name = 'state_projection_' + name
        if clone_name in cut['cells'] or clone_name in cut['netnames']:
            raise ValueError('Reserved state projection name collision')
        cut['cells'][clone_name] = cell
        visiting.remove(bit)
        return cloned[bit]

    next_state = [after(b) for b in bits]
    state = []
    for b in bits:
        if b in flops:
            state.append(b)
        else:
            state.append(next_free)
            next_free += 1
    for name, direction, bs in [('state', 'input', state), ('next_state', 'output', next_state)]:
        if name in cut['ports'] or name in cut['netnames']:
            raise ValueError('Reserved state port collision')
        cut['ports'][name] = {'direction': direction, 'bits': bs}
        cut['netnames'][name] = {'hide_name': 0, 'bits': bs, 'attributes': {}}
    return cut, {'logical_state_bits': len(bits), 'physical_flip_flops': len(flops),
                 'pruned_state_positions': [k for k, b in enumerate(bits) if b in dead],
                 'derived_or_constant_state_bits': len(bits) - len(flops) - sum(b in dead for b in bits)}


def project_pruned_state(reference, candidate, projection, expected_pruned):
    """Compare all outputs and surviving state to arbitrary-state reference RTL.

    The independently mapped baseline and candidate must prune the same slots.
    Only next values of those absent slots are omitted. Reference current-state
    inputs remain arbitrary: SAT must prove they cannot affect any observation
    or surviving next-state bit. No reset/reachability assumption is introduced.
    """
    positions = projection['pruned_state_positions']
    width = len(reference['ports']['state']['bits'])
    if positions != expected_pruned or len(set(positions)) != len(positions) or any(
            type(k) is not int or not 0 <= k < width for k in positions):
        raise ValueError('State pruning differs from the mapped reference')
    if projection['logical_state_bits'] != width or any(
            len(cut['ports'][p]['bits']) != width
            for cut in (reference, candidate) for p in ('state', 'next_state')):
        raise ValueError('State projection widths disagree')
    used = {b for cell in candidate['cells'].values() for bs in cell['connections'].values() for b in bs}
    used.update(b for p in candidate['ports'].values() if p['direction'] == 'output' for b in p['bits'])
    for k in positions:
        if candidate['ports']['next_state']['bits'][k] != '0' or candidate['ports']['state']['bits'][k] in used:
            raise ValueError('Pruned state still has a use')
    result = deepcopy(reference)
    bits = list(result['ports']['next_state']['bits'])
    for k in positions:
        bits[k] = '0'
    result['ports']['next_state']['bits'] = bits
    result['netnames']['next_state']['bits'] = bits
    return result


def chip_metrics(data):
    module = data['modules']['tt_um_pinwheel']
    macros = macro_binding(module)
    cells = {n: c for n, c in module['cells'].items() if c['type'] != '$scopeinfo'}
    roots = {b for p in module['ports'].values() if p['direction'] == 'input' for b in p['bits']}
    loads, counts = Counter(), Counter(c['type'] for c in cells.values())
    drivers, next_bits = {}, []
    for name, c in cells.items():
        if set(c['connections']) != set(c['port_directions']):
            raise ValueError('Missing cell directions')
        ins = [b for p, bs in c['connections'].items() if c['port_directions'][p] == 'input'
               and p not in ('CLK', 'A_CLK', 'A_BIST_CLK') for b in bs]
        outs = [b for p, bs in c['connections'].items() if c['port_directions'][p] == 'output' for b in bs]
        loads.update(ins)
        if c['type'] == FF or name in macros:
            if any(b in roots for b in outs):
                raise ValueError('Multiple state roots')
            roots.update(outs)
            if c['type'] == FF:
                next_bits.extend(c['connections']['D'])
        else:
            for b in outs:
                if type(b) is not int or b in drivers:
                    raise ValueError('Invalid mapped driver')
                drivers[b] = ins
    if set(drivers) & roots:
        raise ValueError('Combinational gate drives a state/input root')
    depths, visiting = {}, set()

    def depth(bit):
        if bit in depths:
            return depths[bit]
        if bit in roots or bit in ('0', '1'):
            return 0
        if bit in visiting or bit not in drivers:
            raise ValueError('Undriven signal or combinational cycle')
        visiting.add(bit)
        depths[bit] = 1 + max(map(depth, drivers[bit]), default=0)
        visiting.remove(bit)
        return depths[bit]

    for bit in drivers:
        depth(bit)
    outputs = {p: v['bits'] for p, v in module['ports'].items() if v['direction'] == 'output'}
    for bs in outputs.values():
        loads.update(bs)
    areas = {kind: float(data['modules'][kind]['attributes']['area']) for kind in counts}
    if any(not math.isfinite(a) or a <= 0 for a in areas.values()):
        raise ValueError('Invalid library area')
    return {'cells': len(cells), 'flip_flops': counts[FF], 'macros': len(macros),
            'combinational_cells': len(cells) - counts[FF] - len(macros), 'cell_types': dict(sorted(counts.items())),
            'standard_cell_area_um2': round(sum(areas[k] * n for k, n in counts.items() if k != MACRO), 4),
            'macro_area_um2': round(areas[MACRO] * counts[MACRO], 4),
            'total_cell_and_macro_area_um2': round(sum(areas[k] * n for k, n in counts.items()), 4),
            'maximum_signal_fanout': max(n for b, n in loads.items() if type(b) is int),
            'macro_address_depth': {name: max(map(depth, cell['connections']['A_ADDR'])) for name, cell in macros.items()},
            'package_output_depth': {p: max(map(depth, bs)) for p, bs in outputs.items()},
            'next_state_depth': max(map(depth, next_bits)),
            'scope': 'Complete mapped chip cell area, conservative gate depth and sink count. Clock excluded; no electrical or wire timing model.'}
