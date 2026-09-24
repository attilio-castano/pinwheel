"""Cost map slices using typed state coordinates and existing mapped connectivity.

This is a partition of an unchanged circuit, not a memory implementation or
placer. Data support includes every cell input; control is absorbed only when
all of its consumers already belong to the same slice.
"""
from collections import Counter, defaultdict
from functools import lru_cache
import math

from chip_organization import mapped_members


def map_coordinates(graph, assembly):
    coordinates, words = {}, {}
    for slot in assembly['registers']:
        location = slot.get('index_location')
        if slot['owner'] != 'index_maps':
            if location is not None:
                raise ValueError('Map coordinates on non-map state')
            continue
        if not isinstance(location, dict) or set(location) != {'bank', 'word'}:
            raise ValueError('Missing typed map coordinates')
        bank, word = location['bank'], location['word']
        if type(bank) is not int or bank not in (0, 1) or type(word) is not int or not 0 <= word < 256:
            raise ValueError('Invalid map coordinate')
        if (bank, word) in words:
            raise ValueError('Duplicate map coordinate')
        bits = graph.registers[slot['name']][1]
        words[bank, word] = bits
        for position, bit in enumerate(bits):
            if type(bit) is not int or bit in coordinates or graph.root_groups.get(bit) != 'index_maps':
                raise ValueError('Aliased or unmapped index bit')
            coordinates[bit] = bank, word, position
    if not words or len({len(bits) for bits in words.values()}) != 1:
        raise ValueError('Missing or inconsistent map words')
    size = max(word for _, word in words) + 1
    if size & (size-1) or set(words) != {(bank, word) for bank in (0, 1) for word in range(size)}:
        raise ValueError('Incomplete atomic map banks')
    return coordinates, size, len(next(iter(words.values())))


def cell_areas(modules, graph):
    """Read retained Liberty area attributes; the caller reconciles their total."""
    areas = {}
    for name, cell in graph.cells.items():
        if name in graph.macros:
            continue
        try:
            area = float(modules[cell['type']]['attributes']['area'])
        except (KeyError, TypeError, ValueError) as error:
            raise ValueError('Missing mapped cell area: ' + cell['type']) from error
        if not math.isfinite(area) or area <= 0:
            raise ValueError('Invalid mapped cell area')
        areas[name] = area
    return areas


def readback_view(report):
    """Compare costs and boundary signals without automatic cell/net names."""
    result = {}
    for kind in ('planes', 'word_tiles', 'read_tree_tiles'):
        item = report[kind]
        selected = item['selected']
        result[kind] = {'groups': item['groups'],
                        'unique_slice_crossing_nets': item['unique_slice_crossing_nets'],
                        'selected_group': selected['group'], 'state_bits': selected['state_bits'],
                        'roles': selected['roles'], 'incoming_roles': selected['incoming_roles'],
                        'incoming_broadcast_groups': selected['incoming_broadcast_groups'],
                        'input_signatures': sorted((b['signature'], b['roles'], b['receiving_groups'],
                                                    b['selected_sink_pins'], b['total_sink_pins'])
                                                   for b in selected['boundary_inputs']),
                        'output_signatures': sorted((b['signature'], b['roles'], b['outside_sink_pins'])
                                                    for b in selected['boundary_outputs'])}
    return result


def map_slice_report(graph, assembly, areas, selected_bit=0, tile_words=16):
    coordinates, bank_words, width = map_coordinates(graph, assembly)
    if type(selected_bit) is not int or not 0 <= selected_bit < width:
        raise ValueError('Invalid map bit selection')
    if type(tile_words) is not int or tile_words <= 0 or tile_words & (tile_words-1) or bank_words % tile_words:
        raise ValueError('Tile size must divide each map bank and be a power of two')
    if len(graph.macros) != 2 or any(len(c['connections']['A_ADDR']) != width+1 for c in graph.macros.values()):
        raise ValueError('Map slices require two index-plus-bank address ports')
    if set(areas) != set(graph.flops) | set(graph.comb):
        raise ValueError('Incomplete standard-cell area census')
    ff_for_q = {c['connections']['Q'][0]: n for n, c in graph.flops.items()}
    if not coordinates.keys() <= ff_for_q.keys():
        raise ValueError('Map state is not implemented by flip-flops')
    root_masks = {bit: 1 << index for index, bit in enumerate(sorted(coordinates))}

    @lru_cache(None)
    def support(bit):
        if isinstance(bit, str) or bit in graph.roots:
            return root_masks.get(bit, 0)
        name = graph.drivers[bit][0]
        result = 0
        for bits in graph.inputs(graph.comb[name]).values():
            for source in bits:
                result |= support(source)
        return result

    cell_support = {name: 0 for name in graph.comb}
    for bit, (name, _, _) in graph.drivers.items():
        cell_support[name] |= support(bit)
    # Check the slice interpretation rather than presuming bit independence.
    for q in coordinates:
        if support(graph.flops[ff_for_q[q]]['connections']['D'][0]) & ~root_masks[q]:
            raise ValueError('Map update depends on another stored map bit')
    for macro in graph.macros.values():
        for position, bit in enumerate(macro['connections']['A_ADDR'][:width]):
            expected = sum(root_masks[q] for q, (_, _, k) in coordinates.items() if k == position)
            if support(bit) != expected:
                raise ValueError('Address bit does not select exactly its stored map plane')

    # Every combinational consumer has greater depth than its producers.
    cell_depth = defaultdict(int)
    for bit, (name, _, _) in graph.drivers.items():
        cell_depth[name] = max(cell_depth[name], graph.depths[bit])
    reverse_order = sorted(graph.comb, key=lambda n: (-cell_depth[n], n))
    cell_loads = defaultdict(list)
    for bit, (name, _, _) in graph.drivers.items():
        cell_loads[name].extend(graph.loads[bit])
    clocks = set(graph.module['ports']['clk']['bits'])

    def partition(group_for_coordinate, selected, read_positions):
        q_groups = {q: group_for_coordinate(c) for q, c in coordinates.items()}
        group_masks = defaultdict(int)
        for q, group in q_groups.items():
            group_masks[group] |= root_masks[q]
        groups = {name: q_groups.get(c['connections']['Q'][0], 'other')
                  for name, c in graph.flops.items()}
        groups.update({name: 'other' for name in graph.macros})
        for name, mask in cell_support.items():
            if mask:
                owners = [g for g, roots in group_masks.items() if mask & roots]
                groups[name] = owners[0] if len(owners) == 1 else 'shared'
        for name in reverse_order:
            if cell_support[name]:
                continue
            destinations = {groups.get(n, 'other') if pin not in ('CLK', 'RESET_B') else 'other'
                            for n, pin in cell_loads[name]}
            groups[name] = next(iter(destinations)) if len(destinations) == 1 and destinations <= group_masks.keys() else 'other'
        # Label the required support that remains outside the slices separately.
        supporting = set()
        endpoints = [b for macro in graph.macros.values() for b in macro['connections']['A_ADDR'][:width]]
        endpoints += [graph.flops[ff_for_q[q]]['connections']['D'][0] for q in coordinates]
        supporting.update(mapped_members(graph, endpoints))
        for name in supporting:
            if groups[name] == 'other':
                groups[name] = 'shared'
        budgets = {g: {'flip_flops': 0, 'combinational_cells': 0, 'area_um2': 0.0}
                   for g in [*sorted(group_masks), 'shared', 'other']}
        for name, area in areas.items():
            budget = budgets[groups[name]]
            budget['flip_flops' if name in graph.flops else 'combinational_cells'] += 1
            budget['area_um2'] += area
        for budget in budgets.values():
            budget['area_um2'] = round(budget['area_um2'], 4)
        incoming, outgoing, internal = defaultdict(list), defaultdict(list), defaultdict(list)
        crossing_bits = set()
        selected_roots = {q for q, g in q_groups.items() if g == selected}
        selected_ffs = {ff_for_q[q] for q in selected_roots}
        role_cones = {'update': mapped_members(graph, [graph.flops[n]['connections']['D'][0] for n in selected_ffs])}
        for index, (name, macro) in enumerate(sorted(graph.macros.items())):
            role_cones[f'read{index}'] = mapped_members(graph, [macro['connections']['A_ADDR'][k] for k in read_positions])
        boundary, outputs = [], []
        role_counts, output_roles, broadcasts = Counter(), Counter(), Counter()
        macro_roles = {name: f'read{k}' for k, name in enumerate(sorted(graph.macros))}
        for bit, loads in sorted(graph.loads.items(), key=lambda item: str(item[0])):
            if type(bit) is not int or bit in clocks:
                continue
            producer = graph.drivers[bit][0] if bit in graph.drivers else ff_for_q.get(bit)
            source = groups.get(producer, 'external')
            destinations = Counter(groups.get(n, 'external') for n, _ in loads)
            touched = ({source} | destinations.keys()) & group_masks.keys()
            for group in touched:
                if source != group and group in destinations:
                    incoming[group].append(bit)
                if source == group and destinations.keys() - {group}:
                    outgoing[group].append(bit)
                if source == group and destinations.keys() <= {group}:
                    internal[group].append(bit)
            if touched and (destinations.keys() - {source}):
                crossing_bits.add(bit)
            if source != selected and selected in destinations:
                selected_loads = [(n, p) for n, p in loads if groups.get(n) == selected]
                roles = set()
                for name, pin in selected_loads:
                    if name in selected_ffs:
                        roles.add('reset' if pin == 'RESET_B' else 'update')
                    else:
                        roles.update(role for role, cone in role_cones.items() if name in cone)
                role_counts['+'.join(sorted(roles))] += 1
                receivers = sorted(destinations.keys() & group_masks.keys())
                broadcasts[len(receivers)] += 1
                boundary.append({'bit': bit, 'signature': graph.signature(bit), 'source_group': source,
                                 'roles': sorted(roles), 'receiving_groups': receivers,
                                 'selected_sink_pins': len(selected_loads), 'total_sink_pins': len(loads),
                                 'state_aliases': graph.aliases[bit]})
            if source == selected and destinations.keys() - {selected}:
                outside = [(n, p) for n, p in loads if groups.get(n) != selected]
                roles = {role for name, _ in outside for role, cone in role_cones.items() if name in cone}
                roles.update(macro_roles[n] for n, pin in outside if n in macro_roles and pin == 'A_ADDR')
                output_roles['+'.join(sorted(roles)) or 'other'] += 1
                outputs.append({'bit': bit, 'signature': graph.signature(bit), 'roles': sorted(roles),
                                'outside_sink_pins': len(outside), 'state_aliases': graph.aliases[bit]})
        for group in group_masks:
            budgets[group].update(incoming_nets=len(incoming[group]), outgoing_nets=len(outgoing[group]),
                                 internal_nets=len(internal[group]))
        selected_cells = {n for n, group in groups.items() if group == selected}
        private_comb = selected_cells & graph.comb.keys()
        role_summary = {role: {'full_cone_cells': len(cone), 'owned_cells': len(cone & private_comb),
                               'support_outside_slice': len(cone - private_comb)}
                        for role, cone in role_cones.items()}
        return {'groups': budgets, 'unique_slice_crossing_nets': len(crossing_bits),
                'selected': {'group': selected, 'cells': sorted(selected_cells),
                             'state_bits': sorted(graph.roots[q] for q in selected_roots),
                             'roles': role_summary, 'incoming_roles': dict(sorted(role_counts.items())),
                             'outgoing_roles': dict(sorted(output_roles.items())),
                             'incoming_broadcast_groups': dict(sorted(broadcasts.items())),
                             'boundary_inputs': boundary, 'boundary_outputs': outputs},
                'cell_groups': dict(sorted(groups.items()))}

    planes = partition(lambda c: f'bit{c[2]}', f'bit{selected_bit}', [selected_bit])
    tiles = partition(lambda c: f'bank{c[0]}_words{c[1]//tile_words*tile_words:03d}', 'bank0_words000', range(width))
    # Execution.readTree selects bit zero last, so its bottom subtrees hold
    # entries with equal low bits, rather than contiguous address ranges.
    stride = bank_words // tile_words
    read_tiles = partition(lambda c: f'bank{c[0]}_low{c[1]%stride:03d}', 'bank0_low000', range(width))
    return {'bank_words': bank_words, 'bits_per_word': width, 'tile_words': tile_words,
            'planes': planes, 'word_tiles': tiles, 'read_tree_tiles': read_tiles,
            'scope': 'All-mode mapped connectivity and retained Liberty area. Bit planes keep both atomic banks; word/read-tree tiles keep all data bits of consecutive/equal-low-bit entries within one bank. Data-bearing gates follow their map support; zero-map-support gates join a slice only when every consumer is local. Remaining shared support is counted once. Clock/constants excluded from net budgets; reset included. These are graph cuts, not placement, wire length, timing or an optimal partition.'}
