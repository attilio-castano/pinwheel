"""Source computations and mapped consumer groups for the existing SRAM chips.

Source bit dependencies are conservative, not timing paths. Mapped cells are
classified by their actual endpoint consumers; shared logic is counted once.
No placement, delay or switching-activity model is implied by these groups.
"""
from collections import Counter, defaultdict
from dataclasses import dataclass
import re


@dataclass(frozen=True)
class Node:
    width: int
    op: str
    args: tuple = ()
    value: int = 0


class SourceGraph:
    """Read the small, unoptimized MLIR vocabulary emitted by NetlistEmit."""

    def __init__(self, text, assembly):
        self.nodes, self.next, self.outputs, self.owners = {}, {}, {}, {}
        header = next(line for line in text.splitlines() if 'hw.module @' in line)
        for name, width in re.findall(r'in %(\w+) : i(\d+)', header):
            self.nodes[name] = Node(int(width), 'input')
            self.owners[name] = ('memory.storage' + name[-1] if name in ('mem_q0', 'mem_q1')
                                 else 'package_inputs')
        self.nodes['clock'] = Node(1, 'clock')
        for slot in assembly['registers']:
            name = slot['name'].removeprefix('controller.')
            if name in self.nodes:
                raise ValueError('Duplicate source register')
            self.nodes[name] = Node(slot['width'], 'reg')
            self.owners[name] = slot['owner']
        output_ports = re.findall(r'out (\w+) : i(\d+)', header)
        for line in text.splitlines():
            line = line.strip()
            if not line or line == '}' or line.startswith(('module ', 'hw.module ', '%clock = seq.to_clock ')):
                continue
            if line.startswith('hw.output '):
                refs = re.findall(r'%(\w+)', line)
                if self.outputs or len(refs) != len(output_ports):
                    raise ValueError('Source output enumeration mismatch')
                for (name, width), ref in zip(output_ports, refs):
                    if ref not in self.nodes or self.nodes[ref].width != int(width):
                        raise ValueError('Source output width mismatch')
                    self.outputs[name] = ref
                continue
            match = re.fullmatch(r'%(\w+) = (.*)', line)
            if not match:
                raise ValueError('Unknown source line: ' + line)
            name, operation = match.groups()
            args = tuple(re.findall(r'%(\w+)', operation))
            widths = list(map(int, re.findall(r'\bi(\d+)\b', operation)))
            if any(a not in self.nodes for a in args):
                raise ValueError('Forward or missing source reference')
            if operation.startswith('seq.compreg '):
                if (name not in self.nodes or self.nodes[name].op != 'reg' or name in self.next
                        or args[1:] != ('clock',) or widths != [self.nodes[name].width]
                        or self.nodes[args[0]].width != self.nodes[name].width):
                    raise ValueError('Source register binding mismatch')
                self.next[name] = args[0]
                continue
            if name in self.nodes:
                raise ValueError('Duplicate source value')
            if operation.startswith('hw.constant '):
                node = Node(widths[0], 'lit', value=int(operation.split()[1]))
            elif operation.startswith('comb.extract '):
                node = Node(widths[1], 'slice', args, int(re.search(r'from (\d+)', operation)[1]))
            elif operation.startswith('comb.concat '):
                node = Node(sum(widths), 'concat', args)
            elif operation.startswith('comb.icmp '):
                node = Node(1, operation.split()[1], args)
            else:
                node = Node(widths[0], operation.split()[0].removeprefix('comb.'), args)
            self.validate(node)
            self.nodes[name] = node
        if set(self.next) != {n for n, v in self.nodes.items() if v.op == 'reg'} or not self.outputs:
            raise ValueError('Incomplete source circuit')
        self.probes = {}
        for probe in assembly['computations']:
            name, ref, width = probe['name'], probe['mlir_value'].removeprefix('%'), probe['width']
            if name in self.probes or ref not in self.nodes or self.nodes[ref].width != width:
                raise ValueError('Invalid computation binding')
            self.probes[name] = ref
        expected = {'successor', 'candidate0', 'candidate1', 'read_address0', 'read_address1',
                    'write_address', 'write_data', 'write_enable'}
        if set(self.probes) != expected:
            raise ValueError('Incomplete computation enumeration')
        # These are exactly the mux cuts justified by SramSchedule.request_on_*.
        for index in (0, 1):
            actual = self.nodes[self.outputs[f'mem_addr{index}']]
            wanted = Node(9, 'mux', tuple(self.probes[n] for n in
                          ('write_enable', 'write_address', f'read_address{index}')))
            if actual != wanted:
                raise ValueError('Request phase does not match actual address mux')
        for port, probe in [('mem_data', 'write_data'), ('mem_write', 'write_enable')]:
            if self.outputs[port] != self.probes[probe]:
                raise ValueError('Request computation is not its emitted port')

    def validate(self, node):
        widths = [self.nodes[a].width for a in node.args]
        if node.width <= 0:
            raise ValueError('Nonpositive source width')
        if node.op == 'lit':
            ok = not widths and 0 <= node.value < 2 ** node.width
        elif node.op == 'slice':
            ok = len(widths) == 1 and 0 <= node.value and node.value + node.width <= widths[0]
        elif node.op == 'concat':
            ok = len(widths) == 2 and sum(widths) == node.width
        elif node.op in ('eq', 'ult'):
            ok = len(widths) == 2 and widths[0] == widths[1] and node.width == 1
        elif node.op in ('and', 'xor', 'sub'):
            ok = widths == [node.width, node.width]
        elif node.op == 'mux':
            ok = widths == [1, node.width, node.width]
        else:
            raise ValueError('Unsupported source operation: ' + node.op)
        if not ok:
            raise ValueError('Source operation width mismatch: ' + node.op)

    def cone(self, refs, cuts=None):
        """Propagate selected bit positions through wiring, muxes and arithmetic.

        Muxes include the select and both data arms. Comparisons include every
        operand bit; subtraction conservatively includes all lower carry bits.
        This is structural dependence, not functional minimal support.
        """
        cuts = cuts or {}
        pending = [(ref, (1 << self.nodes[ref].width) - 1) for ref in refs]
        seen, roots = defaultdict(int), defaultdict(int)
        while pending:
            ref, mask = pending.pop()
            node = self.nodes[ref]
            if mask < 0 or mask >> node.width:
                raise ValueError('Source dependency exceeds signal width')
            mask &= ~seen[ref]
            if not mask:
                continue
            seen[ref] |= mask
            if ref in cuts or node.op in ('input', 'reg'):
                roots[ref] |= mask
            elif node.op == 'lit':
                continue
            elif node.op == 'slice':
                pending.append((node.args[0], mask << node.value))
            elif node.op == 'concat':
                low = self.nodes[node.args[1]].width
                pending += [(node.args[0], mask >> low), (node.args[1], mask & ((1 << low) - 1))]
            elif node.op == 'mux':
                pending += [(node.args[0], 1), (node.args[1], mask), (node.args[2], mask)]
            elif node.op in ('eq', 'ult'):
                pending += [(a, (1 << self.nodes[a].width) - 1) for a in node.args]
            elif node.op in ('and', 'xor', 'sub'):
                mask = (1 << mask.bit_length()) - 1 if node.op == 'sub' else mask
                pending += [(a, mask) for a in node.args]
            else:
                raise ValueError('Unsupported source dependency: ' + node.op)
        counts = Counter()
        for ref, mask in roots.items():
            counts['computation:' + cuts[ref] if ref in cuts else self.owners[ref]] += mask.bit_count()
        return {'operations': sum(self.nodes[n].op not in ('input', 'reg', 'lit', 'clock')
                                  and n not in cuts for n in seen),
                'root_bits_by_owner': dict(sorted(counts.items())),
                'roots': {cuts.get(n, n): [b for b in range(self.nodes[n].width) if m >> b & 1]
                          for n, m in sorted(roots.items())}}

    def report(self):
        computations = {}
        for name, ref in self.probes.items():
            cuts = {v: k for k, v in self.probes.items() if v != ref}
            computations[name] = {'mlir_value': '%' + ref, 'width': self.nodes[ref].width,
                                  'cone': self.cone([ref]), 'frontier': self.cone([ref], cuts)}
        return {'computations': computations, 'request_modes': {
            'all_edges': self.cone([self.outputs[f'mem_addr{b}'] for b in (0, 1)]),
            'read_edge': self.cone([self.probes[f'read_address{b}'] for b in (0, 1)]),
            'write_edge': self.cone([self.probes['write_address']])},
            'scope': 'Unoptimized emitted operations and conservative bit dependencies. Read/write cuts assume actual mem_write=0/1; reads include idle and commit. These counts are not mapped cells or a running-only timing path.'}


def mapped_members(graph, bits):
    pending, seen, cells = list(bits), set(), set()
    while pending:
        bit = pending.pop()
        if isinstance(bit, str) or bit in seen or bit in graph.roots:
            continue
        seen.add(bit)
        name = graph.drivers[bit][0]
        cells.add(name)
        pending.extend(b for bs in graph.inputs(graph.comb[name]).values() for b in bs)
    return cells


def mapped_partition(graph, assembly):
    """Partition by ultimate functional consumers; report explicit shared groups.

    Every cell has one proposed region. SRAM input computations have functional
    roles (e.g. upload data), while the physical macro belongs to fetch. Thus a
    configuration-to-macro bus is still counted as a real region crossing.
    """
    regions = assembly['owner_regions']
    if set(regions) != set(assembly['owners']) or not set(regions.values()) <= {'fetch', 'configuration', 'interface'}:
        raise ValueError('Incomplete or invalid owner regions')
    endpoints, family_regions = defaultdict(list), {}
    def add(family, region, bits):
        if family in family_regions and family_regions[family] != region:
            raise ValueError('Conflicting endpoint region')
        family_regions[family] = region
        endpoints[family].extend(bits)
    cell_regions = {}
    for name, cell in graph.flops.items():
        owner = graph.root_groups[cell['connections']['Q'][0]]
        cell_regions[name] = regions[owner]
        add('state:' + owner, regions[owner], cell['connections']['D'])
        add('reset', 'shared', cell['connections']['RESET_B'])
    for name, cell in graph.macros.items():
        cell_regions[name] = 'fetch'
        for port, bits in graph.inputs(cell).items():
            if port.endswith('CLK'):
                continue
            family, region = ('address:' + name, 'fetch') if port == 'A_ADDR' else (
                ('write_data', 'configuration') if port == 'A_DIN' else ('memory_control', 'shared'))
            add(family, region, bits)
    for port in graph.module['ports'].values():
        if port['direction'] == 'output':
            add('package_outputs', 'interface', port['bits'])
    consumers = {n: set() for n in graph.comb}
    for family, bits in endpoints.items():
        for name in mapped_members(graph, bits):
            consumers[name].add(family)
    histogram = Counter()
    for name, families in consumers.items():
        destinations = {family_regions[f] for f in families}
        region = next(iter(destinations)) if len(destinations) == 1 else 'shared' if destinations else 'unused'
        cell_regions[name] = region
        histogram[tuple(sorted(families))] += 1
    if set(cell_regions) != set(graph.cells):
        raise ValueError('Unassigned physical cells')
    groups = {r: {'combinational_cells': 0, 'flip_flops': 0, 'macros': 0}
              for r in ('fetch', 'configuration', 'interface', 'shared', 'unused')}
    for name, region in cell_regions.items():
        groups[region]['combinational_cells' if name in graph.comb else
                       'flip_flops' if name in graph.flops else 'macros'] += 1
    # Count nets once and sink pins separately; broadcasts are not independent buses.
    clock = set(graph.module['ports']['clk']['bits'])
    crossings, matrix = [], defaultdict(lambda: {'nets': 0, 'sink_pins': 0})
    for bit, loads in sorted(graph.loads.items(), key=lambda item: str(item[0])):
        if type(bit) is not int or bit in clock:
            continue
        if bit in graph.drivers:
            producer = cell_regions[graph.drivers[bit][0]]
        else:
            owner = graph.root_groups[bit]
            producer = 'external' if owner == 'package_inputs' else 'fetch' if owner in graph.macros else regions[owner]
        destinations = Counter(cell_regions[n] if n in graph.cells else 'external' for n, _ in loads)
        external = {r: n for r, n in destinations.items() if r != producer}
        if external:
            crossings.append({'bit': bit, 'producer': producer, 'consumers': external,
                              'state_aliases': graph.aliases[bit]})
            for region, count in external.items():
                pair = matrix[producer + ' -> ' + region]
                pair['nets'] += 1
                pair['sink_pins'] += count
    summary = {'groups': groups, 'consumer_sets': [
        {'consumers': list(k), 'cells': v} for k, v in sorted(histogram.items())],
        'crossing_nets': len(crossings), 'crossing_pairs': dict(sorted(matrix.items())),
        'scope': 'All operating modes. Unique cells assigned by endpoint-consumer regions; shared producers counted once. Clock and constants excluded from crossings; reset included. Region cuts are a communication budget, not wire lengths or placement improvement.'}
    return {'summary': summary, 'cells': {n: {'type': graph.cells[n]['type'], 'region': cell_regions[n],
                                              'consumers': sorted(consumers.get(n, []))}
                                        for n in sorted(cell_regions)}, 'crossings': crossings}


def private_funnels(comb_inputs, drivers, targets, other, constants=(), depths=(3, 5, 8)):
    """Select final stages that feed only one address terminal family.

    Stop at state, macros, shared producers and the chosen depth. A gate feeding
    any other sequential/package endpoint is never eligible, even indirectly.
    """
    if not depths or any(type(d) is not int or d <= 0 for d in depths):
        raise ValueError('Funnel depths must be positive integers')
    constants = set(constants)
    def cone(nets):
        pending, seen = list(nets), set()
        while pending:
            name = drivers.get(pending.pop())
            if name not in comb_inputs or name in seen:
                continue
            seen.add(name)
            pending.extend(comb_inputs[name])
        return seen
    cones = {name: cone(nets) for name, nets in targets.items()}
    other_cone = cone(other)
    result = {}
    for target, nets in targets.items():
        private = cones[target] - other_cone - set().union(*(v for k, v in cones.items() if k != target))
        levels = {}
        pending = [(net, 1) for net in nets]
        while pending:
            net, level = pending.pop()
            cell = drivers.get(net)
            if cell not in private or level > max(depths) or levels.get(cell, level + 1) <= level:
                continue
            levels[cell] = level
            pending.extend((n, level + 1) for n in comb_inputs[cell])
        cuts = {}
        for depth in depths:
            selected = {c for c, d in levels.items() if d <= depth}
            ingress = {n for c in selected for n in comb_inputs[c]
                       if drivers.get(n) not in selected and n not in constants}
            cuts[str(depth)] = {'cells': sorted(selected), 'cell_count': len(selected),
                               'incoming_nets': sorted(ingress, key=str), 'incoming_net_count': len(ingress)}
        result[target] = {'address_cone_cells': len(cones[target]), 'private_address_cells': len(private),
                          'cuts': cuts}
    return result


def placed_funnels(context, combinational_pattern):
    """Apply the same terminal-based selection to a saved OpenDB export.

    Physical synthesis changes cell identities and retains six extra flops in
    this flow. No mapped cell name or equivalence claim is transferred here.
    Distances use cell centers, not standard-cell pin or routed wire positions.
    """
    instances, nets = context['instances'], context['nets']
    comb, drivers, inputs, constants = set(), {}, defaultdict(set), set()
    targets, other = defaultdict(set), set()
    ff = 'sg13cmos5l_dfrbpq_1'
    for name, inst in instances.items():
        master = inst['cell']
        normalized = re.sub(r'_\d+$', '_1', master)
        if inst['macro'] or master == ff or master in ('sg13cmos5l_tiehi', 'sg13cmos5l_tielo'):
            continue
        if not combinational_pattern.fullmatch(normalized) and master != 'sg13cmos5l_dlygate4sd3_1':
            raise ValueError('Unknown placed cell classification: ' + master)
        comb.add(name)
    for net, info in nets.items():
        if info['type'] in ('POWER', 'GROUND'):
            continue
        outputs = [t for t in info['terminals'] if t['direction'] == 'OUTPUT']
        if len(outputs) > 1:
            raise ValueError('Multiple placed net drivers')
        if outputs:
            producer = outputs[0]['instance']
            drivers[net] = producer
            if instances[producer]['cell'] in ('sg13cmos5l_tiehi', 'sg13cmos5l_tielo'):
                constants.add(net)
            if info['ports']:
                other.add(net)
        for terminal in info['terminals']:
            if terminal['direction'] == 'OUTPUT':
                continue
            if terminal['direction'] != 'INPUT':
                raise ValueError('Unsupported placed terminal direction')
            cell, pin = terminal['instance'], terminal['pin']
            if cell in comb:
                inputs[cell].add(net)
            elif instances[cell]['macro'] and re.fullmatch(r'A_ADDR\[\d+\]', pin):
                targets[cell].add(net)
            elif not pin.endswith('CLK'):
                other.add(net)
    if len(targets) != 2 or any(len(nets) != 6 for nets in targets.values()):
        raise ValueError('Expected two placed six-bit hybrid address ports')
    result = private_funnels({c: inputs[c] for c in comb}, drivers, targets, other, constants)
    for name, item in result.items():
        pins = [p['bbox'] for p in context['macro_pins']
                if p['instance'] == name and re.fullmatch(r'A_ADDR\[\d+\]', p['pin'])]
        if not pins:
            raise ValueError('Missing placed address pin geometry')
        envelope = [min(p[0] for p in pins), min(p[1] for p in pins),
                    max(p[2] for p in pins), max(p[3] for p in pins)]
        item['address_pin_envelope_um'] = envelope
        for cut in item['cuts'].values():
            boxes = [instances[c]['bbox'] for c in cut['cells']]
            distance = []
            for x0, y0, x1, y1 in boxes:
                x, y = (x0 + x1) / 2, (y0 + y1) / 2
                distance.append(max(envelope[0] - x, 0, x - envelope[2]) +
                                max(envelope[1] - y, 0, y - envelope[3]))
            cut['cell_area_um2'] = round(sum((x1-x0)*(y1-y0) for x0,y0,x1,y1 in boxes), 3)
            cut['mean_center_distance_um'] = round(sum(distance)/len(distance), 3) if distance else None
            cut['max_center_distance_um'] = round(max(distance), 3) if distance else None
            cut['bbox_um'] = ([min(b[0] for b in boxes), min(b[1] for b in boxes),
                               max(b[2] for b in boxes), max(b[3] for b in boxes)] if boxes else None)
    return {'database': context['database'], 'database_sha256': context['database_sha256'],
            'physical_flip_flops': sum(i['cell'] == ff for i in instances.values()),
            'funnels': result,
            'scope': 'Saved placed connectivity, with a fresh terminal-based selection. Depth counts combinational stages including buffers and delay cells. Cell-center distances to the macro address-pin envelope are geometric proxies, not wire lengths, timing or demonstrated improvement.'}


def projection_screen(context, funnels, windows, depth=3):
    """Measure a proposed pin-window projection across every incident signal net.

    Clamp each selected cell center to its window, leaving half its width/height
    inside. Other cells stay fixed. This is an unlegalized geometric screen:
    cells may overlap, and no timing, buffering or routing is modeled. Rejecting
    this projection does not prove all placements in these windows are worse.
    """
    if set(windows) != set(funnels):
        raise ValueError('Locality windows must cover exactly the selected macros')
    instances = context['instances']
    pins, ports = defaultdict(list), defaultdict(list)
    for pin in context['macro_pins']:
        pins[pin['instance'], pin['pin']].append(pin['bbox'])
    for port in context['ports']:
        ports[port['name']].append(port['bbox'])
    def center(box):
        return ((box[0] + box[2])/2, (box[1] + box[3])/2)
    def envelope(boxes):
        if not boxes:
            raise ValueError('Missing endpoint geometry in locality screen')
        return [min(b[0] for b in boxes), min(b[1] for b in boxes),
                max(b[2] for b in boxes), max(b[3] for b in boxes)]
    projected, owners = {}, {}
    for name, window in windows.items():
        if (len(window) != 4 or not all(isinstance(v, (float, int)) for v in window)
                or not window[0] < window[2] or not window[1] < window[3]):
            raise ValueError('Invalid locality window')
        for cell in funnels[name]['cuts'][str(depth)]['cells']:
            if cell in projected:
                raise ValueError('Overlapping private address selections')
            box = instances[cell]['bbox']
            x, y = center(box)
            w, h = (box[2]-box[0])/2, (box[3]-box[1])/2
            if 2*w > window[2]-window[0] or 2*h > window[3]-window[1]:
                raise ValueError('Cell exceeds locality window')
            projected[cell] = (max(window[0]+w, min(x, window[2]-w)),
                               max(window[1]+h, min(y, window[3]-h)))
            owners[cell] = name
    nets = {n: info for n, info in context['nets'].items()
            if info['type'] not in ('CLOCK', 'POWER', 'GROUND')
            and any(t['instance'] in projected for t in info['terminals'])}
    def span(info, moved):
        points = []
        for terminal in info['terminals']:
            name = terminal['instance']
            if name in moved:
                point = moved[name]
            elif instances[name]['macro']:
                point = center(envelope(pins[name, terminal['pin']]))
            else:
                point = center(instances[name]['bbox'])
            points.append(point)
        for port in info['ports']:
            points.append(center(envelope(ports[port])))
        return max(p[0] for p in points)-min(p[0] for p in points) + max(p[1] for p in points)-min(p[1] for p in points)
    baseline = {n: span(info, {}) for n, info in nets.items()}
    def measure(moved):
        affected = {n: info for n, info in nets.items()
                    if any(t['instance'] in moved for t in info['terminals'])}
        before = sum(baseline[n] for n in affected)
        after = sum(span(info, moved) for info in affected.values())
        return {'cells': len(moved), 'incident_nets': len(affected),
                'before_span_um': round(before, 3), 'projected_span_um': round(after, 3),
                'delta_percent': round(100*(after/before-1), 3) if before else None}
    isolated = {cell: measure({cell: point}) for cell, point in projected.items()}
    return {'depth': depth, 'windows_um': windows,
            'per_macro': {n: measure({cell: p for cell, p in projected.items() if owners[cell] == n})
                          for n in windows},
            'joint': measure(projected),
            'isolated_improving_moves': [n for n, r in isolated.items()
                                        if r['projected_span_um'] < r['before_span_um']],
            'isolated_cells': isolated,
            'projected_centers_um': projected,
            'scope': 'Sum of signal-net bounding-box half perimeters, counted once per net. Standard-cell centers and macro/package pin-envelope centers approximate endpoints. Includes incoming, internal and outgoing nets; excludes clock/power/ground. Fixed neighbors and overlapping projected cells; no legalized placement, route, capacitance or timing claim.'}
