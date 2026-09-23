"""Bound a received-frame region in an exact, frozen physical netlist.

This is a connectivity and terminal-span screen. Moving terminal geometry does
not predict routed capacitance, skew, hold slack, congestion or legal placement.
"""
from collections import Counter, defaultdict
from functools import lru_cache
import json
from pathlib import Path
import re

from physical_floorplan import overlaps
from sram_interface import hpwl, incident_points
from upload_locality import Distribution, FF, point
from validation_run import sha


def bind_readback(context, module):
    """Reconcile every non-power physical terminal and net with fresh readback."""
    if set(context['instances']) != set(module['cells']):
        raise ValueError('Readback instance set differs')
    actual = {}
    for name, cell in module['cells'].items():
        if cell['type'] != context['instances'][name]['cell']:
            raise ValueError('Readback cell type differs: ' + name)
        for pin, bits in cell['connections'].items():
            for k, bit in enumerate(bits):
                terminal = (name, pin if len(bits) == 1 else f'{pin}[{k}]')
                actual[terminal] = bit, cell['port_directions'][pin].upper()
    seen, bit_nets, net_bits = set(), {}, {}
    for net, info in context['nets'].items():
        if info['type'] in ('POWER', 'GROUND'):
            continue
        bits = set()
        for terminal in info['terminals']:
            key = terminal['instance'], terminal['pin']
            if key in seen or key not in actual:
                raise ValueError('Duplicate or missing readback terminal')
            bit, direction = actual[key]
            if direction != terminal['direction']:
                raise ValueError('Readback pin direction differs')
            seen.add(key)
            bits.add(bit)
        for port in info['ports']:
            # ODB uses scalar bus-terminal names; Yosys uses vector ports.
            name, _, index = port.partition('[')
            k = int(index[:-1]) if index else 0
            bits.add(module['ports'][name]['bits'][k])
        if not info['terminals'] and not info['ports']:
            continue  # ODB may retain unused named nets after optimization.
        if len(bits) != 1:
            raise ValueError('Readback splits a physical net: ' + net)
        bit = next(iter(bits))
        if type(bit) is not int or bit in bit_nets:
            raise ValueError('Readback merges physical nets or folds a constant')
        bit_nets[bit], net_bits[net] = net, bit
    if seen != set(actual):
        raise ValueError('Unaccounted readback terminal')
    return net_bits


def bind_state(context, baseline, description, semantic):
    """Join typed reference -> tiled slot -> mapped FF -> physical instance.

    Semantic ownership is inherited from the retained typed assembly. It is not
    inferred from names, and does not imply a physical placement partition.
    """
    slots = {s['name']: s for s in semantic['registers']}
    if len(slots) != len(semantic['registers']) or len({s['reference'] for s in description['registers']}) != len(description['registers']):
        raise ValueError('Duplicate state projection slot')
    q_ffs = {c['connections']['Q'][0]: n for n, c in baseline['cells'].items()
             if c['type'] == FF}
    result = {}
    for slot in description['registers']:
        ref = slots['controller.' + slot['reference']]
        bits = baseline['netnames']['controller.' + slot['name']]['bits']
        if ref['width'] != slot['width'] or len(bits) != slot['width']:
            raise ValueError('State projection width differs')
        for k, bit in enumerate(bits):
            if bit not in q_ffs:
                continue  # Named pruned/derived bits are not physical registers.
            name = q_ffs[bit]
            if name in result or context['instances'].get(name, {}).get('cell') != FF:
                raise ValueError('Duplicate or missing physical state')
            result[name] = dict(owner=ref['owner'], register=ref['name'], bit=k)
    physical = {n for n, c in context['instances'].items() if c['cell'] == FF}
    if set(result) != physical or len(q_ffs) != len(result):
        raise ValueError('State binding does not cover every physical FF')
    return result


class Region:
    def __init__(self, context, state, word_width=64):
        self.context, self.state = context, state
        self.distribution = Distribution(context)
        self.pins, self.drivers = self.distribution.pins, self.distribution.drivers
        self.inputs, self.outputs = defaultdict(list), defaultdict(list)
        self.port_directions = {}
        self.comb = set(context['instances']) - set(state) - {
            n for n, c in context['instances'].items() if c['macro']}
        known = re.compile(r'sg13cmos5l_(?:(?:a21o|a21oi|a221oi|a22oi|and[234]|'
            r'mux[24]|nand[234]|nand[23]b|nor[234]|nor2b|o21ai|or[234]|xnor2|xor2)_1|'
            r'(?:buf|inv)_[1248]|dlygate4sd3_1|tiehi|tielo)')
        if any(not known.fullmatch(context['instances'][n]['cell']) for n in self.comb):
            raise ValueError('Unknown combinational cell type')
        for net, info in context['nets'].items():
            if info['type'] in ('POWER', 'GROUND'):
                continue
            for t in info['terminals']:
                (self.inputs if t['direction'] == 'INPUT' else self.outputs)[t['instance']].append(net)
        self.serial = {n for n, s in state.items() if s['owner'] == 'serial_receiver'}
        self.serial_bits = {self.pins[n, 'Q']: 1 << k for k, n in enumerate(sorted(self.serial))}
        self.word = self.distribution.payload(['memory.storage0', 'memory.storage1'], word_width)
        self.word_mask = sum(self.serial_bits[b['root_net']] for b in self.word)
        self._visiting = set()
        # Analyze all nets, including logic outside the intended region.
        for net, info in context['nets'].items():
            if info['type'] not in ('POWER', 'GROUND'):
                self.support(net)

    @lru_cache(None)
    def support(self, net):
        """Receiver-root bit mask plus presence of any other dynamic root.

        Every combinational input is charged; no sensitization is assumed.
        Clock/reset are sequential boundaries, not data input dependencies.
        """
        if net in self.serial_bits:
            return self.serial_bits[net], False
        if net in self._visiting:
            raise ValueError('Combinational cycle')
        driver = self.drivers.get(net)
        if driver is None or driver[0] not in self.comb:
            return 0, True
        name, _ = driver
        self._visiting.add(net)
        mask, other = 0, False
        for source in self.inputs[name]:
            smask, sother = self.support(source)
            mask |= smask
            other |= sother
        self._visiting.remove(net)
        return mask, other

    def cone(self, nets):
        todo, cells = list(nets), set()
        while todo:
            driver = self.drivers.get(todo.pop())
            if driver is not None and driver[0] in self.comb and driver[0] not in cells:
                cells.add(driver[0])
                todo.extend(self.inputs[driver[0]])
        return cells

    def members(self):
        pure = {n for n in self.comb if any(mask and not other
                for mask, other in (self.support(net) for net in self.outputs[n]))}
        feedback = self.cone(self.pins[n, 'D'] for n in self.serial)
        members = pure | feedback | self.serial
        # Local constant drivers may move only if every sink is in the region.
        constants = {n for n in self.comb if not self.inputs[n] and self.outputs[n]}
        private_ties = {n for n in constants if all(
            not self.context['nets'][net]['ports'] and
            all(t['direction'] == 'OUTPUT' or t['instance'] in members
                for t in self.context['nets'][net]['terminals'])
            for net in self.outputs[n])}
        members |= private_ties
        return dict(serial=self.serial, pure=pure, feedback=feedback,
                    private_ties=private_ties, members=members)

    def endpoints(self):
        """All register/macro/package endpoints influenced by received data."""
        endpoints = []
        for net, info in self.context['nets'].items():
            if info['type'] in ('POWER', 'GROUND'):
                continue
            mask, mixed = self.support(net)
            if not mask & self.word_mask:
                continue
            for t in info['terminals']:
                n, p = t['instance'], t['pin']
                if t['direction'] != 'INPUT' or n in self.comb:
                    continue
                if n in self.state and p != 'D':
                    raise ValueError('Received data reaches a clock/reset pin')
                label = self.state[n]['owner'] if n in self.state else n + '/' + p.split('[')[0]
                endpoints.append(dict(net=net, instance=n, pin=p, owner=label,
                                      received_bits=(mask & self.word_mask).bit_count(), mixed=mixed))
            for p in info['ports']:
                endpoints.append(dict(net=net, instance='@port', pin=p, owner='package_outputs',
                                      received_bits=(mask & self.word_mask).bit_count(), mixed=mixed))
        return endpoints


def envelope(context, members):
    boxes = [context['instances'][n]['bbox_dbu'] for n in members]
    return [min(b[0] for b in boxes), min(b[1] for b in boxes),
            max(b[2] for b in boxes), max(b[3] for b in boxes)]


def census(context, members):
    return dict(cells=len(members), types=dict(sorted(Counter(context['instances'][n]['cell']
        for n in members).items())), area_um2=sum((b[2]-b[0])*(b[3]-b[1])
        for n in members for b in [context['instances'][n]['bbox_dbu']])/context['dbu_per_micron']**2,
        bbox_dbu=envelope(context, members) if members else None)


class SpanCost:
    """Translate every pin of a moved cell; preserve orientation and all sinks.

    Include complete incident nets once, with clocks and static ties separated.
    This includes wires to the unchanged consumers and to displaced neighbors.
    """
    def __init__(self, context, geometry):
        self.context, self.geometry = context, geometry
        if context['database_sha256'] != geometry['database_sha256']:
            raise ValueError('Geometry database differs')
        self.points, self.nets_by_cell = {}, defaultdict(set)
        self.roles = {}
        for net, info in context['nets'].items():
            if info['type'] in ('POWER', 'GROUND'):
                continue
            if not info['terminals'] and not info['ports']:
                continue
            entries = [(t['instance'], point(context, geometry, (t['instance'], t['pin'])))
                       for t in info['terminals']]
            ports = incident_points(context, geometry, net)[len(entries):]
            entries += [('@port', p) for p in ports]
            self.points[net] = entries
            for n, _ in entries:
                if n != '@port':
                    self.nets_by_cell[n].add(net)
            drivers = [t['instance'] for t in info['terminals'] if t['direction'] == 'OUTPUT']
            static = drivers and all(context['instances'][n]['cell'] in
                                    ('sg13cmos5l_tiehi', 'sg13cmos5l_tielo') for n in drivers)
            self.roles[net] = 'clock' if info['type'] == 'CLOCK' else 'static' if static else 'signal'
        self.baseline = {n: hpwl([p for _, p in ps]) for n, ps in self.points.items()}

    def report(self, moves):
        nets = set().union(*(self.nets_by_cell[n] for n in moves)) if moves else set()
        rows, totals = {}, defaultdict(lambda: dict(nets=0, before_um=0., after_um=0.))
        scale = self.context['dbu_per_micron']
        for net in sorted(nets):
            after = hpwl([[p[0]+moves.get(n, (0,0))[0], p[1]+moves.get(n, (0,0))[1]]
                          for n, p in self.points[net]])
            before = self.baseline[net]
            rows[net] = dict(role=self.roles[net], before_um=before/scale, after_um=after/scale,
                             change_um=(after-before)/scale)
            total = totals[self.roles[net]]
            total['nets'] += 1
            total['before_um'] += before/scale
            total['after_um'] += after/scale
        totals['all'] = {k: sum(v[k] for v in totals.values()) for k in ('nets','before_um','after_um')}
        for total in totals.values():
            total['change_um'] = total['after_um'] - total['before_um']
            total['change_percent'] = 100*total['change_um']/total['before_um'] if total['before_um'] else None
        return dict(totals=dict(totals), nets=rows)


def moved_box(context, name, delta):
    b = context['instances'][name]['bbox_dbu']
    return [b[0]+delta[0], b[1]+delta[1], b[2]+delta[0], b[3]+delta[1]]


def collisions(context, moves):
    """Count every displaced neighbor; edge contact is not an overlap."""
    collisions = set()
    for name, delta in moves.items():
        box = moved_box(context, name, delta)
        for other, cell in context['instances'].items():
            if other != name and overlaps(box, moved_box(context, other, moves.get(other,(0,0)))):
                collisions.add(tuple(sorted((name, other))))
    return sorted(collisions)


def exchange_sites(context, region, cost, radius_dbu, max_pairs=64):
    """One bounded greedy pass; preserve occupied sites and clock geometry.

    Exchange equal footprints/orientations. FFs may exchange only within the
    same clock leaf and master. Hold cells, ties, macros and all other cells
    touching clocks are fixed. Every displaced cell's complete net cost counts.
    This heuristic is not a global optimum, nor does it certify electrical fit.
    """
    if radius_dbu <= 0 or max_pairs <= 0:
        raise ValueError('Invalid bounded exchange request')
    dist = region.distribution
    keys, groups = {}, defaultdict(list)
    clock_cells = {t['instance'] for info in context['nets'].values() if info['type'] == 'CLOCK'
                   for t in info['terminals']}
    for name, cell in context['instances'].items():
        kind, box = cell['cell'], cell['bbox_dbu']
        if cell['macro'] or kind in ('sg13cmos5l_tiehi', 'sg13cmos5l_tielo', 'sg13cmos5l_dlygate4sd3_1'):
            continue
        if name in clock_cells and kind != FF:
            continue
        key = (box[2]-box[0], box[3]-box[1], cell['orientation'],
               ('ff', dist.pins[name, 'CLK'], kind) if kind == FF else ('comb',))
        keys[name] = key
        groups[key].append(name)
    positions = {n: c['bbox_dbu'][:2] for n, c in context['instances'].items()}
    moves, used, accepted = {}, set(), []
    current = dict(cost.baseline)
    evaluated = 0
    members = region.members()['members']
    ordered = sorted(members & keys.keys(), key=lambda n: (-sum(current[k] for k in cost.nets_by_cell[n]),n))
    for name in ordered:
        if name in used or len(accepted) == max_pairs:
            continue
        x, y = positions[name]
        candidates = [n for n in groups[keys[name]] if n != name and n not in used and
                      abs(positions[n][0]-x)+abs(positions[n][1]-y) <= radius_dbu]
        # Deterministic radius cap: consider the nearest 24 compatible sites.
        candidates.sort(key=lambda n: (abs(positions[n][0]-x)+abs(positions[n][1]-y), n))
        best = None
        for other in candidates[:24]:
            ox, oy = positions[other]
            trial = {name: (ox-x, oy-y), other: (x-ox,y-oy)}
            nets = cost.nets_by_cell[name] | cost.nets_by_cell[other]
            values = {net: hpwl([[p[0]+trial.get(n,moves.get(n,(0,0)))[0],
                                  p[1]+trial.get(n,moves.get(n,(0,0)))[1]]
                                 for n,p in cost.points[net]]) for net in nets}
            gain = sum(current[net]-value for net,value in values.items())
            evaluated += 1
            if gain > 0 and (best is None or gain > best[0]):
                best = gain, other, trial, values
        if best is not None:
            gain, other, trial, values = best
            moves.update(trial)
            used.update(trial)
            current.update(values)
            accepted.append(dict(cells=[name,other], gain_um=gain/context['dbu_per_micron'],
                                 displaced_outside_region=other not in members))
    return dict(moves=moves, pairs=accepted, evaluated_pairs=evaluated,
                radius_dbu=radius_dbu, pair_cap=max_pairs,
                boundary='Greedy fixed-site exchange; no optimality, electrical or routing claim.')


def clock_geometry(context, geometry, moves):
    """Compare the complete terminal-coordinate multiset of each clock net."""
    changed = []
    for net, info in context['nets'].items():
        if info['type'] != 'CLOCK':
            continue
        before, after = [], []
        for t in info['terminals']:
            p = point(context, geometry, (t['instance'],t['pin']))
            d = moves.get(t['instance'],(0,0))
            before.append(tuple(p)); after.append((p[0]+d[0],p[1]+d[1]))
        if sorted(before) != sorted(after):
            changed.append(net)
    return dict(nets=sum(i['type']=='CLOCK' for i in context['nets'].values()),
                changed_geometry_nets=changed,
                boundary='Same masters, connectivity and terminal-coordinate multisets; no new clock RC or skew measurement.')


def hold_arc_changes(context, geometry, moves):
    """Expose changed terminal distances adjacent to retained delay cells.

    This intentionally makes no slack inference. Even fixed delay cells do not
    preserve hold timing when their input/output wires or upstream paths change.
    """
    rows = []
    for net, info in context['nets'].items():
        if info['type'] in ('POWER','GROUND','CLOCK'):
            continue
        terms = info['terminals']
        if not any(t['instance'] in moves for t in terms) or not any(
                context['instances'][t['instance']]['cell']=='sg13cmos5l_dlygate4sd3_1' for t in terms):
            continue
        drivers = [t for t in terms if t['direction']=='OUTPUT']
        if len(drivers)!=1:
            raise ValueError('Ambiguous hold-adjacent driver')
        driver=drivers[0]; p=point(context,geometry,(driver['instance'],driver['pin']))
        dp=moves.get(driver['instance'],(0,0))
        for sink in terms:
            if sink['direction']!='INPUT':
                continue
            q=point(context,geometry,(sink['instance'],sink['pin']));dq=moves.get(sink['instance'],(0,0))
            before=abs(q[0]-p[0])+abs(q[1]-p[1])
            after=abs(q[0]+dq[0]-p[0]-dp[0])+abs(q[1]+dq[1]-p[1]-dp[1])
            if after!=before:
                rows.append(dict(net=net,driver=driver['instance']+'/'+driver['pin'],
                    sink=sink['instance']+'/'+sink['pin'],before_um=before/context['dbu_per_micron'],
                    after_um=after/context['dbu_per_micron'],change_um=(after-before)/context['dbu_per_micron']))
    return dict(changed_arcs=len(rows), shortened_arcs=sum(r['change_um']<0 for r in rows),
                largest_shortening_um=max(0,-min((r['change_um'] for r in rows),default=0)),arcs=rows,
                boundary='Manhattan pin-distance changes beside hold cells, not hold slack or path delay.')


def analyze(inputs):
    """All conclusions are tied to exact input bytes, with no CAD mutation."""
    import importlib.util
    import time
    start = time.monotonic()
    root = Path(__file__).resolve().parents[1]
    def checked(name):
        item = inputs[name]
        path = root / item['path']
        if sha(path) != item['sha256']:
            raise ValueError('Changed region input: ' + name)
        return path
    paths = {name:checked(name) for name in inputs}
    read = lambda name: json.loads(paths[name].read_text())
    context, geometry = read('context'), read('geometry')
    if context['dbu_per_micron'] != 1000 or geometry['dbu_per_micron'] != 1000:
        raise ValueError('This IHP window/guide study requires 1000 DBU per micron')
    if sha(paths['database']) != context['database_sha256']:
        raise ValueError('Source ODB hash differs')
    net_bits = bind_readback(context, read('readback')['modules']['tt_um_pinwheel'])
    state = bind_state(context, read('baseline')['modules']['tt_um_pinwheel'],
                       read('assembly')['chip'],read('semantic'))
    region = Region(context,state)
    groups, endpoints = region.members(), region.endpoints()
    cost = SpanCost(context,geometry)
    family = read('locality')['directed_roles']
    roots = {b['root_net']:b['bit'] for b in region.word}
    bit_nets = {net:roots[region.distribution.path_to_root(net)[-1]] for net in family}
    spec=importlib.util.spec_from_file_location('guide_report',Path(__file__).with_name('report-routing-guides.py'))
    parser=importlib.util.module_from_spec(spec);spec.loader.exec_module(parser)
    guides=parser.parse_guides(paths['guides'].read_text(),context['dbu_per_micron'])
    interior = {g['net'] for g in guides if g['net'] in family and g['layer']=='Metal4' and any(
        overlaps(g['bbox_dbu'],[b[0]+10000,b[1]+10000,b[2]-10000,b[3]-10000])
        for n,c in context['instances'].items() if c['macro'] for b in [c['bbox_dbu']])}
    boundary=[]
    for net,info in context['nets'].items():
        if info['type'] in ('POWER','GROUND'):
            continue
        inside=[t for t in info['terminals'] if t['instance'] in groups['members']]
        outside=[t for t in info['terminals'] if t['instance'] not in groups['members']]
        if inside and (outside or info['ports']):
            boundary.append(dict(net=net,type=info['type'],
                direction='outgoing' if any(t['direction']=='OUTPUT' for t in inside) else 'incoming',
                inside_terminals=inside,outside_terminals=outside,ports=info['ports']))
    by_field={}
    for label,lo,hi in [('map_payload_0_4',0,5),('metadata_bit_5',5,6),('remaining_6_63',6,64)]:
        nets={net for net,k in bit_nets.items() if lo<=k<hi}
        by_field[label]=dict(bits=list(range(lo,hi)),nets=len(nets),span_um=sum(cost.baseline[n] for n in nets)/1000,
                            interior_guide_nets=sorted(interior & nets))
    source_bits=[]
    for bit in region.word:
        box=context['instances'][bit['source_ff']]['bbox_dbu']
        location=('below_sram0' if 252000<=box[0] and box[2]<=1036480 and box[3]<=30000 else
                  'below_sram1' if 252000<=box[0] and box[2]<=1036480 and 119180<=box[1] and box[3]<=144000 else
                  'above_macros' if box[1]>=208360 else 'right_of_macros' if box[0]>=1036480 else 'other')
        source_bits.append(dict(**bit, bbox_dbu=box,location=location,
            nonbuffer_leaf_pins=len(region.distribution.leaves(bit['root_net']))))
    electrical={item['net'] for item in read('electrical')['classification']}
    cases={}
    for radius in (20000,40000,80000):
        t=time.monotonic()
        exchange=exchange_sites(context,region,cost,radius)
        moves=exchange['moves']
        span=cost.report(moves)
        clocks=clock_geometry(context,geometry,moves)
        hold=hold_arc_changes(context,geometry,moves)
        occupied=collisions(context,moves)
        if occupied or clocks['changed_geometry_nets']:
            raise ValueError('Site-exchange geometry contract failed')
        changes={net:span['nets'].get(net,{}).get('change_um',0) for net in electrical}
        changed_interior={net:span['nets'][net]['change_um'] for net in interior & span['nets'].keys()
                          if span['nets'][net]['change_um']}
        # Require demonstrated effect on the diagnosed nets; generic HPWL gain
        # elsewhere cannot admit a routing experiment. Hold remains a separate
        # timing obligation even when this local distance check does not change.
        gate=(any(v<0 for v in changes.values()) and all(v<=0 for v in changes.values())
              and not hold['shortened_arcs'])
        outside=set(moves)-groups['members']
        cases[str(radius//1000)+'um']=dict(exchange=exchange,span=span,clock=clocks,hold=hold,
            occupancy_collisions=occupied,displaced_outside_region=census(context,outside),
            displaced_cells=sorted(outside),
            complete_region_and_displacement_span=cost.report({n:moves.get(n,(0,0))
                for n in groups['members'] | set(moves)})['totals'],
            electrical_target_changes_um=changes,interior_guide_net_span_changes_um=changed_interior,
            physical_probe_admitted=gate,
            gate_reason=('geometry-screen-only-requires-qualified-local-timing' if gate else
                         'no-complete-diagnosed-net-benefit-with-hold-distance-preservation'),
            seconds=round(time.monotonic()-t,3))
    result=dict(schema=1,inputs_sha256=inputs,physical_state_binding=dict(flip_flops=len(state),
        readback_instances=len(context['instances']),readback_nets=len(net_bits),
        claim='Every physical FF bound to a retained typed slot; all fresh-readback non-power pins/nets reconciled.'),
        groups={k:dict(census=census(context,v),members=sorted(v)) for k,v in groups.items()},
        endpoints=endpoints,endpoint_owners=dict(Counter(p['owner'] for p in endpoints)),
        source_bits=source_bits,source_locations=dict(Counter(b['location'] for b in source_bits)),
        boundary=boundary,boundary_summary=dict(Counter(b['direction'] for b in boundary)),
        word_fields=by_field,original_region_span=cost.report({n:(0,0) for n in groups['members']})['totals'],
        exchanges=cases,seconds=round(time.monotonic()-start,3),
        decision='reject-local-site-exchanges' if not any(c['physical_probe_admitted'] for c in cases.values())
                  else 'local-timing-obligation-before-physical-promotion',
        limits=['All combinational inputs conservatively influence outputs; no sensitized-path or activity claim.',
                'Typed state ownership does not make downstream mixed logic exclusive to this region.',
                'Three bounded greedy exchange searches are not a global placement optimum.',
                'Same occupied footprints and clock pin sets do not establish unchanged RC or timing.',
                'Guide overlap is measured on the retained route only; no new guide, DRC, antenna or extracted timing result.'])
    for name in inputs:
        checked(name)
    return result


def main():
    import argparse
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--inputs',required=True,type=Path)
    p.add_argument('--output',required=True,type=Path)
    args=p.parse_args()
    if args.output.exists():
        raise FileExistsError('Refusing to replace a region receipt')
    result=analyze(json.loads(args.inputs.read_text()))
    with args.output.open('x') as f:
        json.dump(result,f,indent=2);f.write('\n')
    print(result['decision']+': '+str(args.output))


if __name__=='__main__':main()
