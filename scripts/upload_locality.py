"""Cost upload-stage locality from a frozen chip; no placement or routing.

Directed consumers distinguish SRAM-only branches from the wider word-distribution
family. Free-row packing and idealized payload-net spans are necessary screens,
not legal-placement, electrical, timing or complete-chip cost predictions.
"""
from collections import Counter, defaultdict
import importlib.util
import json
from pathlib import Path
import re

from physical_floorplan import overlaps
from sram_interface import center, hpwl, incident_points, traffic_groups
from validation_run import sha

BUFFER = re.compile(r'sg13cmos5l_(buf_[1248]|dlygate4sd3_1)')
FF = 'sg13cmos5l_dfrbpq_1'


class Distribution:
    def __init__(self, context):
        self.context = context
        self.pins, self.drivers = {}, {}
        self.buffers = {n for n, i in context['instances'].items() if BUFFER.fullmatch(i['cell'])}
        for net, info in context['nets'].items():
            drivers = []
            for t in info['terminals']:
                key = (t['instance'], t['pin'])
                if key in self.pins:
                    raise ValueError('Terminal belongs to multiple nets')
                self.pins[key] = net
                if t['direction'] == 'OUTPUT':
                    drivers.append(key)
                elif t['direction'] != 'INPUT' and info['type'] not in ('POWER', 'GROUND'):
                    raise ValueError('Unsupported signal direction')
            if len(drivers) > 1:
                raise ValueError('Multiple drivers on ' + net)
            if drivers:
                self.drivers[net] = drivers[0]
        self.cache = {}

    def leaves(self, net, active=frozenset()):
        if net in active:
            raise ValueError('Buffer cycle')
        if net not in self.cache:
            result = set()
            for t in self.context['nets'][net]['terminals']:
                key = (t['instance'], t['pin'])
                if t['direction'] == 'OUTPUT':
                    continue
                if key[0] in self.buffers:
                    if key[1] != 'A':
                        raise ValueError('Unexpected buffer sink')
                    if (key[0], 'X') in self.pins:
                        result.update(self.leaves(self.pins[key[0], 'X'], active | {net}))
                        continue
                result.add(key)
            result.update(('@port', p) for p in self.context['nets'][net]['ports'])
            self.cache[net] = result
        return self.cache[net]

    def is_upload(self, terminal):
        i, p = terminal
        return (i in self.context['instances'] and self.context['instances'][i]['macro']
                and re.fullmatch(r'A_DIN\[\d+\]', p) is not None)

    def role(self, net):
        leaves = self.leaves(net)
        macros = {p for p in leaves if self.is_upload(p)}
        return 'sram-only' if macros and macros == leaves else ('shared' if macros else 'other-consumers')

    def path_to_root(self, net):
        path = []
        while True:
            if net in path:
                raise ValueError('Buffer cycle')
            path.append(net)
            if net not in self.drivers:
                raise ValueError('Missing data driver')
            inst, pin = self.drivers[net]
            if inst not in self.buffers:
                if pin != 'Q' or self.context['instances'][inst]['cell'] != FF:
                    raise ValueError('Upload root is not the expected FF Q')
                return path
            if pin != 'X' or (inst, 'A') not in self.pins:
                raise ValueError('Unexpected buffer source')
            net = self.pins[inst, 'A']

    def payload(self, macros, width=64):
        bits = []
        for bit in range(width):
            terminals = [(m, f'A_DIN[{bit}]') for m in macros]
            paths = [self.path_to_root(self.pins[t]) for t in terminals]
            if len({p[-1] for p in paths}) != 1:
                raise ValueError('Replica payload roots disagree')
            # Last common ancestor that must remain for another consumer. Remove
            # only buffer/delay branches exclusive to the old macro data pins.
            common = set.intersection(*(set(p) for p in paths))
            feed = next(n for n in paths[0] if n in common and
                        (self.role(n) != 'sram-only' or n == paths[0][-1]))
            bits.append(dict(bit=bit, terminals=terminals, source_net=feed,
                             root_net=paths[0][-1], source_ff=self.drivers[paths[0][-1]][0]))
        if len({b['root_net'] for b in bits}) != width:
            raise ValueError('Aliased payload bit roots')
        return bits


def free_rows(context, window, removed=frozenset()):
    """Exact row rectangles minus retained footprints; no site or power claim."""
    free, area = [], 0
    for row in context['rows']:
        x0, y0, x1, y1 = row['bbox_dbu']
        lo, hi = max(x0, window[0]), min(x1, window[2])
        if y0 < window[1] or y1 > window[3] or lo >= hi:
            continue
        area += (hi-lo)*(y1-y0)
        occupied = sorted((max(i['bbox_dbu'][0], lo), min(i['bbox_dbu'][2], hi))
                          for n, i in context['instances'].items()
                          if n not in removed and overlaps([lo, y0, hi, y1], i['bbox_dbu']))
        start = lo
        for left, right in occupied:
            if left > start:
                free.append([start, y0, left, y1])
            start = max(start, right)
        if start < hi:
            free.append([start, y0, hi, y1])
    return area, free


def width_capacity(rectangles, width, height):
    if width <= 0 or height <= 0:
        raise ValueError('Invalid cell dimensions')
    return sum((b[2]-b[0]) // width for b in rectangles if b[3]-b[1] >= height)


def cell_size(context, kind):
    sizes = {(b[2]-b[0], b[3]-b[1]) for i in context['instances'].values()
             if i['cell'] == kind for b in [i['bbox_dbu']]}
    if len(sizes) != 1:
        raise ValueError('Missing or ambiguous cell footprint: ' + kind)
    return next(iter(sizes))


def stage_census(module):
    """Bind the required payload clusters to actual mapped FF and D drivers."""
    drivers = {}
    for name, cell in module['cells'].items():
        for pin, bits in cell['connections'].items():
            if cell['port_directions'][pin] == 'output':
                for bit in bits:
                    if bit in drivers:
                        raise ValueError('Multiple mapped drivers')
                    drivers[bit] = (name, pin)
    groups, occupied = {}, set()
    for reg, width in [('upload_data',64),('upload_address',6),('upload_pending',1)]:
        bits = module['netnames']['controller.r_'+reg]['bits']
        if len(bits) != width or len(set(bits)) != width:
            raise ValueError('Wrong stage register width')
        rows = []
        for bit in bits:
            name, pin = drivers[bit]
            ff = module['cells'][name]
            if pin != 'Q' or ff['type'] != FF or name in occupied:
                raise ValueError('Stage register is not a distinct mapped FF')
            occupied.add(name)
            if ff['connections']['CLK'] != module['ports']['clk']['bits'] or ff['connections']['RESET_B'] != ['1']:
                raise ValueError('Unexpected stage clock/reset')
            source, _ = drivers[ff['connections']['D'][0]]
            rows.append(dict(ff=name,input_driver=source,input_cell=module['cells'][source]['type']))
        groups[reg] = dict(bits=width,input_cells=dict(Counter(r['input_cell'] for r in rows)),cells=rows)
    return dict(groups=groups,total_ff=len(occupied),
                payload_mux_pairs=groups['upload_data']['input_cells'].get('sg13cmos5l_mux2_1',0))


def point(context, geometry, terminal):
    name = terminal[0] + '/' + terminal[1]
    boxes = [s['bbox_dbu'] for s in geometry['pins'][name]]
    if not boxes:
        raise ValueError('Missing terminal shape')
    return center([min(b[0] for b in boxes), min(b[1] for b in boxes),
                   max(b[2] for b in boxes), max(b[3] for b in boxes)])


def payload_projection(context, geometry, dist, bits, removed, windows, ff_width):
    """Optimistic payload-only cost: preserve every other sink, ignore packing.

    A data FF's D/Q and private feedback mux share one point. Existing exclusive
    branches may be removed, but no shared hold/buffer or other consumer moves.
    Address/grant/reset/clock wiring and new hold repair have no cost here; their
    omission cannot make this a complete placed or timed implementation.
    """
    terminals = {t for bit in bits for t in bit['terminals']}
    affected = {n for n, info in context['nets'].items() if info['type'] not in ('POWER','GROUND') and
                any((t['instance'], t['pin']) in terminals or t['instance'] in removed
                    for t in info['terminals'])}
    affected.update(b['source_net'] for b in bits)
    retained = {}
    for net in affected:
        info = context['nets'][net]
        if net in dist.drivers and dist.drivers[net][0] in removed:
            continue
        # Payload trees cannot have package ports: their roots were verified FF Qs.
        if info['ports']:
            raise ValueError('Unexpected package port in payload projection')
        retained[net] = [point(context, geometry, (t['instance'], t['pin']))
                         for t in info['terminals'] if t['instance'] not in removed
                         and (t['instance'], t['pin']) not in terminals]
    before = sum(hpwl(incident_points(context, geometry, n)) for n in affected)
    after = sum(hpwl(ps) for ps in retained.values())
    placements = []
    for bit in bits:
        endpoints = [point(context, geometry, t) for t in bit['terminals']]
        if endpoints[0][0] != endpoints[1][0]:
            raise ValueError('Aligned replica pins required for this projection')
        source = retained[bit['source_net']]
        candidates = []
        for window in windows:
            for row in context['rows']:
                x0, y0, x1, y1 = row['bbox_dbu']
                lo, hi = max(x0, window[0])+ff_width/2, min(x1, window[2])-ff_width/2
                if y0 < window[1] or y1 > window[3] or lo > hi:
                    continue
                x = min(max(endpoints[0][0], lo), hi)
                p = (x, (y0+y1)/2)
                delta = hpwl(source+[p])-hpwl(source)+hpwl(endpoints+[p])
                candidates.append((delta, hpwl(endpoints+[p]), p))
        if not candidates:
            raise ValueError('No row for idealized stage point')
        delta, q_span, p = min(candidates)
        after += delta
        placements.append(dict(bit=bit['bit'],point_dbu=p,source_net=bit['source_net'],
                               added_data_span_um=delta/context['dbu_per_micron'],
                               output_span_um=q_span/context['dbu_per_micron']))
    units = context['dbu_per_micron']
    return dict(affected_nets=len(affected),before_um=before/units,after_um=after/units,
                change_um=(after-before)/units,change_percent=100*(after/before-1),
                idealized_stage_points=placements,
                assumptions='All other consumers fixed; exclusive buffer/delay branches removed; no packing, D/Q/mux offset, control/address/reset/clock wires or new hold repair. Not a legal placement or routed-wire estimate.')


def analyze(context, geometry, guides, windows, stage):
    if context['database_sha256'] != geometry['database_sha256'] or context['dbu_per_micron'] != geometry['dbu_per_micron']:
        raise ValueError('Geometry/checkpoint mismatch')
    if geometry.get('source_unchanged') is not True:
        raise ValueError('Geometry source was not preserved')
    dist = Distribution(context)
    labels = traffic_groups(context)
    family = {n for n, role in labels.items() if role == 'upload'}
    roles = {n:dist.role(n) for n in family}
    macros = sorted(n for n, i in context['instances'].items() if i['macro'])
    if len(macros) != 2:
        raise ValueError('Expected exactly two SRAM replicas')
    bits = dist.payload(macros)
    if len({b['source_net'] for b in bits}) != 64:
        raise ValueError('Payload stage feeds are not distinct')
    removed = {i for i in dist.buffers if (i, 'X') in dist.pins and
               roles.get(dist.pins[i, 'X']) == 'sram-only'}
    guide_counts = {}
    for inset in (0, 10*context['dbu_per_micron']):
        counted = {g['net'] for g in guides if g['layer'] == 'Metal4' and g['net'] in family
                   and any(overlaps(g['bbox_dbu'], [b[0]+inset,b[1]+inset,b[2]-inset,b[3]-inset])
                           for m in macros for b in [context['instances'][m]['bbox_dbu']])}
        guide_counts['body' if inset == 0 else 'interior_inset_10um'] = dict(Counter(roles[n] for n in counted))
    ff_w, ff_h = cell_size(context, FF)
    mux_w, mux_h = cell_size(context, 'sg13cmos5l_mux2_1')
    if mux_h != ff_h:
        raise ValueError('Pair heights differ')
    row_cost = {}
    for name, window in windows.items():
        modes = {}
        for mode, excluded in [('retained',set()),('optimistic_exclusive_release',removed)]:
            area, free = free_rows(context, window, excluded)
            modes[mode] = dict(row_area_um2=area/context['dbu_per_micron']**2,
                free_area_um2=sum((b[2]-b[0])*(b[3]-b[1]) for b in free)/context['dbu_per_micron']**2,
                free_fragments=free,ff_capacity=width_capacity(free,ff_w,ff_h),
                adjacent_ff_mux_capacity=width_capacity(free,ff_w+mux_w,ff_h))
        row_cost[name] = dict(window_dbu=window,**modes)
    projections = {name:payload_projection(context,geometry,dist,bits,removed,[window],ff_w)
                   for name,window in windows.items()}
    projections['split'] = payload_projection(context,geometry,dist,bits,removed,list(windows.values()),ff_w)
    hold = Counter(roles[dist.pins[i, 'X']] for i,cell in context['instances'].items()
                   if cell['cell']=='sg13cmos5l_dlygate4sd3_1' and dist.pins.get((i,'X')) in family)
    return dict(schema=1,database_sha256=context['database_sha256'],
        directed_family_counts=dict(Counter(roles.values())),directed_roles=roles,
        metal4_guide_counts=guide_counts,source_bits=bits,
        exclusive_release=dict(cells=sorted(removed),types=dict(Counter(context['instances'][i]['cell'] for i in removed)),
            area_um2=sum((c['bbox_dbu'][2]-c['bbox_dbu'][0])*(c['bbox_dbu'][3]-c['bbox_dbu'][1])
                         for i in removed for c in [context['instances'][i]])/context['dbu_per_micron']**2,
            boundary='Optimistic release of macro-only branches; no hold-repair credit is certified.'),
        existing_upload_hold_cells=dict(hold),
        mapped_stage=stage,
        footprint=dict(ff_width_dbu=ff_w,mux_width_dbu=mux_w,height_dbu=ff_h,
                       payload_pairs_required=stage['payload_mux_pairs'],total_new_ff=stage['total_ff']),
        windows=row_cost,payload_projections=projections,
        decision='reject-fixed-neighbor-adjacent-stage-layouts' if
            sum(w['optimistic_exclusive_release']['adjacent_ff_mux_capacity'] for w in row_cost.values())<stage['payload_mux_pairs']
            else 'requires-complete-candidate-placement-and-electrical-cost',
        limits=['The wider source family is not synonymous with exclusive SRAM upload traffic.',
                'Adjacent FF/mux capacity bounds only the stated fixed-neighbor arrangements; repacking or separated logic is a different candidate.',
                'No existing clock or shared hold-delay cells may be assumed removable.',
                'Payload HPWL is an optimistic geometric model, not total area, wire capacitance, congestion, timing or DRC.'])


def main():
    import argparse
    p=argparse.ArgumentParser(description=__doc__)
    for name in ('source','windows','output'):
        p.add_argument('--'+name,required=True,type=Path)
    args=p.parse_args()
    root=Path(__file__).resolve().parents[1]
    selected=json.loads(args.source.read_text())
    receipt_path=root/selected['report']
    if sha(receipt_path)!=selected['report_sha256']:
        raise ValueError('Changed source report')
    receipt=json.loads(receipt_path.read_text())
    for name,h in receipt['artifacts_sha256'].items():
        if sha(root/name)!=h:
            raise ValueError('Changed prior artifact: '+name)
    analysis_path=root/selected['geometry']['analysis']['path']
    if sha(analysis_path)!=selected['geometry']['analysis']['sha256']:
        raise ValueError('Changed interface analysis')
    prior=json.loads(analysis_path.read_text())
    for name,h in prior['inputs_sha256'].items():
        if sha(root/name)!=h:
            raise ValueError('Changed interface input: '+name)
    def input_path(suffix):
        paths=[root/n for n in prior['inputs_sha256'] if n.endswith(suffix)]
        if len(paths)!=1:raise ValueError('Ambiguous input: '+suffix)
        return paths[0]
    context_path=input_path('/context.json');geometry_path=input_path('/geometry.json')
    guide_path=input_path('/after_grt.guide')
    mapping_report=root/selected['receipts']['matched-synthesis']['path']
    if sha(mapping_report)!=selected['receipts']['matched-synthesis']['sha256']:
        raise ValueError('Changed mapping report')
    mapped=mapping_report.parent/'pipeline.json'
    if sha(mapped)!=json.loads(mapping_report.read_text())['artifacts_sha256']['pipeline.json']:
        raise ValueError('Changed mapped stage')
    stage=stage_census(json.loads(mapped.read_text())['modules']['tt_um_pinwheel'])
    spec=importlib.util.spec_from_file_location('guide_report',Path(__file__).with_name('report-routing-guides.py'))
    parser=importlib.util.module_from_spec(spec);spec.loader.exec_module(parser)
    context=json.loads(context_path.read_text());geometry=json.loads(geometry_path.read_text())
    guides=parser.parse_guides(guide_path.read_text(),context['dbu_per_micron'])
    result=analyze(context,geometry,guides,json.loads(args.windows.read_text()),stage)
    result['source_report']={'path':str(receipt_path),'sha256':sha(receipt_path)}
    result['inputs_sha256']={str(q):sha(q) for q in [Path(__file__),args.source,args.windows,receipt_path,
        analysis_path,context_path,geometry_path,guide_path,mapping_report,mapped,Path(parser.__file__),
        Path(__file__).with_name('sram_interface.py'),Path(__file__).with_name('physical_floorplan.py')]}
    with args.output.open('x') as f:json.dump(result,f,indent=2);f.write('\n')
    print(json.dumps({k:result[k] for k in ['decision','metal4_guide_counts','existing_upload_hold_cells']},indent=2))


if __name__=='__main__':
    main()
