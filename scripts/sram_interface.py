"""Classify SRAM communication and screen saved geometry without rerouting.

All distances are pin-based geometric proxies. Rectangular clearance uses only
nominal width/minimum spacing; it is not detailed pin-access or DRC certification.
"""
from bisect import bisect_left, bisect_right
from collections import Counter, defaultdict
import importlib.util
import json
from pathlib import Path
import re

from physical_floorplan import overlaps
from validation_run import sha

CAPACITY_SOURCE = ('https://github.com/The-OpenROAD-Project/OpenROAD/blob/'
    'dcf36133a369abc8f3c5e5738cd4d82e4903c0e0/src/grt/src/fastroute/src/FastRoute.cpp#L1129')


def traffic_groups(context):
    """Follow only known noninverting buffer/delay cells, in both directions."""
    nets = context['nets']
    parent = {n: n for n in nets}
    def root(n):
        while parent[n] != n:
            parent[n] = parent[parent[n]]
            n = parent[n]
        return n
    terminals = defaultdict(dict)
    for net, info in nets.items():
        for term in info['terminals']:
            if info['type'] not in ('POWER', 'GROUND'):
                terminals[term['instance']][term['pin']] = net
    for name, inst in context['instances'].items():
        if re.fullmatch(r'sg13cmos5l_(buf_[1248]|dlygate4sd3_1)', inst['cell']):
            pins = terminals[name]
            if not set(pins) <= {'A', 'X'}:
                raise ValueError('Unexpected buffer interface: ' + name)
            # Clock load cells deliberately leave their output unconnected.
            if set(pins) == {'A', 'X'}:
                parent[root(pins['A'])] = root(pins['X'])
    roles = defaultdict(set)
    fixed = set()
    for n, info in nets.items():
        group = root(n)
        if info['type'] == 'CLOCK':
            roles[group].add('clock')
        for term in info['terminals']:
            inst = context['instances'][term['instance']]
            if inst['cell'] in ('sg13cmos5l_tiehi', 'sg13cmos5l_tielo'):
                fixed.add(group)
            if not inst['macro']:
                continue
            pin = term['pin']
            if pin.startswith('A_DIN['):
                role = 'upload'
            elif pin.startswith('A_DOUT['):
                role = 'return'
            elif pin.startswith('A_ADDR['):
                role = 'address'
            elif pin == 'A_CLK':
                role = 'clock'
            elif pin.startswith(('A_BIST_', 'A_BM[')) or pin in ('A_DLY', 'A_MEN'):
                role = 'static'
            elif pin in ('A_WEN', 'A_REN'):
                role = 'control'
            elif info['type'] in ('POWER', 'GROUND'):
                role = 'power'
            else:
                raise ValueError('Unclassified macro terminal: ' + pin)
            roles[group].add(role)
    result = {}
    for n in nets:
        group = root(n)
        r = roles[group]
        if group in fixed:
            if r & {'upload', 'return', 'address', 'clock'}:
                raise ValueError('Unexpected constant on active interface')
            label = 'static'
        else:
            if 'static' in r:
                raise ValueError('Macro static terminal lacks a verified tie driver')
            label = '+'.join(sorted(r)) if r else 'transit'
        result[n] = label
    return result


def center(rect):
    return ((rect[0]+rect[2])/2, (rect[1]+rect[3])/2)


def hpwl(points):
    if not points:
        raise ValueError('Empty pin set')
    return max(p[0] for p in points)-min(p[0] for p in points) + max(p[1] for p in points)-min(p[1] for p in points)


def incident_points(context, geometry, net, mirrored=()):
    points = []
    for t in context['nets'][net]['terminals']:
        key = t['instance'] + '/' + t['pin']
        shapes = geometry['pins'][key]
        if not shapes:
            raise ValueError('Terminal has no geometry: ' + key)
        # One terminal is represented by its complete shape envelope, not by
        # an arbitrarily selected access point. This is an explicitly geometric proxy.
        b = [min(s['bbox_dbu'][0] for s in shapes), min(s['bbox_dbu'][1] for s in shapes),
             max(s['bbox_dbu'][2] for s in shapes), max(s['bbox_dbu'][3] for s in shapes)]
        x, y = center(b)
        if t['instance'] in mirrored:
            macro = context['instances'][t['instance']]
            if macro['orientation'] != 'R0':
                raise ValueError('Mirror projection requires R0 control')
            mb = macro['bbox_dbu']
            y = mb[1]+mb[3]-y
        points.append((x, y))
    for port in context['nets'][net]['ports']:
        shapes = [p['bbox_dbu'] for p in context['ports'] if p['name'] == port]
        if not shapes:
            raise ValueError('Missing port geometry')
        points.append(center([min(b[0] for b in shapes), min(b[1] for b in shapes),
                              max(b[2] for b in shapes), max(b[3] for b in shapes)]))
    return points


def union_area(rectangles):
    """Exact union of axis-aligned rectangles; do not sum overlapping areas."""
    xs = sorted({b[i] for b in rectangles for i in (0, 2)})
    area = 0
    for x0, x1 in zip(xs, xs[1:]):
        intervals = sorted((b[1], b[3]) for b in rectangles if b[0] < x1 and b[2] > x0)
        length, end = 0, None
        for y0, y1 in intervals:
            length += max(0, y1-max(y0, end if end is not None else y0))
            end = max(y1, end if end is not None else y1)
        area += (x1-x0)*length
    return area


def clipped(rectangles, region):
    return [[max(b[0],region[0]),max(b[1],region[1]),min(b[2],region[2]),min(b[3],region[3])]
            for b in rectangles if overlaps(b,region)]


def analyze(context, geometry, guides, grid):
    if context['database_sha256'] != geometry['database_sha256'] or context['database_sha256'] != grid['database_sha256']:
        raise ValueError('Geometry/grid belong to different checkpoints')
    units = context['dbu_per_micron']
    if units != geometry['dbu_per_micron'] or units != grid['dbu_per_micron']:
        raise ValueError('Inconsistent coordinate units')
    macros = {n: i['bbox_dbu'] for n,i in context['instances'].items() if i['macro']}
    labels = traffic_groups(context)
    categories = defaultdict(lambda:defaultdict(set))
    interior = defaultdict(lambda:defaultdict(set))
    for g in guides:
        label = labels[g['net']]
        if any(overlaps(g['bbox_dbu'], b) for b in macros.values()):
            categories[g['layer']][label].add(g['net'])
        if any(overlaps(g['bbox_dbu'], [b[0]+10000,b[1]+10000,b[2]-10000,b[3]-10000]) for b in macros.values()):
            interior[g['layer']][label].add(g['net'])
    counts = lambda d: {l:{r:len(ns) for r,ns in sorted(v.items())} for l,v in sorted(d.items())}
    blockage = {}
    for name, region in macros.items():
        area = (region[2]-region[0])*(region[3]-region[1])
        blockage[name] = {}
        for layer in ('Metal2','Metal3','Metal4'):
            obs = [o['bbox_dbu'] for o in context['macro_obstructions'] if o['instance']==name and o['layer']==layer]
            power = [p['bbox_dbu'] for p in context['power_shapes']+geometry['power_via_shapes'] if p['layer']==layer]
            blockage[name][layer] = {
                'macro_obstruction_fraction':union_area(clipped(obs,region))/area,
                'with_power_fraction':union_area(clipped(obs+power,region))/area}
    # Test a straight two-micron escape ray against rectangular shapes and the
    # nominal minimum spacing. Via, end-of-line and detailed-router access remain open.
    layer = context['layers']['Metal2']
    half = layer['width_dbu']/2
    spacing = layer['spacing_dbu']
    obstacles = [x['bbox_dbu'] for x in context['macro_obstructions']+context['power_shapes']+
                 geometry['power_via_shapes']+context['routing_obstructions'] if x['layer']=='Metal2']
    pins = [p for p in context['macro_pins'] if p['layer']=='Metal2' and p['type'] not in ('POWER','GROUND')]
    escape = []
    tracks = geometry['tracks']['Metal2']['x']
    for pin in pins:
        b = pin['bbox_dbu'];x,_=center(b)
        row = dict(instance=pin['instance'],pin=pin['pin'],role=labels[pin['net']])
        other = [p['bbox_dbu'] for p in pins if p['net']!=pin['net']]
        for direction, y0,y1 in [('south',b[1]-2000,b[1]),('north',b[3],b[3]+2000)]:
            corridor=[x-half-spacing,y0-spacing,x+half+spacing,y1+spacing]
            row[direction+'_blocked'] = any(overlaps(corridor,o) for o in obstacles+other)
        row['track_fits_pin_width'] = bisect_left(tracks,b[0]+half)<bisect_right(tracks,b[2]-half)
        escape.append(row)
    capacity = {}
    for layer, values in grid['layers'].items():
        rows=defaultdict(lambda:Counter())
        for ix,x in enumerate(grid['grid_x'][:-1]):
            for iy,y in enumerate(grid['grid_y'][:-1]):
                point=((x+grid['grid_x'][ix+1])/2,(y+grid['grid_y'][iy+1])/2)
                name=next((n for n,b in macros.items() if b[0]<=point[0]<b[2] and b[1]<=point[1]<b[3]),None)
                if name:
                    cap=values['capacity'][ix][iy];usage=values['usage'][ix][iy]
                    rows[name].update(cells=1,stored_capacity=cap,stored_usage_including_reductions=usage,
                                      saved_overflow=max(0,usage-cap))
        capacity[layer]={k:dict(v) for k,v in rows.items()}
    # Evaluate every signal/clock net incident to a moved macro, including all
    # static tie wires and all other terminals. No standard cells are moved.
    mirrors=[]
    names=sorted(macros)
    for changed in [(names[0],),(names[1],),tuple(names)]:
        costs=defaultdict(lambda:Counter())
        for n,info in context['nets'].items():
            if info['type'] in ('POWER','GROUND') or not any(t['instance'] in changed for t in info['terminals']):
                continue
            before=hpwl(incident_points(context,geometry,n))/units
            after=hpwl(incident_points(context,geometry,n,changed))/units
            costs[labels[n]].update(nets=1,before_um=before,after_um=after)
        before=sum(v['before_um'] for v in costs.values());after=sum(v['after_um'] for v in costs.values())
        mirrors.append(dict(mirrored=list(changed),by_role={k:dict(v) for k,v in costs.items()},
                            before_um=before,after_um=after,change_percent=100*(after/before-1)))
    return dict(schema=1,database_sha256=context['database_sha256'],
                guide_overlap_nets=counts(categories),guide_interior_overlap_nets=counts(interior),
                net_roles=labels,blockage=blockage,capacity=capacity,escape=escape,
                capacity_accounting=dict(source=CAPACITY_SOURCE,
                    stored_capacity='remaining capacity + capacity reduction',
                    stored_usage='routed usage + capacity reduction, summed over directions',
                    interpretation='A nonzero stored capacity is not free routing capacity; equal stored capacity maps do not establish equal obstruction effects.'),
                escape_summary=dict(pins=len(escape),south_clear=sum(not r['south_blocked'] for r in escape),
                    north_clear=sum(not r['north_blocked'] for r in escape),
                    track_fits=sum(r['track_fits_pin_width'] for r in escape)),
                mirror_projections=mirrors,
                limits=['Guide overlap and geometric area are not routed demand attribution or DRC.',
                    'Buffer-connected traffic classes are structural, not phase-qualified activity.',
                    'Pin escape is a nominal rectangular clearance screen, not a legal via/access proof.',
                    'Mirror projections hold all other terminals fixed; power must be regenerated and independently checked.',
                    'HPWL uses terminal shape-envelope centers and is not actual wire length or delay.'])


def main():
    import argparse
    p=argparse.ArgumentParser(description=__doc__)
    for name in ('context','geometry','guides','grid','guide-receipt','geometry-receipt','output'):
        p.add_argument('--'+name,type=Path,required=True)
    args=p.parse_args()
    guide_receipt=json.loads(args.guide_receipt.read_text())
    for path,digest in guide_receipt['artifacts'].items():
        if sha(path)!=digest:
            raise ValueError('Changed completed guide dependency: '+path)
    for path in [args.context,args.guides]:
        if guide_receipt['artifacts'].get(str(path))!=sha(path):
            raise ValueError('Guide receipt does not bind selected geometry/guides')
    extraction=json.loads(args.geometry_receipt.read_text())
    if (extraction['status']!='passed' or not extraction['source_unchanged'] or
            extraction['container_termination'] not in ('absent','stopped') or
            extraction['artifacts_sha256'].get(args.geometry.name)!=sha(args.geometry)):
        raise ValueError('Unsettled or changed geometry extraction')
    context=json.loads(args.context.read_text());geometry=json.loads(args.geometry.read_text())
    grids=json.loads(args.grid.read_text())['runs']
    matched=[g for g in grids if g['database_sha256']==context['database_sha256']]
    if len(matched)!=1:
        raise ValueError('Require exactly one matching saved capacity grid')
    spec=importlib.util.spec_from_file_location('guide_report',Path(__file__).with_name('report-routing-guides.py'))
    reporter=importlib.util.module_from_spec(spec);spec.loader.exec_module(reporter)
    guides=reporter.parse_guides(args.guides.read_text(),context['dbu_per_micron'])
    result=analyze(context,geometry,guides,matched[0])
    result['inputs_sha256']={str(q):sha(q) for q in [args.context,args.geometry,args.guides,args.grid,
        args.guide_receipt,args.geometry_receipt,Path(__file__),Path(reporter.__file__),
        Path(__file__).with_name('physical_floorplan.py'),Path(__file__).with_name('validation_run.py')]}
    with args.output.open('x') as f:
        json.dump(result,f,indent=2);f.write('\n')
    print(json.dumps({k:result[k] for k in ['guide_overlap_nets','escape_summary','mirror_projections']},indent=2))


if __name__=='__main__':
    main()
