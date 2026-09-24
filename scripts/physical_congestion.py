"""Reconcile native routing markers with the matching saved congestion grid.

OpenROAD's saved usage includes capacity reductions. Native markers separate
available capacity from routed demand and identify nets crossing the edge.
Overlapping guide rectangles remain a wider geometric association. No marker
set, even one stored in the same ODB, establishes freshness without reconciliation.
"""
from collections import Counter
from decimal import Decimal
import re

from physical_floorplan import overlaps


def reconcile_markers(native, geometry, context, expected_overflow, guides):
    if geometry['database_sha256'] != context['database_sha256']:
        raise ValueError('Congestion geometry does not match the selected database')
    if set(native) != {'Global route'} or native['Global route'].get('source') != 'GRT':
        raise ValueError('Require native global-routing markers')
    units=geometry['dbu_per_micron']
    if type(units) is not int or units <= 0 or units != context['dbu_per_micron']:
        raise ValueError('Invalid congestion coordinate units')
    cells={}
    for layer,row in geometry['layers'].items():
        for h in row['hotspots']:
            ix,iy=h['index']
            box=(geometry['grid_x'][ix],geometry['grid_y'][iy],geometry['grid_x'][ix+1],geometry['grid_y'][iy+1])
            direction=context['layers'][layer]['direction']
            key=(direction,box)
            if key in cells:raise ValueError('Ambiguous congested layers for a native marker')
            if (h['usage'] != row['usage'][ix][iy] or h['capacity'] != row['capacity'][ix][iy] or
                    h['overflow'] != h['usage']-h['capacity'] or h['overflow'] <= 0):
                raise ValueError('Inconsistent saved congestion cell')
            cells[key]=(layer,h)
    seen=set();output=[]
    categories=native['Global route'].get('category',{})
    if set(categories)-{'Horizontal congestion','Vertical congestion'}:
        raise ValueError('Unknown global-routing marker category')
    for name,category in categories.items():
        direction=name.split()[0].upper()
        if category.get('source')!='GRT':raise ValueError('Wrong congestion marker source')
        for marker in category.get('violations',[]):
            match=re.fullmatch(r'capacity:(\d+) usage:(\d+) overflow:(\d+)',marker['comment'])
            if not match or marker.get('waived')!='false':raise ValueError('Invalid or waived congestion marker')
            capacity,usage,overflow=map(int,match.groups())
            if overflow<=0 or usage-capacity!=overflow:raise ValueError('Invalid native overflow accounting')
            shapes=marker['shape']
            if len(shapes)!=1 or shapes[0]['type']!='box' or len(shapes[0]['points'])!=2:
                raise ValueError('Require one native congestion rectangle')
            coords=[Decimal(p[k])*units for p in shapes[0]['points'] for k in ['x','y']]
            if any(c!=int(c) for c in coords):raise ValueError('Off-grid native marker coordinate')
            box=tuple(int(c) for c in coords);key=(direction,box)
            if key in seen or key not in cells:raise ValueError('Duplicate or stale native congestion marker')
            seen.add(key);layer,h=cells[key]
            reduction=h['capacity']-capacity
            if reduction<0 or h['usage']-usage!=reduction or h['overflow']!=overflow:
                raise ValueError('Native demand does not reconcile with saved grid accounting')
            sources=marker['sources'];nets=[s['name'] for s in sources]
            if (not sources or any(s['type']!='net' or s['name'] not in context['nets'] for s in sources) or
                    len(nets)!=len(set(nets)) or len(nets)>usage):
                raise ValueError('Invalid native crossing-net attribution')
            associated=sorted({g['net'] for g in guides if g['layer']==layer and overlaps(g['bbox_dbu'],box)})
            if not set(nets)<=set(associated):raise ValueError('Native crossing absent from saved guide geometry')
            output.append(dict(layer=layer,index=h['index'],bbox_dbu=list(box),
                direction=direction,available_capacity=capacity,routed_demand=usage,overflow=overflow,
                saved_capacity=h['capacity'],saved_usage=h['usage'],capacity_reduction=reduction,
                crossing_nets=sorted(nets),guide_associations=associated,
                guide_only_nets=sorted(set(associated)-set(nets)),
                crossing_net_types=dict(Counter(context['nets'][n]['type'] for n in nets)),
                macro_obstruction_overlap=any(o['layer']==layer and overlaps(o['bbox_dbu'],box)
                    for o in context['macro_obstructions'])))
    if seen!=set(cells) or sum(r['overflow'] for r in output)!=expected_overflow:
        raise ValueError('Incomplete or stale native congestion coverage')
    return dict(hotspots=sorted(output,key=lambda r:(r['layer'],r['index'])),
        overflow=expected_overflow,marker_count=len(output),
        capacity_demand_counts=dict(Counter(f"{r['available_capacity']}/{r['routed_demand']}" for r in output)),
        zero_capacity_edges=sum(r['available_capacity']==0 for r in output),
        crossing_nets=len({n for r in output for n in r['crossing_nets']}),
        guide_association_nets=len({n for r in output for n in r['guide_associations']}),
        boundary='Native marker demand reconciles with this saved whole-chip grid and flow total. Crossing attribution is distinct from guide-area overlap and does not prove one net caused the shared overflow.')
