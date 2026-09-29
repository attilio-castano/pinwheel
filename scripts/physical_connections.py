"""Join measured physical connections to typed state and exact consumers.

Traversal stops at state, SRAM and package boundaries. Combinational ownership
is a conservative set of reachable owners, never an exclusive block assignment.
"""
from collections import defaultdict
import math
import re
from tiled_chip import FF


NUMBER = r'-?(?:\d+(?:\.\d*)?|\.\d+)(?:[eE][+-]?\d+)?'


def connection_terminals(context, name):
    net = context['nets'][name]
    drivers = [t['instance']+'/'+t['pin'] for t in net['terminals'] if t['direction']=='OUTPUT']
    loads = [t['instance']+'/'+t['pin'] for t in net['terminals'] if t['direction']=='INPUT']
    if (net['type'] != 'SIGNAL' or len(drivers)!=1 or
            any(t['direction'] not in ('INPUT','OUTPUT') for t in net['terminals'])):
        raise ValueError('Repair target must be a singly driven signal net')
    return dict(driver=drivers[0], consumers=sorted(loads), ports=sorted(net['ports']))


def parse_measurements(text, expected, *, missing_fanout_limits=()):
    """Require all limits unless the caller explicitly names an absent fanout limit.

    Some SRAM output libraries specify capacitance and slew but no max fanout.
    Preserve that absence as None; never manufacture a passing numerical limit.
    """
    missing_fanout_limits = set(missing_fanout_limits)
    if not missing_fanout_limits <= set(expected):
        raise ValueError('Unknown optional fanout-limit connection')
    parts = re.split(r'^PINWHEEL_CONNECTION (\S+)\n', text, flags=re.M)
    result = {}
    for name, body in zip(parts[1::2], parts[2::2]):
        if name in result or name not in expected or not body.startswith('Net '+name+'\n'):
            raise ValueError('Duplicate, unknown or mismatched measured net')
        row = {}
        for title, key in [('Pin capacitance', 'pin_cap_pf'), ('Wire capacitance', 'wire_cap_pf'),
                           ('Total capacitance', 'total_cap_pf')]:
            m = re.search(r'^ '+title+': (.+)$', body, re.M)
            values = re.fullmatch('('+NUMBER+')(?:-('+NUMBER+'))?', m[1]) if m else None
            if not values:
                raise ValueError('Missing capacitance range')
            pair = [float(v) for v in values.groups() if v is not None]
            row[key] = [min(pair), max(pair)]
        row['loads'] = int(re.search(r'^ Number of loads: (\d+)$', body, re.M)[1])
        row['drivers'] = int(re.search(r'^ Number of drivers: (\d+)$', body, re.M)[1])
        for title, key in [('max slew', 'slew'), ('max capacitance', 'capacitance'), ('max fanout', 'fanout')]:
            chunk = body.split('\n'+title+'\n', 1)
            if len(chunk) != 2:
                if key == 'fanout' and name in missing_fanout_limits:
                    row[key] = None
                    continue
                raise ValueError('Missing electrical measurement')
            section = re.split(r'\n(?:max (?:slew|capacitance|fanout)\n|Startpoint: )',
                               chunk[1], maxsplit=1)[0]
            m = re.search(r'^(\S+)\s+('+NUMBER+r')\s+('+NUMBER+r')\s+('+NUMBER+r')\s+\((MET|VIOLATED)\)$',
                          section, re.M)
            if not m:
                raise ValueError('Missing electrical limit/slack')
            row[key] = dict(pin=m[1], limit=float(m[2]), actual=float(m[3]), slack=float(m[4]), verdict=m[5])
        row['paths'] = {}
        for section in body.split('Startpoint: ')[1:]:
            kind = re.search(r'^Path Type: (min|max)$', section, re.M)
            slack = re.search(r'^\s*('+NUMBER+r')\s+slack \((MET|VIOLATED)\)$', section, re.M)
            endpoint = re.search(r'^Endpoint: (\S+)', section, re.M)
            if not kind or not slack or not endpoint or kind[1] in row['paths']:
                raise ValueError('Missing or ambiguous connection timing path')
            row['paths'][kind[1]] = dict(startpoint=section.split()[0], endpoint=endpoint[1],
                slack_ns=float(slack[1]), verdict=slack[2],
                cells=sorted(set(re.findall(r'[\^v] (\S+)/\S+ \(', section))))
        if row['drivers'] != 1 or set(row['paths']) != {'min','max'}:
            raise ValueError('Connection requires one driver and both min/max timing paths')
        values = [v for k in ['pin_cap_pf','wire_cap_pf','total_cap_pf'] for v in row[k]]
        values += [row[k][v] for k in ['slew','capacitance','fanout'] if row[k] is not None
                   for v in ['limit','actual','slack']]
        values += [p['slack_ns'] for p in row['paths'].values()]
        if not all(math.isfinite(v) for v in values):
            raise ValueError('Nonfinite measured connection value')
        result[name] = row
    if set(result) != set(expected):
        raise ValueError('Incomplete connection measurement')
    return result


class Connectivity:
    def __init__(self, context, ownership):
        self.context = context
        self.state = {}
        for owner, bits in ownership['registers'].items():
            for bit in bits:
                if bit['cell'] in self.state:
                    raise ValueError('Ambiguous state owner')
                self.state[bit['cell']] = dict(owner=owner, bit=bit['bit'])
        if set(self.state)!={n for n,i in context['instances'].items() if i['cell']==FF}:
            raise ValueError('Typed ownership must cover every physical flip-flop')
        self.pin_net, self.cell_terms = {}, defaultdict(list)
        for name, net in context['nets'].items():
            if net['type'] in ('POWER','GROUND'):
                continue
            for t in net['terminals']:
                pin = t['instance']+'/'+t['pin']
                if pin in self.pin_net:
                    raise ValueError('Physical pin appears on multiple nets')
                self.pin_net[pin] = name
                self.cell_terms[t['instance']].append((pin, t['direction'], name))

    def terminals(self, name):
        return connection_terminals(self.context,name)

    def boundary(self, name, forward):
        todo, visited, boundary = [name], set(), {}
        seen_cells = set()
        direction = 'INPUT' if forward else 'OUTPUT'
        cross_direction = 'OUTPUT' if forward else 'INPUT'
        while todo:
            net_name = todo.pop()
            if net_name in visited:
                continue
            visited.add(net_name)
            net = self.context['nets'][net_name]
            for port in net['ports']:
                boundary[port] = dict(kind='package', pin=port)
            for t in net['terminals']:
                if t['direction'] != direction:
                    continue
                cell, pin = t['instance'], t['instance']+'/'+t['pin']
                if cell in self.state:
                    boundary[pin] = dict(kind='state', pin=pin, **self.state[cell])
                elif self.context['instances'][cell]['macro']:
                    boundary[pin] = dict(kind='macro', pin=pin)
                else:
                    seen_cells.add(cell)
                    todo += [n for _, d, n in self.cell_terms[cell] if d==cross_direction and
                             self.context['nets'][n]['type']=='SIGNAL']
        return dict(endpoints=[boundary[p] for p in sorted(boundary)], combinational_cells=sorted(seen_cells))

    def record(self, name, roles):
        terminals = self.terminals(name)
        upstream, downstream = self.boundary(name, False), self.boundary(name, True)
        sources = {v['pin'] for v in upstream['endpoints']}
        sinks = {v['pin'] for v in downstream['endpoints']}
        roles = [n for n,r in roles.items() if sources.intersection(r['sources']) and sinks.intersection(r['sinks'])]
        owners = lambda rows: sorted({r['owner'] for r in rows if r['kind']=='state'})
        cell = terminals['driver'].rsplit('/',1)[0]
        return dict(net=name, **terminals, driver_cell=self.context['instances'][cell]['cell'],
            driver_bbox_um=self.context['instances'][cell]['bbox'],
            source_boundary=upstream['endpoints'], sink_boundary=downstream['endpoints'],
            source_owners=owners(upstream['endpoints']), sink_owners=owners(downstream['endpoints']),
            semantic_roles=sorted(roles), shared=len({(r['kind'], r.get('owner',r['pin'].split('/')[0]))
                                                     for r in downstream['endpoints']})>1,
            boundary='Conservative combinational reachability; shared owners are retained, not physical partitions.')


def guide_summary(guides, selected):
    rows = {name:defaultdict(lambda: dict(rectangles=0, corridor_area_um2=0.0)) for name in selected}
    for g in guides:
        if g['net'] in rows:
            r = rows[g['net']][g['layer']]
            x0,y0,x1,y1 = g['bbox']
            r['rectangles'] += 1
            r['corridor_area_um2'] += (x1-x0)*(y1-y0)
    if any(not row for row in rows.values()):
        raise ValueError('Missing guide for measured net')
    return {n:dict(v) for n,v in rows.items()}
