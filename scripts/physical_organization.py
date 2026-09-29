"""Screen physical distribution choices on a saved chip, without editing it.

The existing inventory owns family discovery; this layer reconstructs transport
trees and compares grouping, drive and placement choices. Area and connectivity
are exact within the declared edits. Pin-envelope span and fixed-wire scenarios
are screens, never routed timing or electrical qualification.
"""
from collections import Counter
from copy import deepcopy
import hashlib
from itertools import product
import math
import re

from physical_buffer_repair import BUFFERS, _bufferless
from physical_connections import connection_terminals, parse_measurements
from physical_distribution import CHAIN_CELLS
from physical_floorplan import overlaps
from physical_floorplan import to_dbu
from physical_repair_plan import placement_hint
from tiled_chip import FF


def _group(text, kind, name):
    pattern = r'\b'+kind+r'\s*\(\s*"?'+re.escape(name)+r'"?\s*\)\s*\{'
    matches = list(re.finditer(pattern, text))
    if len(matches) != 1:
        raise ValueError('Missing or ambiguous Liberty group: '+kind+' '+name)
    start = matches[0].end(); depth = 1
    for token in re.finditer(r'"(?:\\.|[^"\\])*"|[{}]', text[start:]):
        if token[0] == '{': depth += 1
        elif token[0] == '}': depth -= 1
        if depth == 0: return text[start:start+token.start()]
    raise ValueError('Unclosed Liberty group')


def _header(body):
    return re.split(r'\b\w+\s*\([^{};]*\)\s*\{', body, maxsplit=1)[0]


def _number(body, name):
    values = re.findall(r'\b'+name+r'\s*:\s*"?([\d.eE+-]+)"?\s*;', body)
    if len(values) != 1 or not math.isfinite(float(values[0])) or float(values[0]) < 0:
        raise ValueError('Missing finite nonnegative Liberty attribute: '+name)
    return float(values[0])


class Library:
    """Restricted pinned Liberty reader: scalar pins and inherited bus capacitance.

    No timing-table interpolation. The caller reconciles pin-capacitance ranges
    with independent saved STA before using any candidate's input-load delta.
    """
    def __init__(self, texts):
        self.texts, self.cells, self.pins, self.caps, self.buffers = texts, {}, {}, {}, {}
        for sources in texts.values():
            for text in sources:
                if not re.search(r'capacitive_load_unit\s*\(\s*1\s*,\s*pf\s*\)', text):
                    raise ValueError('Require explicit pF Liberty units')

    def cell(self, corner, cell):
        key = corner, cell
        if key not in self.cells:
            sources = [s for s in self.texts[corner] if re.search(
                r'\bcell\s*\(\s*"?'+re.escape(cell)+r'"?\s*\)', s)]
            if len(sources) != 1: raise ValueError('Unresolved Liberty cell: '+cell)
            self.cells[key] = _group(sources[0], 'cell', cell)
        return self.cells[key]

    def has_fanout_limit(self, corner, cell, pin):
        """Include inherited bus/bit limits and the owning library's default.

        Attribute presence is enough to require a report, even if its value is
        malformed. A bad characterization must never authorize missing evidence.
        """
        header = self.pin(corner, cell, pin)
        if not re.search(r'\bdirection\s*:\s*"?output"?\s*;', header):
            raise ValueError('Expected a library output pin')
        source = next(s for s in self.texts[corner] if re.search(
            r'\bcell\s*\(\s*"?'+re.escape(cell)+r'"?\s*\)', s))
        return bool(re.search(r'\bmax_fanout\b', header) or
                    re.search(r'\bdefault_max_fanout\b', source))

    def pin(self, corner, cell, pin):
        key = corner, cell, pin
        if key not in self.pins:
            body = self.cell(corner, cell)
            if '[' in pin:
                base, index = re.fullmatch(r'([^[]+)\[(\d+)\]', pin).groups()
                bus = _group(body, 'bus', base)
                ranges = re.findall(r'\bpin\s*\(\s*'+re.escape(base)+r'\[(\d+):(\d+)\]\s*\)', bus)
                if len(ranges) != 1 or not min(map(int,ranges[0])) <= int(index) <= max(map(int,ranges[0])):
                    raise ValueError('Unresolved bus pin range')
                # A bus supplies defaults; range and individual-bit groups can
                # override them. SRAM address pins use different capacitances
                # per bit, even though a common range owns their timing tables.
                headers = [_header(bus), _header(_group(body, 'pin',
                    f'{base}[{ranges[0][0]}:{ranges[0][1]}]'))]
                if re.search(r'\bpin\s*\(\s*"?'+re.escape(pin)+r'"?\s*\)',bus):
                    headers.append(_header(_group(bus,'pin',pin)))
                attributes = {}
                for source in headers:
                    seen = set()
                    for match in re.finditer(r'\b([A-Za-z_]\w*)\s*(?::[^;]+|\([^{};]*\))\s*;',source):
                        attribute = match[1]
                        if attribute in seen:raise ValueError('Ambiguous inherited pin attribute')
                        seen.add(attribute);attributes[attribute] = match[0]
                header = '\n'.join(attributes.values())
            else:
                header = _header(_group(body, 'pin', pin))
            self.pins[key] = header
        return self.pins[key]

    def capacitance_edges(self, corner, cell, pin):
        key=corner,cell,pin
        if key in self.caps:return self.caps[key]
        header = self.pin(corner, cell, pin)
        if not re.search(r'\bdirection\s*:\s*"?input"?\s*;', header):
            raise ValueError('Expected a library input pin')
        base=_number(header,'capacitance');result={}
        for edge in ['rise','fall']:
            pairs=re.findall(r'\b'+edge+r'_capacitance_range\s*\(\s*([\d.eE+-]+)\s*,\s*([\d.eE+-]+)\s*\)',header)
            scalar=re.findall(r'\b'+edge+r'_capacitance\s*:\s*([\d.eE+-]+)',header)
            if len(pairs)>1 or len(scalar)>1:raise ValueError('Ambiguous edge capacitance')
            values=list(map(float,pairs[0])) if pairs else [float(scalar[0]) if scalar else base]*2
            if values[0]>values[1] or any(not math.isfinite(v) or v<0 for v in values):raise ValueError('Invalid edge capacitance range')
            result[edge]=values
        self.caps[key]=result
        return result

    def capacitance(self, corner, cell, pin):
        edges=self.capacitance_edges(corner,cell,pin)
        return [min(v[0] for v in edges.values()),max(v[1] for v in edges.values())]

    def buffer(self, corner, cell):
        if (corner,cell) in self.buffers:return self.buffers[corner,cell]
        if cell not in BUFFERS: raise ValueError('Unsupported buffer kind')
        output = self.pin(corner, cell, 'X')
        if not re.search(r'\bfunction\s*:\s*"A"\s*;', output):
            raise ValueError('Buffer does not implement identity')
        result=dict(area_um2=_number(_header(self.cell(corner,cell)), 'area'),
            input_cap_pf=self.capacitance(corner,cell,'A'), output_limit_pf=_number(output,'max_capacitance'))
        self.buffers[corner,cell]=result
        return result


# The comparison SDC defines no fanout constraints. Pin this reviewed program
# instead of attempting to infer Tcl behavior from a missing report section or
# a substring search. Other SDC programs retain the strict parser behavior.
COMPARISON_SDC_SHA256 = '860a5afd856cc92bbecc838b147a9f7c8259abd66bcd62c0f211cb7e8edc4db1'


def parse_diagnostic_measurements(text, expected, context, library, corner, sdc):
    """Replay a diagnostic with source-derived, per-corner macro exceptions.

    Callers bind context, libraries, SDC and report bytes to the saved collection.
    This adapter is for the pinned comparison flow, not physical admission.
    An absent bound remains None, never a numerical limit or a passing verdict.
    """
    expected = set(expected)
    missing = set()
    terms = {name: connection_terminals(context, name) for name in expected}
    if hashlib.sha256(sdc.encode()).hexdigest() == COMPARISON_SDC_SHA256:
        for name, terminals in terms.items():
            instance, pin = terminals['driver'].rsplit('/', 1)
            driver = context['instances'][instance]
            if driver['macro'] and not library.has_fanout_limit(corner, driver['cell'], pin):
                missing.add(name)
    measured = parse_measurements(text, expected, missing_fanout_limits=missing)
    for name, row in measured.items():
        terminals = terms[name]
        if (row['capacitance']['pin'] != terminals['driver'] or
                row['loads'] != len(terminals['consumers']) + len(terminals['ports']) or
                row['slew']['pin'] not in {terminals['driver'], *terminals['consumers'], *terminals['ports']} or
                (row['fanout'] is not None and row['fanout']['pin'] != terminals['driver'])):
            raise ValueError('Diagnostic measurement differs from physical connection: '+name)
    return measured


def span(points):
    return sum(max(p[k] for p in points)-min(p[k] for p in points) for k in (0,1)) if points else 0


class BufferGeometry:
    """Read only rectangular buffer pins and their site from a pinned LEF.

    Coordinates are checked against saved terminal geometry before use. A row
    grid and empty footprint do not establish power continuity or pin access.
    """
    def __init__(self,text,cells,units):
        self.cells={};self.units=units
        for cell in cells:
            bodies=re.findall(r'^MACRO '+re.escape(cell)+r'\s*\n(.*?)^END '+re.escape(cell)+r'\s*$',text,re.M|re.S)
            if len(bodies)!=1:raise ValueError('Missing or ambiguous LEF buffer')
            body=bodies[0]
            if not re.search(r'\bORIGIN\s+0\s+0\s*;',body):raise ValueError('Unsupported LEF origin')
            sizes=re.findall(r'\bSIZE\s+([\d.]+)\s+BY\s+([\d.]+)\s*;',body)
            sites=re.findall(r'\bSITE\s+(\w+)\s*;',body)
            if len(sizes)!=1 or len(sites)!=1:raise ValueError('Ambiguous LEF size/site')
            width,height=to_dbu(sizes[0],units)
            sb=re.findall(r'^SITE\s+'+re.escape(sites[0])+r'\s*\n(.*?)^END\s+'+re.escape(sites[0])+r'\s*$',text,re.M|re.S)
            if len(sb)!=1:raise ValueError('Missing LEF site')
            ss=re.findall(r'\bSIZE\s+([\d.]+)\s+BY\s+([\d.]+)\s*;',sb[0])
            if len(ss)!=1:raise ValueError('Ambiguous site size')
            pitch,row_height=to_dbu(ss[0],units)
            if pitch<=0 or height!=row_height or width%pitch:raise ValueError('Incompatible buffer site')
            pins={}
            for pin in ['A','X']:
                pb=re.findall(r'^\s*PIN\s+'+pin+r'\s*\n(.*?)^\s*END\s+'+pin+r'\s*$',body,re.M|re.S)
                if len(pb)!=1 or re.search(r'\b(?:POLYGON|PATH|VIA)\b',pb[0]):raise ValueError('Unsupported LEF buffer pin')
                rects=[to_dbu(r,units) for r in re.findall(r'\bRECT\s+([\d.-]+)\s+([\d.-]+)\s+([\d.-]+)\s+([\d.-]+)\s*;',pb[0])]
                if not rects or any(not 0<=r[0]<r[2]<=width or not 0<=r[1]<r[3]<=height for r in rects):
                    raise ValueError('Invalid LEF signal rectangle')
                pins[pin]=rects
            self.cells[cell]=dict(width=width,height=height,pitch=pitch,pins=pins)

    def points(self,cell,box,orientation):
        m=self.cells[cell];w,h=m['width'],m['height']
        if box[2]-box[0]!=w or box[3]-box[1]!=h or orientation not in ['R0','MX','MY','R180']:
            raise ValueError('Unsupported buffer footprint/orientation')
        points={}
        for pin,rects in m['pins'].items():
            x=(min(r[0] for r in rects)+max(r[2] for r in rects))/2
            y=(min(r[1] for r in rects)+max(r[3] for r in rects))/2
            if orientation in ('MY','R180'):x=w-x
            if orientation in ('MX','R180'):y=h-y
            points[pin]=[(box[0]+x)/self.units,(box[1]+y)/self.units]
        return points


def validate_refinement(refinement,policy,context):
    required={'schema','source_database_sha256','base_policy_sha256','relocation','exchange','boundary'}
    if set(refinement)!=required or refinement['schema']!=1 or refinement['source_database_sha256']!=context['database_sha256']:
        raise ValueError('Invalid refinement policy')
    move=refinement['relocation'];exchange=refinement['exchange']
    if (set(move)!={'instance','cell','max_displacement_sites','row','orientation'} or
        move['instance'] not in context['instances'] or move['instance'] in policy['protected_instances'] or
        context['instances'][move['instance']]['cell'] not in BUFFERS or move['cell'] not in policy['resize_cells'] or
        type(move['max_displacement_sites']) is not int or not 1<=move['max_displacement_sites']<=20 or
        move['row']!='same' or move['orientation']!='same' or
        set(exchange)!={'objective','max_passes'} or exchange['objective']!='worst_wire_pressure' or
        type(exchange['max_passes']) is not int or not 1<=exchange['max_passes']<=32):
        raise ValueError('Unsupported bounded relocation or exchange rule')


def reconstruct(context, coverage, geometry):
    """Rebuild every family branch, including shared trunks and protected delays."""
    if context['database_sha256'] != coverage['source_database_sha256'] or geometry['database_sha256'] != context['database_sha256']:
        raise ValueError('Organization inputs belong to different checkpoints')
    records = {r['net']:r for r in coverage['connections']}
    if len(records) != len(coverage['connections']): raise ValueError('Duplicate branch')
    pin_net = {t['instance']+'/'+t['pin']:n for n,v in context['nets'].items()
        if v['type'] not in ('POWER','GROUND') for t in v['terminals']}
    points = {}
    for r in records.values():
        if connection_terminals(context,r['net']) != {k:r[k] for k in ['driver','consumers','ports']}:
            raise ValueError('Changed branch endpoints')
        for pin in [r['driver'],*r['consumers']]:
            boxes = [s['bbox_dbu'] for s in geometry['pins'][pin]]
            box = [min(b[k] for b in boxes) for k in (0,1)]+[max(b[k] for b in boxes) for k in (2,3)]
            points[pin] = [(box[k]+box[k+2])/2/context['dbu_per_micron'] for k in (0,1)]
    trees = [];seen_nets=set();seen_buffers=set()
    for component in coverage['components']:
        root = component['root']; members=set(component['nets'])
        if seen_nets & members: raise ValueError('Shared branch counted in two trees')
        visiting=set();visited=set();leaves=set();buffers=set()
        def walk(net):
            if net in visiting or net in visited: raise ValueError('Cyclic or reconvergent transport tree')
            visiting.add(net);visited.add(net)
            for pin in records[net]['consumers']:
                cell,terminal=pin.rsplit('/',1)
                if context['instances'][cell]['cell'] in CHAIN_CELLS:
                    if terminal!='A' or cell+'/X' not in pin_net: raise ValueError('Invalid transport cell')
                    downstream=pin_net[cell+'/X']
                    if downstream not in members: raise ValueError('Missing transport branch')
                    buffers.add(cell);walk(downstream)
                else:
                    if pin in leaves: raise ValueError('Duplicated consumer ownership')
                    leaves.add(pin)
            leaves.update('@port/'+p for p in records[net]['ports'])
            visiting.remove(net)
        walk(root)
        if visited!=members or buffers & seen_buffers: raise ValueError('Incomplete or double-counted tree')
        if context['instances'][records[root]['driver'].rsplit('/',1)[0]]['cell'] in CHAIN_CELLS:
            raise ValueError('Tree root is an internal buffer')
        trees.append(dict(root=root,nets=sorted(members),families=component['families'],
            leaves=sorted(leaves),buffer_instances=sorted(n for n in buffers if context['instances'][n]['cell'] in BUFFERS),
            delay_instances=sorted(n for n in buffers if context['instances'][n]['cell'] not in BUFFERS),
            transport_area_um2=sum(area(context['instances'][n]['bbox_dbu'],context['dbu_per_micron']) for n in buffers)))
        seen_nets.update(members);seen_buffers.update(buffers)
    if seen_nets!=set(records): raise ValueError('Missing family branch')
    return dict(source_database_sha256=context['database_sha256'],trees=trees,points_um=points,
        branch_count=len(records),transport_count=len(seen_buffers),
        buffer_count=sum(len(t['buffer_instances']) for t in trees),
        delay_count=sum(len(t['delay_instances']) for t in trees),
        transport_area_um2=sum(t['transport_area_um2'] for t in trees),
        leaf_count=sum(len(t['leaves']) for t in trees))


def area(box,units):
    return (box[2]-box[0])*(box[3]-box[1])/units**2


class Planner:
    def __init__(self, context, coverage, geometry, measurements, library, policy, contract):
        self.context,self.geometry,self.measurements,self.library=context,geometry,measurements,library
        self.model=reconstruct(context,coverage,geometry)
        self.rows={r['net']:r for r in coverage['connections']}
        self.policy=policy;self.contract=contract
        required={'schema','source_database_sha256','contract_sha256','transforms','resize_cells',
            'grouping','placement','protected_instances','max_exchange_passes','boundary'}
        if (set(policy)!=required or policy['schema']!=1 or policy['source_database_sha256']!=context['database_sha256'] or
            policy['transforms']!=['resize_buffer','exchange_leaf_consumers','add_macro_receiver'] or
            policy['grouping']!='same_transport_tree_fixed_drivers_equal_count_exchanges' or
            policy['placement']!=dict(resize='same_origin_free_growth',receiver='free_row_near_macro_pin') or
            policy['resize_cells']!=['sg13cmos5l_buf_2','sg13cmos5l_buf_4','sg13cmos5l_buf_8'] or
            type(policy['max_exchange_passes']) is not int or not 1<=policy['max_exchange_passes']<=32 or
            len(set(policy['protected_instances']))!=len(policy['protected_instances']) or
            not set(policy['protected_instances'])<=set(context['instances'])):
            raise ValueError('Invalid organization policy')
        if not 0<contract['reserve_fraction']<1:raise ValueError('Invalid reserve')
        self.corners=sorted(measurements)
        if set(self.corners)!=set(contract['timing_floors_ns']):raise ValueError('Missing policy corner')
        self.pin_net={t['instance']+'/'+t['pin']:n for n,v in context['nets'].items()
            if v['type'] not in ('POWER','GROUND') for t in v['terminals']}
        self.sizes={cell:sorted({(i['bbox_dbu'][2]-i['bbox_dbu'][0],i['bbox_dbu'][3]-i['bbox_dbu'][1])
            for i in context['instances'].values() if i['cell']==cell}) for cell in BUFFERS}
        if any(len(v)!=1 for v in self.sizes.values()):raise ValueError('Ambiguous physical buffer size')
        for corner in self.corners:
            for cell,sizes in self.sizes.items():
                if not math.isclose(math.prod(sizes[0])/context['dbu_per_micron']**2,
                                    library.buffer(corner,cell)['area_um2'],abs_tol=1e-6):
                    raise ValueError('Liberty and physical buffer areas disagree')
        self.current_area=sum(area(i['bbox_dbu'],context['dbu_per_micron']) for i in context['instances'].values())
        self.area_limit=contract['area_reference']['area_um2']*(1+contract['max_added_area_fraction'])

    def input_cap(self,corner,pin):
        cell,terminal=pin.rsplit('/',1)
        return self.library.capacitance(corner,self.context['instances'][cell]['cell'],terminal)

    def input_edges(self,corner,pin):
        cell,terminal=pin.rsplit('/',1)
        return self.library.capacitance_edges(corner,self.context['instances'][cell]['cell'],terminal)

    def pin_caps(self,corner,pins):
        sums={e:[sum(self.input_edges(corner,p)[e][k] for p in pins) for k in (0,1)] for e in ['rise','fall']}
        return [min(v[0] for v in sums.values()),max(v[1] for v in sums.values())]

    def reconcile_pins(self,nets):
        checked=0
        for net in sorted(nets):
            row=self.rows[net]
            if row['ports']:raise ValueError('Package loading needs a separate model')
            for corner in self.corners:
                actual=self.pin_caps(corner,row['consumers'])
                saved=self.measurements[corner][net]
                if (saved['loads']!=len(row['consumers']) or saved['drivers']!=1 or
                    any(not math.isclose(a,b,rel_tol=0,abs_tol=1e-7) for a,b in zip(actual,saved['pin_cap_pf']))):
                    raise ValueError('Library pin loads disagree with saved STA: '+net+' '+corner)
                checked+=1
        return checked

    def _placement(self,box,removed=()):
        contained=any(r['bbox_dbu'][0]<=box[0]<box[2]<=r['bbox_dbu'][2] and
                      r['bbox_dbu'][1]<=box[1]<box[3]<=r['bbox_dbu'][3] for r in self.context['rows'])
        instances=sorted(n for n,i in self.context['instances'].items()
                         if n not in removed and overlaps(box,i['bbox_dbu']))
        blockages=[index for index,b in enumerate(self.context.get('placement_blockages',[]))
                   if overlaps(box,b['bbox_dbu'])]
        return dict(footprint_dbu=box,row_contained=contained,overlapping_instances=instances,
            overlapping_blockages=blockages,pass_geometric_screen=contained and not instances and not blockages,
            legal_placement_qualified=False)

    def _free(self,box,removed=()):
        return self._placement(box,removed)['pass_geometric_screen']

    def _finish(self,kind,root,targets,edits,delta,geometry_pass,branches,notes):
        limits={}
        for corner in self.corners:
            limits[corner]={}
            for net,pins,driver_cell in branches:
                cap=self.pin_caps(corner,pins)[1]
                limit=self.library.buffer(corner,driver_cell)['output_limit_pf']
                limits[corner][net]=dict(pin_cap_pf=cap,wire_budget_pf=limit*(1-self.contract['reserve_fraction'])-cap,
                    saved_wire_cap_pf=self.measurements[corner][net]['wire_cap_pf'][1])
        return dict(kind=kind,root=root,targets=sorted(targets),edits=edits,added_area_um2=delta,
            cumulative_area_um2=self.current_area+delta,area_screen_pass=self.current_area+delta<=self.area_limit+1e-6,
            footprint_screen_pass=geometry_pass,branch_budgets=limits,notes=notes,
            execution_admitted=False,electrical_qualified=False,timing_qualified=False,
            required_checks=['independent_exact_edit_and_functional_identity','complete_family_and_upstream_STA',
                'placement_power_and_pin_geometry','whole_chip_routing_and_electrical_revalidation'])

    def resize(self,root,targets,cell):
        edits=[];delta=0;free=True;branches=[];upstream={c:{} for c in self.corners};placement=[]
        for net in sorted(targets):
            row=self.rows[net];inst=row['driver'].rsplit('/',1)[0];old=row['driver_cell']
            if old not in BUFFERS or inst in self.policy['protected_instances'] or cell not in self.policy['resize_cells']:
                raise ValueError('Resize touches an unsupported or protected driver')
            box=self.context['instances'][inst]['bbox_dbu'];w,h=self.sizes[cell][0]
            new=[box[0],box[1],box[0]+w,box[1]+h]
            if area(new,1)<=area(box,1):return None
            place=self._placement(new,{inst});placement.append(dict(instance=inst,**place))
            free &= place['pass_geometric_screen'] and not any(overlaps(new,e['footprint_dbu']) for e in edits)
            delta+=area(new,self.context['dbu_per_micron'])-area(box,self.context['dbu_per_micron'])
            edits.append(dict(instance=inst,old_cell=old,cell=cell,footprint_dbu=new,net=net))
            branches.append((net,row['consumers'],cell));parent=self.pin_net[inst+'/A']
            if parent not in self.rows:raise ValueError('Missing upstream branch')
            for corner in self.corners:
                deltas=upstream[corner].setdefault(parent,dict(rise=0,fall=0))
                for edge in deltas:
                    deltas[edge]+=self.library.capacitance_edges(corner,cell,'A')[edge][1]-self.library.capacitance_edges(corner,old,'A')[edge][1]
        result=self._finish('resize_buffer',root,targets,edits,delta,bool(free),branches,
            ['Output limits use the proposed driver. Saved wire loads are a conditional comparison, not a prediction.',
             'Fixed-origin growth must have free row space; changed pin shapes and timing need recollection.'])
        result['upstream']={c:{n:dict(added_pin_cap_pf=max(d.values()),added_pin_cap_pf_by_edge=d,
            saved_total_cap_pf=self.measurements[c][n]['capacitance']['actual'],
            total_with_saved_wire_pf=self.measurements[c][n]['wire_cap_pf'][1]+
                max(sum(self.input_edges(c,p)[e][1] for p in self.rows[n]['consumers'])+d[e] for e in d),
            trial_limit_pf=self.measurements[c][n]['capacitance']['limit']*(1-self.contract['reserve_fraction']))
            for n,d in parents.items()} for c,parents in upstream.items()}
        result['placement_screen']=placement
        return result

    def wire_pressure(self,net):
        row=self.rows[net];pressure=[]
        for corner in self.corners:
            cap=self.pin_caps(corner,row['consumers'])[1]
            budget=self.library.buffer(corner,row['driver_cell'])['output_limit_pf']*(1-self.contract['reserve_fraction'])-cap
            if budget<=0:raise ValueError('No positive wire budget')
            pressure.append(self.measurements[corner][net]['wire_cap_pf'][1]/budget)
        return max(pressure)

    def exchange(self,root,targets,*,objective='total_span',max_passes=None):
        passes=self.policy['max_exchange_passes'] if max_passes is None else max_passes
        if objective not in ('total_span','worst_wire_pressure') or type(passes) is not int or not 1<=passes<=32:
            raise ValueError('Invalid exchange objective or bound')
        tree=next(t for t in self.model['trees'] if t['root']==root)
        groups={}
        for net in tree['nets']:
            r=self.rows[net];inst=r['driver'].rsplit('/',1)[0]
            if (r['driver_cell'] not in BUFFERS or inst in self.policy['protected_instances'] or r['ports']):continue
            groups[net]=r['consumers'][:]
        def movable(pin):
            inst=pin.rsplit('/',1)[0];cell=self.context['instances'][inst]
            return not cell['macro'] and cell['cell'] not in CHAIN_CELLS|{FF} and inst not in self.policy['protected_instances']
        original=deepcopy(groups);points=self.model['points_um']
        score=lambda n,p:span([points[self.rows[n]['driver']],*[points[x] for x in p]])
        pressures={n:self.wire_pressure(n) for n in targets if n in groups}
        spans={n:score(n,pins) for n,pins in original.items()}
        if any(spans[n]<=0 for n in pressures):raise ValueError('Cannot scale a zero target span')
        def rank(replacements):
            if objective=='total_span':return ()
            return tuple(sorted((round(pressures[n]*score(n,replacements.get(n,groups[n]))/spans[n],12)
                                 for n in pressures),reverse=True))
        swaps=[]
        for _ in range(passes):
            best=None
            for a in sorted(set(targets)&set(groups)):
                for b in sorted(groups):
                    if a==b or self.rows[a]['driver_cell']!=self.rows[b]['driver_cell']:continue
                    old=score(a,groups[a])+score(b,groups[b])
                    for p in groups[a]:
                        if not movable(p):continue
                        for q in groups[b]:
                            if not movable(q):continue
                            aa=sorted(set(groups[a])-{p}|{q});bb=sorted(set(groups[b])-{q}|{p})
                            # Preserve both branches' pin-capacitance upper bound
                            # in every corner; do not move an electrical cost to a neighbor.
                            if any(abs(self.input_edges(c,p)[e][1]-self.input_edges(c,q)[e][1])>1e-10
                                   for c in self.corners for e in ['rise','fall']):continue
                            gain=old-score(a,aa)-score(b,bb)
                            if gain<=1e-6 or score(a,aa)>score(a,groups[a])+1e-6 or score(b,bb)>score(b,groups[b])+1e-6:continue
                            ranking=rank({a:aa,b:bb})
                            if ranking>rank({}):continue
                            choice=(ranking,-gain,a,b,p,q,aa,bb)
                            if best is None or choice[:6]<best[:6]:best=choice
            if best is None:break
            _,_,a,b,p,q,aa,bb=best;groups[a]=aa;groups[b]=bb
            swaps.append(dict(first_net=a,second_net=b,first_pin=p,second_pin=q))
        edits=[dict(net=n,driver=self.rows[n]['driver'],before=original[n],after=groups[n])
               for n in sorted(groups) if groups[n]!=original[n]]
        validate_exchanges(self.context,self.rows,tree,edits,self.policy['protected_instances'])
        result=self._finish('exchange_leaf_consumers',root,targets,edits,0,True,
            [(e['net'],e['after'],self.rows[e['net']]['driver_cell']) for e in edits],
            ['Same electrical root, fixed driver cells/locations, unchanged per-branch consumer count.',
             'Every corner retains or reduces each changed branch pin-capacitance upper bound.',
             'Pin-envelope HPWL is a geometric screen; it does not predict routed capacitance or congestion.'])
        result.update(swaps=swaps,geometry={n:dict(before_span_um=score(n,original[n]),after_span_um=score(n,groups[n]))
            for n in sorted(groups)},improved_targets=sorted(n for n in targets if n in groups and score(n,groups[n])<score(n,original[n])-1e-6))
        result['objective']=objective
        result['wire_span_scenario']={n:dict(saved_wire_to_budget=pressures[n],
            scaled_wire_to_budget=pressures[n]*score(n,groups[n])/spans[n],
            physical_prediction=False) for n in pressures}
        return result

    def relocate(self,rule,masters):
        inst=rule['instance'];info=self.context['instances'][inst];old=info['bbox_dbu'];cell=rule['cell']
        if inst in self.policy['protected_instances'] or info['cell'] not in BUFFERS:raise ValueError('Protected relocation')
        net=self.pin_net[inst+'/X'];parent=self.pin_net[inst+'/A'];root=self.rows[net]['distribution_root']
        if {t['pin'] for n,v in self.context['nets'].items() if v['type'] not in ('POWER','GROUND')
            for t in v['terminals'] if t['instance']==inst}!={'A','X'}:raise ValueError('Unaccounted incident signal pin')
        before=masters.points(info['cell'],old,info['orientation'])
        if any(before[p]!=self.model['points_um'][inst+'/'+p] for p in before):raise ValueError('LEF pins disagree with saved geometry')
        m=masters.cells[cell];pitch=m['pitch'];width=m['width'];height=m['height']
        if (width,height)!=self.sizes[cell][0]:raise ValueError('LEF master differs from physical size')
        rows=[r for r in self.context['rows'] if r['bbox_dbu'][1]==old[1] and r['bbox_dbu'][3]==old[3]
              and r['bbox_dbu'][0]<=old[0]<old[2]<=r['bbox_dbu'][2]]
        if len(rows)!=1 or (old[0]-rows[0]['bbox_dbu'][0])%pitch:raise ValueError('Ambiguous or off-grid original row')
        base=self.resize(root,[net],cell)
        if base is None:raise ValueError('Relocation requires a stronger buffer')
        candidates=[]
        for shift in range(-rule['max_displacement_sites'],rule['max_displacement_sites']+1):
            if shift==0:continue
            box=[old[0]+shift*pitch,old[1],old[0]+shift*pitch+width,old[1]+height]
            place=self._placement(box,{inst})
            if not place['pass_geometric_screen']:continue
            points=masters.points(cell,box,info['orientation']);candidate=deepcopy(base)
            candidate.update(kind='move_resize_buffer',footprint_screen_pass=True,
                placement_screen=[dict(instance=inst,**place)],displacement_um=abs(shift*pitch)/self.context['dbu_per_micron'],
                notes=['Same row and orientation, pinned site grid, all incident A/X connections costed; legal placement and power remain unqualified.'])
            candidate['edits'][0].update(footprint_dbu=box,old_footprint_dbu=old,orientation=info['orientation'])
            incident={}
            for n in [parent,net]:
                row=self.rows[n];terminals=[row['driver'],*row['consumers']]
                old_points=[self.model['points_um'][p] for p in terminals]
                new_points=[points[p.rsplit('/',1)[1]] if p.startswith(inst+'/') else self.model['points_um'][p] for p in terminals]
                incident[n]=dict(before_span_um=span(old_points),after_span_um=span(new_points))
            candidate['incident_geometry']=incident;candidate['old_pin_points_um']=before;candidate['new_pin_points_um']=points
            candidates.append(candidate)
        return sorted(candidates,key=lambda c:(sum(v['after_span_um']-v['before_span_um'] for v in c['incident_geometry'].values()),
            c['displacement_um'],c['edits'][0]['footprint_dbu']))

    def receiver(self,root,net,cell):
        r=self.rows[net];macro=[p for p in r['consumers'] if self.context['instances'][p.rsplit('/',1)[0]]['macro']]
        if len(macro)!=1 or '/A_DIN[' not in macro[0] or cell not in BUFFERS:raise ValueError('Require one macro data receiver')
        point=[v*self.context['dbu_per_micron'] for v in self.model['points_um'][macro[0]]]
        box=placement_hint(self.context,self.sizes[cell][0],point)
        result=self._finish('add_macro_receiver',root,[net],[dict(net=net,receiver=macro[0],cell=cell,footprint_dbu=box)],
            area(box,self.context['dbu_per_micron']),self._free(box),[],
            ['Separate the macro receiver while retaining all other consumers. New wire capacitance is unknown.',
             'The existing receiver-buffer compiler can represent this operation; no execution is admitted.'])
        result['receiver_budgets']={c:dict(new_input_cap_pf=self.library.buffer(c,cell)['input_cap_pf'][1],
            removed_input_cap_pf=self.input_cap(c,macro[0])[1],
            source_total_with_saved_wire_pf=self.measurements[c][net]['wire_cap_pf'][1]+max(
                sum(self.input_edges(c,p)[e][1] for p in r['consumers'] if p!=macro[0])+
                self.library.capacitance_edges(c,cell,'A')[e][1] for e in ['rise','fall']),
            new_branch_wire_budget_pf=self.library.buffer(c,cell)['output_limit_pf']*(1-self.contract['reserve_fraction'])-
                self.input_cap(c,macro[0])[1]) for c in self.corners}
        result['placement_screen']=[self._placement(box)]
        return result


def validate_exchanges(context,rows,tree,edits,protected):
    seen=set();before=[];after=[]
    pin_net={t['instance']+'/'+t['pin']:n for n,v in context['nets'].items()
        if v['type'] not in ('POWER','GROUND') for t in v['terminals']}
    def root(net):
        visited=set()
        while True:
            if net in visited:raise ValueError('Cyclic source tree')
            visited.add(net);driver=connection_terminals(context,net)['driver'];inst=driver.rsplit('/',1)[0]
            if context['instances'][inst]['cell'] not in CHAIN_CELLS:return net
            if driver!=inst+'/X' or inst+'/A' not in pin_net:raise ValueError('Malformed source transport')
            net=pin_net[inst+'/A']
    for edit in edits:
        net=edit['net']
        if net in seen or net not in tree['nets']:raise ValueError('Duplicate or cross-tree exchange')
        seen.add(net);row=rows[net];inst=row['driver'].rsplit('/',1)[0]
        if root(net)!=tree['root'] or connection_terminals(context,net)!={k:row[k] for k in ['driver','consumers','ports']}:
            raise ValueError('Exchange endpoints do not share the declared electrical root')
        if (row['driver_cell'] not in BUFFERS or inst in protected or row['ports'] or edit['driver']!=row['driver'] or
            edit['before']!=row['consumers'] or len(edit['after'])!=len(edit['before']) or
            len(set(edit['after']))!=len(edit['after'])):raise ValueError('Invalid exchange source or consumer count')
        before+=edit['before'];after+=edit['after']
    if Counter(before)!=Counter(after) or len(set(after))!=len(after):raise ValueError('Lost, duplicated or external consumer')
    moved={pin for edit in edits for pin in set(edit['after'])^set(edit['before'])}
    for pin in moved:
        inst,terminal=pin.rsplit('/',1);cell=context['instances'][inst]
        if cell['macro'] or cell['cell'] in CHAIN_CELLS|{FF} or inst in protected:
            raise ValueError('Exchange touches state, macro or a protected transport branch')


def portfolios(candidates,targets,current_area,area_limit):
    roots=sorted({c['root'] for c in candidates});options=[]
    for root in roots:
        rows=[c for c in candidates if c['root']==root and c['footprint_screen_pass'] and c['edits'] and
            (c['kind']!='exchange_leaf_consumers' or set(c['improved_targets'])==set(c['targets']))]
        options.append(rows)
    output=[]
    for choices in product(*options):
        covered={n for c in choices for n in c['targets']}
        if covered!=set(targets):raise ValueError('Incomplete portfolio target coverage')
        delta=sum(c['added_area_um2'] for c in choices)
        boxes=[e['footprint_dbu'] for c in choices for e in c['edits'] if 'footprint_dbu' in e]
        nonoverlap=not any(overlaps(a,b) for i,a in enumerate(boxes) for b in boxes[i+1:])
        output.append(dict(candidates=[c['id'] for c in choices],added_area_um2=delta,
            area_screen_pass=current_area+delta<=area_limit+1e-6,combined_footprints_disjoint=nonoverlap,
            geometrically_screened_only=True,execution_admitted=False))
    return sorted(output,key=lambda r:(r['added_area_um2'],r['candidates']))


def mechanism_screen(candidate,measurements,reserve):
    """A falsifiable reason to try a probe, never electrical qualification.

    Saved wire is held constant for sizing. For exchanged or relocated pins,
    proportional span scaling is an explicitly conditional ranking scenario.
    A new receiver branch still has unmeasured wire even when it has a budget.
    """
    checks=[];kind=candidate['kind']
    for corner,branches in candidate['branch_budgets'].items():
        for net,b in branches.items():
            if kind=='exchange_leaf_consumers':continue
            ratio=1
            if kind=='move_resize_buffer':
                g=candidate['incident_geometry'][net]
                if g['before_span_um']<=0:raise ValueError('Cannot scale zero incident span')
                ratio=g['after_span_um']/g['before_span_um']
            checks.append(b['saved_wire_cap_pf']*ratio<=b['wire_budget_pf'])
    for corner,parents in candidate.get('upstream',{}).items():
        for net,b in parents.items():
            total=b['total_with_saved_wire_pf']
            if kind=='move_resize_buffer':
                g=candidate['incident_geometry'][net]
                if g['before_span_um']<=0:raise ValueError('Cannot scale zero incident span')
                total+=measurements[corner][net]['wire_cap_pf'][1]*(g['after_span_um']/g['before_span_um']-1)
            checks.append(total<=b['trial_limit_pf'])
    if kind=='exchange_leaf_consumers':
        checks=[len(candidate['wire_span_scenario'])==len(candidate['targets']),
                all(v['scaled_wire_to_budget']<=1 for v in candidate['wire_span_scenario'].values())]
    if kind=='add_macro_receiver':
        for corner,b in candidate['receiver_budgets'].items():
            net=candidate['targets'][0]
            checks.extend([b['source_total_with_saved_wire_pf']<=measurements[corner][net]['capacitance']['limit']*(1-reserve),
                           b['new_branch_wire_budget_pf']>0])
    return dict(pass_conditional_screen=bool(candidate['edits']) and bool(checks) and all(checks),
        physical_prediction=False,timing_qualified=False,
        assumption='Saved wire for unchanged geometry; branch-specific proportional span scaling for changed geometry. New receiver wire and all slew/timing are unknown.')


def screen_exchange_identity(reference,edits):
    """Check a virtual regrouping against an independently saved Yosys readback.

    Only scalar input exchanges are supported. This edits an in-memory copy,
    compares the complete circuit after buffer contraction, and discards it.
    It is not a readback of a new physical implementation or a timing check.
    """
    if not edits:raise ValueError('Require an actual exchange')
    candidate=deepcopy(reference);assigned=set();before=[];after=[];changed=0
    def bit(module,terminal,direction):
        inst,pin=terminal.rsplit('/',1);cell=module['cells'][inst]
        if cell['port_directions'].get(pin)!=direction or len(cell['connections'][pin])!=1:
            raise ValueError('Require a scalar readback terminal with the expected direction')
        return cell['connections'][pin][0]
    for edit in edits:
        driver=edit['driver'];inst=driver.rsplit('/',1)[0]
        if reference['cells'][inst]['type'] not in BUFFERS:raise ValueError('Require an identity buffer driver')
        wire=bit(reference,driver,'output')
        for pin in edit['before']:
            if bit(reference,pin,'input')!=wire:raise ValueError('Exchange disagrees with saved readback')
        before+=edit['before'];after+=edit['after']
        if len(edit['before'])!=len(edit['after']):raise ValueError('Changed branch consumer count')
        for terminal in edit['after']:
            if terminal in assigned:raise ValueError('Duplicate exchanged terminal')
            assigned.add(terminal);old=bit(reference,terminal,'input')
            inst,pin=terminal.rsplit('/',1)
            candidate['cells'][inst]['connections'][pin]=[wire]
            changed+=old!=wire
    if Counter(before)!=Counter(after):raise ValueError('Exchange drops or adds a consumer')
    if not changed:raise ValueError('Require changed input connections')
    if _bufferless(reference)!=_bufferless(candidate):raise ValueError('Changed functional source after buffer contraction')
    return dict(checked=True,rewired_scalar_inputs=changed,whole_circuit_buffer_contracted_identity=True,
        actual_physical_edit=False,independent_new_physical_readback=False,timing_qualified=False)
