"""Exact copies of two pinned combinational gates for regional experiments.

Keep the original state, cells, clocks, holds and interfaces. The independent
Verilog readback folds only a declared same-cell, same-input copy. This proves
signal connectivity under the pinned cell interpretation, not physical timing.
"""
from copy import deepcopy
import math
import re

from mapped_physical import connection_signature
from physical_connections import connection_terminals
from physical_floorplan import overlaps
from physical_organization_edits import FIXED
from physical_buffer_repair import BUFFERS, compare_buffer_repair


CELLS = {'sg13cmos5l_xor2_1': 'X', 'sg13cmos5l_nor2_1': 'Y'}


def _footprint(context, box, size, pitch, orientation, other_boxes):
    if (len(box) != 4 or any(type(v) is not int for v in box)
            or (box[2]-box[0], box[3]-box[1]) != size):
        raise ValueError('Footprint differs from its pinned master')
    rows = [r for r in context['rows'] if r['bbox_dbu'][0] <= box[0] < box[2] <= r['bbox_dbu'][2]
            and r['bbox_dbu'][1] == box[1] < box[3] == r['bbox_dbu'][3]
            and (box[0]-r['bbox_dbu'][0]) % pitch == 0]
    if (not rows or any(overlaps(box, i['bbox_dbu']) for i in context['instances'].values())
            or any(overlaps(box, b['bbox_dbu']) for b in context['placement_blockages'])
            or any(overlaps(box, b) for b in other_boxes)):
        raise ValueError('Illegal or occupied decoder-copy footprint')
    parity = {i['orientation'] in ('MX', 'R180') for i in context['instances'].values()
              if not i['macro'] and i['bbox_dbu'][1] == box[1] and i['bbox_dbu'][3] == box[3]}
    if len(parity) != 1 or orientation not in ('R0','MX') or (orientation == 'MX') not in parity:
        raise ValueError('Copy orientation conflicts with row rails')


def gate(context, name):
    info = context['instances'][name]
    if info['macro'] or info['cell'] not in CELLS:
        raise ValueError('Only the pinned combinational XOR/NOR cells may be copied')
    pins = {}
    for net, row in context['nets'].items():
        if row['type'] in ('POWER', 'GROUND'):
            continue
        for terminal in row['terminals']:
            if terminal['instance'] != name:
                continue
            pin = terminal['pin']
            if pin in pins or row['type'] != 'SIGNAL' or row['ports']:
                raise ValueError('Invalid gate signal or package/clock boundary')
            pins[pin] = (net, terminal['direction'])
    output = CELLS[info['cell']]
    if (set(pins) != {'A', 'B', output} or
            any(pins[p][1] != 'INPUT' for p in ('A', 'B')) or pins[output][1] != 'OUTPUT'):
        raise ValueError('Malformed pinned gate interface')
    if pins[output][0] in {pins[p][0] for p in ('A', 'B')}:
        raise ValueError('Gate feedback cannot be replicated')
    for net, _ in pins.values():
        connection_terminals(context, net)
    return {p:n for p,(n,_) in pins.items()}


def validate_plan(plan, context):
    fields = {'schema', 'source_database_sha256', 'site_pitch_dbu', 'copies', 'added_area_um2'}
    if (set(plan) not in (fields, fields | {'input_buffers'})
            or plan['schema'] != 1 or plan['source_database_sha256'] != context['database_sha256']
            or type(plan['site_pitch_dbu']) is not int or plan['site_pitch_dbu'] <= 0
            or not plan['copies']):
        raise ValueError('Invalid or unbound decoder-copy plan')
    pitch, units = plan['site_pitch_dbu'], context['dbu_per_micron']
    sources, names, nets, boxes = set(), set(), set(), []
    total = 0
    for op in plan['copies']:
        if set(op) != {'source', 'instance', 'new_net', 'consumers', 'footprint_dbu', 'orientation'}:
            raise ValueError('Invalid decoder-copy fields')
        identifiers = [op['source'], op['instance'], op['new_net'], *op['consumers']]
        if any(not isinstance(s, str) or not re.fullmatch(r'[A-Za-z0-9_./\[\]$-]+', s) for s in identifiers):
            raise ValueError('Unsafe decoder-copy identifier')
        pins = gate(context, op['source']); old = context['instances'][op['source']]
        output = CELLS[old['cell']]
        consumers = connection_terminals(context, pins[output])['consumers']
        moved = set(op['consumers'])
        if (op['source'] in sources or op['instance'] in names or op['instance'] in context['instances']
                or op['new_net'] in nets or op['new_net'] in context['nets']
                or len(moved) != len(op['consumers']) or not moved or not moved < set(consumers)):
            raise ValueError('Duplicate copy or incomplete/disallowed consumer partition')
        # Copies are independent leaves of the edit plan, never inputs to one another.
        if any(p.rsplit('/', 1)[0] in {o['source'] for o in plan['copies']} for p in moved):
            raise ValueError('Interdependent decoder copies')
        box, original = op['footprint_dbu'], old['bbox_dbu']
        _footprint(context, box, (original[2]-original[0], original[3]-original[1]), pitch, op['orientation'], boxes)
        total += (box[2]-box[0])*(box[3]-box[1])/units**2
        sources.add(op['source']); names.add(op['instance']); nets.add(op['new_net']); boxes.append(box)
    buffered = set()
    for op in plan.get('input_buffers', []):
        if (set(op) != {'source','pin','parent','instance','new_net','cell','footprint_dbu','orientation'}
                or op['source'] not in sources or op['pin'] not in ('A','B')
                or op['cell'] not in BUFFERS or (op['source'],op['pin']) in buffered
                or op['parent'] != gate(context,op['source'])[op['pin']]
                or op['instance'] in names or op['instance'] in context['instances']
                or op['new_net'] in nets or op['new_net'] in context['nets']):
            raise ValueError('Invalid or duplicate input distribution buffer')
        if any(not isinstance(op[k],str) or not re.fullmatch(r'[A-Za-z0-9_./\[\]$-]+',op[k])
               for k in ('source','pin','parent','instance','new_net','cell')):
            raise ValueError('Unsafe input-buffer identifier')
        sizes = {(i['bbox_dbu'][2]-i['bbox_dbu'][0],i['bbox_dbu'][3]-i['bbox_dbu'][1])
                 for i in context['instances'].values() if i['cell']==op['cell']}
        if len(sizes)!=1:raise ValueError('Missing or ambiguous pinned buffer dimensions')
        box=op['footprint_dbu']
        _footprint(context,box,sizes.pop(),pitch,op['orientation'],boxes)
        total+=(box[2]-box[0])*(box[3]-box[1])/units**2
        buffered.add((op['source'],op['pin']));names.add(op['instance']);nets.add(op['new_net']);boxes.append(box)
    if (type(plan['added_area_um2']) not in (int, float) or not math.isfinite(plan['added_area_um2'])
            or abs(plan['added_area_um2']-total) > 1e-6):
        raise ValueError('Incorrect declared decoder area')
    return dict(copies=len(sources), input_buffers=len(buffered), added_area_um2=total)


def render_tcl(plan, context, output_dir):
    validate_plan(plan, context)
    if not re.fullmatch(r'/probe/[A-Za-z0-9_-]+', output_dir):
        raise ValueError('Expected a local probe output directory')
    literal = lambda s:'{'+s+'}'
    touched = {n for op in plan['copies'] for n in gate(context, op['source']).values()}
    lines = ['# Identical combinational copies; original cells and clocks stay fixed.',
             'set_routing_layers -signal Metal2-Metal4 -clock Metal2-Metal4',
             'set_global_routing_layer_adjustment * 0.3', 'global_route -start_incremental']
    for net in sorted(touched):
        row = connection_terminals(context, net)
        lines += [f'set wire [$::block findNet {literal(net)}]',
            'if {$wire eq "NULL" || [$wire getSigType] ne "SIGNAL" || [llength [$wire getBTerms]] != 0} {error "Changed source net"}',
            'set actual {}', 'foreach it [$wire getITerms] {lappend actual "[[$it getInst] getName]/[[$it getMTerm] getName]"}',
            'if {[lsort $actual] ne [lsort [list '+' '.join(map(literal, [row['driver'], *row['consumers']]))+']]} {error "Changed source terminals"}']
    for op in plan['copies']:
        pins = gate(context, op['source']); cell = context['instances'][op['source']]['cell']
        x,y = op['footprint_dbu'][:2]
        lines += [f'if {{[[$::block findInst {literal(op["source"])}] getMaster] ne [[ord::get_db] findMaster {literal(cell)}]}} {{error "Changed gate master"}}',
            f'if {{[$::block findInst {literal(op["instance"])}] ne "NULL" || [$::block findNet {literal(op["new_net"])}] ne "NULL"}} {{error "Copy name collision"}}',
            f'set copy [odb::dbInst_create $::block [[ord::get_db] findMaster {literal(cell)}] {literal(op["instance"])}]',
            f'odb::dbNet_create $::block {literal(op["new_net"])}',
            f'$copy setOrient {op["orientation"]}', f'$copy setLocation {x} {y}', '$copy setPlacementStatus PLACED']
        for pin in ('A','B'):
            lines.append(f'[$copy findITerm {pin}] connect [$::block findNet {literal(pins[pin])}]')
        lines.append(f'[$copy findITerm {CELLS[cell]}] connect [$::block findNet {literal(op["new_net"])}]')
        for pin in op['consumers']:
            lines += [f'set it [$::block findITerm {literal(pin)}]', '$it disconnect',
                      f'$it connect [$::block findNet {literal(op["new_net"])}]']
    copies={o['source']:o['instance'] for o in plan['copies']}
    for op in plan.get('input_buffers',[]):
        x,y=op['footprint_dbu'][:2]
        lines += [f'if {{[$::block findInst {literal(op["instance"])}] ne "NULL" || [$::block findNet {literal(op["new_net"])}] ne "NULL"}} {{error "Input-buffer name collision"}}',
            f'set buffer [odb::dbInst_create $::block [[ord::get_db] findMaster {literal(op["cell"])}] {literal(op["instance"])}]',
            f'odb::dbNet_create $::block {literal(op["new_net"])}',
            f'$buffer setOrient {op["orientation"]}',f'$buffer setLocation {x} {y}','$buffer setPlacementStatus PLACED',
            f'[$buffer findITerm A] connect [$::block findNet {literal(op["parent"])}]',
            f'[$buffer findITerm X] connect [$::block findNet {literal(op["new_net"])}]']
        for inst in (op['source'],copies[op['source']]):
            lines += [f'set it [$::block findITerm {literal(inst+"/"+op["pin"])}]', '$it disconnect',
                      f'$it connect [$::block findNet {literal(op["new_net"])}]']
    lines += ['check_placement -verbose', 'global_connect', 'global_route -end_incremental -allow_congestion',
              'estimate_parasitics -global_routing', f'write_guide {output_dir}/repaired.guide',
              f'write_verilog {output_dir}/repaired.v', f'write_db {output_dir}/repaired.odb']
    return '\n'.join(lines)+'\n'


def compare_readback(reference, repaired, copies, input_buffers=()):
    """Check actual Verilog connectivity by merging identical gate outputs.

    This is independent of placement and of the Tcl generator. All original
    cells and all nets must match after precisely the declared copies are folded.
    """
    original, current = reference['cells'], repaired['cells']
    pairs = {o['instance']:o['source'] for o in copies}
    buffers={o['instance']:o['cell'] for o in input_buffers}
    if (len(pairs) != len(copies) or not pairs or len(set(pairs.values())) != len(pairs)
            or len(buffers)!=len(input_buffers) or set(pairs)&set(buffers)
            or set(current) != set(original) | set(pairs) | set(buffers)
            or set(original) & (set(pairs)|set(buffers))):
        raise ValueError('Unexpected decoder-copy membership')
    if any(cell not in BUFFERS or current[n]['type']!=cell for n,cell in buffers.items()):
        raise ValueError('Unexpected input distribution cell')
    for name, before in original.items():
        after = current[name]
        for key in ('type', 'parameters', 'port_directions'):
            if before.get(key, {}) != after.get(key, {}):
                raise ValueError('Changed original cell: '+name)
    drivers = {}
    def driver(bit):
        if type(bit) is not int or bit in drivers:
            raise ValueError('Constant or multiply driven physical net')
        drivers[bit] = True
    for p in repaired['ports'].values():
        if p['direction'] == 'input':
            for b in p['bits']: driver(b)
    for c in current.values():
        if set(c['connections']) != set(c['port_directions']):
            raise ValueError('Unclassified physical terminal')
        for pin,bits in c['connections'].items():
            if c['port_directions'][pin] == 'output':
                for b in bits: driver(b)
    aliases = {}
    for name, source in pairs.items():
        c, s = current[name], current[source]
        if s['type'] not in CELLS or c['type'] != s['type'] or c.get('parameters') or s.get('parameters'):
            raise ValueError('Require identical pinned combinational gates')
        output = CELLS[s['type']]; directions = {'A':'input','B':'input',output:'output'}
        if any(v['port_directions'] != directions or set(v['connections']) != set(directions)
               or any(len(b) != 1 for b in v['connections'].values()) for v in (s,c)):
            raise ValueError('Malformed decoder-copy interface')
        if any(c['connections'][p] != s['connections'][p] for p in ('A','B')):
            raise ValueError('Copy inputs differ from original gate')
        old, new = s['connections'][output][0], c['connections'][output][0]
        if old == new or new in aliases or old in aliases or new in aliases.values():
            raise ValueError('Shorted or interdependent decoder output')
        aliases[new] = old
    reduced = deepcopy(repaired)
    for name in pairs: del reduced['cells'][name]
    def fold(bits):
        for bit in bits:
            if bit not in ('0','1') and (type(bit) is not int or bit not in drivers):
                raise ValueError('Unknown or undriven physical signal')
        return [aliases.get(b,b) for b in bits]
    for p in reduced['ports'].values(): p['bits'] = fold(p['bits'])
    for c in reduced['cells'].values():
        for pin,bits in c['connections'].items(): c['connections'][pin] = fold(bits)
    transport = compare_buffer_repair(reference,reduced) if buffers else None
    if not buffers and connection_signature(reference) != connection_signature(reduced):
        raise ValueError('Changed connectivity after folding decoder copies')
    return dict(original_cells=len(original), copied_gates=pairs, input_distribution=transport,
                exact_folded_connectivity=True)


def verify_context(plan, before, after):
    """Check actual ODB terminals, power, cell placement and immutable geometry."""
    result = validate_plan(plan, before)
    expected = deepcopy(before)
    for op in plan['copies']:
        name, source = op['instance'], op['source']; old = before['instances'][source]
        pins = gate(before, source); output = CELLS[old['cell']]; net = pins[output]
        moved = set(op['consumers'])
        removed = [t for t in expected['nets'][net]['terminals'] if t['instance']+'/'+t['pin'] in moved]
        expected['nets'][net]['terminals'] = [t for t in expected['nets'][net]['terminals'] if t not in removed]
        expected['nets'][op['new_net']] = dict(type='SIGNAL', ports=[], terminals=removed+[
            dict(instance=name,pin=output,direction='OUTPUT')])
        for pin in ('A','B'):
            expected['nets'][pins[pin]]['terminals'].append(dict(instance=name,pin=pin,direction='INPUT'))
        for net,pin in [('VPWR','VDD'),('VGND','VSS')]:
            expected['nets'][net]['terminals'].append(dict(instance=name,pin=pin,direction='INOUT'))
        expected['instances'][name] = dict(cell=old['cell'],macro=False,orientation=op['orientation'],
            bbox_dbu=op['footprint_dbu'],bbox=[v/before['dbu_per_micron'] for v in op['footprint_dbu']])
    copies={o['source']:o['instance'] for o in plan['copies']}
    for op in plan.get('input_buffers',[]):
        name=op['instance'];targets={op['source'],copies[op['source']]};terms=expected['nets'][op['parent']]['terminals']
        moved=[t for t in terms if t['instance'] in targets and t['pin']==op['pin']]
        if len(moved)!=2:raise ValueError('Missing input-distribution terminals')
        expected['nets'][op['parent']]['terminals']=[t for t in terms if t not in moved]+[dict(instance=name,pin='A',direction='INPUT')]
        expected['nets'][op['new_net']]=dict(type='SIGNAL',ports=[],terminals=moved+[dict(instance=name,pin='X',direction='OUTPUT')])
        for net,pin in [('VPWR','VDD'),('VGND','VSS')]:
            expected['nets'][net]['terminals'].append(dict(instance=name,pin=pin,direction='INOUT'))
        expected['instances'][name]=dict(cell=op['cell'],macro=False,orientation=op['orientation'],
            bbox_dbu=op['footprint_dbu'],bbox=[v/before['dbu_per_micron'] for v in op['footprint_dbu']])
    norm = lambda c:{n:(v['type'],sorted(v['ports']),sorted((t['instance'],t['pin'],t['direction']) for t in v['terminals'])) for n,v in c['nets'].items()}
    if norm(expected) != norm(after): raise ValueError('Unexpected signal, clock or power edit')
    if expected['instances'] != after['instances']: raise ValueError('Unexpected instance or placement change')
    if (any(before[k] != after[k] for k in FIXED) or before['macro_pins'] != after['macro_pins']
            or before['dbu_per_micron'] != after['dbu_per_micron']):
        raise ValueError('Changed fixed physical geometry')
    return dict(result, exact_plan_implemented=True, original_cells_fixed=True,
                clock_connections_unchanged=True, power_bindings_retained=True)
