"""Declared physical edits, independent of candidate search and experiment names.

The policy grants bounded changes to a frozen database. The plan proposes exact
edits; readback verifies them. None of these checks predicts routed parasitics.
"""
from copy import deepcopy
import math
import re

from physical_buffer_repair import BUFFERS, compare_buffer_repair
from physical_connections import connection_terminals
from physical_floorplan import overlaps
from physical_organization import validate_exchanges


KINDS = {'resize_buffer', 'move_resize_buffer', 'regroup_consumers', 'insert_receiver'}
FIXED = ('ports', 'rows', 'placement_blockages', 'power_shapes', 'routing_obstructions',
         'macro_obstructions', 'die', 'layers', 'exclusions')


def import_local_plan(local):
    """Translate the retained experiment format without changing its authority."""
    if local.get('schema') != 1 or local.get('execution_scope') != 'one_bounded_local_probe':
        raise ValueError('Unsupported local organization plan')
    operations = []
    for entry in local['resizes']:
        moved = entry['before']['bbox_dbu'][:2] != entry['footprint_dbu'][:2]
        operations.append(dict(deepcopy(entry), kind='move_resize_buffer' if moved else 'resize_buffer'))
    if local['exchanges']:
        operations.append(dict(kind='regroup_consumers', branches=deepcopy(local['exchanges'])))
    operations.append(dict(deepcopy(local['receiver']), kind='insert_receiver'))
    rule = deepcopy(local['relocation'])
    instance, pitch = rule.pop('instance'), rule.pop('site_pitch_dbu')
    policy = dict(schema=1, source_database_sha256=local['source_database']['sha256'],
        protected_instances=local['protected_instances'], resize_cells=sorted(BUFFERS),
        receiver_cells=sorted(BUFFERS), receiver_pins=[local['receiver']['receiver']],
        site_pitch_dbu=pitch, relocations={instance:rule})
    return dict(schema=1, source_database=deepcopy(local['source_database']),
        operations=operations, added_area_um2=local['added_area_um2']), policy


def incident_nets(plan, context):
    changed, added = set(), set()
    for op in plan['operations']:
        kind = op['kind']
        if kind in ('resize_buffer', 'move_resize_buffer'):
            changed.update(n for n, net in context['nets'].items()
                           if any(t['instance'] == op['instance'] and t['pin'] in ('A','X')
                                  for t in net['terminals']))
        elif kind == 'regroup_consumers':
            changed.update(e['net'] for e in op['branches'])
        elif kind == 'insert_receiver':
            changed.add(op['net']); added.add(op['new_net'])
        else:
            raise ValueError('Unknown organization edit')
    return changed, added


def measurement_plan(plan, context):
    """Include both sides of every moved/resized cell and every new branch."""
    changed, _ = incident_nets(plan, context)
    branches = {n:[] for n in changed}
    for op in plan['operations']:
        if op['kind'] == 'insert_receiver':
            branches[op['net']].append(dict(new_net=op['new_net']))
    return dict(source_database=plan['source_database'],
                operations=[dict(net=n, stages=branches[n]) for n in sorted(branches)])


def validate_plan(plan, context, policy):
    """Check supported edits and their complete footprint/connectivity obligations."""
    if (set(plan) != {'schema','source_database','operations','added_area_um2'} or plan['schema'] != 1 or
            set(policy) != {'schema','source_database_sha256','protected_instances','resize_cells',
                           'receiver_cells','receiver_pins','site_pitch_dbu','relocations'} or
            policy['schema'] != 1 or plan['source_database']['sha256'] != context['database_sha256'] or
            policy['source_database_sha256'] != context['database_sha256'] or not plan['operations']):
        raise ValueError('Invalid or unlinked declared organization edits')
    pitch = policy['site_pitch_dbu']
    protected = set(policy['protected_instances'])
    if (type(pitch) is not int or pitch <= 0 or len(protected) != len(policy['protected_instances']) or
            not protected <= context['instances'].keys() or
            not set(policy['resize_cells']) <= BUFFERS or not set(policy['receiver_cells']) <= BUFFERS):
        raise ValueError('Invalid physical edit policy')
    changes, additions, regrouped, used_receivers = {}, {}, set(), set()
    units = context['dbu_per_micron']
    sizes = {cell:{(i['bbox_dbu'][2]-i['bbox_dbu'][0], i['bbox_dbu'][3]-i['bbox_dbu'][1])
                   for i in context['instances'].values() if i['cell'] == cell} for cell in BUFFERS}
    for op in plan['operations']:
        kind = op.get('kind')
        if kind not in KINDS:
            raise ValueError('Unknown organization edit')
        if kind in ('resize_buffer', 'move_resize_buffer'):
            if set(op) != {'kind','instance','before','cell','footprint_dbu','net'}:
                raise ValueError('Invalid buffer edit fields')
            name = op['instance']; old = context['instances'][name]; box = op['footprint_dbu']
            if (name in changes or name in protected or old != op['before'] or old['macro'] or
                    old['cell'] not in BUFFERS or op['cell'] not in policy['resize_cells'] or
                    connection_terminals(context, op['net'])['driver'] != name+'/X' or
                    box[2]-box[0] <= old['bbox_dbu'][2]-old['bbox_dbu'][0]):
                raise ValueError('Invalid, duplicate or protected resize')
            dx, dy = box[0]-old['bbox_dbu'][0], box[1]-old['bbox_dbu'][1]
            if kind == 'resize_buffer':
                if dx or dy:
                    raise ValueError('Undeclared moved instance')
            else:
                rule = policy['relocations'].get(name, {})
                if (set(rule) != {'cell','max_displacement_sites','row','orientation'} or
                        type(rule['max_displacement_sites']) is not int or
                        not 1 <= rule['max_displacement_sites'] <= 20 or
                        rule['row'] != 'same' or rule['orientation'] != 'same' or
                        rule['cell'] != op['cell'] or dy or dx % pitch or
                        not 0 < abs(dx) <= pitch*rule['max_displacement_sites']):
                    raise ValueError('Move exceeds declared same-row authority')
            changes[name] = op
        elif kind == 'insert_receiver':
            if set(op) != {'kind','net','receiver','instance','new_net','cell','footprint_dbu','orientation'}:
                raise ValueError('Invalid receiver edit fields')
            name, pin = op['instance'], op['receiver']; macro = pin.rsplit('/',1)[0]
            if (name in context['instances'] or name in additions or op['new_net'] in context['nets'] or
                    any(e['new_net'] == op['new_net'] for e in additions.values()) or
                    pin in used_receivers or pin not in policy['receiver_pins'] or
                    not context['instances'][macro]['macro'] or
                    op['cell'] not in policy['receiver_cells'] or
                    pin not in connection_terminals(context, op['net'])['consumers']):
                raise ValueError('Invalid, duplicate or unauthorized receiver')
            additions[name] = op; used_receivers.add(pin)
        else:
            if set(op) != {'kind','branches'} or not op['branches']:
                raise ValueError('Invalid regrouping fields')
            nets = [e['net'] for e in op['branches']]
            if len(set(nets)) != len(nets) or regrouped.intersection(nets):
                raise ValueError('Duplicate regrouped branch')
            rows = {n:dict(net=n, **connection_terminals(context,n),
                driver_cell=context['instances'][connection_terminals(context,n)['driver'].rsplit('/',1)[0]]['cell'])
                for n in nets}
            if len({r['driver_cell'] for r in rows.values()}) != 1:
                raise ValueError('Regrouping requires same-size source buffers')
            pin_net = {t['instance']+'/'+t['pin']:n for n,v in context['nets'].items()
                       if v['type'] not in ('POWER','GROUND') for t in v['terminals']}
            root, seen = nets[0], set()
            while True:
                if root in seen:
                    raise ValueError('Source cycle')
                seen.add(root); driver = connection_terminals(context,root)['driver'].rsplit('/',1)[0]
                if context['instances'][driver]['cell'] not in BUFFERS:
                    break
                root = pin_net[driver+'/A']
            validate_exchanges(context, rows, dict(root=root,nets=nets), op['branches'], protected)
            regrouped.update(nets)
    if any(e['net'] in regrouped for e in additions.values()):
        raise ValueError('Receiver and regrouping edit overlap')
    identifiers = []
    for op in plan['operations']:
        if op['kind'] == 'regroup_consumers':
            for branch in op['branches']:
                identifiers.extend([branch['net'],branch['driver'],*branch['before'],*branch['after']])
        else:
            identifiers.extend(op[k] for k in ('instance','net','cell'))
            if op['kind'] == 'insert_receiver':
                identifiers.extend([op['new_net'],op['receiver']])
    if any(not isinstance(n,str) or not re.fullmatch(r'[A-Za-z0-9_./\[\]$-]+',n) for n in identifiers):
        raise ValueError('Unsafe organization identifier')
    incident, _ = incident_nets(plan, context)
    if any(context['nets'][n]['type'] != 'SIGNAL' or context['nets'][n]['ports'] for n in incident):
        raise ValueError('Clock, supply and package edits are outside this policy')
    boxes, delta = [], 0
    for name, op in {**changes, **additions}.items():
        box = op['footprint_dbu']; width, height = box[2]-box[0], box[3]-box[1]
        rows = [r for r in context['rows'] if r['bbox_dbu'][0] <= box[0] < box[2] <= r['bbox_dbu'][2]
                and r['bbox_dbu'][1] == box[1] < box[3] == r['bbox_dbu'][3]
                and (box[0]-r['bbox_dbu'][0]) % pitch == 0]
        if (len(box) != 4 or any(type(v) is not int for v in box) or
                (width,height) not in sizes[op['cell']] or not rows or
                any(overlaps(box,i['bbox_dbu']) for n,i in context['instances'].items() if n != name) or
                any(overlaps(box,b['bbox_dbu']) for b in context['placement_blockages'])):
            raise ValueError('Illegal or occupied organization footprint')
        if name in additions:
            neighbors = [i for i in context['instances'].values() if not i['macro']
                         and i['bbox_dbu'][1] == box[1] and i['bbox_dbu'][3] == box[3]]
            parity = {i['orientation'] in ('MX','R180') for i in neighbors}
            if (len(parity) != 1 or op['orientation'] not in ('R0','MX') or
                    (op['orientation'] == 'MX') not in parity):
                raise ValueError('Receiver orientation conflicts with row rails')
        else:
            b = context['instances'][name]['bbox_dbu']; delta -= (b[2]-b[0])*(b[3]-b[1])
        delta += width*height; boxes.append(box)
    if any(overlaps(a,b) for i,a in enumerate(boxes) for b in boxes[i+1:]):
        raise ValueError('Overlapping declared edits')
    if (type(plan['added_area_um2']) not in (float,int) or not math.isfinite(plan['added_area_um2']) or
            abs(delta/units**2-plan['added_area_um2']) > 1e-6):
        raise ValueError('Incorrect declared edit area')
    return dict(resized_buffers=len(changes), added_buffers=len(additions),
                regrouped_branches=len(regrouped), added_area_um2=delta/units**2)


def verify_actual(plan, policy, before, after, reference, repaired):
    """Derive the exact edit from declarations, then check independent readbacks."""
    validate_plan(plan, before, policy)
    proof = compare_buffer_repair(reference, repaired, allow_resizing=True, allow_rewiring=True)
    resized = {op['instance']:op for op in plan['operations'] if op['kind'] in ('resize_buffer','move_resize_buffer')}
    added = {op['instance']:op for op in plan['operations'] if op['kind'] == 'insert_receiver'}
    expected_resizes = {n:dict(before=op['before']['cell'],after=op['cell']) for n,op in resized.items()}
    if set(proof['added_instances']) != set(added) or proof.get('resized_buffers',{}) != expected_resizes:
        raise ValueError('Unexpected cell edit')
    expected = deepcopy(before)
    for name, op in resized.items():
        expected['instances'][name].update(cell=op['cell'], bbox_dbu=op['footprint_dbu'],
            bbox=[v/before['dbu_per_micron'] for v in op['footprint_dbu']])
    for op in plan['operations']:
        if op['kind'] == 'regroup_consumers':
            for e in op['branches']:
                expected['nets'][e['net']]['terminals'] = [dict(instance=p.rsplit('/',1)[0],pin=p.rsplit('/',1)[1],direction='INPUT') for p in e['after']]
                expected['nets'][e['net']]['terminals'].append(dict(instance=e['driver'].rsplit('/',1)[0],pin=e['driver'].rsplit('/',1)[1],direction='OUTPUT'))
    for name, op in added.items():
        mi, mp = op['receiver'].rsplit('/',1); terminals = expected['nets'][op['net']]['terminals']
        terminals[:] = [t for t in terminals if (t['instance'],t['pin']) != (mi,mp)]
        terminals.append(dict(instance=name,pin='A',direction='INPUT'))
        expected['nets'][op['new_net']] = dict(type='SIGNAL',ports=[],terminals=[
            dict(instance=name,pin='X',direction='OUTPUT'),dict(instance=mi,pin=mp,direction='INPUT')])
        for net, pin in [('VPWR','VDD'),('VGND','VSS')]:
            expected['nets'][net]['terminals'].append(dict(instance=name,pin=pin,direction='INOUT'))
    norm = lambda c:{n:(v['type'],sorted(v['ports']),sorted((t['instance'],t['pin'],t['direction']) for t in v['terminals'])) for n,v in c['nets'].items()}
    if norm(expected) != norm(after):
        raise ValueError('Unexpected connection or power edit')
    if set(after['instances']) != set(before['instances']) | set(added):
        raise ValueError('Unexpected instance membership')
    if any(after['instances'][n] != i for n,i in expected['instances'].items()):
        raise ValueError('Unexpected original cell placement or type')
    for name, op in added.items():
        new = after['instances'][name]
        if (new['cell'] != op['cell'] or new['bbox_dbu'] != op['footprint_dbu'] or new['macro'] or
                new['orientation'] != op['orientation'] or
                new['bbox'] != [v/before['dbu_per_micron'] for v in op['footprint_dbu']]):
            raise ValueError('Unexpected receiver footprint')
    if any(before[k] != after[k] for k in FIXED) or before['dbu_per_micron'] != after['dbu_per_micron']:
        raise ValueError('Changed fixed physical geometry')
    shapes = lambda c:[{k:v for k,v in p.items() if k != 'net'} for p in c['macro_pins']]
    if shapes(before) != shapes(after):
        raise ValueError('Changed macro pin geometry')
    return dict(proof, exact_plan_implemented=True, power_bindings_retained=True,
        original_cells_fixed_except=sorted(resized), clock_connections_unchanged=True,
        boundary='Exact signal edit, readback identity and declared footprints; electrical/timing and pin access remain separate.')
