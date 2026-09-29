"""Bound combinational placement to a named cone and verify actual readbacks.

The placer owns coordinate selection. This contract permits no logic, size,
clock, state, hold-cell, package, macro or power change. Timing and routing
qualification are independent of placement identity and legality.
"""
from collections import defaultdict, deque
import re

from physical_floorplan import overlaps
from physical_organization_edits import FIXED


COMBINATIONAL = re.compile(
    r'sg13cmos5l_(?:buf|inv|and[234]|or[234]|nand[234]b?|nor[234]b?|'
    r'a(?:21|22|221)o?i?|o(?:21|22|221)a?i?|mux[24]|xnor2|xor2)_\d+')


def select_region(context, output_net, depth, protected=()):
    if output_net not in context['nets'] or type(depth) is not int or not 1 <= depth <= 32:
        raise ValueError('Invalid output cone or depth')
    pins = defaultdict(list)
    forbidden = set(protected)
    if forbidden - context['instances'].keys():
        raise ValueError('Unknown protected instance')
    for net, row in context['nets'].items():
        if row['type'] in ('POWER', 'GROUND'):
            continue
        for term in row['terminals']:
            pins[term['instance']].append((net, term['direction']))
            if row['type'] != 'SIGNAL' or row['ports']:
                forbidden.add(term['instance'])
    levels = {}
    pending = deque([(output_net, 0)])
    while pending:
        net, level = pending.popleft()
        for term in context['nets'][net]['terminals']:
            if term['direction'] != 'OUTPUT':
                continue
            name = term['instance']; inst = context['instances'][name]
            if name in levels or inst['macro'] or inst['cell'].startswith('sg13cmos5l_df'):
                continue
            levels[name] = level
            for upstream, direction in pins[name]:
                if direction == 'INPUT':
                    pending.append((upstream, level + 1))
    selected = sorted(n for n, d in levels.items() if d <= depth and n not in forbidden
                      and not n.startswith('hold') and COMBINATIONAL.fullmatch(context['instances'][n]['cell']))
    incident = sorted({net for n in selected for net, _ in pins[n]})
    if not selected or any(context['nets'][n]['ports'] or context['nets'][n]['type'] != 'SIGNAL' for n in incident):
        raise ValueError('Empty region or unprotected boundary')
    return dict(instances=selected, incident_nets=incident, levels={n:levels[n] for n in selected},
                complete_cone_cells=len(levels), excluded_cells=sorted(set(levels) - set(selected)))


def validate_policy(policy, context):
    if (set(policy) != {'schema', 'source_database_sha256', 'output_net', 'depth', 'protected',
                       'instances', 'max_instances', 'site_pitch_dbu', 'max_displacement_um'}
            or policy['schema'] != 1 or policy['source_database_sha256'] != context['database_sha256']
            or type(policy['max_instances']) is not int or not 1 <= policy['max_instances'] <= 2500
            or type(policy['site_pitch_dbu']) is not int or policy['site_pitch_dbu'] <= 0
            or type(policy['max_displacement_um']) not in (int, float)
            or not 0 < policy['max_displacement_um'] <= 2000):
        raise ValueError('Invalid placement policy')
    region = select_region(context, policy['output_net'], policy['depth'], policy['protected'])
    if policy['instances'] != region['instances'] or len(region['instances']) > policy['max_instances']:
        raise ValueError('Region differs from frozen selection')
    if any(not re.fullmatch(r'[A-Za-z0-9_./\[\]$-]+', n) for n in region['instances']):
        raise ValueError('Unsafe instance identifier')
    return region


def verify_context(policy, before, after, row_definitions=None):
    region = validate_policy(policy, before); allowed = set(region['instances'])
    norm = lambda c: {n:(v['type'], sorted(v['ports']), sorted(
        (t['instance'], t['pin'], t['direction']) for t in v['terminals'])) for n,v in c['nets'].items()}
    if norm(before) != norm(after):
        raise ValueError('Changed signal, clock or power connectivity')
    if any(before[k] != after[k] for k in (*FIXED, 'macro_pins', 'dbu_per_micron')):
        raise ValueError('Changed fixed physical geometry')
    if before['instances'].keys() != after['instances'].keys():
        raise ValueError('Changed instance membership')
    units = before['dbu_per_micron']; pitch = policy['site_pitch_dbu']; changed = {}; row_parity = defaultdict(set)
    for inst in before['instances'].values():
        if not inst['macro']:
            b = inst['bbox_dbu']; row_parity[b[1], b[3]].add(inst['orientation'] in ('MX', 'R180'))
    # An empty original row has no neighboring cell from which to infer rails.
    # In that case require separately extracted, source-bound OpenDB row data.
    if row_definitions is not None:
        if set(row_definitions) != {r['name'] for r in before['rows']}:
            raise ValueError('Incomplete authoritative row definitions')
        for row in before['rows']:
            definition = row_definitions[row['name']]; b = row['bbox_dbu']
            if (definition['orientation'] not in ('R0', 'MX', 'MY', 'R180')
                    or definition['site_width_dbu'] != pitch
                    or definition['site_height_dbu'] != b[3]-b[1]):
                raise ValueError('Incompatible authoritative row definition')
            expected = {definition['orientation'] in ('MX', 'R180')}
            if row_parity[b[1], b[3]] and row_parity[b[1], b[3]] != expected:
                raise ValueError('Row definition disagrees with original cell rails')
            row_parity[b[1], b[3]] = expected
    for name, old in before['instances'].items():
        new = after['instances'][name]
        if new == old:
            continue
        if name not in allowed:
            raise ValueError('Moved protected or out-of-region instance: ' + name)
        a = old['bbox_dbu']; b = new['bbox_dbu']
        if (set(new) != set(old) or any(new[k] != old[k] for k in old if k not in ('bbox', 'bbox_dbu', 'orientation'))
                or len(b) != 4 or any(type(v) is not int for v in b)
                or (b[2]-b[0], b[3]-b[1]) != (a[2]-a[0], a[3]-a[1])
                or new['bbox'] != [v / units for v in b] or new['orientation'] not in ('R0', 'MX', 'MY', 'R180')):
            raise ValueError('Changed cell or inconsistent footprint')
        displacement = (abs(a[0]-b[0]) + abs(a[1]-b[1])) / units
        if displacement > policy['max_displacement_um']:
            raise ValueError('Exceeded displacement bound')
        rows = [r for r in after['rows'] if r['bbox_dbu'][0] <= b[0] < b[2] <= r['bbox_dbu'][2]
                and r['bbox_dbu'][1] == b[1] < b[3] == r['bbox_dbu'][3]
                and (b[0]-r['bbox_dbu'][0]) % pitch == 0]
        parity = row_parity[b[1], b[3]]
        if not rows or len(parity) != 1 or (new['orientation'] in ('MX','R180')) not in parity:
            raise ValueError('Illegal site, row or power-rail orientation')
        if any(overlaps(b, v['bbox_dbu']) for n,v in after['instances'].items() if n != name):
            raise ValueError('Overlapping placed cells')
        if any(overlaps(b, v['bbox_dbu']) for v in after['placement_blockages']):
            raise ValueError('Cell intersects placement blockage')
        changed[name] = dict(before=a, after=b, orientation_before=old['orientation'],
                             orientation_after=new['orientation'], displacement_um=displacement)
    return dict(allowed_instances=len(allowed), moved_instances=len(changed), changes=changed,
                maximum_displacement_um=max((c['displacement_um'] for c in changed.values()), default=0),
                added_area_um2=0, exact_connectivity=True, protected_instances_fixed=True,
                cell_types_and_dimensions_unchanged=True, power_bindings_retained=True)


def render_tcl(policy, context, output_dir, timing_driven=False):
    validate_policy(policy, context)
    if not re.fullmatch(r'/probe/[A-Za-z0-9_-]+', output_dir) or type(timing_driven) is not bool:
        raise ValueError('Unsafe placement output or mode')
    names = ' '.join('{' + n + '}' for n in policy['instances'])
    lines = ['set_routing_layers -signal Metal2-Metal4 -clock Metal2-Metal4',
             'set_global_routing_layer_adjustment * 0.3', 'global_route -start_incremental',
             'set original_status [dict create]', 'set selected [dict create]',
             f'foreach name [list {names}] {{dict set selected $name 1}}',
             'foreach inst [$::block getInsts] {',
             '  set name [$inst getName]', '  dict set original_status $name [$inst getPlacementStatus]',
             '  if {[dict exists $selected $name]} {$inst setPlacementStatus PLACED} else {$inst setPlacementStatus FIRM}',
             '}']
    command = 'global_placement -skip_initial_place -density 0.50 -overflow 0.10'
    if timing_driven:
        command += ' -timing_driven -keep_resize_below_overflow 0 -timing_driven_net_weight_max 5'
    lines += [command, 'detailed_placement', 'check_placement -verbose',
              'foreach inst [$::block getInsts] {', '  set name [$inst getName]',
              '  if {![dict exists $original_status $name]} {error {Placement added an instance}}',
              '  $inst setPlacementStatus [dict get $original_status $name]', '}',
              'global_route -end_incremental -allow_congestion', 'estimate_parasitics -global_routing',
              f'write_guide {output_dir}/repaired.guide', f'write_db {output_dir}/repaired.odb']
    return '\n'.join(lines) + '\n'
