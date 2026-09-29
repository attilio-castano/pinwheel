"""Check actual buffer/delay repair and legalization after global routing.

Native optimization is allowed to propose changes; this validator only accepts
retained original cells plus pinned noninverting buffers and delay cells.
Optional drive-strength changes require identical all-corner pin functions.
Timing, electrical limits and routing require separate measurements.
"""
from copy import deepcopy
import re

from mapped_physical import connection_signature
from physical_buffer_repair import compare_buffer_repair
from physical_distribution import CHAIN_CELLS
from physical_floorplan import overlaps
from physical_organization_edits import FIXED
from physical_region_placement import COMBINATIONAL

# Native routed repair also selects this pinned drive strength. Keep the
# earlier buffer-only experiment's allowed set unchanged; verify every pin
# function at every requested corner before contracting these cells below.
REPAIR_TRANSPORT_CELLS = CHAIN_CELLS | {'sg13cmos5l_buf_16'}


def compare_repair(reference, candidate, library, corners, *, allow_resizing=False):
    if not corners or len(set(corners)) != len(corners):
        raise ValueError('Require explicit distinct Liberty corners')
    before, after = reference['cells'], candidate['cells']
    if before.keys() - after.keys():
        raise ValueError('Removed original cells')
    resized = {}
    for name, cell in before.items():
        if cell.get('parameters', {}) != after[name].get('parameters', {}):
            raise ValueError('Changed original cell parameters')
        a, b = cell['type'], after[name]['type']
        if a == b:
            continue
        if (not allow_resizing or not COMBINATIONAL.fullmatch(a) or not COMBINATIONAL.fullmatch(b)
                or a.rsplit('_', 1)[0] != b.rsplit('_', 1)[0]):
            raise ValueError('Unsupported cell replacement')
        for corner in corners:
            for pin, direction in cell['port_directions'].items():
                headers = [library.pin(corner, kind, pin) for kind in [a, b]]
                if any(re.findall(r'\bdirection\s*:\s*"?(\w+)"?\s*;', body) != [direction] for body in headers):
                    raise ValueError('Changed resized pin direction')
                functions = [re.findall(r'\bfunction\s*:\s*"([^"]*)"\s*;', body) for body in headers]
                if direction == 'output' and (len(functions[0]) != 1 or functions[0] != functions[1]):
                    raise ValueError('Changed resized gate function')
        resized[name] = dict(before=a, after=b)
    added = after.keys() - before.keys()
    if any(after[n]['type'] not in REPAIR_TRANSPORT_CELLS for n in added):
        raise ValueError('Added a non-transport cell')
    kinds = {c['type'] for c in after.values() if c['type'] in REPAIR_TRANSPORT_CELLS}
    for corner in corners:
        for cell in kinds:
            for pin, direction in [('A', 'input'), ('X', 'output')]:
                body = library.pin(corner, cell, pin)
                if re.findall(r'\bdirection\s*:\s*"?(\w+)"?\s*;', body) != [direction]:
                    raise ValueError('Changed transport pin direction')
                if pin == 'X' and re.findall(r'\bfunction\s*:\s*"([^"]*)"\s*;', body) != ['A']:
                    raise ValueError('Transport cell does not implement identity')
    copies = [deepcopy(reference), deepcopy(candidate)]
    for name, change in resized.items():
        copies[1]['cells'][name]['type'] = change['before']
    for module in copies:
        for cell in module['cells'].values():
            if cell['type'] in REPAIR_TRANSPORT_CELLS:
                cell['type'] = 'sg13cmos5l_buf_1'
    if connection_signature(copies[0]) == connection_signature(copies[1]):
        return dict(original_cells=len(before), added_instances=[], resized_cells=resized,
                    normalized_signal_identity=True, pinned_resize_functions_checked=True)
    proof = compare_buffer_repair(*copies, allow_rewiring=True)
    proof.pop('added_buffers')
    proof['added_cells'] = {n: after[n]['type'] for n in sorted(added)}
    proof['pinned_transport_functions_checked'] = True
    proof['resized_cells'] = resized
    proof['pinned_resize_functions_checked'] = True
    return proof


def verify_geometry(before, after, protected, row_definitions, *, max_added=1000, resized=None):
    if any(before[k] != after[k] for k in (*FIXED, 'dbu_per_micron')):
        raise ValueError('Changed fixed geometry')
    shapes = lambda c: [{k: v for k, v in p.items() if k != 'net'} for p in c['macro_pins']]
    if shapes(before) != shapes(after):
        raise ValueError('Changed macro pin shapes')
    original, current = before['instances'], after['instances']
    resized = {} if resized is None else resized
    if original.keys() - current.keys() or not set(protected) <= original.keys():
        raise ValueError('Missing original or protected cell')
    added = current.keys() - original.keys()
    if len(added) > max_added or any(current[n]['cell'] not in REPAIR_TRANSPORT_CELLS for n in added):
        raise ValueError('Unexpected new cells')
    actual_resizes = {n: dict(before=v['cell'], after=current[n]['cell']) for n, v in original.items()
                      if v['cell'] != current[n]['cell']}
    if actual_resizes != resized:
        raise ValueError('Resizing lacks a matching function-equivalence check')
    for n, old in original.items():
        new = current[n]
        if n in protected and old != new:
            raise ValueError('Moved or changed protected cell')
        allowed = ('bbox', 'bbox_dbu', 'orientation', 'cell') if n in resized else ('bbox', 'bbox_dbu', 'orientation')
        if set(old) != set(new) or any(old[k] != new[k] for k in old if k not in allowed):
            raise ValueError('Changed original cell type or attributes')
        if n not in resized and [old['bbox_dbu'][i+2]-old['bbox_dbu'][i] for i in (0, 1)] != [new['bbox_dbu'][i+2]-new['bbox_dbu'][i] for i in (0, 1)]:
            raise ValueError('Changed original cell dimensions')
    norm = lambda v: (v['type'], sorted(v['ports']), sorted((t['instance'], t['pin'], t['direction']) for t in v['terminals']))
    clock = lambda c: {n: norm(v) for n, v in c['nets'].items() if v['type'] == 'CLOCK'}
    if clock(before) != clock(after):
        raise ValueError('Changed clock topology')
    expected_power = {n: deepcopy(v) for n, v in before['nets'].items() if v['type'] in ('POWER', 'GROUND')}
    for net, pin in [('VPWR', 'VDD'), ('VGND', 'VSS')]:
        for n in added:
            expected_power[net]['terminals'].append(dict(instance=n, pin=pin, direction='INOUT'))
    actual_power = {n: v for n, v in after['nets'].items() if v['type'] in ('POWER', 'GROUND')}
    if {n: norm(v) for n, v in expected_power.items()} != {n: norm(v) for n, v in actual_power.items()}:
        raise ValueError('Changed or incomplete power bindings')
    if set(row_definitions) != {r['name'] for r in before['rows']}:
        raise ValueError('Incomplete row definitions')
    units = before['dbu_per_micron']; changed = {}
    for n, new in current.items():
        if n in original and new == original[n]:
            continue
        b = new['bbox_dbu']
        if (len(b) != 4 or any(type(v) is not int for v in b) or new['macro']
                or b[0] >= b[2] or b[1] >= b[3] or new['bbox'] != [v / units for v in b]
                or new['orientation'] not in ('R0', 'MX', 'MY', 'R180')):
            raise ValueError('Invalid changed footprint')
        rows = [r for r in after['rows'] if r['bbox_dbu'][0] <= b[0] < b[2] <= r['bbox_dbu'][2]
                and r['bbox_dbu'][1] == b[1] < b[3] == r['bbox_dbu'][3]]
        legal = False
        for row in rows:
            d = row_definitions[row['name']]; pitch = d['site_width_dbu']
            if (type(pitch) is int and pitch > 0 and d['site_height_dbu'] == b[3]-b[1]
                    and (b[0]-row['bbox_dbu'][0]) % pitch == 0 and (b[2]-b[0]) % pitch == 0
                    and d['orientation'] in ('R0', 'MX', 'MY', 'R180')
                    and (new['orientation'] in ('MX', 'R180')) == (d['orientation'] in ('MX', 'R180'))):
                legal = True
        if not legal or any(overlaps(b, v['bbox_dbu']) for other, v in current.items() if other != n):
            raise ValueError('Illegal row, orientation or overlap')
        if any(overlaps(b, v['bbox_dbu']) for v in after['placement_blockages']):
            raise ValueError('Cell overlaps placement blockage')
        if n in original:
            a = original[n]['bbox_dbu']; delta = [abs(a[i]-b[i])/units for i in (0, 1)]
            if delta[0] > 500 or delta[1] > 100:
                raise ValueError('Exceeded declared displacement')
            changed[n] = delta
    area = lambda c: sum((v['bbox_dbu'][2]-v['bbox_dbu'][0])*(v['bbox_dbu'][3]-v['bbox_dbu'][1]) for v in c['instances'].values())/units**2
    return dict(original_cells=len(original), added_cells=sorted(added), resized_cells=resized, moved_original_cells=len(changed),
                max_displacement_xy_um=[max((v[i] for v in changed.values()), default=0) for i in (0, 1)],
                area_um2=area(after), added_area_um2=area(after)-area(before), protected_cells_fixed=True,
                clock_topology_unchanged=True, power_bindings_retained=True, legal_changed_footprints=True)
