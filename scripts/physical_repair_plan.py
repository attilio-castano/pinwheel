"""Checked descriptions of additive signal-buffer repairs.

Plans retain the source ODB, all consumers and original cells. Compiling a plan
does not admit execution or establish electrical, timing or placement success.
Historical recipes are left intact; future probes can consume generated Tcl.
"""
from copy import deepcopy
import math
import re

from physical_connections import connection_terminals
from physical_floorplan import overlaps
from upload_locality import free_rows
from physical_buffer_repair import BUFFERS
from tiled_chip import FF

ROUTING_POLICY = dict(signal_layers='Metal2-Metal4', clock_layers='Metal2-Metal4',
    capacity_adjustment=0.3, nondefault_rules='preserve-bindings-record-effective-router-warnings')


def placement_hint(context, size, point):
    """Choose an unoccupied row rectangle; legalization and power remain required."""
    units = context['dbu_per_micron']
    _, free = free_rows(context, [round(v*units) for v in context['die']])
    w,h = size
    choices = []
    for x0,y0,x1,y1 in free:
        if x1-x0 < w or y1-y0 < h:
            continue
        x = max(x0, min(x1-w, round(point[0]-w/2)))
        box = [x,y0,x+w,y0+h]
        if any(overlaps(box,b['bbox_dbu']) for b in context.get('placement_blockages', [])):
            continue
        choices.append((abs(x+w/2-point[0])+abs(y0+h/2-point[1]), box))
    if not choices:
        raise ValueError('No unoccupied row footprint for candidate buffer')
    return min(choices)[1]


def build_plan(records, context, geometry, database, *, namespace='prepared'):
    if not isinstance(namespace, str) or not re.fullmatch(r'[A-Za-z][A-Za-z0-9_]*', namespace):
        raise ValueError('Invalid repair namespace')
    work = deepcopy(context)
    size = geometry['buffer_masters']['sg13cmos5l_buf_8']
    size = [size['width_dbu'],size['height_dbu']]
    operations = []
    for i, r in enumerate(records):
        macro = [p for p in r['consumers'] if context['instances'][p.rsplit('/',1)[0]]['macro']]
        mode = 'receiver' if macro else 'driver'
        if macro and (len(macro)!=1 or '/A_DIN[' not in macro[0]):
            raise ValueError('Receiver candidate must identify one SRAM data input')
        pin = macro[0] if macro else r['driver']
        shapes = geometry['pins'][pin]
        box = shapes[0]['bbox_dbu']
        point = [(box[0]+box[2])/2,(box[1]+box[3])/2]
        footprint = placement_hint(work,size,point)
        name = namespace+'_signal_'+str(i)
        new_net = namespace+'_branch_'+str(i)
        if name in work['instances'] or new_net in context['nets']:
            raise ValueError('Repair namespace collides with the source')
        op = dict(net=r['net'],driver=r['driver'],driver_cell=r['driver_cell'],
            consumers=r['consumers'],ports=r['ports'],mode=mode,receiver=macro[0] if macro else None,
            cell='sg13cmos5l_buf_8',instance=name,new_net=new_net,
            footprint_dbu=footprint,logical_family=r['family'])
        operations.append(op)
        work['instances'][name] = dict(bbox_dbu=footprint)
    return dict(schema=1,status='checked-plan-only',source_database=database,
        dbu_per_micron=context['dbu_per_micron'],buffer_size_dbu=size,
        routing_policy=dict(ROUTING_POLICY),
        invariants=dict(original_cells_fixed=True,original_hold_cells_retained=True,
                        clock_connections_fixed=True,state_changes=0,added_pipeline_cycles=0),
        operations=operations,
        acceptance=dict(all_corner_setup_hold_positive=True,all_corner_electrical_zero=True,
            all_consumed_nets_annotated=True,buffer_contracted_identity=True,original_geometry_and_power_retained=True,
            added_cells_legal_and_power_bound=True,all_affected_connections_reported=True,
            fresh_whole_chip_route_required=True,detailed_route_admitted=False),
        boundary='Unoccupied row rectangles are placement hints, not legal placement or pin-access evidence. Execution is a separate bounded probe.')


def validate_plan(plan, context, database_sha256):
    if plan.get('schema') == 2:
        return validate_explicit_plan(plan, context, database_sha256)
    required = {'schema','status','source_database','dbu_per_micron','buffer_size_dbu','invariants',
                'operations','acceptance','boundary','routing_policy'}
    if set(plan)!=required or plan['schema']!=1 or plan['status']!='checked-plan-only':
        raise ValueError('Unsupported repair plan')
    if plan['source_database']['sha256']!=database_sha256 or context['database_sha256']!=database_sha256:
        raise ValueError('Plan belongs to a different checkpoint')
    invariant = dict(original_cells_fixed=True,original_hold_cells_retained=True,
                     clock_connections_fixed=True,state_changes=0,added_pipeline_cycles=0)
    acceptance = dict(all_corner_setup_hold_positive=True,all_corner_electrical_zero=True,
        all_consumed_nets_annotated=True,buffer_contracted_identity=True,original_geometry_and_power_retained=True,
        added_cells_legal_and_power_bound=True,all_affected_connections_reported=True,
        fresh_whole_chip_route_required=True,detailed_route_admitted=False)
    if plan['invariants']!=invariant or plan['acceptance']!=acceptance or not plan['operations']:
        raise ValueError('Changed repair invariants or acceptance gates')
    if plan['dbu_per_micron']!=context['dbu_per_micron']:
        raise ValueError('Changed coordinate units')
    if plan['routing_policy']!=ROUTING_POLICY:
        raise ValueError('Unsupported routing-policy change')
    actual_sizes = {(i['bbox_dbu'][2]-i['bbox_dbu'][0],i['bbox_dbu'][3]-i['bbox_dbu'][1])
                    for i in context['instances'].values() if i['cell']=='sg13cmos5l_buf_8'}
    if actual_sizes!={tuple(plan['buffer_size_dbu'])}:
        raise ValueError('Buffer footprint does not match the source library')
    nets, instances, fresh_nets, boxes = set(),set(),set(),[]
    fields={'net','driver','driver_cell','consumers','ports','mode','receiver','cell','instance','new_net',
            'footprint_dbu','logical_family'}
    for op in plan['operations']:
        if set(op)!=fields:
            raise ValueError('Incomplete or unknown repair operation')
        strings=[op[k] for k in ['net','driver','driver_cell','cell','instance','new_net']]+op['consumers']+op['ports']
        if op['receiver'] is not None:strings.append(op['receiver'])
        if any(not isinstance(v,str) or not re.fullmatch(r'[A-Za-z0-9_./\[\]$-]+',v) for v in strings):
            raise ValueError('Unsafe repair identifier')
        r=connection_terminals(context,op['net']);cell=op['driver'].rsplit('/',1)[0]
        if (r!=dict(driver=op['driver'],consumers=op['consumers'],ports=op['ports']) or
                context['instances'][cell]['cell']!=op['driver_cell'] or op['cell']!='sg13cmos5l_buf_8'):
            raise ValueError('Changed driver, consumers or buffer kind')
        if (op['mode'] not in ('driver','receiver') or
                (op['mode']=='driver' and op['receiver'] is not None) or
                (op['mode']=='receiver' and (op['receiver'] not in op['consumers'] or
                    not context['instances'][op['receiver'].rsplit('/',1)[0]]['macro'] or '/A_DIN[' not in op['receiver']))):
            raise ValueError('Invalid repair operation or receiver')
        if (op['net'] in nets or op['instance'] in instances or op['instance'] in context['instances'] or
                op['new_net'] in fresh_nets or op['new_net'] in context['nets']):
            raise ValueError('Conflicting repair operations')
        nets.add(op['net']);instances.add(op['instance']);fresh_nets.add(op['new_net'])
        b=op['footprint_dbu'];w,h=plan['buffer_size_dbu']
        if (not isinstance(b,list) or len(b)!=4 or any(type(v)!=int for v in b) or
                [b[2]-b[0],b[3]-b[1]]!=[w,h] or
                not any(r['bbox_dbu'][0]<=b[0]<b[2]<=r['bbox_dbu'][2] and
                        r['bbox_dbu'][1]<=b[1]<b[3]<=r['bbox_dbu'][3] for r in context['rows']) or
                any(overlaps(b,i['bbox_dbu']) for i in context['instances'].values()) or
                any(overlaps(b,q['bbox_dbu']) for q in context.get('placement_blockages',[])) or
                any(overlaps(b,q) for q in boxes)):
            raise ValueError('Candidate footprint lacks unoccupied row space')
        boxes.append(b)
    return dict(operations=len(nets),added_area_um2=len(nets)*math.prod(plan['buffer_size_dbu'])/plan['dbu_per_micron']**2,
                scope='Plan validation only; fresh physical and functional checks required after execution.')


def render_tcl(plan, context, database_sha256):
    if plan.get('schema') == 2:
        return render_explicit_tcl(plan, context, database_sha256)
    validate_plan(plan,context,database_sha256)
    literal=lambda s:'{'+s+'}'
    lines=['# Generated from a checked additive signal repair plan. No pipeline change.',
           'write_verilog /probe/before.v', 'set originals [$::block getInsts]',
           'set_routing_layers -signal Metal2-Metal4 -clock Metal2-Metal4',
           'set_global_routing_layer_adjustment * 0.3','global_route -start_incremental']
    for op in plan['operations']:
        expected=sorted([op['driver'],*op['consumers']])
        x,y=op['footprint_dbu'][:2]
        lines += [f'set wire [$::block findNet {literal(op["net"])}]',
            'if {$wire eq "NULL" || [$wire getSigType] ne "SIGNAL"} {error "Missing signal net"}',
            'set actual {}', 'foreach it [$wire getITerms] {lappend actual "[[$it getInst] getName]/[[$it getMTerm] getName]"}',
            'if {[lsort $actual] ne [lsort [list '+' '.join(map(literal,expected))+']]} {error "Changed consumer set"}',
            'set actual {}','foreach bt [$wire getBTerms] {lappend actual [$bt getName]}',
            'if {[lsort $actual] ne [lsort [list '+' '.join(map(literal,op['ports']))+']]} {error "Changed package consumers"}',
            f'set driver [$::block findITerm {literal(op["driver"])}]',
            f'if {{[[[$driver getInst] getMaster] getName] ne {literal(op["driver_cell"])}}} {{error "Changed driver type"}}',
            f'if {{[$::block findInst {literal(op["instance"])}] ne "NULL" || [$::block findNet {literal(op["new_net"])}] ne "NULL"}} {{error "Repair name collision"}}',
            f'set inst [odb::dbInst_create $::block [[ord::get_db] findMaster {op["cell"]}] {literal(op["instance"])}]',
            f'set branch [odb::dbNet_create $::block {literal(op["new_net"])}]']
        if op['mode']=='driver':
            lines += ['$driver disconnect','$driver connect $branch','[$inst findITerm A] connect $branch',
                      '[$inst findITerm X] connect $wire']
        else:
            lines += [f'set receiver [$::block findITerm {literal(op["receiver"])}]',
                      '$receiver disconnect','$receiver connect $branch','[$inst findITerm A] connect $wire',
                      '[$inst findITerm X] connect $branch']
        lines += [f'$inst setLocation {x} {y}','$inst setPlacementStatus PLACED']
    lines += ['set statuses {}','foreach inst $originals {',
        '  lappend statuses $inst [$inst getPlacementStatus]',
        '  if {[$inst getPlacementStatus] eq "PLACED"} {$inst setPlacementStatus FIRM}', '}',
        'detailed_placement -max_displacement {50 20}','check_placement -verbose',
        'foreach {inst status} $statuses {$inst setPlacementStatus $status}', 'global_connect',
        'global_route -end_incremental -allow_congestion','estimate_parasitics -global_routing',
        'write_guide /probe/repaired.guide','write_verilog /probe/repaired.v','write_db /probe/repaired.odb']
    return '\n'.join(lines)+'\n'


def build_explicit_plan(requests, context, geometry, database, *, namespace='path'):
    """Compile declared driver/receiver buffering, including endpoint delay chains.

    Cell choice and stage count are explicit inputs, not inferred from fanout.
    This schema retains the legacy single-buffer plan and its renderer unchanged.
    """
    if not isinstance(namespace, str) or not re.fullmatch(r'[A-Za-z][A-Za-z0-9_]*', namespace):
        raise ValueError('Invalid repair namespace')
    work, operations, sizes = deepcopy(context), [], {}
    for index, request in enumerate(requests):
        if set(request) != {'net', 'mode', 'receiver', 'cells', 'purpose'}:
            raise ValueError('Incomplete explicit repair request')
        if (not isinstance(request['cells'], list) or not 1 <= len(request['cells']) <= 4 or
                any(cell not in BUFFERS for cell in request['cells'])):
            raise ValueError('Require one to four pinned noninverting buffers')
        row = connection_terminals(context, request['net'])
        pin = request['receiver'] if request['mode'] == 'receiver' else row['driver']
        box = geometry['pins'][pin][0]['bbox_dbu']
        point = [(box[0]+box[2])/2, (box[1]+box[3])/2]
        stages = []
        for stage_index, cell in enumerate(request['cells']):
            master = geometry['buffer_masters'][cell]
            size = [master['width_dbu'], master['height_dbu']]
            sizes[cell] = size
            footprint = placement_hint(work, size, point)
            name = f'{namespace}_{index}_{stage_index}'
            if name in work['instances']:
                raise ValueError('Repair namespace collides with the source')
            stages.append(dict(instance=name, cell=cell, new_net=name+'_net', footprint_dbu=footprint))
            work['instances'][name] = dict(bbox_dbu=footprint)
        operations.append(dict(net=request['net'], **row,
            driver_cell=context['instances'][row['driver'].rsplit('/', 1)[0]]['cell'],
            mode=request['mode'], receiver=request['receiver'], purpose=request['purpose'], stages=stages))
    plan = dict(schema=2, status='checked-plan-only', source_database=database,
        dbu_per_micron=context['dbu_per_micron'], buffer_sizes_dbu=sizes, routing_policy=dict(ROUTING_POLICY),
        invariants=dict(original_cells_fixed=True, original_hold_cells_retained=True,
            clock_connections_fixed=True, state_changes=0, added_pipeline_cycles=0),
        operations=operations,
        acceptance=dict(all_corner_setup_hold_positive=True, all_corner_electrical_zero=True,
            all_consumed_nets_annotated=True, buffer_contracted_identity=True, original_geometry_and_power_retained=True,
            added_cells_legal_and_power_bound=True, all_affected_connections_reported=True,
            fresh_whole_chip_route_required=True, detailed_route_admitted=False),
        boundary='Explicit signal buffering only. Stage count and footprint are checked; timing, added input load, legal placement and power require independent measurements.')
    validate_explicit_plan(plan, context, database['sha256'])
    return plan


def validate_explicit_plan(plan, context, database_sha256):
    required = {'schema','status','source_database','dbu_per_micron','buffer_sizes_dbu',
                'routing_policy','invariants','operations','acceptance','boundary'}
    invariants = dict(original_cells_fixed=True, original_hold_cells_retained=True,
        clock_connections_fixed=True, state_changes=0, added_pipeline_cycles=0)
    acceptance = dict(all_corner_setup_hold_positive=True, all_corner_electrical_zero=True,
        all_consumed_nets_annotated=True, buffer_contracted_identity=True, original_geometry_and_power_retained=True,
        added_cells_legal_and_power_bound=True, all_affected_connections_reported=True,
        fresh_whole_chip_route_required=True, detailed_route_admitted=False)
    if (set(plan) != required or plan['schema'] != 2 or plan['status'] != 'checked-plan-only' or
            plan['invariants'] != invariants or plan['acceptance'] != acceptance or
            plan['routing_policy'] != ROUTING_POLICY or not plan['operations']):
        raise ValueError('Unsupported explicit repair plan or changed invariants')
    if (plan['source_database']['sha256'] != database_sha256 or context['database_sha256'] != database_sha256 or
            plan['dbu_per_micron'] != context['dbu_per_micron']):
        raise ValueError('Explicit plan belongs to a different checkpoint or units')
    used_cells = {s['cell'] for op in plan['operations'] for s in op['stages']}
    if set(plan['buffer_sizes_dbu']) != used_cells or not used_cells <= BUFFERS:
        raise ValueError('Unknown or unused explicit buffer footprint')
    for cell, size in plan['buffer_sizes_dbu'].items():
        actual = {(i['bbox_dbu'][2]-i['bbox_dbu'][0], i['bbox_dbu'][3]-i['bbox_dbu'][1])
                  for i in context['instances'].values() if i['cell'] == cell}
        if actual != {tuple(size)}:
            raise ValueError('Explicit buffer footprint differs from the pinned source')
    nets, instances, new_nets, boxes, area = set(), set(), set(), [], 0
    for op in plan['operations']:
        if set(op) != {'net','driver','driver_cell','consumers','ports','mode','receiver','purpose','stages'}:
            raise ValueError('Incomplete explicit operation')
        row = connection_terminals(context, op['net'])
        if (row != {k:op[k] for k in ['driver','consumers','ports']} or
                context['instances'][op['driver'].rsplit('/',1)[0]]['cell'] != op['driver_cell']):
            raise ValueError('Changed explicit driver or consumers')
        if (op['mode'] not in ('driver','receiver') or
                op['mode'] == 'driver' and op['receiver'] is not None or
                op['mode'] == 'receiver' and op['receiver'] not in op['consumers'] or
                op['purpose'] not in ('electrical','setup','hold')):
            raise ValueError('Invalid explicit repair mode, receiver or purpose')
        if op['purpose'] == 'hold' and (op['mode'] != 'receiver' or
                context['instances'][op['receiver'].rsplit('/',1)[0]]['cell'] != FF or
                op['receiver'].rsplit('/',1)[1] != 'D'):
            raise ValueError('Hold delay must target a declared state data input')
        if op['net'] in nets or not isinstance(op['stages'], list) or not 1 <= len(op['stages']) <= 4:
            raise ValueError('Duplicate explicit net or invalid chain length')
        nets.add(op['net'])
        names = [op[k] for k in ['net','driver','driver_cell']] + op['consumers'] + op['ports']
        if op['receiver'] is not None:
            names.append(op['receiver'])
        for stage in op['stages']:
            if set(stage) != {'instance','cell','new_net','footprint_dbu'}:
                raise ValueError('Incomplete explicit buffer stage')
            names.extend(stage[k] for k in ['instance','cell','new_net'])
            if (stage['instance'] in instances or stage['instance'] in context['instances'] or
                    stage['new_net'] in new_nets or stage['new_net'] in context['nets']):
                raise ValueError('Conflicting explicit repair stage')
            instances.add(stage['instance']); new_nets.add(stage['new_net'])
            box = stage['footprint_dbu']; w,h = plan['buffer_sizes_dbu'][stage['cell']]
            if (not isinstance(box,list) or len(box) != 4 or any(type(v) is not int for v in box) or
                    [box[2]-box[0],box[3]-box[1]] != [w,h] or
                    not any(r['bbox_dbu'][0]<=box[0]<box[2]<=r['bbox_dbu'][2] and
                            r['bbox_dbu'][1]<=box[1]<box[3]<=r['bbox_dbu'][3] for r in context['rows']) or
                    any(overlaps(box,i['bbox_dbu']) for i in context['instances'].values()) or
                    any(overlaps(box,b['bbox_dbu']) for b in context.get('placement_blockages',[])) or
                    any(overlaps(box,b) for b in boxes)):
                raise ValueError('Explicit stage lacks an unoccupied row footprint')
            boxes.append(box); area += w*h
        if any(not isinstance(v,str) or not re.fullmatch(r'[A-Za-z0-9_./\[\]$-]+',v) for v in names):
            raise ValueError('Unsafe explicit repair identifier')
    return dict(operations=len(nets), added_buffers=len(instances),
        added_area_um2=area/plan['dbu_per_micron']**2,
        scope='Explicit plan validation only; fresh physical and functional checks required after execution.')


def render_explicit_tcl(plan, context, database_sha256):
    validate_explicit_plan(plan, context, database_sha256)
    literal = lambda s:'{'+s+'}'
    lines = ['# Generated from an explicit additive path repair. No pipeline change.',
        'write_verilog /probe/before.v', 'set originals [$::block getInsts]',
        'set_routing_layers -signal Metal2-Metal4 -clock Metal2-Metal4',
        'set_global_routing_layer_adjustment * 0.3', 'global_route -start_incremental']
    for op in plan['operations']:
        expected = sorted([op['driver'], *op['consumers']])
        lines += [f'set wire [$::block findNet {literal(op["net"])}]',
            'if {$wire eq "NULL" || [$wire getSigType] ne "SIGNAL"} {error "Missing signal net"}',
            'set actual {}', 'foreach it [$wire getITerms] {lappend actual "[[$it getInst] getName]/[[$it getMTerm] getName]"}',
            'if {[lsort $actual] ne [lsort [list '+' '.join(map(literal,expected))+']]} {error "Changed consumer set"}',
            'set actual {}', 'foreach bt [$wire getBTerms] {lappend actual [$bt getName]}',
            'if {[lsort $actual] ne [lsort [list '+' '.join(map(literal,op['ports']))+']]} {error "Changed package consumers"}',
            f'set driver [$::block findITerm {literal(op["driver"])}]',
            f'if {{[[[$driver getInst] getMaster] getName] ne {literal(op["driver_cell"])}}} {{error "Changed driver type"}}']
        for stage in op['stages']:
            inst, net = literal(stage['instance']), literal(stage['new_net'])
            x,y = stage['footprint_dbu'][:2]
            lines += [f'if {{[$::block findInst {inst}] ne "NULL" || [$::block findNet {net}] ne "NULL"}} {{error "Repair name collision"}}',
                f'set inst [odb::dbInst_create $::block [[ord::get_db] findMaster {stage["cell"]}] {inst}]',
                f'odb::dbNet_create $::block {net}', f'$inst setLocation {x} {y}', '$inst setPlacementStatus PLACED']
        stages = op['stages']
        if op['mode'] == 'driver':
            lines += ['$driver disconnect', f'$driver connect [$::block findNet {literal(stages[0]["new_net"])}]']
        else:
            lines += [f'set receiver [$::block findITerm {literal(op["receiver"])}]', '$receiver disconnect',
                f'$receiver connect [$::block findNet {literal(stages[-1]["new_net"])}]']
        for index, stage in enumerate(stages):
            if op['mode'] == 'driver':
                incoming = stage['new_net']
                outgoing = stages[index+1]['new_net'] if index+1 < len(stages) else op['net']
            else:
                incoming = op['net'] if index == 0 else stages[index-1]['new_net']
                outgoing = stage['new_net']
            lines += [f'set inst [$::block findInst {literal(stage["instance"])}]',
                f'[$inst findITerm A] connect [$::block findNet {literal(incoming)}]',
                f'[$inst findITerm X] connect [$::block findNet {literal(outgoing)}]']
    lines += ['set statuses {}', 'foreach inst $originals {',
        '  lappend statuses $inst [$inst getPlacementStatus]',
        '  if {[$inst getPlacementStatus] eq "PLACED"} {$inst setPlacementStatus FIRM}', '}',
        'detailed_placement -max_displacement {50 20}', 'check_placement -verbose',
        'foreach {inst status} $statuses {$inst setPlacementStatus $status}', 'global_connect',
        'global_route -end_incremental -allow_congestion', 'estimate_parasitics -global_routing',
        'write_guide /probe/repaired.guide', 'write_verilog /probe/repaired.v', 'write_db /probe/repaired.odb']
    return '\n'.join(lines)+'\n'
