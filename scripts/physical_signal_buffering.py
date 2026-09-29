"""Declared noninverting signal branches with independent physical readback.

This is an experimental edit, not route admission. Original cells, clocks,
hold cells and placements are fixed. Both sides and all siblings need timing.
"""
from copy import deepcopy
import math
import re

from physical_buffer_repair import BUFFERS, compare_buffer_repair
from physical_connections import connection_terminals
from physical_decoder_replication import _footprint
from physical_organization_edits import FIXED


def validate_plan(plan, context):
    if (set(plan) != {'schema','source_database_sha256','site_pitch_dbu','buffers','added_area_um2'}
            or plan['schema'] != 1 or plan['source_database_sha256'] != context['database_sha256']
            or type(plan['site_pitch_dbu']) is not int or plan['site_pitch_dbu'] <= 0
            or not plan['buffers']):
        raise ValueError('Invalid or unbound signal-buffer plan')
    names, nets, moved, boxes = set(), set(), set(), []
    area = 0
    for op in plan['buffers']:
        if set(op) != {'net','driver','consumers','instance','new_net','cell','footprint_dbu','orientation'}:
            raise ValueError('Invalid signal-buffer fields')
        identifiers = [op[k] for k in ('net','driver','instance','new_net','cell')] + op['consumers']
        if any(not isinstance(s,str) or not re.fullmatch(r'[A-Za-z0-9_./\[\]$-]+',s) for s in identifiers):
            raise ValueError('Unsafe signal-buffer identifier')
        row = connection_terminals(context,op['net']); selected = set(op['consumers'])
        if (context['nets'][op['net']]['type'] != 'SIGNAL' or row['ports'] or row['driver'] != op['driver']
                or op['cell'] not in BUFFERS or not selected or len(selected) != len(op['consumers'])
                or not selected <= set(row['consumers']) or moved & selected
                or op['instance'] in context['instances'] or op['instance'] in names
                or op['new_net'] in context['nets'] or op['new_net'] in nets):
            raise ValueError('Disallowed signal branch, collision or consumer partition')
        sizes = {(i['bbox_dbu'][2]-i['bbox_dbu'][0],i['bbox_dbu'][3]-i['bbox_dbu'][1])
                 for i in context['instances'].values() if i['cell'] == op['cell']}
        if len(sizes) != 1:raise ValueError('Missing or ambiguous buffer master dimensions')
        box = op['footprint_dbu']
        _footprint(context,box,sizes.pop(),plan['site_pitch_dbu'],op['orientation'],boxes)
        area += (box[2]-box[0])*(box[3]-box[1])/context['dbu_per_micron']**2
        names.add(op['instance']);nets.add(op['new_net']);moved.update(selected);boxes.append(box)
    if (type(plan['added_area_um2']) not in (int,float) or not math.isfinite(plan['added_area_um2'])
            or abs(plan['added_area_um2']-area)>1e-6):
        raise ValueError('Incorrect added signal-buffer area')
    return dict(added_buffers=len(names),added_area_um2=area)


def render_tcl(plan, context, output_dir):
    validate_plan(plan,context)
    if not re.fullmatch(r'/probe/[A-Za-z0-9_-]+',output_dir):raise ValueError('Unsafe output directory')
    literal=lambda s:'{'+s+'}'
    lines=['set_routing_layers -signal Metal2-Metal4 -clock Metal2-Metal4',
           'set_global_routing_layer_adjustment * 0.3','global_route -start_incremental']
    for net in sorted({op['net'] for op in plan['buffers']}):
        row=connection_terminals(context,net)
        lines += [f'set wire [$::block findNet {literal(net)}]',
            'if {$wire eq "NULL" || [$wire getSigType] ne "SIGNAL" || [llength [$wire getBTerms]] != 0} {error "Changed signal source"}',
            'set actual {}','foreach it [$wire getITerms] {lappend actual "[[$it getInst] getName]/[[$it getMTerm] getName]"}',
            'if {[lsort $actual] ne [lsort [list '+' '.join(map(literal,[row['driver'],*row['consumers']]))+']]} {error "Changed source terminals"}']
    for op in plan['buffers']:
        x,y=op['footprint_dbu'][:2]
        lines += [f'if {{[$::block findInst {literal(op["instance"])}] ne "NULL" || [$::block findNet {literal(op["new_net"])}] ne "NULL"}} {{error "Signal-buffer collision"}}',
            f'set buffer [odb::dbInst_create $::block [[ord::get_db] findMaster {literal(op["cell"])}] {literal(op["instance"])}]',
            f'odb::dbNet_create $::block {literal(op["new_net"])}',
            f'$buffer setOrient {op["orientation"]}',f'$buffer setLocation {x} {y}','$buffer setPlacementStatus PLACED',
            f'[$buffer findITerm A] connect [$::block findNet {literal(op["net"])}]',
            f'[$buffer findITerm X] connect [$::block findNet {literal(op["new_net"])}]']
        for pin in op['consumers']:
            lines += [f'set it [$::block findITerm {literal(pin)}]','$it disconnect',
                f'$it connect [$::block findNet {literal(op["new_net"])}]']
    lines += ['check_placement -verbose','global_connect','global_route -end_incremental -allow_congestion',
        'estimate_parasitics -global_routing',f'write_guide {output_dir}/repaired.guide',
        f'write_verilog {output_dir}/repaired.v',f'write_db {output_dir}/repaired.odb']
    return '\n'.join(lines)+'\n'


def verify_context(plan, before, after):
    result=validate_plan(plan,before);expected=deepcopy(before)
    for op in plan['buffers']:
        name=op['instance'];terms=expected['nets'][op['net']]['terminals'];selected=set(op['consumers'])
        moved=[t for t in terms if t['instance']+'/'+t['pin'] in selected]
        if len(moved)!=len(selected):raise ValueError('Missing selected terminals')
        expected['nets'][op['net']]['terminals']=[t for t in terms if t not in moved]+[dict(instance=name,pin='A',direction='INPUT')]
        expected['nets'][op['new_net']]=dict(type='SIGNAL',ports=[],terminals=moved+[dict(instance=name,pin='X',direction='OUTPUT')])
        for net,pin in [('VPWR','VDD'),('VGND','VSS')]:
            expected['nets'][net]['terminals'].append(dict(instance=name,pin=pin,direction='INOUT'))
        expected['instances'][name]=dict(cell=op['cell'],macro=False,orientation=op['orientation'],
            bbox_dbu=op['footprint_dbu'],bbox=[v/before['dbu_per_micron'] for v in op['footprint_dbu']])
    norm=lambda c:{n:(v['type'],sorted(v['ports']),sorted((t['instance'],t['pin'],t['direction']) for t in v['terminals'])) for n,v in c['nets'].items()}
    if norm(expected)!=norm(after):raise ValueError('Unexpected signal, clock or power edit')
    if expected['instances']!=after['instances']:raise ValueError('Unexpected cell or placement edit')
    if any(before[k]!=after[k] for k in FIXED) or before['dbu_per_micron']!=after['dbu_per_micron']:
        raise ValueError('Changed fixed physical geometry')
    # Rebinding a macro signal may change only the net associated with its pin.
    shapes=lambda c:[{k:v for k,v in p.items() if k!='net'} for p in c['macro_pins']]
    if shapes(before)!=shapes(after):raise ValueError('Changed macro pin geometry')
    pin_net={t['instance']+'/'+t['pin']:n for n,v in after['nets'].items() for t in v['terminals']}
    if any(p['net']!=pin_net.get(p['instance']+'/'+p['pin']) for p in after['macro_pins']):
        raise ValueError('Inconsistent macro pin binding')
    return dict(result,exact_plan_implemented=True,power_bindings_retained=True,original_placements_retained=True)


def verify_actual(plan, before, after, reference, repaired):
    physical=verify_context(plan,before,after)
    logic=compare_buffer_repair(reference,repaired)
    expected={op['instance']:op['cell'] for op in plan['buffers']}
    if set(logic['added_instances'])!=set(expected) or any(repaired['cells'][n]['type']!=cell for n,cell in expected.items()):
        raise ValueError('Unexpected added buffer membership')
    return dict(physical=physical,connectivity=logic)
