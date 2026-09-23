"""Compile a screened organization into exact signal edits and check their readback.

This does not extend whole-chip route admission. A successful local edit still
needs the original complete numerical contract and a separate route gate.
"""
from copy import deepcopy

from physical_connections import connection_terminals
from physical_organization_edits import import_local_plan, validate_plan as validate_edits, verify_actual as verify_edits


def build_plan(candidates,context,source_database,protected,relocation_rule,site_pitch_dbu):
    if any(not c['area_screen_pass'] or not c['footprint_screen_pass'] or
           not c['mechanism_screen']['pass_conditional_screen'] for c in candidates):
        raise ValueError('Require conditionally screened choices')
    resizes=[];exchanges=[];receivers=[]
    for c in candidates:
        if c['kind'] in ('resize_buffer','move_resize_buffer'):
            for e in c['edits']:
                resizes.append(dict(instance=e['instance'],before=deepcopy(context['instances'][e['instance']]),
                    cell=e['cell'],footprint_dbu=e['footprint_dbu'],net=e['net']))
        elif c['kind']=='exchange_leaf_consumers':
            exchanges+=deepcopy(c['edits'])
        elif c['kind']=='add_macro_receiver':
            receivers+=deepcopy(c['edits'])
        else:raise ValueError('Unsupported organization edit')
    if len(receivers)!=1 or len(resizes)!=2 or not exchanges:raise ValueError('Require the bounded mixed experiment')
    receiver=receivers[0];receiver.update(instance='paired_locality_receiver_14',new_net='paired_locality_receiver_14_net')
    box=receiver['footprint_dbu']
    neighbors=[(abs(i['bbox_dbu'][0]-box[0]),i['orientation']) for i in context['instances'].values()
        if not i['macro'] and i['bbox_dbu'][1]==box[1] and i['bbox_dbu'][3]==box[3]]
    if not neighbors:raise ValueError('Missing same-row orientation evidence')
    orientations={o in ('MX','R180') for _,o in neighbors}
    if len(orientations)!=1:raise ValueError('Inconsistent row rail orientation')
    receiver['orientation']='MX' if orientations.pop() else 'R0'
    plan=dict(schema=1,source_database=source_database,resizes=resizes,exchanges=exchanges,receiver=receiver,
        selected_candidates=[c['id'] for c in candidates],protected_instances=sorted(protected),
        relocation=dict(relocation_rule,site_pitch_dbu=site_pitch_dbu),
        added_area_um2=sum(c['added_area_um2'] for c in candidates),execution_scope='one_bounded_local_probe')
    validate_plan(plan,context)
    return plan


def validate_plan(plan,context):
    """Compatibility adapter for the retained local experiment's plan format."""
    edits, policy = import_local_plan(plan)
    return validate_edits(edits, context, policy)


def render_tcl(plan,context):
    validate_plan(plan,context);literal=lambda s:'{'+s+'}'
    nets={e['net'] for e in plan['exchanges']}|{e['net'] for e in plan['resizes']}|{plan['receiver']['net']}
    lines=['# Exact organization experiment; no clock or state edits.', 'write_verilog /probe/before.v',
        'set_routing_layers -signal Metal2-Metal4 -clock Metal2-Metal4',
        'set_global_routing_layer_adjustment * 0.3','global_route -start_incremental']
    for net in sorted(nets):
        row=connection_terminals(context,net);expected=[row['driver'],*row['consumers']]
        lines += [f'set wire [$::block findNet {literal(net)}]',
            'if {$wire eq "NULL" || [$wire getSigType] ne "SIGNAL"} {error "Missing signal source"}',
            'set actual {}','foreach it [$wire getITerms] {lappend actual "[[$it getInst] getName]/[[$it getMTerm] getName]"}',
            'if {[lsort $actual] ne [lsort [list '+' '.join(map(literal,expected))+']]} {error "Changed source consumers"}']
        if row['ports']:raise ValueError('Package branches are outside the experiment')
        lines+=['if {[llength [$wire getBTerms]] != 0} {error "Unexpected package branch"}']
    for e in plan['resizes']:
        inst=literal(e['instance']);x,y=e['footprint_dbu'][:2]
        lines += [f'set inst [$::block findInst {inst}]',
            f'if {{[[$inst getMaster] getName] ne {literal(e["before"]["cell"])}}} {{error "Changed resize source"}}',
            f'replace_cell {inst} {e["cell"]}',f'$inst setOrient {e["before"]["orientation"]}',f'$inst setLocation {x} {y}']
    for e in plan['exchanges']:
        for pin in sorted(set(e['after'])-set(e['before'])):
            lines += [f'set it [$::block findITerm {literal(pin)}]','$it disconnect',f'$it connect [$::block findNet {literal(e["net"])}]']
    r=plan['receiver'];x,y=r['footprint_dbu'][:2]
    lines += [f'if {{[$::block findInst {literal(r["instance"])}] ne "NULL" || [$::block findNet {literal(r["new_net"])}] ne "NULL"}} {{error "Receiver name collision"}}',
        f'set inst [odb::dbInst_create $::block [[ord::get_db] findMaster {r["cell"]}] {literal(r["instance"])}]',
        f'odb::dbNet_create $::block {literal(r["new_net"])}',f'$inst setOrient {r["orientation"]}',f'$inst setLocation {x} {y}',
        '$inst setPlacementStatus PLACED',f'[$inst findITerm A] connect [$::block findNet {literal(r["net"])}]',
        f'[$inst findITerm X] connect [$::block findNet {literal(r["new_net"])}]',
        f'set it [$::block findITerm {literal(r["receiver"])}]','$it disconnect',f'$it connect [$::block findNet {literal(r["new_net"])}]',
        'check_placement -verbose','global_connect','global_route -end_incremental -allow_congestion',
        'estimate_parasitics -global_routing','write_guide /probe/repaired.guide','write_verilog /probe/repaired.v','write_db /probe/repaired.odb']
    return '\n'.join(lines)+'\n'


def verify_actual(plan,before,after,reference,repaired):
    """Use the shared exact-edit checker for the retained local plan format."""
    edits, policy = import_local_plan(plan)
    return verify_edits(edits, policy, before, after, reference, repaired)
