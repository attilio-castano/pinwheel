"""Distribution-family coverage and measured margins for a frozen physical chip.

Membership follows typed boundaries and closes over existing buffer/hold chains.
Families may overlap. Measurements describe named saved routes, not a bound on
future wire load; a generated repair still needs independent physical checks.
"""
from collections import Counter
import math

from physical_buffer_repair import BUFFERS
from physical_connections import Connectivity
from physical_repair_plan import validate_plan

CHAIN_CELLS = BUFFERS | {'sg13cmos5l_dlygate4sd3_1'}


def inventory(context, ownership, roles, scope):
    """Include every branching match, all declared macro inputs and chain neighbors."""
    if set(scope) != {'source_owner', 'sink_owner', 'sink_owner_prefix', 'macro_inputs'}:
        raise ValueError('Incomplete distribution scope')
    if (scope['source_owner'] not in ownership['registers'] or
            scope['sink_owner'] not in ownership['registers'] or
            not scope['sink_owner_prefix'] or not any(
                n.startswith(scope['sink_owner_prefix']) for n in ownership['registers'])):
        raise ValueError('Unresolved distribution owner')
    inputs = scope['macro_inputs']
    if not inputs or len(set(inputs)) != len(inputs):
        raise ValueError('Require distinct declared macro inputs')
    graph = Connectivity(context, ownership)
    seeds, cached = {}, {}
    for name, net in context['nets'].items():
        if net['type'] != 'SIGNAL' or sum(t['direction'] == 'INPUT' for t in net['terminals']) < 2:
            continue
        row = graph.record(name, roles)
        cached[name] = row
        families = []
        if row['source_owners'] == [scope['source_owner']]:
            families.append('serial_data')
        if row['sink_owners'] == [scope['sink_owner']]:
            families.append('serial_control')
        if row['sink_owners'] and all(n.startswith(scope['sink_owner_prefix']) for n in row['sink_owners']):
            families.append('parameter_distribution')
        if families:
            seeds[name] = set(families)
    for pin in inputs:
        if pin not in graph.pin_net:
            raise ValueError('Missing distribution macro input: ' + pin)
        cell = pin.rsplit('/', 1)[0]
        net = graph.pin_net[pin]
        if (not context['instances'][cell]['macro'] or
                pin not in graph.terminals(net)['consumers']):
            raise ValueError('Declared distribution endpoint is not a macro input')
        seeds.setdefault(net, set()).add('sram_write_input')
    selected, todo = set(seeds), list(seeds)
    adjacency = {}
    while todo:
        name = todo.pop()
        neighbors = set()
        for terminal in context['nets'][name]['terminals']:
            cell = terminal['instance']
            if context['instances'][cell]['cell'] not in CHAIN_CELLS:
                continue
            for _, _, other in graph.cell_terms[cell]:
                if context['nets'][other]['type'] == 'SIGNAL' and other != name:
                    neighbors.add(other)
        adjacency[name] = neighbors
        for other in neighbors - selected:
            selected.add(other)
            todo.append(other)
    components, remaining = [], set(selected)
    while remaining:
        todo, members = [min(remaining)], set()
        while todo:
            name = todo.pop()
            if name in members:
                continue
            members.add(name)
            todo.extend(adjacency[name] - members)
        remaining -= members
        families = sorted({f for n in members for f in seeds.get(n, ())})
        roots = [n for n in members if context['instances'][graph.terminals(n)['driver'].rsplit('/', 1)[0]]['cell'] not in CHAIN_CELLS]
        if len(roots) != 1:
            raise ValueError('Distribution chain requires one driven root')
        components.append(dict(root=roots[0], nets=sorted(members), families=families))
    records = []
    for component in sorted(components, key=lambda c:c['root']):
        for name in component['nets']:
            row = cached[name] if name in cached else graph.record(name, roles)
            boxes = {pin:context['instances'][pin.rsplit('/', 1)[0]]['bbox']
                     for pin in [row['driver'], *row['consumers']]}
            centers = [[(b[0]+b[2])/2, (b[1]+b[3])/2] for b in boxes.values()]
            span = sum(max(p[i] for p in centers)-min(p[i] for p in centers) for i in (0, 1))
            records.append(dict(row, families=component['families'], distribution_root=component['root'],
                seed_families=sorted(seeds.get(name, ())), terminal_cell_boxes_um=boxes,
                cell_center_span_um=span))
    records.sort(key=lambda r:r['net'])
    return dict(schema=1, source_database_sha256=context['database_sha256'], scope=scope,
        seed_nets=len(seeds), connections=records, components=components,
        families=dict(Counter(f for r in records for f in r['families'])),
        boundary='All branching typed-owner matches plus declared macro inputs, closed over buffer and hold chains. Shared families are retained. Cell-center span is not routed length. Chain traversal does not remove or authorize changes to hold cells.')


def assess(records, measurements, corners, reserve_fraction):
    """Apply an explicit experimental headroom gate to every covered connection."""
    if (type(reserve_fraction) not in (int,float) or not 0 < reserve_fraction < 1 or
            not math.isfinite(reserve_fraction)):
        raise ValueError('Invalid experimental reserve fraction')
    if not corners or len(set(corners)) != len(corners):
        raise ValueError('Require distinct measurement corners')
    names = {r['net'] for r in records}
    if len(names) != len(records) or set(measurements) != {'local', 'route'}:
        raise ValueError('Incomplete distribution measurements')
    for checkpoint in measurements.values():
        if set(checkpoint) != set(corners) or any(set(rows) != names for rows in checkpoint.values()):
            raise ValueError('Missing distribution net or corner')
    output = []
    for record in records:
        net = record['net']
        margins, failing, below_reserve, ratios = [], False, False, []
        for corner in corners:
            before, after = [measurements[label][corner][net] for label in ['local', 'route']]
            if (before['pin_cap_pf'] != after['pin_cap_pf'] or
                    before['loads'] != after['loads'] or after['drivers'] != 1 or
                    after['loads'] != len(record['consumers']) + len(record['ports'])):
                raise ValueError('Changed distribution pin load or consumer count')
            per_corner = dict(corner=corner)
            for title in ['capacitance', 'slew']:
                limit, actual = after[title]['limit'], after[title]['actual']
                if not all(math.isfinite(v) for v in [limit, actual]) or limit <= 0 or actual < 0:
                    raise ValueError('Missing finite positive distribution limit')
                fraction = (limit - actual) / limit
                per_corner[title] = dict(limit=limit, actual=actual, reserve_fraction=fraction,
                    remaining_budget=limit-actual, trial_budget=limit*(1-reserve_fraction))
                failing |= fraction < -1e-8
                below_reserve |= fraction < reserve_fraction
            per_corner['setup_ns'] = after['paths']['max']['slack_ns']
            per_corner['hold_ns'] = after['paths']['min']['slack_ns']
            per_corner['wire_budget_pf'] = (after['capacitance']['limit'] * (1-reserve_fraction)
                                           - after['pin_cap_pf'][1])
            per_corner['measured_wire_cap_pf'] = after['wire_cap_pf'][1]
            margins.append(per_corner)
            old_wire, new_wire = before['wire_cap_pf'][1], after['wire_cap_pf'][1]
            if old_wire > 0:
                ratios.append(new_wire / old_wire)
        output.append(dict(net=net, families=record['families'], distribution_root=record['distribution_root'],
            verdict='failing' if failing else 'below_trial_reserve' if below_reserve else 'within_trial_reserve',
            corners=margins, measured_wire_ratio_range=[min(ratios),max(ratios)] if ratios else None))
    return dict(reserve_fraction=reserve_fraction, connections=output,
        counts=dict(Counter(r['verdict'] for r in output)),
        boundary='The reserve is an explicit experimental selection/acceptance criterion, not a PDK requirement or guarantee against future routing. Observed wire ratios are descriptive only.')


def validate_contract(contract, coverage, assessment, plan, context, source_timing):
    """Check a proposed contract and its exact plan, without admitting execution."""
    fields = {'schema','status','source_database_sha256','scope','reserve_fraction',
              'selected_nets','max_added_area_fraction','max_timing_regression_fraction',
              'timing_floors_ns','acceptance','boundary'}
    if set(contract) != fields or contract['schema'] != 1 or contract['status'] != 'checked-plan-only':
        raise ValueError('Incomplete distribution contract')
    if (contract['source_database_sha256'] != context['database_sha256'] or
            coverage['source_database_sha256'] != context['database_sha256'] or
            contract['scope'] != coverage['scope']):
        raise ValueError('Changed distribution source or coverage')
    if contract['reserve_fraction'] != assessment['reserve_fraction']:
        raise ValueError('Changed measured reserve policy')
    covered = {r['net'] for r in coverage['connections']}
    if (len(covered) != len(coverage['connections']) or
            {r['net'] for r in assessment['connections']} != covered or
            len(assessment['connections']) != len(covered)):
        raise ValueError('Missing passing distribution neighbor')
    if any(r['verdict'] not in {'within_trial_reserve','below_trial_reserve','failing'}
           for r in assessment['connections']):
        raise ValueError('Unknown distribution margin verdict')
    selected = sorted(r['net'] for r in assessment['connections'] if r['verdict'] != 'within_trial_reserve')
    if (contract['selected_nets'] != selected or
            sorted(op['net'] for op in plan['operations']) != selected):
        raise ValueError('Plan drops a failing or low-margin family member')
    area_fraction, regression = contract['max_added_area_fraction'], contract['max_timing_regression_fraction']
    if (not all(type(v) in (int,float) and math.isfinite(v) for v in [area_fraction, regression]) or
            not 0 < area_fraction <= .01 or not 0 <= regression < 1):
        raise ValueError('Invalid bounded area or timing budget')
    result = validate_plan(plan, context, context['database_sha256'])
    area = sum((i['bbox_dbu'][2]-i['bbox_dbu'][0]) * (i['bbox_dbu'][3]-i['bbox_dbu'][1])
               for i in context['instances'].values()) / context['dbu_per_micron']**2
    if result['added_area_um2'] > area * area_fraction:
        raise ValueError('Distribution plan exceeds its area budget')
    floors = {corner:{kind:values['timing__'+kind+'__ws'] * (1-regression) for kind in ['setup','hold']}
              for corner,values in source_timing.items()}
    if (not floors or any(not math.isfinite(v) or v <= 0 for row in floors.values() for v in row.values()) or
            contract['timing_floors_ns'] != floors):
        raise ValueError('Missing, weakened or nonpositive timing floor')
    acceptance = dict(all_covered_and_added_connections_measured=True,
        all_corner_capacitance_and_slew_reserve=True,all_corner_setup_hold_floors=True,
        all_chip_electrical_zero=True,buffer_contracted_identity=True,
        original_cells_clocks_and_hold_retained=True,added_cells_legal_and_power_bound=True,
        whole_chip_routing_revalidation_required=True,congestion_and_effective_clock_rules_reported=True,
        repair_executed=False,new_route_admitted=False,detailed_route_admitted=False)
    if contract['acceptance'] != acceptance:
        raise ValueError('Weakened distribution acceptance or premature execution claim')
    return dict(covered_connections=len(covered),selected_connections=len(selected),
        added_area_um2=result['added_area_um2'],source_area_um2=area,
        added_area_fraction=result['added_area_um2']/area,area_budget_um2=area*area_fraction,
        timing_floors_ns=floors,scope='Checked unexecuted plan; proposed budgets still require measurements after the edit.')
