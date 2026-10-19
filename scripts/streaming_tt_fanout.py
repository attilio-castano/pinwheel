"""Unexecuted positive-buffer cloning plans from actual ODB pin inventories.

An equal-master clone shares the original input and partitions its outputs.
A public root overload requires an explicitly balanced common prefix level.
Recursive upstream loads are counted. Native legal placement, rerouting,
clock/data kernel certificates and STA remain separate.
"""
from copy import deepcopy

from streaming_tt_quality import inventory_context
from streaming_tt_physical import require


def positive_buffers(library):
    return {name for name, cell in library.cells.items() if name.startswith('sg13cmos5l_buf_') and
        not cell.sequential and cell.directions == {'A': 'input', 'X': 'output'} and
        cell.output == 'X' and cell.function == ('variable', 'A')}


def loads(inventory):
    context, _ = inventory_context(inventory)
    result = {}
    for name, net in context['nets'].items():
        if net['type'] not in ('SIGNAL', 'CLOCK'): continue
        terms = [('iterm', row['instance'], row['pin']) for row in net['terminals'] if row['direction'] == 'INPUT']
        terms += [('bterm', port) for port in net['ports'] if inventory['public_bterms'][port]['direction'] == 'output']
        drivers = [('iterm', row['instance'], row['pin']) for row in net['terminals'] if row['direction'] == 'OUTPUT']
        drivers += [('bterm', port) for port in net['ports'] if inventory['public_bterms'][port]['direction'] == 'input']
        result[name] = dict(loads=sorted(terms), drivers=drivers, kind=net['type'])
    return result


def apply_operation(inventory, operation, buffers, *, context=None):
    """Validate and project one exact clone; this does not edit a native ODB."""
    expected = {'kind', 'source_net', 'source_instance', 'master', 'upstream_net', 'new_instance', 'new_net', 'loads'}
    require(set(operation) == expected, 'Incomplete clone operation')
    net, source = operation['source_net'], operation['source_instance']
    require(net in inventory['nets'] and operation['master'] in buffers, 'Missing actual positive-buffer source')
    table = loads(inventory) if context is None else context
    context = table[net]
    if operation['kind'] == 'clone':
        require(source in inventory['instances'], 'Missing actual clone source')
        original = inventory['instances'][source]
        require(original['master'] == operation['master'], 'Clone master differs from actual source buffer')
        require(context['drivers'] == [('iterm', source, 'X')], 'Clone source does not uniquely drive selected actual net')
    else:
        require(source is None and operation['upstream_net'] == net and
            ((operation['kind'] == 'clock_root_prefix' and context['kind'] == 'CLOCK' and
            context['drivers'] == [('bterm', 'clk')]) or (operation['kind'] == 'signal_buffer' and
            context['kind'] == 'SIGNAL' and len(context['drivers']) == 1)),
            'Positive insertion is restricted to an actual signal driver or the exact public clock root')
        candidates = [row for row in inventory['instances'].values() if row['master'] == operation['master']]
        require(candidates, 'No actual equal-master rail template for root prefix')
        original = deepcopy(candidates[0]); original['terminals']['A']['net'] = net
        original['terminals']['X']['net'] = net
    terms = original['terminals']
    require({name: row['direction'] for name, row in terms.items() if row['signal_type'] not in ('POWER', 'GROUND')} ==
        {'A': 'INPUT', 'X': 'OUTPUT'} and terms['X']['net'] == net and terms['A']['net'] == operation['upstream_net'] and
        (operation['kind'] != 'clone' or operation['upstream_net'] != net),
        'Clone input/output differs from actual source buffer')
    moved = [tuple(value) for value in operation['loads']]
    require(moved and len(moved) == len(set(moved)) and set(moved) <= set(context['loads']), 'Clone drops or invents an actual load')
    name, branch = operation['new_instance'], operation['new_net']
    require(name not in inventory['instances'] and branch not in inventory['nets'], 'Clone names collide')
    clone = deepcopy(original); clone['terminals']['X']['net'] = branch
    rails = {kind: [row['net'] for row in clone['terminals'].values() if row['signal_type'] == kind]
        for kind in ('POWER', 'GROUND')}
    require(rails == {'POWER': ['VPWR'], 'GROUND': ['VGND']} and inventory['nets']['VPWR']['signal_type'] == 'POWER' and
        inventory['nets']['VGND']['signal_type'] == 'GROUND', 'Clone rail bindings are not actual distinct rails')
    inventory['instances'][name] = clone
    inventory['nets'][branch] = dict(wire=max(row['wire'] for row in inventory['nets'].values())+1,
        signal_type=inventory['nets'][net]['signal_type'])
    for terminal in moved:
        if terminal[0] == 'iterm': inventory['instances'][terminal[1]]['terminals'][terminal[2]]['net'] = branch
        else: inventory['public_bterms'][terminal[1]]['net'] = branch
    inventory['instance_counts'][operation['master']] = inventory['instance_counts'].get(operation['master'], 0)+1
    inventory['signal_model_instances'] += 1
    moved_set = set(moved)
    context['loads'] = [identity for identity in context['loads'] if identity not in moved_set]
    table[branch] = dict(loads=sorted(moved), drivers=[('iterm', name, 'X')], kind=context['kind'])
    table[operation['upstream_net']]['loads'].append(('iterm', name, 'A'))


def build_plan(inventory, library, *, maximum=8, maximum_added=1024):
    require(type(maximum) is int and maximum == 8 and type(maximum_added) is int and 0 < maximum_added <= 1024,
        'Unsupported bounded fanout policy')
    work = deepcopy(inventory); buffers = positive_buffers(library); require(buffers, 'No actual positive buffers')
    operations = []; before = loads(work); context = deepcopy(before); root_prefixes = 0; signal_insertions = []
    depths = {}; visiting = set()
    def depth(name):
        if name in depths: return depths[name]
        require(name not in visiting, 'Cyclic unary-buffer ancestry is unsupported')
        visiting.add(name); value = 0
        row = before[name]
        if len(row['drivers']) == 1 and row['drivers'][0][0] == 'iterm':
            instance = work['instances'][row['drivers'][0][1]]
            cell = library.cells.get(instance['master'])
            inputs = [pin for pin, term in instance['terminals'].items() if term['direction'] == 'INPUT' and
                term['signal_type'] not in ('POWER', 'GROUND')]
            if cell is not None and not cell.sequential and len(inputs) == 1:
                upstream = instance['terminals'][inputs[0]]['net']
                if upstream in before: value = depth(upstream)+1
        visiting.remove(name); depths[name] = value
        return value
    for name in before: depth(name)
    while True:
        over = [(name, row) for name, row in context.items() if len(row['loads']) > maximum]
        if not over: break
        # Finish every recursive internal/source repair before one final root
        # prefix batch. No later clone may attach an unrecorded root input.
        name, row = min(over, key=lambda item: (item[1]['drivers'] == [('bterm', 'clk')],
            item[1]['kind'] != 'CLOCK', -depths[item[0]], item[0]))
        require(len(operations) < maximum_added, 'Clone expansion exceeds explicit cell budget')
        require(len(row['drivers']) == 1, 'Overloaded nonunique driver needs a separate repair')
        driver_instance = None if row['drivers'][0][0] == 'bterm' else row['drivers'][0][1]
        nonbuffer = driver_instance is None or work['instances'][driver_instance]['master'] not in buffers
        if nonbuffer:
            root_prefix = row['kind'] == 'CLOCK'
            require((root_prefix and row['drivers'] == [('bterm', 'clk')] and root_prefixes == 0) or
                row['kind'] == 'SIGNAL', 'Overloaded non-positive internal clock driver needs a separate repair')
            require(len(row['loads']) <= maximum*maximum, 'More than one uniformly declared prefix level would be required')
            original_loads = list(row['loads']); master = 'sg13cmos5l_buf_8'
            require(master in buffers and master in work['masters'], 'No actual positive root-prefix master')
            for offset in range(0, len(original_loads), maximum):
                require(len(operations) < maximum_added, 'Clone expansion exceeds explicit cell budget')
                number = len(operations)
                operation = dict(kind='clock_root_prefix' if root_prefix else 'signal_buffer', source_net=name, source_instance=None, master=master,
                    upstream_net=name, new_instance='streaming_tt_fanout_clone_'+str(number),
                    new_net='streaming_tt_fanout_branch_'+str(number),
                    loads=[list(value) for value in original_loads[offset:offset+maximum]])
                apply_operation(work, operation, buffers, context=context); operations.append(operation)
                depths[operation['new_net']] = depths[name]+1
            if root_prefix: root_prefixes += 1
            else: signal_insertions.append(name)
            continue
        source = row['drivers'][0][1]; original = work['instances'][source]
        require(original['master'] in buffers, 'Overloaded non-buffer driver needs a separate repair: '+name)
        moved = row['loads'][maximum:maximum*2]
        number = len(operations)
        operation = dict(kind='clone', source_net=name, source_instance=source, master=original['master'],
            upstream_net=original['terminals']['A']['net'], new_instance='streaming_tt_fanout_clone_'+str(number),
            new_net='streaming_tt_fanout_branch_'+str(number), loads=[list(value) for value in moved])
        apply_operation(work, operation, buffers, context=context); operations.append(operation)
        depths[operation['new_net']] = depths[name]
    plan = dict(schema='pinwheel.streaming-tt-fanout-clone-plan.v1', qualified=False, status='unexecuted',
        maximum_loads=maximum, maximum_added_cells=maximum_added, operations=operations,
        initial_over_limit={name: len(row['loads']) for name, row in before.items() if len(row['loads']) > maximum},
        final_projected_over_limit={}, projected_added_cells=len(operations), all_passive_loads_counted=True,
        upstream_loads_recounted_after_each_clone=True, preserves_internal_positive_buffer_depth=True,
        balanced_public_clock_prefix_levels=root_prefixes,
        signal_nets_with_new_positive_buffer_level=signal_insertions,
        acceptance_requires=['native placement and global rails', 'fresh whole-chip routing',
            'actual all-corner setup hold and electrical checks', 'actual data and clock kernel correspondence'],
        boundary='Exact actual-pin partition proposal. Internal additions are equal-master positive-buffer clones '
            'sharing the original upstream net. If cloning overloads the public clock root, all its current loads '
            'receive one balanced positive-buffer prefix level. Geometry, routing and timing are not predicted.')
    verify_result(inventory, work, plan, library)
    return plan, work


def verify_result(before, actual, plan, library):
    require(plan.get('schema') == 'pinwheel.streaming-tt-fanout-clone-plan.v1' and plan.get('qualified') is False and
        plan.get('status') == 'unexecuted' and plan.get('maximum_loads') == 8, 'Wrong clone proposal boundary')
    projected = deepcopy(before); buffers = positive_buffers(library); context = loads(projected)
    prefix_loads = None; moved_prefix = []; prefix_source = None; prefix_seen = False; prefix_ended = False
    signal_insertions = set()
    for operation in plan['operations']:
        if operation['kind'] == 'clock_root_prefix':
            require(not prefix_ended, 'Root prefix operations must form one balanced batch')
            if not prefix_seen:
                prefix_seen = True; prefix_source = operation['source_net']
                prefix_loads = set(context[prefix_source]['loads'])
                require(8 < len(prefix_loads) <= 64, 'Unsupported uniform root prefix depth')
            require(operation['source_net'] == prefix_source, 'Changed common root prefix source')
            moved_prefix.extend(tuple(value) for value in operation['loads'])
        elif prefix_seen:
            prefix_ended = True
            require(False, 'No clone or signal insertion may follow the final common root prefix')
        if operation['kind'] == 'signal_buffer': signal_insertions.add(operation['source_net'])
        apply_operation(projected, operation, buffers, context=context)
    require(not prefix_seen or (len(moved_prefix) == len(set(moved_prefix)) and set(moved_prefix) == prefix_loads),
        'Root prefix does not cover all original root loads at one uniform depth')
    if prefix_seen:
        expected_root_loads = {('iterm', operation['new_instance'], 'A') for operation in plan['operations']
            if operation['kind'] == 'clock_root_prefix'}
        require(set(loads(actual)[prefix_source]['loads']) == expected_root_loads,
            'Final public clock root has an unrecorded bypass or missing prefix input')
    require(plan.get('balanced_public_clock_prefix_levels') == int(prefix_seen) and
        plan.get('preserves_internal_positive_buffer_depth') is True and
        set(plan.get('signal_nets_with_new_positive_buffer_level', [])) == signal_insertions,
        'Hidden or misstated positive-buffer depth change')
    def named_inventory(value):
        value = deepcopy(value)
        # Exporter-local numeric wire labels change after sorting added names.
        # All net names, types, public/instance pins and unused-output names
        # remain exact; the actual exporter checks unique concrete wire IDs.
        for row in value['nets'].values(): row.pop('wire')
        value['unconnected_signal_outputs'] = sorted(value['unconnected_signal_outputs'])
        return value
    require(named_inventory(projected) == named_inventory(actual),
        'Native/projected clone result changes an unadmitted cell, pin, load or rail')
    require(not any(len(row['loads']) > 8 for row in loads(actual).values()), 'Recursive actual fanout remains over eight')
    require(len(actual['instances'])-len(before['instances']) == len(plan['operations']) == plan['projected_added_cells'],
        'Added clone inventory differs')
    return dict(passed=True, qualified=False, original_instances_retained=len(before['instances']),
        exact_pin_partition_checked=True, positive_clone_cells=len(plan['operations']),
        all_signal_and_clock_loads_at_most_eight=True, native_placement_or_timing_qualified=False)


def main():
    import argparse
    import json
    from pathlib import Path
    import subprocess
    from streaming_tt_physical import ROOT, committed, regular, read, sha, write
    from streaming_tt_intake import dependency_closure
    from streaming_tt_simulation import libraries
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--export-report', type=Path, required=True)
    parser.add_argument('--corners-json', type=Path, required=True)
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    export_path = regular(args.export_report).resolve(); exported = read(export_path)
    require(exported.get('schema') == 'pinwheel.streaming-tt-odb-export-run.v1' and exported.get('passed') is True and
        exported.get('inputs_unchanged') is True and exported.get('staged_inputs_unchanged') is True and
        exported.get('runtime_unchanged') is True and exported.get('native_export_binding') is True and
        exported.get('container_termination', {}).get('status') == 'absent', 'Actual native ODB export is not closed')
    inventory_path = regular(export_path.parent/'native/export/inventory.json')
    require(exported.get('artifact_sha256', {}).get('native/export/inventory.json') == sha(inventory_path),
        'Actual inventory differs from closed native export')
    inventory = read(inventory_path); corners_path = regular(args.corners_json).resolve(); corners = read(corners_path)
    closure = dependency_closure(ROOT, ['scripts/streaming_tt_fanout.py'])
    for name in closure['files']: committed(ROOT/name)
    paths = [export_path, inventory_path, corners_path, *(regular(row['path']) for row in corners.values()),
        *(ROOT/name for name in closure['files'])]
    before = {str(path): sha(path) for path in paths}
    library, functional = libraries(corners, set(inventory['masters'])-set(inventory['physical_only_instances'].values()))
    plan, projected = build_plan(inventory, library)
    validation = verify_result(inventory, projected, plan, library)
    require(before == {str(path): sha(path) for path in paths}, 'Clone proposal inputs changed during analysis')
    args.out.mkdir(parents=True, exist_ok=False); write(args.out/'plan.json', plan)
    write(args.out/'report.json', dict(schema='pinwheel.streaming-tt-fanout-proposal.v1', qualified=False,
        status='unexecuted_proposal', source_commit=exported['source_commit'],
        producer_commit=subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(),
        actual_odb_sha256=exported['actual_odb_sha256'], input_sha256=before,
        input_unchanged=True, producer_dependency_closure=closure, actual_three_corner_functions=functional,
        plan_sha256=sha(args.out/'plan.json'), validation=validation,
        native_transformation_executed=False, native_placement_or_route_qualified=False))
    print(args.out/'report.json')


if __name__ == '__main__': main()
