"""Native positive-buffer partition and legal-placement derivative.

Run in pinned OpenROAD embedded Python. This never edits the input ODB and
does not route, qualify timing, or inherit an upstream kernel certificate.
"""
import argparse
import json
from pathlib import Path

from streaming_tt_export_odb import export_block
from streaming_tt_fanout import apply_operation, loads, positive_buffers, verify_result
from streaming_tt_intake import dependency_closure
from streaming_tt_physical import read, regular, require, sha, write
from streaming_tt_simulation import libraries


def geometry(block):
    return {instance.getName(): dict(location=list(instance.getLocation()), orient=str(instance.getOrient()),
        status=str(instance.getPlacementStatus()), master=instance.getMaster().getName())
        for instance in block.getInsts()}


def terminal(block, identity):
    if identity[0] == 'bterm':
        term = block.findBTerm(identity[1]); require(term is not None, 'Missing selected public load')
    else:
        require(identity[0] == 'iterm' and len(identity) == 3, 'Malformed actual load identity')
        instance = block.findInst(identity[1]); require(instance is not None, 'Missing selected load instance')
        term = instance.findITerm(identity[2]); require(term is not None, 'Missing selected actual load pin')
    return term


def checked_tcl(design, command, journal):
    """The embedded API returns Tcl errors as text; Python exit is insufficient."""
    status = design.evalTclString('catch {'+command+'} _pinwheel_tcl_message')
    message = design.evalTclString('set _pinwheel_tcl_message')
    journal.append(dict(command=command, tcl_catch_status=status, tcl_result=message))
    require(type(status) is str and status == '0' and type(message) is str,
        'Native Tcl command failed or returned an unrecognized status: '+command+'; status='+repr(status)+'; '+str(message))
    return message


def execute(odb, database, block, operation):
    """Only the exact admitted positive buffer and listed loads are changed."""
    net = block.findNet(operation['source_net']); upstream = block.findNet(operation['upstream_net'])
    require(net is not None and upstream is not None, 'Missing actual native branch net')
    source = None if operation['source_instance'] is None else block.findInst(operation['source_instance'])
    def connected(term, name):
        actual = None if term is None else term.getNet()
        return actual is not None and actual.getName() == name
    if operation['kind'] == 'clone':
        require(source is not None and source.getMaster().getName() == operation['master'] and
            connected(source.findITerm('X'), operation['source_net']) and
            connected(source.findITerm('A'), operation['upstream_net']),
            'Native clone source differs from projected actual buffer')
    else: require(operation['kind'] in ('clock_root_prefix', 'signal_buffer'), 'Unknown native buffer operation')
    require(block.findInst(operation['new_instance']) is None and block.findNet(operation['new_net']) is None,
        'Native partition name collision')
    master = database.findMaster(operation['master']); require(master is not None, 'Actual native buffer master absent')
    selected = []
    for identity in operation['loads']:
        term = terminal(block, identity)
        require(connected(term, operation['source_net']) and str(term.getIoType()) == ('OUTPUT' if identity[0] == 'bterm' else 'INPUT'),
            'Selected actual load moved before native partition')
        selected.append(term)
    require(selected and len(selected) == len(operation['loads']), 'Vacuous native output partition')
    instance = odb.dbInst_create(block, master, operation['new_instance'])
    branch = odb.dbNet_create(block, operation['new_net']); branch.setSigType(net.getSigType())
    require(instance is not None and branch is not None, 'Native buffer/net creation failed')
    for term in instance.getITerms():
        kind = str(term.getMTerm().getSigType()); pin = term.getMTerm().getName()
        if kind in ('POWER', 'GROUND'):
            rail = block.findNet('VPWR' if kind == 'POWER' else 'VGND')
            require(rail is not None and str(rail.getSigType()) == kind, 'Missing actual distinct global rail')
            term.connect(rail)
        elif pin == 'A': term.connect(upstream)
        elif pin == 'X': term.connect(branch)
        else: raise ValueError('Native buffer contains an unadmitted signal terminal')
    for term in selected: term.connect(branch)
    if source is not None: point = source.getLocation()
    else:
        points = []
        for term, identity in zip(selected, operation['loads']):
            if identity[0] == 'iterm':
                valid, x, y = term.getAvgXY(); require(valid, 'Actual load has no geometric anchor')
                points.append((x, y))
        require(points, 'No physical load anchor for inserted root/signal buffer')
        point = tuple(round(sum(value[axis] for value in points)/len(points)) for axis in (0, 1))
    rows = list(block.getRows()); require(rows, 'Actual native placement rows absent')
    row = min(rows, key=lambda item: abs(item.getOrigin()[1]-point[1]))
    x0, y0 = row.getOrigin(); width = row.getSite().getWidth(); box = row.getBBox()
    x = x0+round((point[0]-x0)/width)*width
    x = max(box.xMin(), min(x, box.xMax()-master.getWidth()))
    instance.setOrient(row.getOrient()); instance.setLocation(x, y0); instance.setPlacementStatus('PLACED')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ('database', 'reference', 'inventory', 'plan', 'proposal-report', 'corners-json', 'out'):
        parser.add_argument('--'+name, type=Path, required=True)
    parser.add_argument('--top', required=True)
    args = parser.parse_args()
    require(args.out.is_absolute() and not set('{}\\\r\n') & set(str(args.out)), 'Native output path is not safe for literal Tcl')
    inputs = {name: regular(getattr(args, name.replace('-', '_'))).resolve() for name in
        ('database', 'reference', 'inventory', 'plan', 'proposal-report', 'corners-json')}
    proposal, plan = read(inputs['proposal-report']), read(inputs['plan'])
    require(proposal.get('schema') == 'pinwheel.streaming-tt-fanout-proposal.v1' and
        proposal.get('status') == 'unexecuted_proposal' and proposal.get('qualified') is False and
        proposal.get('native_transformation_executed') is False and proposal.get('input_unchanged') is True and
        proposal.get('validation', {}).get('passed') is True and proposal.get('actual_odb_sha256') == sha(inputs['database']) and
        proposal.get('plan_sha256') == sha(inputs['plan']), 'Native input is not the exact proposed actual ODB/plan')
    inventory_pins = [value for name, value in proposal['input_sha256'].items() if name.endswith('/native/export/inventory.json')]
    require(inventory_pins == [sha(inputs['inventory'])], 'Native source inventory differs from actual proposal')
    inventory, reference, corners = read(inputs['inventory']), read(inputs['reference']), read(inputs['corners-json'])
    library, functions = libraries(corners, set(inventory['masters'])-set(inventory['physical_only_instances'].values()))
    require(json.dumps(functions['actual_functions'], sort_keys=True) ==
        json.dumps(proposal['actual_three_corner_functions']['actual_functions'], sort_keys=True),
        'Actual native positive/sequential functions differ from proposal')
    root = Path(__file__).resolve().parents[1]
    closure = dependency_closure(root, ['scripts/streaming_tt_apply_fanout.py'])
    files = [*inputs.values(), *(regular(value['path']) for value in corners.values()), *(root/name for name in closure['files'])]
    before_hashes = {str(path): sha(path) for path in files}
    from openroad import Tech, Design
    import odb
    tech = Tech()
    typ = [row['path'] for row in corners.values() if row['sha256'] ==
        '34163f3e7de9f854afac57332ba06f1739b78e7ac35660a8a5ddd39c570124ad']
    require(len(typ) == 1, 'Missing actual nominal native Liberty')
    tech.readLiberty(typ[0]); design = Design(tech); design.readDb(str(inputs['database']))
    database = design.getDb(); block = design.getBlock()
    _, actual_before = export_block(block, reference, args.top)
    require(actual_before == inventory, 'Native actual ODB re-read differs from the proposal source inventory')
    original_geometry = geometry(block); buffers = positive_buffers(library); projected = json.loads(json.dumps(inventory))
    context = loads(projected)
    ff_before = {name for name, row in inventory['instances'].items() if row['master'] in library.cells and
        library.cells[row['master']].sequential}
    require(len(ff_before) == 6039, 'Native source is not the complete depth-two state inventory')
    for operation in plan['operations']:
        apply_operation(projected, operation, buffers, context=context); execute(odb, database, block, operation)
    _, actual_partitioned = export_block(block, reference, args.top)
    topology = verify_result(inventory, actual_partitioned, plan, library)
    partition_geometry = geometry(block)
    require(all(partition_geometry[name] == value for name, value in original_geometry.items()),
        'Native partition moved an original instance before legalization')
    args.out.mkdir(parents=True, exist_ok=False)
    journal = []
    checked_tcl(design, 'write_db {'+str(args.out/'partitioned-before-legalization.odb')+'}', journal)
    checked_tcl(design, 'set_thread_count 1', journal)
    checked_tcl(design, 'detailed_placement -max_displacement {500 100}', journal)
    checked_tcl(design, 'check_placement -verbose', journal)
    _, actual_legal = export_block(block, reference, args.top)
    verify_result(inventory, actual_legal, plan, library)
    target = args.out/'implemented.odb'
    checked_tcl(design, 'write_db {'+str(target)+'}', journal)
    checked_tcl(design, 'write_def {'+str(args.out/'implemented.def')+'}', journal)
    checked_tcl(design, 'write_verilog {'+str(args.out/'implemented.v')+'}', journal)
    reread = odb.dbDatabase.create(); odb.read_db(reread, str(target))
    document, actual_written = export_block(reread.getChip().getBlock(), reference, args.top)
    verify_result(inventory, actual_written, plan, library)
    after_geometry = geometry(reread.getChip().getBlock())
    moved = {name: dict(before=value, after=after_geometry[name]) for name, value in original_geometry.items()
        if after_geometry[name] != value}
    require(before_hashes == {str(path): sha(path) for path in files}, 'Native partition source changed before closeout')
    write(args.out/'inventory.json', actual_written); write(args.out/'connectivity.json', document)
    write(args.out/'original-placement-changes.json', moved)
    artifacts = {str(path.relative_to(args.out)): sha(path) for path in sorted(args.out.iterdir()) if path.is_file()}
    write(args.out/'report.json', dict(schema='pinwheel.streaming-tt-native-fanout-partition.v1', passed=True, completed=True,
        qualified=False, physical_acceptance_claim=False, source_odb_sha256=sha(inputs['database']),
        source_commit=proposal['source_commit'], plan_sha256=sha(inputs['plan']), input_sha256=before_hashes,
        inputs_unchanged=True, producer_dependency_closure=closure, exact_source_inventory_re_read=True,
        exact_topology_checked=True, placement_passed=True,
        native_tcl_commands=journal, native_tcl_all_success=all(row['tcl_catch_status'] == '0' for row in journal),
        topology=topology, original_ff_bits=6039, original_instances_moved_during_legalization=len(moved),
        native_detailed_placement_executed=True, native_check_placement_executed=True,
        actual_odb_roundtrip_checked=True, inherited_netlist=False, artifacts_sha256=artifacts,
        rerouting_required=True, clock_and_data_kernel_correspondence_required=True, fresh_all_corner_STA_required=True,
        boundary='Actual positive-buffer topology and native legal-placement derivative only. Original input ODB is unchanged. '
            'All routed views are stale; independent whole-chip routing, actual clock/data kernel proof, '
            'setup/hold/electrical, DRC/LVS/antenna/power and official TT precheck remain required.'))


if __name__ == '__main__': main()
