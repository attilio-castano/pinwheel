#!/usr/bin/env python3
"""Compare organization choices against a hash-bound saved-chip diagnosis.

No CAD, source circuit edits or physical admission. The existing planner owns
virtual consumer exchanges; the study adds timing obligations and the cost of
local combinational copies, including their upstream loads.
"""
import argparse
from collections import Counter
from copy import deepcopy
from datetime import datetime, timezone
from fnmatch import fnmatch
import json
from pathlib import Path
import re
import time

from physical_connections import connection_terminals, parse_measurements
from physical_organization import Library, Planner, mechanism_screen, screen_exchange_identity
from physical_organization_study import timing_budget, replication_cost
from validation_run import fresh_directory, sha


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--study', type=Path, required=True)
    ap.add_argument('--check-tag', required=True)
    args = ap.parse_args()
    root, started, inputs = Path.cwd(), time.monotonic(), {}
    out = fresh_directory(root / 'build/validation', args.check_tag)

    def text(path, expected=None):
        path = root / path
        digest = sha(path)
        if expected is not None and digest != expected:
            raise ValueError('Changed input: ' + str(path))
        inputs[str(path)] = digest
        return path.read_text()

    def read(path, expected=None):
        return json.loads(text(path, expected))

    def reference(ref):
        return read(ref['path'], ref['sha256'])

    def artifact(report, directory, name):
        return read(directory / name, report['artifacts_sha256'][name])

    def write(name, value):
        with (out / name).open('x') as output:
            output.write(json.dumps(value, indent=2, allow_nan=False) + '\n')

    study = read(args.study)
    if study['schema'] != 1 or study['added_pipeline_cycles'] != 0:
        raise ValueError('Study must preserve the edge contract')
    if not study['replicated_decoders'] or len(set(study['replicated_decoders'])) != len(study['replicated_decoders']):
        raise ValueError('Require distinct decoder proposals')
    for ref in study['semantic_sources']:
        text(ref['path'], ref['sha256'])
    manifest = reference(study['source_diagnosis'])
    source_path = Path(manifest['report'])
    source = read(source_path, manifest['report_sha256'])
    if (source['status'] != 'passed' or not source['evidence_collection_passed'] or
            source['new_physical_qualification'] or set(source['containers'].values()) != {'absent'}):
        raise ValueError('Require a settled diagnostic, not an assumed qualified chip')
    for name, digest in source['artifacts_sha256'].items():
        # Verify binary artifacts without interpreting them as UTF-8.
        path = root / source_path.parent / name
        if sha(path) != digest:
            raise ValueError('Changed diagnostic artifact: ' + str(path))
        inputs[str(path)] = digest
    analysis = reference(source['evidence']['analysis.json'])
    for name, digest in analysis['inputs_sha256'].items():
        path = root / name
        if sha(path) != digest:
            raise ValueError('Changed matched-path input: ' + str(path))
        inputs[str(path)] = digest
    families = reference(source['evidence']['families.json'])
    request = reference(source['evidence']['request.json'])
    geometry = reference(source['evidence']['geometry.json'])['after']
    saved = reference(source['evidence']['measurements.json'])
    watch = reference(source['measured_watchlist'])
    contract = reference(watch['original_budget_contract'])
    if set(study['path_roles']) != set(request['paths']):
        raise ValueError('Incomplete semantic path classification')
    if not (set(saved['after']) == set(saved['before']) == set(analysis['matched_paths']) ==
            set(contract['timing_floors_ns'])):
        raise ValueError('Missing timing corner')

    route_manifest = reference(source['candidate_full_route'])
    route_path = Path(route_manifest['report'])
    route = read(route_path, route_manifest['report_sha256'])
    invocation = reference(route['invocation'])
    design = Path('build/physical') / invocation['design']
    tag = request['checkpoints']['after']['tag']
    context_path = Path('build/physical/mapped-diagnostics') / tag / 'context.json'
    context = read(context_path, analysis['inputs_sha256'][str(context_path)])
    if context['database_sha256'] != watch['source_database_sha256']:
        raise ValueError('Watchlist belongs to a different chip')
    for label, entry in request['checkpoints'].items():
        database = root / design / entry['database'].removeprefix('/work/core/')
        if sha(database) != entry['sha256'] or entry['sha256'] != source['source_databases'][label]:
            raise ValueError('Changed source physical database')
        inputs[str(database)] = entry['sha256']
    parent = reference(watch['parent_inventory'])
    complete = parent['connections'] + watch['additional_connections']
    if (parent['source_database_sha256'] != context['database_sha256'] or
            len({r['net'] for r in complete}) != len(complete) or
            len(complete) != watch['proposed_total_connections']):
        raise ValueError('Incomplete or overlapping inherited coverage')
    for row in complete:
        if connection_terminals(context, row['net']) != {k: row[k] for k in ('driver', 'consumers', 'ports')}:
            raise ValueError('Inherited coverage changed endpoints')
    rows = {r['net']: r for r in families['connections']}
    for label in ('before', 'after'):
        for corner, data in saved[label].items():
            path = source_path.parent / 'measurements' / label / corner / 'connections.rpt'
            if parse_measurements(text(path, analysis['inputs_sha256'][str(path)]), set(rows)) != data:
                raise ValueError('Measurement differs from raw connection report')
    coverage = dict(source_database_sha256=context['database_sha256'], connections=list(rows.values()),
                    components=[dict(root=f['root'], nets=f['nets'], families=[seed])
                                for seed, f in families['families'].items()])
    for component in coverage['components']:
        for net in component['nets']:
            rows[net]['distribution_root'] = component['root']

    resolved = read(design / 'runs' / tag / 'resolved.json', request['checkpoints']['after']['config_sha256'])
    sdc = design / 'experiments' / tag / 'core.sdc'
    text(sdc, invocation['snapshot_files_sha256']['core.sdc'])
    current_sdc = next(ref for ref in study['semantic_sources'] if ref['path'] == 'physical/chip.sdc')
    if sha(sdc) != current_sdc['sha256']:
        raise ValueError('Current timing assumptions differ from the measured chip')
    pdk = Path(invocation['pdk_root'])
    installed = read(pdk / 'installed.json', invocation['pdk_receipt_sha256'])
    library_texts = {}
    for corner in saved['after']:
        names = [p for p in resolved['CELL_LIBS'][corner] if '/sg13cmos5l_stdcell/' in p]
        if len(names) != 1:
            raise ValueError('Require one standard-cell library per corner')
        for macro in resolved['MACROS'].values():
            matches = [p for pattern, paths in macro['lib'].items() if fnmatch(corner, pattern) for p in paths]
            if len(matches) != 1:
                raise ValueError('Missing or ambiguous macro timing library')
            names.extend(matches)
        library_texts[corner] = []
        for name in names:
            if name.startswith('/work/pdk/'):
                relative = name.removeprefix('/work/pdk/')
                path, digest = pdk / relative, installed['files_sha256'][relative]
            elif name.startswith('/work/core/'):
                path = design / name.removeprefix('/work/core/')
                relative = str(path.relative_to(design / 'experiments' / tag))
                digest = invocation['snapshot_files_sha256'][relative]
            else:
                raise ValueError('Unbound library location')
            library_texts[corner].append(text(path, digest))
    library = Library(library_texts)
    policy = reference(study['exchange_policy'])
    policy = deepcopy(policy)
    policy['source_database_sha256'] = context['database_sha256']
    policy['contract_sha256'] = watch['original_budget_contract']['sha256']
    planner = Planner(context, coverage, geometry, saved['after'], library, policy, contract)
    pins_checked = planner.reconcile_pins(set(rows))
    if abs(planner.current_area - route['area']['candidate_um2']) > 1e-4:
        raise ValueError('Area reconstruction differs from the saved chip')
    reference_netlist = artifact(route, route_path.parent, 'functional/after.json')['modules']['tt_um_pinwheel']

    timing = {}
    for corner, comparisons in analysis['matched_paths'].items():
        if set(comparisons) != set(request['paths']):
            raise ValueError('Missing matched timing path')
        timing[corner] = {}
        for name, comparison in comparisons.items():
            spec = request['paths'][name]
            kind = 'setup' if spec['delay'] == 'max' else 'hold'
            timing[corner][name] = timing_budget(comparison, spec, contract['timing_floors_ns'][corner][kind])

    budget_rows, exchanges, connections = [], [], []
    for seed, family in families['families'].items():
        tree = next(t for t in planner.model['trees'] if t['root'] == family['root'])
        measured = analysis['families'][seed]
        counts, targets = {}, []
        for label in ('before', 'after'):
            verdicts = []
            for net in tree['nets']:
                corner_budgets = {}
                for corner, all_nets in saved[label].items():
                    values = all_nets[net]
                    reserve = min((values[k]['limit'] - values[k]['actual']) / values[k]['limit']
                                  for k in ('capacitance', 'slew'))
                    wire_budget = (1-contract['reserve_fraction']) * values['capacitance']['limit'] - values['pin_cap_pf'][1]
                    corner_budgets[corner] = dict(minimum_electrical_reserve=reserve,
                        saved_wire_capacitance_pf=values['wire_cap_pf'][1],
                        wire_capacitance_budget_pf=wire_budget,
                        required_wire_reduction_pf=max(0, values['wire_cap_pf'][1]-wire_budget))
                minimum = min(c['minimum_electrical_reserve'] for c in corner_budgets.values())
                verdict = 'failing' if minimum < 0 else 'below_reserve' if minimum < contract['reserve_fraction'] else 'within_reserve'
                verdicts.append(verdict)
                if label == 'after':
                    connections.append(dict(family=seed, net=net, verdict=verdict, corners=corner_budgets))
                    if verdict != 'within_reserve': targets.append(net)
            counts[label] = dict(Counter(verdicts))
        if counts != measured['counts']:
            raise ValueError('Recomputed family margins disagree with the diagnosis')
        candidate = planner.exchange(family['root'], targets, objective='worst_wire_pressure')
        candidate['family_seed'] = seed
        candidate['mechanism_screen'] = mechanism_screen(candidate, saved['after'], contract['reserve_fraction'])
        if candidate['edits']:
            candidate['virtual_identity'] = screen_exchange_identity(reference_netlist, candidate['edits'])
        exchanges.append(candidate)
        budget_rows.append(dict(seed=seed, root=family['root'], driver=family['root_driver'],
                                source_owners=rows[family['root']]['source_owners'],
                                connections=len(tree['nets']), terminal_consumers=len(tree['leaves']),
                                buffers=len(tree['buffer_instances']), protected_delays=len(tree['delay_instances']),
                                transport_area_um2=tree['transport_area_um2'], counts=counts,
                                targets=targets, congested_edges=measured['native_edges_crossed'],
                                native_edge_crossings=measured['native_edge_crossings']))

    # Parent nets can have evidence outside the 118-connection diagnostic slice.
    # Reuse the full saved collection before declaring a measurement missing.
    full_measurements = reference(route['evidence']['measurements.json'])
    parent_names = {net for net, record in context['nets'].items()
                    if any(t['instance'] in study['replicated_decoders'] and t['direction'] == 'INPUT'
                           for t in record['terminals'])} & {r['net'] for r in parent['connections']}
    collection_ref = route['evidence']['connections/collection.json']
    collection = reference(collection_ref)
    if collection['status'] != 'passed' or not collection['source_unchanged'] or set(collection['containers'].values()) != {'absent'}:
        raise ValueError('Require settled parent-net measurements')
    if set(full_measurements) != set(planner.corners):
        raise ValueError('Incomplete parent measurement corners')
    for corner in planner.corners:
        relative = 'after/' + corner + '/connections.rpt'
        raw = text(Path(collection_ref['path']).parent / relative, collection['artifacts_sha256'][relative])
        parts = re.split(r'^PINWHEEL_CONNECTION (\S+)\n', raw, flags=re.M)
        selected = ''.join('PINWHEEL_CONNECTION '+name+'\n'+body
                           for name, body in zip(parts[1::2], parts[2::2]) if name in parent_names)
        if parse_measurements(selected, parent_names) != {n: full_measurements[corner][n] for n in parent_names}:
            raise ValueError('Parent measurement differs from raw report')

    replications = []
    for instance in study['replicated_decoders']:
        cost = replication_cost(context, library, instance, planner.corners)
        if cost['output_net'] not in {f['root'] for f in families['families'].values()}:
            raise ValueError('Replication must name a diagnosed family root')
        row = rows[cost['output_net']]
        # A two-region proposal at the widest geometric separation. The original
        # driver retains the nearer group. The other centroid is guidance only.
        points = planner.model['points_um']
        if len(row['consumers']) < 2 or row['ports']:
            raise ValueError('Require at least two internal consumers for regional replication')
        axis = max((0, 1), key=lambda k: max(points[p][k] for p in row['consumers']) - min(points[p][k] for p in row['consumers']))
        ordered = sorted(row['consumers'], key=lambda p: (points[p][axis], p))
        groups = [ordered[:len(ordered)//2], ordered[len(ordered)//2:]]
        centers = [[sum(points[p][k] for p in group)/len(group) for k in (0, 1)] for group in groups]
        origin = points[row['driver']]
        keep = min(range(2), key=lambda i: sum(abs(centers[i][k]-origin[k]) for k in (0, 1)))
        cost['parent_capacitance_screen'] = {}
        for corner in planner.corners:
            cost['parent_capacitance_screen'][corner] = {}
            for net, increment in cost['extra_upstream_pin_capacitance_pf'][corner].items():
                measured = full_measurements[corner].get(net)
                if net not in parent_names:
                    cost['parent_capacitance_screen'][corner][net] = None
                    continue
                available = (1-contract['reserve_fraction']) * measured['capacitance']['limit']
                upper = measured['total_cap_pf'][1] + increment
                cost['parent_capacitance_screen'][corner][net] = dict(
                    saved_total_plus_extra_pin_upper_pf=upper,
                    extra_wire_budget_pf=available-upper,
                    passes_with_saved_wire=upper <= available,
                    new_slew_and_timing_qualified=False)
        cost.update(retained_consumers=groups[keep], replicated_consumers=groups[1-keep],
                    suggested_region_center_um=centers[1-keep],
                    preserves_all_existing_cells=True,
                    fits_remaining_increment_budget=cost['extra_cell_area_um2'] <= planner.area_limit - planner.current_area,
                    upstream_electrical_measurements_complete=all(n['net'] in parent_names for n in cost['inputs']))
        replications.append(cost)

    affected = [c for c in exchanges if c['targets']]
    all_exchange_pass = bool(affected) and all(c['mechanism_screen']['pass_conditional_screen'] for c in affected)
    all_edits = [edit for candidate in affected for edit in candidate['edits']]
    portfolio_identity = screen_exchange_identity(reference_netlist, all_edits) if all_edits else None
    write('timing-budgets.json', timing)
    write('family-budgets.json', budget_rows)
    write('connection-budgets.json', connections)
    write('regional-exchanges.json', exchanges)
    write('local-decoding.json', replications)
    write('effective-screen-policy.json', policy)
    report = dict(schema=1, status='passed', recorded_at_utc=datetime.now(timezone.utc).isoformat(),
                  study=dict(path=str(args.study), sha256=sha(args.study)),
                  source_diagnosis=study['source_diagnosis'], source_database_sha256=context['database_sha256'],
                  path_roles=study['path_roles'], timing_budgets=timing, family_budgets=budget_rows,
                  timing_assumptions=dict(clock_period_ns=resolved['CLOCK_PERIOD'],
                      sdc=dict(path=str(sdc), sha256=sha(sdc)), current_sdc_matches=True),
                  inherited_coverage_connections=len(complete), independent_pin_corner_checks=pins_checked,
                  area=dict(reference_um2=contract['area_reference']['area_um2'], current_um2=planner.current_area,
                            limit_um2=planner.area_limit, remaining_um2=planner.area_limit-planner.current_area),
                  regional_exchange=dict(affected_families=len(affected),
                      swaps=sum(len(c['swaps']) for c in affected),
                      changed_branches=sum(len(c['edits']) for c in affected),
                      combined_virtual_identity=portfolio_identity,
                      all_targets_pass_conditional_screen=all_exchange_pass),
                  local_decoding=replications,
                  congestion={k: source['congestion'][k] for k in ('overflow', 'marker_count', 'family_edge_count',
                              'clock_edge_count', 'ndr_edge_count', 'all_edges_have_other_signal_traffic')},
                  decision=('The exchange portfolio passes its conditional wire screen; physical and timing qualification remain open.'
                            if all_exchange_pass else
                            'The bounded exchange portfolio has no complete conditional pass; retain local decoding for a separate structural comparison with upstream measurements.'),
                  physical_qualification=False, whole_chip_route_admitted=False, executed_cad_commands=0,
                  added_pipeline_cycles=0, production_admission_changed=False,
                  boundary=['One-sided matched-path clock bounds do not constitute a feasible clock tree or complete timing proof.',
                            'Exchanges retain existing cells and per-corner pin loads; span scaling is a conditional heuristic.',
                            'Decoder replication costs include extra gate area and parent pin load, but unknown wires and placement.',
                            'Regional guidance is not a physical edit. No candidate is promoted on geometry or local budgets alone.',
                            'The fast corner retains the historical standard-cell -40 C / SRAM -55 C mismatch.'],
                  seconds=round(time.monotonic()-started, 3), inputs_sha256=inputs,
                  source_sha256={str(p): sha(p) for p in [Path(__file__).resolve().relative_to(root),
                      *[Path('scripts') / n for n in ['physical_organization_study.py', 'physical_organization.py',
                        'physical_connections.py', 'physical_distribution.py', 'physical_buffer_repair.py',
                        'physical_repair_plan.py', 'physical_floorplan.py', 'tiled_chip.py', 'validation_run.py']]]})
    # A consumed artifact changing during this read-only run invalidates the study.
    if any(sha(path) != digest for path, digest in inputs.items()):
        raise ValueError('An input changed during the study')
    report['artifacts_sha256'] = {p.name: sha(p) for p in out.iterdir() if p.is_file()}
    write('report.json', report)
    print(json.dumps({k: report[k] for k in ('status', 'seconds', 'area', 'regional_exchange', 'executed_cad_commands')}))


if __name__ == '__main__':
    main()
