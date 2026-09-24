"""Admit the selected local repair to one coarse route with unchanged placement.

This consumes hash-bound repair and functional receipts, not an arbitrary ODB.
It deliberately admits only GlobalRouting, without CTS or repair stages.
"""
from decimal import Decimal
import json
import math
from pathlib import Path
import re

from physical_checkpoint import artifact_path
from validation_run import sha


def ihp_layer_rc(tech_lef):
    """Explicit nominal LEF defaults in the pinned IHP library's kohm/pF/um.

    R/length = sheet resistance / width; C/length = area C * width + 2*edge C.
    Fresh OpenROAD diagnostics independently compare these with dblayer_wire_rc.
    This reader is scoped to the selected IHP technology, not general LEF syntax.
    """
    layers = {}
    for name, body in re.findall(r'^LAYER (\w+)\s*\n(.*?)^END \1\s*$',
                                 Path(tech_lef).read_text(), re.M | re.S):
        if not re.search(r'^\s*TYPE\s+ROUTING\s*;', body, re.M):
            continue

        def number(key):
            match = re.search(r'^\s*' + key + r'\s+([\d.Ee+-]+)\s*;', body, re.M)
            if not match:
                raise ValueError('Missing nominal LEF value: ' + name + '/' + key)
            value = Decimal(match[1])
            if value <= 0:
                raise ValueError('Nonpositive nominal LEF RC')
            return value

        width = number('WIDTH')
        layers[name] = dict(res=float(number('RESISTANCE RPERSQ') / width / 1000),
                           cap=float(number('CAPACITANCE  *CPERSQDIST') * width +
                                     2 * number('EDGECAPACITANCE')))
    if set(layers) != {'Metal1', 'Metal2', 'Metal3', 'Metal4', 'TopMetal1'}:
        raise ValueError('Unexpected IHP routing layer set')
    return {'nom_*': layers}


def validate_repair_route(selection_path, state_path, design, from_step, stop_step,
                          overrides, timeout_seconds, pdk_root, root):
    root, design, pdk_root = map(lambda p: Path(p).resolve(), (root, design, pdk_root))
    if (from_step != 'OpenROAD.GlobalRouting' or stop_step != from_step or
            type(timeout_seconds) is not int or not 0 < timeout_seconds <= 600):
        raise ValueError('Local repair permits only one bounded GlobalRouting step')
    if not state_path:
        raise ValueError('Local repair requires its frozen ODB state')

    def checked(path, digest):
        path = (root / path).resolve()
        if not path.is_relative_to(root) or sha(path) != digest:
            raise ValueError('Changed selected repair evidence: ' + str(path))
        return path

    selection_path = Path(selection_path).resolve()
    selection = json.loads(selection_path.read_text())
    if selection.get('schema') in (4, 5):
        from physical_added_route import validate_added_buffer_route
        return validate_added_buffer_route(selection_path, selection, state_path, design,
                                           overrides, pdk_root, root, checked)
    if selection.get('schema') == 3:
        return validate_target_repair_route(selection_path, selection, state_path, design,
                                            overrides, pdk_root, root, checked)
    if selection.get('schema') == 2:
        return validate_buffer_route(selection_path, selection, state_path, design,
                                     overrides, pdk_root, root, checked)
    decision = 'local-repair-validated-coarse-routing-still-required'
    if selection.get('schema') != 1 or selection.get('status') != 'passed' or selection.get('decision') != decision:
        raise ValueError('Require the validated local repair selection')
    report_path = checked(selection['report'], selection['report_sha256'])
    report = json.loads(report_path.read_text())
    if (report.get('status') != 'passed' or report.get('decision') != decision or
            not report.get('original_geometry_unchanged') or not report.get('corridor_clear') or
            not report.get('connectivity', {}).get('buffer_contracted_connectivity') or
            report.get('receipts') != selection['receipts']):
        raise ValueError('Incomplete selected repair validation')

    evidence = {}

    def receipt(role):
        entry = selection['receipts'][role]
        path = checked(entry['report'], entry['sha256'])
        data = json.loads(path.read_text())
        if data.get('status') != 'passed':
            raise ValueError('Unsuccessful selected repair receipt: ' + role)
        evidence[role] = dict(path=str(path.relative_to(root)), sha256=sha(path))
        return path, data

    repair_path, repair = receipt('targeted-03')
    measure_path, measure = receipt('local-measure-03')
    oracle_path, oracle = receipt('oracle')
    odb = checked(repair_path.parent / 'repaired.odb', repair['artifacts_sha256']['repaired.odb'])
    netlist = checked(measure_path.parent / 'implemented.v', measure['artifacts_sha256']['implemented.v'])
    if (measure['inputs_sha256'].get(str(odb)) != sha(odb) or
            not measure.get('original_geometry_unchanged') or not measure.get('corridor_clear') or
            oracle.get('edges') != 508252 or oracle.get('mutants_rejected') != 1 or
            not any(Path(p).name == 'implemented.v' and h == sha(netlist)
                    for p, h in oracle['inputs_sha256'].items())):
        raise ValueError('Repaired ODB/export/oracle identity is not linked')

    state = json.loads(Path(state_path).read_text())
    if set(state) != {'odb', 'metrics'} or state['metrics'] != {}:
        raise ValueError('Repaired route must carry only ODB and empty metrics')
    if sha(artifact_path(state['odb'], design)) != sha(odb):
        raise ValueError('Staged ODB differs from the validated repair')

    source = selection['source_selection']
    prior_selection = json.loads(checked(source['path'], source['sha256']).read_text())
    prior_entry = prior_selection['receipts']['physical']
    prior_report = json.loads(checked(prior_entry['report'], prior_entry['report_sha256']).read_text())
    invocation_path = checked('build/physical/' + prior_report['tag'] + '-invocation.json',
                              prior_report['invocation_sha256'])
    prior_invocation = json.loads(invocation_path.read_text())
    if (prior_invocation['design'] != design.name or
            prior_invocation['inputs_sha256'] != sha(design / 'inputs.json') or
            prior_invocation['base_config_sha256'] != sha(design / 'core.json') or
            prior_invocation['pdk_receipt_sha256'] != sha(pdk_root / 'installed.json')):
        raise ValueError('Repair continuation differs from the verified design or PDK')
    resolved = design / 'runs' / prior_report['tag'] / 'resolved.json'
    if measure['inputs_sha256'].get(str(resolved)) != sha(resolved):
        raise ValueError('Repair uses a different source configuration')
    config = json.loads(resolved.read_text())
    if config.get('LAYERS_RC') or config.get('VIAS_R'):
        raise ValueError('Do not replace custom RC with nominal LEF defaults')
    tech_lef = pdk_root / 'ihp-sg13cmos5l/libs.ref/sg13cmos5l_stdcell/lef/sg13cmos5l_tech.lef'
    expected = dict(prior_invocation['overrides'], RUN_POST_GRT_DESIGN_REPAIR=False,
                    RUN_POST_GRT_RESIZER_TIMING=False, RUN_ANTENNA_REPAIR=False,
                    LAYERS_RC=ihp_layer_rc(tech_lef))
    if overrides != expected:
        raise ValueError('Repair routing controls differ beyond explicit nominal layer RC')
    return dict(selection=str(selection_path.relative_to(root)), selection_sha256=sha(selection_path),
                report=str(report_path.relative_to(root)), report_sha256=sha(report_path),
                evidence=evidence, candidate_database=str(odb.relative_to(root)),
                candidate_database_sha256=sha(odb), netlist_sha256=sha(netlist),
                control_invocation=str(invocation_path.relative_to(root)),
                control_invocation_sha256=sha(invocation_path),
                nominal_tech_lef=str(tech_lef), nominal_tech_lef_sha256=sha(tech_lef),
                scope='One coarse route, frozen cells and placement, explicit nominal layer RC; no CTS or repair')


def validate_buffer_route(selection_path, selection, state_path, design, overrides, pdk_root, root, checked):
    """Admit a functionally checked buffer edit for diagnostic routing only.

    Placement annotation failures are an explicit reason to request fresh wire
    estimates, never evidence of timing closure. The same one-step/time bounds
    are enforced by validate_repair_route before dispatching here.
    """
    if (selection.get('status') != 'passed' or
            selection.get('decision') != 'admit-one-diagnostic-coarse-route' or
            selection.get('timing_admission') != 'requires-fresh-complete-wire-estimates'):
        raise ValueError('Require an explicit diagnostic buffer-route selection')
    evidence = {}

    def receipt(role):
        entry = selection['receipts'][role]
        path = checked(entry['path'], entry['sha256'])
        evidence[role] = dict(path=str(path.relative_to(root)), sha256=sha(path))
        return path, json.loads(path.read_text())

    probe_path, probe = receipt('probe')
    measure_path, measure = receipt('measurement')
    _, oracle = receipt('oracle')
    inv_path, inv = receipt('control_invocation')
    _, physical = receipt('control_physical')
    if (any(r.get('status') != 'passed' for r in [probe, measure, oracle]) or
            not measure.get('original_geometry_unchanged') or not measure.get('corridor_clear') or
            not measure.get('clock_nets_unchanged') or not measure.get('nontarget_signal_nets_unchanged') or
            not measure.get('connectivity', {}).get('buffer_contracted_connectivity')):
        raise ValueError('Require completed buffer, clock and geometry validation')
    odb = checked(probe_path.parent / 'repaired.odb', probe['artifacts_sha256']['repaired.odb'])
    netlist = checked(measure_path.parent / 'implemented.v', measure['artifacts_sha256']['implemented.v'])
    if (measure['inputs_sha256'].get(str(odb)) != sha(odb) or
            oracle.get('edges') != 508252 or oracle.get('mutants_rejected') != 1 or
            oracle['inputs_sha256'].get(str(netlist)) != sha(netlist) or
            oracle['inputs_sha256'].get(str(measure_path)) != sha(measure_path)):
        raise ValueError('Unlinked buffer database, export or independent oracle')
    for name, digest in measure['artifacts_sha256'].items():
        checked(measure_path.parent / name, digest)
    if (physical['invocation_sha256'] != sha(inv_path) or inv.get('exit_code') != 0 or
            physical['artifact_sha256'].get(probe['source_database']) != probe['source_database_sha256']):
        raise ValueError('Changed source of the local repair')
    checked(probe['source_database'], probe['source_database_sha256'])
    if (inv['design'] != design.name or inv['inputs_sha256'] != sha(design / 'inputs.json') or
            inv['base_config_sha256'] != sha(design / 'core.json') or
            inv['pdk_receipt_sha256'] != sha(pdk_root / 'installed.json')):
        raise ValueError('Buffer continuation differs from its source design or PDK')
    state = json.loads(Path(state_path).read_text())
    if set(state) != {'odb', 'metrics'} or state['metrics'] != {}:
        raise ValueError('Buffer route must carry only ODB and empty metrics')
    if sha(artifact_path(state['odb'], design)) != sha(odb):
        raise ValueError('Staged ODB differs from the validated buffer edit')
    tech = pdk_root / 'ihp-sg13cmos5l/libs.ref/sg13cmos5l_stdcell/lef/sg13cmos5l_tech.lef'
    if (overrides != inv['overrides'] or overrides.get('LAYERS_RC') != ihp_layer_rc(tech) or
            any(overrides.get(k) is not False for k in
                ['RUN_POST_GRT_DESIGN_REPAIR', 'RUN_POST_GRT_RESIZER_TIMING', 'RUN_ANTENNA_REPAIR'])):
        raise ValueError('Diagnostic route must preserve explicit RC and disable all repair')
    return dict(selection=str(selection_path.relative_to(root)), selection_sha256=sha(selection_path),
                evidence=evidence, candidate_database=str(odb.relative_to(root)),
                candidate_database_sha256=sha(odb), netlist_sha256=sha(netlist),
                control_invocation=str(inv_path.relative_to(root)), control_invocation_sha256=sha(inv_path),
                nominal_tech_lef=str(tech), nominal_tech_lef_sha256=sha(tech),
                timing_admission=selection['timing_admission'],
                scope='One diagnostic coarse route of a verified buffer edit; placement timing unqualified; no CTS or repair')


def validate_target_repair_route(selection_path, selection, state_path, design,
                                 overrides, pdk_root, root, checked):
    """Carry a target's measured buffer resize and prior pin evidence into routing.

    The closure receipt links independently collected artifacts. Recheck their
    identities, connectivity, geometry and measurement qualification here; the
    caller enforces the one-step and 600-second bounds. Old experiment helpers
    may evolve, but their receipts and executed artifacts are never rewritten.
    """
    from physical_buffer_repair import compare_buffer_repair

    if (selection.get('status') != 'passed' or
            selection.get('decision') != 'admit-one-validated-repair-coarse-route'):
        raise ValueError('Require an explicit validated target-repair selection')
    evidence = {}

    def receipt(role, ref):
        path = checked(ref['path'], ref['sha256'])
        data = json.loads(path.read_text())
        evidence[role] = dict(path=str(path.relative_to(root)), sha256=sha(path))
        return path, data

    report_path, report = receipt('validation', selection['validation'])
    if report.get('status') != 'passed':
        raise ValueError('Unsuccessful target repair validation')
    for name, digest in report['artifact_sha256'].items():
        checked(report_path.parent / name, digest)
    probe_path, probe = receipt('probe', report['probe_receipts'][selection['probe']])
    measure_path, measure = receipt('measurement', report['measurement_receipts'][selection['measurement']])
    control_path, control = receipt('reference_measurement',
                                   report['measurement_receipts'][selection['reference_measurement']])
    _, oracle = receipt('oracle', report['functional']['report'])
    parent_path, parent = receipt('parent_state', report['selected_parent_state'])
    _, physical = receipt('parent_physical', report['selected_parent_physical_report'])
    inv_path, inv = receipt('parent_invocation', dict(
        path='build/physical/' + physical['tag'] + '-invocation.json', sha256=physical['invocation_sha256']))
    for path, data in [(probe_path, probe), (measure_path, measure), (control_path, control)]:
        if (data.get('status') != 'passed' or not data.get('containers') or
                set(data['containers'].values()) - {'absent', 'stopped'}):
            raise ValueError('Unsettled or unsuccessful target repair producer')
        for name, digest in data['artifacts_sha256'].items():
            checked(path.parent / name, digest)
    odb = checked(report['selected_database']['path'], report['selected_database']['sha256'])
    netlist = checked(report['selected_netlist']['path'], report['selected_netlist']['sha256'])
    source = artifact_path(parent['odb'], design)
    if (physical['state_sha256'] != sha(parent_path) or inv.get('exit_code') != 0 or
            physical['artifact_sha256'].get(str(source.relative_to(root))) != sha(source) or
            probe.get('physical_tag') != physical['tag'] or not probe.get('source_unchanged') or
            probe.get('source_database') != str(source.relative_to(root)) or
            probe.get('source_database_sha256') != sha(source) or
            probe['artifacts_sha256'].get('repaired.odb') != sha(odb) or
            measure.get('source_database') != str(odb.relative_to(root)) or
            measure.get('source_database_sha256') != sha(odb) or
            measure.get('netlist') != str(netlist.relative_to(root)) or
            measure.get('netlist_sha256') != sha(netlist) or
            measure.get('repair_probe', {}).get('sha256') != sha(probe_path) or
            control.get('source_database_sha256') != sha(source)):
        raise ValueError('Unlinked target repair, parent database or measured export')
    resolved = design / 'runs' / physical['tag'] / 'resolved.json'
    if (inv['design'] != design.name or inv['inputs_sha256'] != sha(design / 'inputs.json') or
            inv['base_config_sha256'] != sha(design / 'core.json') or
            inv['pdk_receipt_sha256'] != sha(pdk_root / 'installed.json') or
            measure['inputs_sha256'].get(str(resolved.relative_to(root))) != sha(resolved)):
        raise ValueError('Target repair continuation differs from its design, configuration or PDK')
    config = json.loads(resolved.read_text())
    corners = set(config['STA_CORNERS'])
    if (not corners or set(measure['fresh_timing']) != corners or
            set(measure['measurement_quality']) != corners or
            set(measure['estimation_modes'].values()) != {'placement'} or
            not measure.get('corridor_clear') or
            measure.get('target', {}).get('database_sha256') != sha(odb)):
        raise ValueError('Incomplete target or placement measurement')
    for corner in corners:
        timing = measure['fresh_timing'][corner]
        annotation = measure['measurement_quality'][corner]['wire_annotation']
        if (any(not math.isfinite(timing[k]) or timing[k] <= 0 for k in
                ['timing__setup__ws', 'timing__hold__ws']) or
                any(timing[k] != 0 for k in ['design__max_fanout_violation__count',
                    'design__max_slew_violation__count', 'design__max_cap_violation__count']) or
                not annotation.get('complete_for_consumed_nets') or
                annotation['partially_unannotated'] != 0 or annotation['consumed_unannotated']):
            raise ValueError('Unqualified target repair timing, electrical limits or wire estimates')

    # Hash-bound readbacks retain the original chip oracle through buffer sizing.
    modules = []
    for role in ['before', 'after']:
        name = selection['readbacks'][role]
        path = checked(report_path.parent / name, report['artifact_sha256'][name])
        modules.append(json.loads(path.read_text())['modules'][selection['module']])
    proof = compare_buffer_repair(*modules, allow_resizing=True)
    if proof != report['connectivity'] or proof['added_instances']:
        raise ValueError('Target repair differs from its validated buffer resize')
    before, after = [json.loads(checked(path.parent / 'context.json',
                                      data['artifacts_sha256']['context.json']).read_text())
                     for path, data in [(control_path, control), (measure_path, measure)]]
    if (before['instances'].keys() != after['instances'].keys() or
            {n for n in before['instances'] if before['instances'][n] != after['instances'][n]}
            != set(proof['resized_buffers']) or any(before[k] != after[k] for k in
                ['nets', 'macro_pins', 'ports', 'rows', 'placement_blockages',
                 'power_shapes', 'routing_obstructions', 'macro_obstructions', 'die'])):
        raise ValueError('Target repair changed unrelated placement, connectivity or macro pins')
    reference_netlist = checked(control['netlist'], control['netlist_sha256'])
    if (oracle.get('status') != 'passed' or oracle.get('edges', 0) <= 0 or
            oracle.get('edges') != report['functional']['edges'] or oracle.get('mutants_rejected') != 1 or
            oracle['input_sha256'].get(str(reference_netlist)) != sha(reference_netlist)):
        raise ValueError('Target repair has no linked independent pin evidence')
    for name, digest in oracle['input_sha256'].items():
        if sha(root / name) != digest:
            raise ValueError('Changed pin oracle input: ' + name)
    state = json.loads(Path(state_path).read_text())
    if set(state) != {'odb', 'metrics'} or state['metrics'] != {}:
        raise ValueError('Target repair route must carry only ODB and empty metrics')
    if sha(artifact_path(state['odb'], design)) != sha(odb):
        raise ValueError('Staged ODB differs from the validated target repair')
    if config.get('LAYERS_RC') or config.get('VIAS_R'):
        raise ValueError('Do not replace custom RC with nominal LEF defaults')
    tech = pdk_root / 'ihp-sg13cmos5l/libs.ref/sg13cmos5l_stdcell/lef/sg13cmos5l_tech.lef'
    expected = dict(inv['overrides'], RUN_POST_GRT_DESIGN_REPAIR=False,
                    RUN_POST_GRT_RESIZER_TIMING=False, RUN_ANTENNA_REPAIR=False,
                    LAYERS_RC=ihp_layer_rc(tech))
    if overrides != expected:
        raise ValueError('Target routing must preserve controls, set nominal RC and disable all repair')
    return dict(selection=str(selection_path.relative_to(root)), selection_sha256=sha(selection_path),
                evidence=evidence, candidate_database=str(odb.relative_to(root)),
                candidate_database_sha256=sha(odb), netlist_sha256=sha(netlist),
                nominal_tech_lef=str(tech), nominal_tech_lef_sha256=sha(tech),
                resized_buffers=len(proof['resized_buffers']), pin_edges_reused=oracle['edges'],
                timing_admission='positive-placement-margins-complete-wire-estimates',
                scope='One coarse route of the exact validated target repair; frozen cells, placement and clocks; explicit nominal layer RC; no repair')
