"""Admit added noninverting buffers, including clock branches, to one coarse route.

The caller enforces the single-stage/time bound. This distinct contract retains
the original placement, independently checks functional identity, and requires
qualified coarse-wire measurements. It never admits detailed routing.
"""
import json
import math
import os
from pathlib import Path

from physical_buffer_repair import BUFFERS, compare_buffer_repair
from physical_checkpoint import artifact_path
from physical_route_intake import ihp_layer_rc
from validation_run import sha


def added_buffer_geometry(before, after, proof, module):
    """Only declared buffers may appear; original cells and physical boundaries stay fixed."""
    added = set(proof['added_instances'])
    if (not added or set(after['instances']) != set(before['instances']) | added or
            set(before['instances']) & added or
            any(after['instances'][n] != v for n, v in before['instances'].items())):
        raise ValueError('Added-buffer repair changed original placement or cell identity')
    for name in added:
        if (after['instances'][name]['cell'] not in BUFFERS or
                after['instances'][name]['cell'] != module['cells'][name]['type'] or
                after['instances'][name]['macro']):
            raise ValueError('Added instance is not the independently read-back buffer')
    fixed = ['ports', 'rows', 'placement_blockages', 'power_shapes', 'routing_obstructions',
             'macro_obstructions', 'die', 'layers', 'exclusions']
    if any(before[k] != after[k] for k in fixed):
        raise ValueError('Added-buffer repair changed fixed geometry or corridor')
    # Buffering an input changes its net name, not the macro terminal's shape.
    shapes = lambda c: [{k: v for k, v in p.items() if k != 'net'} for p in c['macro_pins']]
    if shapes(before) != shapes(after):
        raise ValueError('Added-buffer repair changed macro pin geometry')
    for net, pin, kind in [('VPWR', 'VDD', 'POWER'), ('VGND', 'VSS', 'GROUND')]:
        old, new = before['nets'][net], after['nets'][net]
        terminals = lambda n: {(t['instance'], t['pin'], t['direction']) for t in n['terminals']}
        retained = {t for t in terminals(new) if t[0] not in added}
        if (new['type'] != kind or old['type'] != kind or retained != terminals(old) or
                new['ports'] != old['ports'] or
                {t for t in terminals(new) if t[0] in added} !=
                {(n, pin, 'INOUT') for n in added}):
            raise ValueError('Added-buffer repair has changed or missing power bindings')


def validate_added_buffer_route(selection_path, selection, state_path, design,
                                overrides, pdk_root, root, checked):
    organization = selection.get('schema') == 5
    decision = ('admit-one-validated-organization-coarse-route' if organization else
                'admit-one-validated-added-buffer-coarse-route')
    if (selection.get('status') != 'passed' or selection.get('decision') != decision):
        raise ValueError('Require an explicit validated added-buffer selection')
    evidence = {}

    def checked_input(name, digest, executables=()):
        # The pinned PDK may be shared with another checkout. Only input views
        # may live there; selections, artifacts and candidates stay under root.
        declared = Path(os.path.abspath(root / name))
        path = declared.resolve()
        if not (declared.is_relative_to(root) or path.is_relative_to(pdk_root) or path in executables):
            raise ValueError('Input outside the checkout and pinned PDK: ' + str(path))
        if sha(path) != digest:
            raise ValueError('Changed functional input: ' + str(path))

    def receipt(role, entry, artifacts=False, settled=False):
        p = checked(entry['path'], entry['sha256'])
        data = json.loads(p.read_text())
        evidence[role] = dict(path=str(p.relative_to(root)), sha256=sha(p))
        if artifacts:
            for name, digest in data.get('artifacts_sha256', data.get('artifact_sha256', {})).items():
                checked(p.parent / name, digest)
        if settled and (data.get('status') != 'passed' or not data.get('containers') or
                        set(data['containers'].values()) - {'absent', 'stopped'}):
            raise ValueError('Require settled successful added-buffer evidence: ' + role)
        return p, data

    report_path, report = receipt('validation', selection['validation'], artifacts=True)
    if organization != (report.get('decision') == 'retain-locally-qualified-organization-repair-extend-shared-intake-before-whole-chip-route'):
        raise ValueError('Organization evidence requires its declared-edit admission gate')
    distribution = report.get('decision') == 'retain-qualified-local-distribution-repair-diagnose-congestion-before-route-intake'
    paths = report.get('decision') == 'retain-locally-qualified-path-repair-bind-expanded-intake-before-whole-chip-route'
    direct = organization or paths or distribution or report.get('decision') == 'retain-local-signal-repair-require-whole-chip-qualification'
    if (report.get('status') != 'passed' or not report.get('local_quantitative_contract_pass' if organization else 'local_estimated_timing_pass') or
            not (direct or report.get('decision') ==
                 'retain-local-repair-require-fresh-whole-chip-coarse-route-and-pin-access')):
        raise ValueError('Incomplete local added-buffer validation')
    if direct:
        stage = dict(producer=report['probe'],measurement=report['measurement']) if organization else {k:report[k] for k in ['producer','measurement']}
        _, identity = receipt('local_identity', report['evidence']['identity.json'] if organization else report['functional']['identity'], artifacts=True)
        if identity.get('status') != 'passed' or not (identity.get('proof',{}) if organization else identity).get('exact_plan_implemented'):
            raise ValueError('Incomplete local signal-plan identity')
        local_proof = identity['proof']
    else:
        stage = report['stages'][selection['candidate']]
        local_proof = report['functional']['buffer_identity']
    probe_path, probe = receipt('probe', stage['producer'], artifacts=True, settled=True)
    measure_path, measure = receipt('measurement', stage['measurement'], artifacts=True, settled=True)
    reference_path, reference = receipt('reference_measurement', selection['reference_measurement'],
                                        artifacts=True, settled=True)
    parent_path, parent = receipt('parent_state', selection['parent_state'])
    _, physical = receipt('parent_physical', selection['parent_physical'])
    _, inv = receipt('parent_invocation', dict(path='build/physical/' + physical['tag'] + '-invocation.json',
                                             sha256=physical['invocation_sha256']))
    odb = checked(report['selected_database']['path'], report['selected_database']['sha256'])
    netlist = checked(report['selected_netlist']['path'], report['selected_netlist']['sha256'])
    source = artifact_path(parent['odb'], design)
    if (physical['state_sha256'] != sha(parent_path) or inv.get('exit_code') != 0 or
            physical['artifact_sha256'].get(str(source.relative_to(root))) != sha(source) or
            not probe.get('source_unchanged') or probe.get('physical_tag') != physical['tag'] or
            probe.get('source_database') != str(source.relative_to(root)) or
            probe.get('source_database_sha256') != sha(source) or
            probe['artifacts_sha256'].get('repaired.odb') != sha(odb) or
            reference.get('source_database_sha256') != sha(source) or
            measure.get('source_database') != str(odb.relative_to(root)) or
            measure.get('source_database_sha256') != sha(odb) or
            measure.get('netlist') != str(netlist.relative_to(root)) or
            measure.get('netlist_sha256') != sha(netlist) or
            measure.get('repair_probe', {}).get('sha256') != sha(probe_path)):
        raise ValueError('Unlinked added-buffer candidate, export or source checkpoint')
    resolved = design / 'runs' / physical['tag'] / 'resolved.json'
    if (inv['design'] != design.name or inv['inputs_sha256'] != sha(design / 'inputs.json') or
            inv['base_config_sha256'] != sha(design / 'core.json') or
            inv['pdk_receipt_sha256'] != sha(pdk_root / 'installed.json') or
            measure['inputs_sha256'].get(str(resolved.relative_to(root))) != sha(resolved)):
        raise ValueError('Changed added-buffer design, configuration or PDK')
    config = json.loads(resolved.read_text())
    corners = set(config['STA_CORNERS'])
    if (not corners or any(set(measure[k]) != corners for k in
            ['fresh_timing', 'measurement_quality', 'estimation_modes']) or
            set(measure['estimation_modes'].values()) != {'global_routing'} or
            measure.get('nominal_layer_rc_verified') is not True or not measure.get('corridor_clear') or
            measure.get('target', {}).get('database_sha256') != sha(odb) or
            measure['target']['state_flip_flops'] != reference['target']['state_flip_flops'] or
            measure.get('target_path_expected') != reference.get('target_path_expected')):
        raise ValueError('Incomplete added-buffer coarse-wire measurement')
    for corner in corners:
        timing = measure['fresh_timing'][corner]
        annotation = measure['measurement_quality'][corner]['wire_annotation']
        if (any(not math.isfinite(timing[k]) or timing[k] <= 0 for k in
                ['timing__setup__ws', 'timing__hold__ws']) or
                any(timing[k] != 0 for k in ['timing__setup_vio__count', 'timing__hold_vio__count',
                    'design__max_fanout_violation__count', 'design__max_slew_violation__count',
                    'design__max_cap_violation__count']) or
                not annotation.get('complete_for_consumed_nets') or annotation['partially_unannotated'] != 0 or
                annotation['consumed_unannotated']):
            raise ValueError('Unqualified added-buffer timing, electrical limits or wire estimates')

    _, functional = receipt('functional_readback', selection['functional'], artifacts=True)
    _, oracle = receipt('oracle', functional['oracle'])
    exports, modules = {}, []
    for role in ['before', 'after']:
        entry = functional['exports'][role]
        exports[role] = checked(entry['path'], entry['sha256'])
        entry = functional['readbacks'][role]
        modules.append(json.loads(checked(entry['path'], entry['sha256']).read_text())['modules'][functional['module']])
    if (functional.get('status') != 'passed' or sha(exports['after']) != sha(netlist) or
            oracle.get('status') != 'passed' or oracle.get('edges', 0) <= 0 or oracle.get('mutants_rejected') != 1 or
            oracle['input_sha256'].get(str(exports['before'])) != sha(exports['before'])):
        raise ValueError('Added-buffer candidate lacks linked functional evidence')
    # Local tool-cache entries can be symlinks to a shared checkout. Admit only
    # the exact executables recorded by this oracle, still checking their bytes.
    oracle_tools = {Path(c['argv'][0]).resolve() for c in oracle.get('commands', [])
                    if c.get('argv') and Path(c['argv'][0]).is_relative_to(root / 'build/tools')}
    for name, digest in oracle['input_sha256'].items():
        checked_input(name, digest, oracle_tools)
    for name, digest in functional['inputs_sha256'].items():
        checked_input(name, digest)
    # The independent reference predates a previously validated buffer resize.
    # Recompute the complete resize+insertion identity to the original pin oracle.
    proof = compare_buffer_repair(*modules, allow_resizing=True)
    if proof != functional['connectivity']:
        raise ValueError('Added-buffer connectivity differs from validated readbacks')
    # A repaired parent already contains some of the oracle-to-candidate additions.
    # Bind and check that intermediate export separately; only the immediate edit
    # belongs in the source-to-candidate placement and power comparison.
    chained = 'source' in functional
    if chained != ('source_connectivity' in functional) or direct and not chained:
        raise ValueError('Incomplete repaired-source functional chain')
    immediate, prior_added = proof, 0
    if chained:
        entry = functional['source']['export']
        source_export = checked(entry['path'], entry['sha256'])
        entry = functional['source']['readback']
        source_module = json.loads(checked(entry['path'], entry['sha256']).read_text())['modules'][functional['module']]
        if (reference.get('netlist') != str(source_export.relative_to(root)) or
                reference.get('netlist_sha256') != sha(source_export) or
                reference['artifacts_sha256'].get(source_export.name) != sha(source_export)):
            raise ValueError('Unlinked repaired-source export')
        prior = compare_buffer_repair(modules[0], source_module, allow_resizing=True)
        immediate = compare_buffer_repair(source_module, modules[1], allow_resizing=organization, allow_rewiring=organization)
        compared_local = {k:local_proof[k] for k in immediate} if organization else local_proof
        if immediate != functional['source_connectivity'] or immediate != compared_local:
            raise ValueError('Immediate buffer edit differs from local validation')
        prior_added = len(prior['added_instances'])
    elif proof['added_instances'] != local_proof['added_instances']:
        raise ValueError('Added-buffer connectivity differs from local validation')
    contexts = [json.loads(checked(p.parent / 'context.json', data['artifacts_sha256']['context.json']).read_text())
                for p, data in [(reference_path, reference), (measure_path, measure)]]
    organization_contract = None
    if organization:
        from physical_organization_route import validate_organization_evidence
        organization_contract = validate_organization_evidence(selection, report, contexts,
            measure, reference, design, root, receipt, source_module, modules[1])
    else:
        added_buffer_geometry(*contexts, immediate, modules[1])
    state = json.loads(Path(state_path).read_text())
    if set(state) != {'odb', 'metrics'} or state['metrics'] != {}:
        raise ValueError('Added-buffer continuation must carry only ODB and empty metrics')
    if sha(artifact_path(state['odb'], design)) != sha(odb):
        raise ValueError('Staged ODB differs from the validated added-buffer candidate')
    tech = pdk_root / 'ihp-sg13cmos5l/libs.ref/sg13cmos5l_stdcell/lef/sg13cmos5l_tech.lef'
    nominal = ihp_layer_rc(tech)
    if config.get('LAYERS_RC') != nominal or config.get('VIAS_R'):
        raise ValueError('Added-buffer measurements require existing nominal layer RC')
    expected = dict(inv['overrides'], RUN_POST_GRT_DESIGN_REPAIR=False,
                    RUN_POST_GRT_RESIZER_TIMING=False, RUN_ANTENNA_REPAIR=False)
    if overrides != expected or overrides.get('LAYERS_RC') != nominal:
        raise ValueError('Added-buffer routing must preserve controls, nominal RC and disabled repair')
    distribution_contract = None
    if distribution:
        from physical_distribution_route import validate_distribution_evidence
        distribution_contract = validate_distribution_evidence(
            report, contexts, measure, reference, design, root, receipt, immediate)
    path_contract = None
    if paths:
        from physical_path_contract import validate_path_evidence
        path_contract = validate_path_evidence(
            report, contexts, measure, reference, design, root, receipt, immediate)
    return dict(selection=str(selection_path.relative_to(root)), selection_sha256=sha(selection_path),
        evidence=evidence, candidate_database=str(odb.relative_to(root)), candidate_database_sha256=sha(odb),
        netlist_sha256=sha(netlist), added_buffers=len(immediate['added_instances']),
        prior_added_buffers=prior_added, total_added_buffers=len(proof['added_instances']),
        prior_resized_buffers=len(proof['resized_buffers']), pin_edges_reused=oracle['edges'],
        validator_sha256=sha(Path(__file__)), nominal_tech_lef_sha256=sha(tech),
        timing_admission='positive-coarse-margins-complete-wire-estimates',
        scope=('One whole-chip coarse route of the exact declared organization; only approved signal edits; fixed clock topology; existing nominal RC; no repair' if organization else
               'One whole-chip coarse route of the exact added-buffer candidate; fixed cells, placement and clock topology; existing nominal RC; no repair'),
        **({'organization_contract': organization_contract} if organization else {}),
        **({'distribution_contract': distribution_contract} if distribution else {}),
        **({'path_contract': path_contract} if paths else {}))
