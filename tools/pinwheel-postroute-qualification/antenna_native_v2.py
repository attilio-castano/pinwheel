"""Optional detailed-wire antenna diagnostic; no repair/insertion/route commands."""
import json
import math
from pathlib import Path
import re
import runpy

from audits import consumed_nets, sha, write

R = Path('/work/diagnostic')
# Reuse the frozen same-ODB full-scope/view readback in this SAME process.
state = runpy.run_path(str(R / 'export_native.py'))
design, block = state['design'], state['block']
snapshot = state['snapshot']
before = state['after']
inventory = json.loads((R / 'input/inventory.json').read_text())
required_nets = consumed_nets(inventory)
missing_detailed = []
for name in required_nets:
    net = block.findNet(name)
    if net is None or net.isSpecial() or net.getWire() is None or str(net.getWireType()) != 'ROUTED':
        missing_detailed.append(name)
assert not missing_detailed, 'Antenna guide-to-wire fallback forbidden: incomplete actual ROUTED detailed wires'
assert required_nets, 'Empty antenna detailed-wire denominator'
tech = design.getDb().getTech()
rules = {}
for layer in tech.getLayers():
    if str(layer.getType()) not in ('ROUTING', 'CUT'):
        continue
    try:
        present = bool(layer.hasDefaultAntennaRule())
        presence_error = None
    except Exception as error:
        present = False
        presence_error = repr(error)
    values = {}
    errors = [presence_error] if presence_error else []
    if present:
        rule = layer.getDefaultAntennaRule()
        for key in ('getPAR', 'getPSR', 'getCAR', 'getCSR'):
            try:
                values[key] = float(getattr(rule, key)())
            except Exception as error:
                errors.append(key + ': ' + repr(error))
    rules[layer.getName()] = {'has_native_rule': present, 'scalar_ratios': values,
        'positive_scalar_rule': any(math.isfinite(value) and value > 0 for value in values.values()), 'query_errors': errors}

# Include the used native via landings/cuts, not every unused technology via.
source_def = (R / 'input/checkpoint.def').read_text()
used_layers = set(state['def_routing_layers'](source_def)['NETS'])
route_body = re.search(r'^NETS\s+\d+\s*;(.*?)^END\s+NETS\s*$', source_def, re.M | re.S)[1]
vias = json.loads((R / 'input/vias.json').read_text())
for name, boxes in vias.items():
    via_name = name.split('/', 1)[1]
    if re.search(r'(?<![\w$])' + re.escape(via_name) + r'(?![\w$])', route_body):
        used_layers.update(box[0] for box in boxes)
rule_missing = sorted(layer for layer in used_layers if layer not in rules or
                      not rules[layer]['positive_scalar_rule'] or rules[layer]['query_errors'])
gate_models = {}
uncovered_inputs = []
input_contacts = 0
covered_contacts = 0
for inst in block.getInsts():
    for term in inst.getITerms():
        net = term.getNet()
        mterm = term.getMTerm()
        if net is None or net.getName() not in required_nets or str(mterm.getIoType()) != 'INPUT':
            continue
        input_contacts += 1
        key = inst.getMaster().getName() + '/' + mterm.getName()
        if key not in gate_models:
            record = {'has_native_model': False, 'gate_areas': [], 'query_error': None}
            try:
                record['has_native_model'] = bool(mterm.hasDefaultAntennaModel())
            except Exception as error:
                record['query_error'] = repr(error)
            if record['has_native_model']:
                try:
                    areas = mterm.getDefaultAntennaModel().getGateArea()
                    record['gate_areas'] = [[float(area), layer.getName() if layer is not None else None] for area, layer in areas]
                except Exception as error:
                    record['query_error'] = repr(error)
            record['positive_gate_area'] = any(math.isfinite(row[0]) and row[0] > 0 for row in record['gate_areas'])
            gate_models[key] = record
        if gate_models[key]['positive_gate_area']:
            covered_contacts += 1
        else:
            uncovered_inputs.append({'instance': inst.getName(), 'pin': mterm.getName(), 'master': inst.getMaster().getName(), 'net': net.getName()})

api = {'command_present': design.evalTclString('llength [info commands check_antennas]') == '1'}
design.evalTclString('help check_antennas')
try:
    api['Tcl_body'] = design.evalTclString('info body check_antennas')
except Exception as error:
    api['Tcl_body'] = None
    api['query_error'] = repr(error)
api['Tcl_binding_check_only'] = bool(api['Tcl_body'] and 'ant::check_antennas' in api['Tcl_body'] and '-verbose' in api['Tcl_body'] and
    not re.search(r'(?:^|[;\n])\s*(?:repair\w*|insert\w*|resize\w*|global_route|detailed_route|makeNetWires\w*|destroyNetWires\w*)\b', api['Tcl_body']))
write(R / 'antenna-API.json', api)
metadata = {'relevant_consumed_net_count': len(required_nets), 'all_have_actual_ROUTED_detailed_wires': True,
    'relevant_connected_INPUT_ITerm_count': input_contacts, 'native_positive_gate_area_contact_count': covered_contacts,
    'uncovered_INPUT_contacts': uncovered_inputs, 'master_gate_models': gate_models,
    'used_metal_and_via_cut_layers': sorted(used_layers), 'native_technology_rules': rules,
    'special_power_wires_excluded_from_gate_antenna_denominator': True,
    'used_layers_without_positive_native_scalar_rule': rule_missing,
    'all_input_gate_area_and_used_layer_rule_coverage_complete': input_contacts > 0 and not uncovered_inputs and not rule_missing,
    'BTerm_boundary': 'Top-level ports are not device gate-area models; their physical wiring/LVS coverage is separate.',
    'rule_qualification': 'Missing native model/query support or scalar rule coverage prevents an antenna pass; no gate area or rule is synthesized.'}
write(R / 'antenna-model-coverage.json', metadata)
admitted = api['command_present'] and api['Tcl_binding_check_only'] and covered_contacts > 0 and any(
    layer in rules and rules[layer]['positive_scalar_rule'] for layer in used_layers)
if admitted:
    # Pinned native detailed-wire branch is required above: never synthesize
    # guides into wires. Only this checker command is executed.
    design.evalTclString('check_antennas -verbose')
else:
    print('PINWHEEL_ANTENNA_DIAGNOSTIC_NOT_ADMITTED_API_OR_MODEL_COVERAGE', flush=True)
design.evalTclString('write_def /work/diagnostic/antenna-after.def')
after = snapshot(design.getDb(), block, 'antenna-after')
assert after == before, 'Antenna checker changed full native inventory/rules/PG/clock topology'
assert state['masters_snapshot']() == json.loads((R / 'input/master-OBS.json').read_text())
assert state['vias_snapshot']() == json.loads((R / 'input/vias.json').read_text())
assert state['tokens']((R / 'antenna-after.def').read_text()) == state['tokens']((R / 'export/checkpoint.def').read_text()), 'Antenna checker changed route/TAPER/PG geometry'
write(R / 'measurement.json', {'schema': 'pinwheel-check-only-antenna-v2', 'status': 'measured',
    'checker_called': admitted, 'source_database_sha256': sha(R / 'input/checkpoint.odb'),
    'native_API': api, 'coverage': metadata, 'full_scope_and_DEF_TAPER_exact': True,
    'actual_command': 'check_antennas -verbose' if admitted else None,
    'antenna_net_violation_count': None, 'antenna_pin_violation_count': None,
    'antenna_pass_qualified': False, 'physical_acceptance_claim': False,
    'qualification': 'Optional check-only detailed-wire model diagnostic; coordinator must reconcile actual native counts and coverage. No repair, cell, route, PG or clock edits.'})
