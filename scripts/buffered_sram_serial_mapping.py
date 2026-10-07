"""Saved frontend mapping equality, separate from initialized serial traces."""
from copy import deepcopy
import json
from pathlib import Path
import re

from buffered_hardware_synthesis import CAD
from buffered_sram_serial_binding import FRONTEND, _yosys_path
from tiled_chip import FF, project_pruned_state, state_cut
from validation_run import sha


def physical_state_quotient(source, candidate, assembly, omitted=()):
    """Check a common quotient of named coordinates onto all actual FF roots.

    Every named coordinate must be a known constant, an explicitly omitted
    declaration coordinate, or an actual physical Q root. Both saved modules
    must have exactly the same constants and alias classes. Synthetic names
    select one existing Q per class; no value, gate or storage is invented.
    """
    omitted = set(omitted)
    coordinates = {(register['name'], index) for register in assembly['registers']
                   for index in range(register['width'])}
    if not omitted <= coordinates:
        raise ValueError('Serial quotient omits an undeclared coordinate')

    def inspect(module):
        roots = set()
        for cell in module['cells'].values():
            kind = cell['type']
            if kind not in (FF, '$_DFF_P_'):
                if (kind.startswith(('sg13cmos5l_df', '$_DFF', '$dff', '$adff',
                        '$sdff', '$_SDFF', '$ff', '$dlatch', '$_DLATCH')) or
                        cell.get('port_directions', {}).get('Q') == 'output'):
                    raise ValueError('Unsupported serial quotient state cell: ' + kind)
                continue
            bits = cell.get('connections', {}).get('Q')
            if (type(bits) is not list or len(bits) != 1 or type(bits[0]) is not int
                    or bits[0] < 2 or bits[0] in roots):
                raise ValueError('Aliased, unknown or malformed serial physical FF root')
            roots.add(bits[0])
        if len(roots) != 370:
            raise ValueError('Serial optimized physical FF census differs from 370')
        groups, constants = {}, {}
        for register in assembly['registers']:
            name, width = register['name'], register['width']
            bits = module['netnames'].get(name, {}).get('bits', [])
            expected = width - sum((name, index) in omitted for index in range(width))
            if len(bits) != expected:
                raise ValueError('Serial quotient named width differs: ' + name)
            for index in range(width):
                coordinate = (name, index)
                if coordinate in omitted:
                    continue
                if index >= len(bits):
                    raise ValueError('Serial quotient omission is not a trailing coordinate')
                bit = bits[index]
                if type(bit) is str and bit in ('0', '1'):
                    constants[coordinate] = bit
                elif type(bit) is int and bit in roots:
                    groups.setdefault(bit, []).append(coordinate)
                else:
                    raise ValueError('Unknown or nonphysical serial named state coordinate: '
                                     + name + '[' + str(index) + ']')
        if set(groups) != roots:
            raise ValueError('Serial physical FF lacks a declared coordinate')
        classes = {tuple(sorted(coordinates)): bit for bit, coordinates in groups.items()}
        return classes, constants

    source_classes, source_constants = inspect(source)
    candidate_classes, candidate_constants = inspect(candidate)
    if source_constants != candidate_constants:
        raise ValueError('Serial optimized state constant vectors differ')
    if set(source_classes) != set(candidate_classes):
        raise ValueError('Serial optimized state alias partitions differ')
    reference, mapped, description = deepcopy(source), deepcopy(candidate), deepcopy(assembly)
    description['registers'] = []
    classes, by_coordinate = [], {}

    def label(coordinate):
        return coordinate[0] + '[' + str(coordinate[1]) + ']'

    for coordinates in sorted(source_classes):
        representative = coordinates[0]
        name = 'quotient_' + representative[0] + '_' + str(representative[1])
        for module, bit in ((reference, source_classes[coordinates]),
                            (mapped, candidate_classes[coordinates])):
            if name in module['netnames'] or name in module['ports'] or name in module['cells']:
                raise ValueError('Reserved serial quotient name collision: ' + name)
            module['netnames'][name] = dict(hide_name=0, bits=[bit], attributes={})
        description['registers'].append(dict(name=name, reference=name, width=1))
        record = dict(representative=label(representative), coordinates=list(map(label, coordinates)),
            netname=name, source_q_bit=source_classes[coordinates],
            candidate_q_bit=candidate_classes[coordinates])
        classes.append(record)
        for coordinate in coordinates:
            by_coordinate[coordinate] = record['representative']
    declared = []
    for register in assembly['registers']:
        for index in range(register['width']):
            coordinate = (register['name'], index)
            entry = dict(coordinate=label(coordinate))
            if coordinate in omitted:
                entry.update(kind='omitted')
            elif coordinate in source_constants:
                entry.update(kind='constant', value=source_constants[coordinate])
            else:
                entry.update(kind='physical', representative=by_coordinate[coordinate])
            declared.append(entry)
    metadata = dict(declared_registers=deepcopy(assembly['registers']),
        declared_coordinate_mapping=declared, physical_classes=classes,
        constants=[dict(coordinate=label(coordinate), value=value)
                   for coordinate, value in sorted(source_constants.items())],
        omitted_declared_coordinates=list(map(label, sorted(omitted))),
        physical_state_bits=len(classes),
        aliased_coordinate_count=sum(len(c['coordinates']) - 1 for c in classes),
        constant_coordinate_count=len(source_constants),
        boundary='Exact common constants and physical-Q alias classes of the optimized source and saved mapping.')
    return reference, mapped, description, metadata


def prove_frontend_mapping(run, out, variant, assembly, data, library):
    """Compare every output and physical next-state bit of saved frontend gates.

    Inputs include unrestricted defined status/pin values. Current represented
    register values in the optimized source representation are arbitrary; no
    reset or reachable-state premise is introduced. The typed 389-bit state is
    qualified separately by post-POR replay. Exact physical state projections
    expose any omitted, pruned or derived coordinates explicitly.
    """
    if variant not in ('generic', 'typical') or assembly.get('module') != FRONTEND:
        raise ValueError('Wrong serial frontend mapping variant or assembly')
    if variant == 'typical' and library is None:
        raise ValueError('Typical serial frontend proof requires its pinned Liberty')
    out = Path(out)
    target = out / variant
    source = json.loads((out / 'source-readback.json').read_text())
    saved = json.loads((target / 'readback.json').read_text())
    if data != saved:
        raise ValueError('Serial frontend proof data differs from the saved readback')
    source_module, saved_module = source['modules'][FRONTEND], saved['modules'][FRONTEND]
    normalized = deepcopy(assembly)
    declared_bits = sum(register['width'] for register in assembly['registers'])
    if declared_bits != 389 or len(assembly['registers']) != 13:
        raise ValueError('Changed declared serial frontend state schema')
    omitted = []
    for register in normalized['registers']:
        name, width = register['name'], register['width']
        source_net = source_module['netnames'].get(name, {})
        saved_net = saved_module['netnames'].get(name, {})
        if (name == 'r_response' and width == 192 and
                len(source_net.get('bits', [])) == 191 and len(saved_net.get('bits', [])) == 191):
            if source_net.get('offset', 0) != 0 or saved_net.get('offset', 0) != 0:
                raise ValueError('Unexpected serial response offset in optimized readback')
            location = source_module.get('attributes', {}).get('src', '')
            match = re.fullmatch(r'(.+):[0-9]+\.[0-9]+-[0-9]+\.[0-9]+', location)
            if match is None or not re.search(r'\breg\s*\[\s*191\s*:\s*0\s*\]\s+r_response\s*;',
                    Path(match.group(1)).read_text()):
                raise ValueError('Missing original 192-bit serial response Verilog declaration')
            register['width'] = 191
            omitted.append('r_response[191]')
        elif len(source_net.get('bits', [])) != width or len(saved_net.get('bits', [])) != width:
            raise ValueError('Unexpected optimized serial frontend named width: ' + name)
    reference_module, candidate_module, quotient_assembly, quotient = physical_state_quotient(
        source_module, saved_module, assembly,
        [('r_response', 191)] if omitted else [])
    quotient_negatives = []

    def reject_quotient(label, mutant, reason):
        try:
            physical_state_quotient(source_module, mutant, assembly,
                [('r_response', 191)] if omitted else [])
        except ValueError as error:
            if reason not in str(error):
                raise ValueError('Unexpected serial quotient negative-control reason') from error
        else:
            raise ValueError('Accepted serial quotient negative control: ' + label)
        quotient_negatives.append(dict(label=label, rejection=reason))

    aliased = next((entry for entry in quotient['physical_classes']
                    if len(entry['coordinates']) > 1), None)
    if aliased is None or not quotient['constants']:
        raise ValueError('Missing expected serial quotient alias or constant qualification')
    coordinate = re.fullmatch(r'(.+)\[([0-9]+)\]', aliased['coordinates'][-1])
    other = next(entry for entry in quotient['physical_classes'] if entry is not aliased)
    mutant = deepcopy(saved_module)
    mutant['netnames'][coordinate.group(1)]['bits'][int(coordinate.group(2))] = other['candidate_q_bit']
    reject_quotient('changed-alias-partition', mutant, 'alias partitions differ')
    coordinate = re.fullmatch(r'(.+)\[([0-9]+)\]', quotient['constants'][0]['coordinate'])
    mutant = deepcopy(saved_module)
    mutant['netnames'][coordinate.group(1)]['bits'][int(coordinate.group(2))] = (
        '1' if quotient['constants'][0]['value'] == '0' else '0')
    reject_quotient('changed-constant-vector', mutant, 'constant vectors differ')
    quotient_path = target / 'state-quotient.json'
    quotient_path.write_text(json.dumps(quotient, indent=2) + '\n')
    reference, source_projection = state_cut(reference_module, quotient_assembly, True)
    candidate, projection = state_cut(candidate_module, quotient_assembly, True)
    reference = project_pruned_state(reference, candidate, projection,
                                     projection['pruned_state_positions'])

    def write(path, module, name):
        path.write_text(json.dumps(dict(modules={name: module}), indent=2) + '\n')

    reference_path, candidate_path = target / 'source-cut.json', target / 'gate-cut.json'
    write(reference_path, reference, 'reference')
    write(candidate_path, candidate, 'candidate')

    def prove(path, label, reject=None):
        lines = []
        if variant == 'typical':
            lines.append('read_liberty -ignore_miss_func ' + _yosys_path(library))
        lines += ['read_json ' + _yosys_path(reference_path),
            'read_json ' + _yosys_path(path),
            'miter -equiv -flatten -make_outputs reference candidate miter',
            'hierarchy -check -top miter', 'flatten', 'opt -full',
            'sat -verify -prove trigger 0 -set-def-inputs miter']
        script = out / (label + '.ys')
        script.write_text('\n'.join(lines) + '\n')
        log = run([CAD / 'yosys', '-Q', '-T', '-s', script], label,
                  timeout=900, reject=reject)
        expected = reject or 'SAT proof finished - no model found: SUCCESS!'
        if expected not in log:
            raise ValueError('Incomplete saved serial frontend mapping comparison')

    prove(candidate_path, 'frontend-' + variant + '-equivalence')
    mutant = deepcopy(candidate)
    miso = mutant['ports'].get('miso', {})
    if miso.get('direction') != 'output' or len(miso.get('bits', [])) != 1:
        raise ValueError('Missing one-bit serial frontend MISO output')
    if 'negative.miso' in mutant['cells']:
        raise ValueError('Reserved serial frontend negative-control name collision')
    all_bits = [bit for cell in mutant['cells'].values()
                for bits in cell['connections'].values() for bit in bits if type(bit) is int]
    all_bits += [bit for port in mutant['ports'].values() for bit in port['bits'] if type(bit) is int]
    all_bits += [bit for net in mutant['netnames'].values() for bit in net['bits'] if type(bit) is int]
    fresh = max(all_bits, default=1) + 1
    original = miso['bits'][0]
    mutant['cells']['negative.miso'] = dict(type='$_NOT_', hide_name=0, parameters={},
        attributes={}, port_directions={'A': 'input', 'Y': 'output'},
        connections={'A': [original], 'Y': [fresh]})
    mutant['ports']['miso']['bits'] = [fresh]
    mutant['netnames']['miso']['bits'] = [fresh]
    negative_path = target / 'gate-cut-negative.json'
    write(negative_path, mutant, 'candidate')
    prove(negative_path, 'frontend-' + variant + '-negative', reject='proof did fail')
    return dict(status='equivalent', projection=projection, source_projection=source_projection,
        outputs=len(assembly['outputs']),
        declared_frontend_state_bits=declared_bits,
        normalized_named_state_bits=sum(register['width'] for register in normalized['registers']),
        omitted_declared_coordinates=omitted,
        physical_state_quotient=dict(physical_state_bits=quotient['physical_state_bits'],
            aliased_coordinate_count=quotient['aliased_coordinate_count'],
            constant_coordinate_count=quotient['constant_coordinate_count'],
            path=str(quotient_path), sha256=sha(quotient_path),
            negative_controls=quotient_negatives),
        source_checkpoint='Yosys optimized source-readback representation',
        negative_control='Inverted serial frontend MISO rejected',
        scope='All 19 frontend outputs and all 370 physical next-state bits for arbitrary defined '
            'status/pin inputs and current state represented in the Yosys optimized source readback; '
            'omitted declared coordinates and physically absent next-state coordinates are explicit. '
            'No initialization or reachability assumption for that representation, and no unrestricted '
            '389-bit typed equation proof. Post-POR typed/RTL replay, initialized serial traces and '
            'SRAM availability remain separate checks.')
