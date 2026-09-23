"""Admission and connection identity for the retained chip mapping's physical intake."""
from collections import Counter, defaultdict
import json
from pathlib import Path

from tiled_chip import chip_metrics
from validation_run import sha

TIES = {'sg13cmos5l_tiehi': ('L_HI', '1'), 'sg13cmos5l_tielo': ('L_LO', '0')}


def selected_mapping(selection_path, role, root):
    """Consume an immutable validated mapping, independently of later source edits."""
    if role not in ('baseline', 'tiled'):
        raise ValueError('Unknown mapped chip role')
    selection_path, root = Path(selection_path).resolve(), Path(root).resolve()
    selection = json.loads(selection_path.read_text())
    if selection.get('decision') != 'eligible-for-bounded-physical-comparison':
        raise ValueError('Mapping is not selected for the bounded physical comparison')
    report_path = root / selection['report']
    validation_path = root / selection['validation']['report']
    if (sha(report_path) != selection['report_sha256'] or
            sha(validation_path) != selection['validation']['report_sha256']):
        raise ValueError('Changed selected mapping or validation report')
    report, validation = (json.loads(p.read_text()) for p in (report_path, validation_path))
    if (report.get('status') != 'passed' or validation.get('status') != 'passed' or
            report.get('organization') != 'combined' or report.get('candidate_fanout_limit') != 8 or
            validation['reports']['mapping']['report_sha256'] != sha(report_path)):
        raise ValueError('Require the completed load-budget comparison and its validation')
    prefix = role + '-typical'
    paths = {k: report_path.parent / name for k, name in {
        'netlist': prefix + '.v', 'mapped': prefix + '-readback.json',
        'assembly': 'assembly.json'}.items()}
    for path in paths.values():
        if sha(path) != report['artifacts_sha256'][path.name]:
            raise ValueError('Changed retained mapped artifact: ' + path.name)
    data = json.loads(paths['mapped'].read_text())
    metrics = chip_metrics(data)
    if metrics != report['variants']['typical'][role]:
        raise ValueError('Retained mapped metrics do not reproduce')
    return paths, dict(role=role, corner='typical', selection=str(selection_path),
        selection_sha256=sha(selection_path), report=str(report_path), report_sha256=sha(report_path),
        validation_report=str(validation_path), validation_report_sha256=sha(validation_path),
        artifacts_sha256={k: sha(p) for k, p in paths.items()}, metrics=metrics,
        libraries_sha256=report['libraries_sha256'], macro_views_sha256=report['macro_views_sha256'])


def connection_signature(module):
    """Compare every named cell pin and package bit, independent of wire names.

    Floorplan initialization materializes constants as the pinned tie cells.
    Fold only those exact zero-input cells; account for them separately. No
    other cell, clock, state, macro connection or net partition may change.
    """
    ties, constants = {}, {}
    for name, cell in module['cells'].items():
        if cell['type'] not in TIES:
            continue
        pin, value = TIES[cell['type']]
        if (set(cell['connections']) != {pin} or cell['port_directions'] != {pin: 'output'} or
                len(cell['connections'][pin]) != 1 or type(cell['connections'][pin][0]) is not int):
            raise ValueError('Malformed physical tie cell')
        bit = cell['connections'][pin][0]
        if bit in constants:
            raise ValueError('Multiple tie drivers')
        constants[bit] = value
        ties[name] = cell['type']
    nets, literals, cells, ports = defaultdict(list), [], {}, {}

    def terminal(bit, identity):
        bit = constants.get(bit, bit)
        if type(bit) is int:
            nets[bit].append(identity)
        elif bit in ('0', '1'):
            literals.append((identity, bit))
        else:
            raise ValueError('Unknown or unsupported physical signal')

    for name, port in module['ports'].items():
        if port['direction'] not in ('input', 'output'):
            raise ValueError('Unexpected mapped package direction')
        ports[name] = (port['direction'], len(port['bits']), port.get('offset', 0), port.get('upto', 0))
        for index, bit in enumerate(port['bits']):
            if port['direction'] == 'input' and bit in constants:
                raise ValueError('Tie cell drives a package input')
            terminal(bit, ('port', name, '', index))
    for name, cell in module['cells'].items():
        if name in ties:
            continue
        if set(cell['connections']) != set(cell['port_directions']):
            raise ValueError('Unclassified physical cell terminal')
        cells[name] = (cell['type'], tuple(sorted((p, cell['port_directions'][p], len(bits))
                                                for p, bits in cell['connections'].items())))
        for pin, bits in cell['connections'].items():
            direction = cell['port_directions'][pin]
            if direction not in ('input', 'output'):
                raise ValueError('Unexpected physical cell direction')
            for index, bit in enumerate(bits):
                if direction == 'output' and bit in constants:
                    raise ValueError('Tie cell shares a logic driver')
                terminal(bit, ('cell', name, pin, index))
    return dict(ports=ports, cells=cells, constants=sorted(literals),
                nets=sorted(sorted(group) for group in nets.values())), dict(sorted(Counter(ties.values()).items()))


def compare_connections(reference, imported):
    before, old_ties = connection_signature(reference)
    after, new_ties = connection_signature(imported)
    if old_ties:
        raise ValueError('Expected the retained mapping before physical tie insertion')
    for key in before:
        if before[key] != after[key]:
            raise ValueError('Physical import changed ' + key)
    return dict(connection_identity=True, retained_cells=len(before['cells']), added_tie_cells=new_ties)


def signal_view(module, power_rails):
    """Project only declared, isolated power ports from a saved signal netlist.

    Liberty signal readback omits physical power terminals. The power nets must
    be checked separately in OpenDB; this projection cannot hide a logic load,
    a shorted rail, another package port, or an unexpected bidirectional signal.
    """
    present = set(module['ports']) & set(power_rails)
    if not present:
        return module, []
    if present != set(power_rails):
        raise ValueError('Incomplete explicit power ports')
    signals = [p for n, p in module['ports'].items() if n not in present]
    used = {b for p in signals for b in p['bits']}
    used.update(b for c in module['cells'].values() for bits in c['connections'].values() for b in bits)
    rails = set()
    for name in sorted(present):
        port = module['ports'][name]
        bits = port['bits']
        if (port['direction'] != 'inout' or len(bits) != 1 or type(bits[0]) is not int or
                bits[0] in used or bits[0] in rails or port.get('offset', 0) != 0):
            raise ValueError('Power port is not an isolated scalar rail: ' + name)
        rails.add(bits[0])
    return dict(module, ports={n: p for n, p in module['ports'].items() if n not in present}), sorted(present)


def validate_start(inputs, state_path, from_step, design):
    """A mapped preparation cannot accidentally enter RTL synthesis."""
    if 'mapped_input' not in inputs:
        return
    if not state_path or not from_step:
        raise ValueError('Mapped chip requires an explicit verified netlist/checkpoint start')
    if from_step == 'OpenROAD.CheckSDCFiles':
        state = json.loads(Path(state_path).read_text())
        if (state.get('nl') != '/work/core/design.sv' or
                state.get('json_h') != '/work/core/mapped.json' or
                set(state) != {'nl', 'json_h', 'metrics'} or state['metrics'] != {}):
            raise ValueError('Mapped intake must start from its exact staged netlist and JSON')
    else:
        # Continuations must follow a completed, independently checked import.
        after_macro = bool(inputs.get('physical_target')) and from_step == 'Odb.RemovePDNObstructions'
        receipt = Path(design) / ('macro-verified.json' if after_macro else 'import-verified.json')
        if not receipt.exists():
            raise ValueError('Mapped continuation requires verified physical import')
        verified = json.loads(receipt.read_text())
        if (verified.get('status') != 'passed' or
                verified.get('inputs_sha256') != sha(Path(design) / 'inputs.json') or
                from_step != ('Odb.RemovePDNObstructions' if after_macro else 'OpenROAD.DumpRCValues') or
                (after_macro and verified.get('continuation_step') != from_step) or
                verified.get('state_sha256') != sha(Path(state_path))):
            raise ValueError('Unsupported or stale mapped continuation')
