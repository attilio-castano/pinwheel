"""Checked handoff from a validated mapping to the shared physical flow.

Target declarations own instances, power, placement and semantic path roles.
Source adapters establish the existing validation contract. The prepared target
then freezes resolved artifacts and endpoints; measurements never edit it.
"""
from collections import Counter
from copy import deepcopy
import json
import re
from pathlib import Path

from mapped_physical import selected_mapping
from physical_floorplan import apply_exclusions, apply_placement, overlaps
from tiled_chip import FF
from validation_run import sha

SUFFIXES = {'typical': 'typ_1p20V_25C', 'slow': 'slow_1p08V_125C',
            'fast': 'fast_1p32V_m55C'}
POWER = {'VPWR': ['VDD!', 'VDDARRAY!'], 'VGND': ['VSS!']}


def read(path):
    return json.loads(Path(path).read_text())


def require_keys(value, keys, label):
    if not isinstance(value, dict) or set(value) != set(keys):
        raise ValueError('Incomplete or unknown ' + label + ' fields')


def declaration(path):
    target = read(path)
    require_keys(target, ['schema', 'name', 'source', 'macro', 'placement_exclusions',
                         'entry_state', 'upload_state'], 'physical target')
    require_keys(target['source'], ['kind', 'selection', 'sha256'], 'target source')
    require_keys(target['macro'], ['master', 'instances', 'power'], 'macro')
    if target['schema'] != 1 or not re.fullmatch(r'[a-z][a-z0-9-]*', target['name']):
        raise ValueError('Unsupported physical target identity')
    macro = target['macro']
    if not re.fullmatch(r'RM_IHPSG13_1P_(64|512)x64_c2_bm_bist', macro['master']):
        raise ValueError('Unsupported target macro')
    if macro['power'] != POWER:
        raise ValueError('Incomplete macro power contract')
    if not macro['instances'] or any(not re.fullmatch(r'[A-Za-z_][A-Za-z0-9_.]*', n)
                                     for n in macro['instances']):
        raise ValueError('Invalid target macro instances')
    for key in ['entry_state', 'upload_state']:
        if (not isinstance(target[key], list) or not target[key] or
                len(set(target[key])) != len(target[key]) or
                any(not re.fullmatch(r'[A-Za-z_][A-Za-z0-9_.]*', n) for n in target[key])):
            raise ValueError('Invalid target state role: ' + key)
    if not isinstance(target['placement_exclusions'], list):
        raise ValueError('Invalid target exclusions')
    return target


def resolve(path, root):
    """Return the selected files and a normalized, immutable source receipt."""
    root, path = Path(root), Path(path)
    target = declaration(path)
    source = target['source']
    selection = root / source['selection']
    if sha(selection) != source['sha256']:
        raise ValueError('Changed physical target selection')
    if source['kind'] == 'local-load':
        paths, provenance = selected_mapping(selection, 'tiled', root)
    elif source['kind'] == 'paired-controller':
        from paired_mapping import cut, metrics
        selected = read(selection)
        report_path = root / selected['report']
        if sha(report_path) != selected['report_sha256']:
            raise ValueError('Changed paired target report')
        report = read(report_path)
        if (report.get('status') != 'passed' or not report.get('inputs_unchanged') or
                not all(v['setup_pass'] and v['signal_electrical_pass'] for v in report['comparison'].values())):
            raise ValueError('Paired mapping did not pass the complete prephysical gate')
        paths = {k: report_path.parent / v for k, v in
                 {'netlist': 'typical/design.v', 'mapped': 'typical/readback.json', 'assembly': 'assembly.json'}.items()}
        for p in paths.values():
            if sha(p) != report['artifact_sha256'][str(p.relative_to(root))]:
                raise ValueError('Changed paired target artifact: ' + str(p))
        assembly, data = read(paths['assembly'])['chip'], read(paths['mapped'])
        measured = metrics(data, assembly)
        _, projection = cut(data['modules']['tt_um_pinwheel'], assembly)
        if (measured != report['variants']['typical']['metrics'] or
                projection != report['variants']['typical']['state_projection']):
            raise ValueError('Paired target census does not reproduce')
        provenance = dict(role='paired', corner='typical', selection=str(selection), selection_sha256=sha(selection),
            report=str(report_path), report_sha256=sha(report_path), metrics=measured,
            artifacts_sha256={k: sha(p) for k, p in paths.items()}, libraries_sha256=report['libraries_sha256'],
            macro_views_sha256={k: v for k, v in read(root / 'tools/storage-macros.json')['files_sha256'].items()
                               if target['macro']['master'] in k})
        for rel, digest in provenance['macro_views_sha256'].items():
            key = 'build/storage/macros/' + Path(rel).name
            if report['source_sha256'].get(key) != digest:
                raise ValueError('Macro view differs from the validated paired source')
    else:
        raise ValueError('Unsupported physical target source adapter')
    module = read(paths['mapped'])['modules']['tt_um_pinwheel']
    macros = {n: c['type'] for n, c in module['cells'].items() if c['type'].startswith('RM_IHP')}
    if macros != {n: target['macro']['master'] for n in target['macro']['instances']}:
        raise ValueError('Declared macros differ from the validated mapping')
    ownership, roles = state_and_paths(module, read(paths['assembly'])['chip'], target)
    return target, paths, provenance, ownership, roles


def state_and_paths(module, description, target):
    """Bind every FF once, then resolve logical roles to exact saved cell pins."""
    flops = {c['connections']['Q'][0]: n for n, c in module['cells'].items() if c['type'] == FF}
    if len(flops) != sum(c['type'] == FF for c in module['cells'].values()):
        raise ValueError('Aliased target FF outputs')
    owners, used = {}, set()
    for slot in description['registers']:
        name = slot['name']
        bits = module['netnames'].get('controller.' + name, {}).get('bits')
        if bits is None or len(bits) != slot['width'] or name in owners:
            raise ValueError('Missing or duplicate typed target state: ' + name)
        owners[name] = []
        for index, bit in enumerate(bits):
            if bit not in flops:
                continue  # Source validation already checked constant/pruned state.
            cell = flops[bit]
            if cell in used:
                raise ValueError('Target FF has more than one state owner')
            used.add(cell)
            owners[name].append(dict(bit=index, cell=cell, d=cell + '/D', q=cell + '/Q'))
    if len(used) != len(flops):
        raise ValueError('Target state does not cover every physical FF')

    def state_pins(names, pin):
        pins = []
        for n in names:
            if n not in owners or not owners[n]:
                raise ValueError('Unresolved target state role: ' + n)
            pins += [r[pin] for r in owners[n]]
        return pins

    def macro_pins(port):
        return [f'{n}/{port}[{i}]' if len(module['cells'][n]['connections'][port]) > 1 else f'{n}/{port}'
                for n in target['macro']['instances'] for i in range(len(module['cells'][n]['connections'][port]))]

    responses = macro_pins('A_DOUT')
    if len(module['ports'].get('uo_out', {}).get('bits', [])) != 8:
        raise ValueError('Missing package rejection output')
    roles = {
        'sram_address': dict(delay='max', sources=responses, sinks=macro_pins('A_ADDR'), sink_kind='pin'),
        'entry_state': dict(delay='max', sources=responses, sinks=state_pins(target['entry_state'], 'd'), sink_kind='pin'),
        'rejection_status': dict(delay='max', sources=responses, sinks=['uo_out[4]'], sink_kind='port'),
        'upload_hold': dict(delay='min', sources=state_pins(target['upload_state'], 'q'), sinks=macro_pins('A_DIN'), sink_kind='pin'),
    }
    return dict(physical_flip_flops=len(flops), registers=owners), roles


def matching_bundle(design, bundle):
    """Attach semantic roles to an older run only for the identical mapped input."""
    design, bundle = Path(design), Path(bundle)
    physical, prepared = read(design / 'inputs.json'), read(bundle / 'inputs.json')
    if not prepared.get('physical_target'):
        raise ValueError('Role bundle is not a prepared physical target')
    for rel, digest in prepared['files_sha256'].items():
        if sha(bundle / rel) != digest:
            raise ValueError('Changed target bundle: ' + rel)
    for key in ['artifacts_sha256', 'libraries_sha256']:
        if physical['mapped_input'][key] != prepared['mapped_input'][key]:
            raise ValueError('Target bundle belongs to another mapped input')
    for rel in ['core.sdc', 'tt_block_6x4_pgvdd.def']:
        if sha(design / rel) != sha(bundle / rel):
            raise ValueError('Target bundle uses another package or timing boundary')
    return bundle


def path_expectations(module, roles):
    """Check combinational reach before STA, including intentionally absent roles.

    FFs and SRAM are path boundaries. This conservative cell graph does not
    infer timing exceptions or conditional Liberty arcs; measured STA must agree.
    """
    def bit(name, kind):
        owner, terminal = name.rsplit('/', 1) if kind == 'pin' else (None, name)
        match = re.fullmatch(r'([^\[\]]+)(?:\[(\d+)\])?', terminal)
        if not match:
            raise ValueError('Invalid role terminal')
        port, index = match.group(1), int(match.group(2) or 0)
        bits = module['cells'][owner]['connections'][port] if owner else module['ports'][port]['bits']
        return bits[index]

    edges = {}
    for cell in module['cells'].values():
        if cell['type'].startswith(('sg13cmos5l_df', 'RM_IHP')):
            continue
        outputs = {b for p, bs in cell['connections'].items() if cell['port_directions'][p] == 'output'
                   for b in bs if type(b) is int}
        for p, bs in cell['connections'].items():
            if cell['port_directions'][p] == 'input':
                for b in bs:
                    if type(b) is int:
                        edges.setdefault(b, set()).update(outputs)
    expected = {}
    for name, role in roles.items():
        reached = {bit(p, 'pin') for p in role['sources']}
        pending = list(reached)
        while pending:
            for sink in edges.get(pending.pop(), set()) - reached:
                reached.add(sink); pending.append(sink)
        expected[name] = any(bit(p, role['sink_kind']) in reached for p in role['sinks'])
    return expected


def configuration(base, target):
    """Only target-owned macro/RTL/placement fields replace the platform defaults."""
    result = deepcopy(base)
    macro = target['macro']; master = macro['master']
    result['VERILOG_FILES'] = ['dir::design.sv']
    result['VERILOG_DEFINES'] = []
    result['MACROS'] = {master: dict(instances=deepcopy(macro['instances']),
        gds=[f'dir::macro/{master}.gds'], lef=[f'dir::macro/{master}.lef'],
        vh=[f'dir::macro/{master}.bb.v'], spice=[f'dir::macro/{master}.cdl'],
        lib={f'*{key}*': [f'dir::macro/{master}_{suffix}.lib']
             for key, suffix in zip(['typ', 'slow', 'fast'], SUFFIXES.values())})}
    result['PDN_MACRO_CONNECTIONS'] = [f'{re.escape(n)} VPWR VGND {pin} VSS!'
        for n in macro['instances'] for pin in macro['power']['VPWR']]
    result.pop('FP_OBSTRUCTIONS', None)
    result = apply_placement(result, macro['instances'])
    if target['placement_exclusions']:
        result = apply_exclusions(result, target['placement_exclusions'])
    return result


def validate_views(target, folder, provenance, base):
    """Check pinned logical views, LEF terminals and the proposed footprint.

    This is a geometric preflight; routed access and metal power continuity are
    separate measurements. Every full view is also verified by the PDK inventory.
    """
    macro = target['macro']; master = macro['master']; folder = Path(folder)
    for rel, digest in provenance['macro_views_sha256'].items():
        if master in rel and sha(folder / Path(rel).name) != digest:
            raise ValueError('Physical view differs from the validated mapping: ' + rel)
    text = (folder / (master + '.lef')).read_text()
    if re.findall(r'^MACRO\s+(\S+)', text, re.M) != [master]:
        raise ValueError('Wrong LEF macro master')
    size = re.findall(r'^\s*SIZE\s+([\d.]+)\s+BY\s+([\d.]+)\s*;', text, re.M)
    if len(size) != 1 or min(map(float, size[0])) <= 0:
        raise ValueError('Invalid LEF macro dimensions')
    width, height = map(float, size[0])
    pins = {}
    for match in re.finditer(r'^\s*PIN\s+(\S+)\s*\n(.*?)^\s*END\s+\1\s*$', text, re.M | re.S):
        name, body = match.groups()
        uses = re.findall(r'\bUSE\s+(\w+)\s*;', body)
        directions = re.findall(r'\bDIRECTION\s+(\w+)\s*;', body)
        if name in pins or len(uses) != 1 or len(directions) != 1:
            raise ValueError('Incomplete LEF terminal: ' + name)
        pins[name] = dict(use=uses[0], direction=directions[0])
    if {n for n, p in pins.items() if p['use'] == 'POWER'} != set(macro['power']['VPWR']) or \
       {n for n, p in pins.items() if p['use'] == 'GROUND'} != set(macro['power']['VGND']):
        raise ValueError('LEF power pins differ from target contract')
    rectangles = {}
    for n, inst in macro['instances'].items():
        w, h = (height, width) if inst['orientation'] in ['E', 'W', 'FE', 'FW'] else (width, height)
        x, y = inst['location']; rect = [x, y, round(x + w, 6), round(y + h, 6)]
        die = base['DIE_AREA']
        if not (die[0] <= x < x+w <= die[2] and die[1] <= y < y+h <= die[3]):
            raise ValueError('Macro footprint leaves the allowed die')
        if any(overlaps(rect, other) for other in rectangles.values()):
            raise ValueError('Overlapping macro footprints')
        if any(overlaps(rect, r) for r in target['placement_exclusions']):
            raise ValueError('Reserved corridor overlaps macro footprint')
        rectangles[n] = rect
    return dict(master=master, size_um=[width, height], pins=pins, macro_bboxes_um=rectangles,
                boundary='Proposed geometry and terminal coverage; no routed pin-access or power-continuity claim.')


def validate_terminals(module, geometry):
    expected = {}
    cell = next(c for c in module['cells'].values() if c['type'] == geometry['master'])
    for name, bits in cell['connections'].items():
        for index in range(len(bits)):
            pin = f'{name}[{index}]' if len(bits) > 1 else name
            expected[pin] = cell['port_directions'][name].upper()
    actual = {n: p['direction'] for n, p in geometry['pins'].items() if p['use'] not in ['POWER', 'GROUND']}
    if expected != actual:
        raise ValueError('LEF signal terminals differ from validated netlist')


def verify_prepared(design, root):
    """Reproduce the target's platform controls before Docker or resume."""
    design, root = Path(design), Path(root)
    inputs = read(design / 'inputs.json')
    if not inputs.get('physical_target'):
        return
    info = inputs['physical_target']
    for p, digest in info['platform_sha256'].items():
        if sha(root / p) != digest:
            raise ValueError('Changed target platform: ' + p)
    target = declaration(design / 'target.json')
    if sha(design / 'target.json') != info['declaration_sha256']:
        raise ValueError('Changed prepared target declaration')
    if read(design / 'core.json') != configuration(read(root / 'physical/chip.json'), target):
        raise ValueError('Prepared target configuration differs from its contract')
    if sha(design / 'core.sdc') != info['platform_sha256']['physical/chip.sdc']:
        raise ValueError('Changed target SDC')
