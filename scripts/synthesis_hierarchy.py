"""Explicit mapping boundaries and checked flattening for the tiled experiment.

These checks interpret mapped module connections, not gate behavior. Existing
SAT/state-projection checks still own functional equivalence. Module ownership
is retained as provenance; it is not a placement constraint.
"""
from collections import Counter
from copy import deepcopy
from dataclasses import asdict, dataclass

from mapped_physical import compare_connections

TOP = 'tt_um_pinwheel'
TILE = 'pinwheel_map_tile'


@dataclass(frozen=True)
class HierarchyPolicy:
    name: str
    rationale: str
    flatten_before_mapping: bool
    keep_modules: tuple
    retained_instances: tuple

    def mapping_commands(self):
        return [f'setattr -mod -set keep_hierarchy 1 {name}' for name in self.keep_modules] + [
            f'synth -top {TOP} -noabc' + (' -flatten' if self.flatten_before_mapping else '')]

    def flatten_commands(self):
        return [f'setattr -mod -unset keep_hierarchy {name}' for name in self.keep_modules] + [
            f'hierarchy -check -top {TOP}', 'flatten', 'clean', 'check -assert']

    def describe(self):
        return asdict(self)


def tiled_policy(variant, organization, manifest):
    if variant not in ('baseline', 'tiled', 'tiled-flat') or organization not in ('separate', 'combined'):
        raise ValueError('Unknown tiled hierarchy policy')
    if variant != 'tiled':
        return HierarchyPolicy('flat', 'Optimize all available logic together before mapping.', True, (), ())
    tiles = tuple(sorted(('controller.map.' + tile['name'], TILE) for tile in manifest['tiles']))
    if organization == 'combined':
        return HierarchyPolicy('storage-tiles',
            'Retain storage ownership while optimizing controller and selection together.',
            True, (TILE,), tiles)
    wrappers = (('controller', 'pinwheel_sram_controller'),
                ('controller.engine', 'pinwheel_tiled_chip_logic'),
                ('controller.map', 'pinwheel_map_tiled'),
                ('controller.map.glue', 'pinwheel_map_glue'),
                ('memory', 'pinwheel_sram_macros'))
    return HierarchyPolicy('separate',
        'Retain the emitted controller, map, glue and storage boundaries during mapping.',
        False, (), tuple(sorted(tiles + wrappers)))


def mapped_view(data, top=TOP):
    """Expand mapped modules into named leaf pins independently of Yosys flatten.

    Port aliases are joined before assigning wire numbers. Only binary constants,
    complete input/output interfaces, acyclic hierarchy and black-box library
    leaves are supported. No logic optimization, buffering or renaming is allowed.
    """
    modules = data['modules']
    parents, cells, owners, instances = {}, {}, {}, {}

    def wire(path, bit):
        if type(bit) is int and bit >= 0:
            key = (path, bit)
        elif type(bit) is str and bit in ('0', '1'):
            key = bit
        else:
            raise ValueError('Unknown or unsupported hierarchy signal')
        parents.setdefault(key, key)
        return key

    def root(key):
        trail = []
        while parents[key] != key:
            trail.append(key)
            key = parents[key]
        for old in trail:
            parents[old] = key
        return key

    def join(left, right):
        left, right = root(left), root(right)
        if left == right:
            return
        if isinstance(left, str) and isinstance(right, str):
            raise ValueError('Conflicting constant port aliases')
        if isinstance(right, str):
            left, right = right, left
        parents[right] = left

    def blackbox(module):
        value = module.get('attributes', {}).get('blackbox', '0')
        return bool(int(value, 2) if isinstance(value, str) else int(value))

    def visit(kind, path, ancestors):
        if kind in ancestors:
            raise ValueError('Recursive mapped hierarchy')
        module = modules[kind]
        if blackbox(module) or module.get('processes') or module.get('memories'):
            raise ValueError('Require an implemented mapped module')
        for name, cell in sorted(module.get('cells', {}).items()):
            if cell['type'] == '$scopeinfo':
                if cell.get('connections'):
                    raise ValueError('Connected scope metadata')
                continue
            child_kind = cell['type']
            if child_kind not in modules or cell.get('parameters'):
                raise ValueError('Unresolved or parameterized mapped cell')
            child = modules[child_kind]
            ports = child['ports']
            if set(cell['connections']) != set(ports) or set(cell['port_directions']) != set(ports):
                raise ValueError('Incomplete hierarchy interface')
            for pin, port in ports.items():
                if (port['direction'] not in ('input', 'output') or
                        cell['port_directions'][pin] != port['direction'] or
                        len(cell['connections'][pin]) != len(port['bits'])):
                    raise ValueError('Changed hierarchy port direction or width')
            child_path = path + (name,)
            identity = '.'.join(child_path)
            if blackbox(child) and path and name.startswith('$'):
                # Pinned Yosys retains private IDs with an escaped scope prefix.
                # The independent pin comparison below must still confirm every
                # generated name and connection in the actual flattened artifact.
                identity = '$flatten' + ''.join('\\' + part + '.' for part in path) + name
            if identity in cells or identity in instances:
                raise ValueError('Ambiguous flattened instance identity')
            if blackbox(child):
                if child.get('cells') or child.get('processes') or child.get('memories'):
                    raise ValueError('Black-box leaf has an implementation')
                cells[identity] = dict(type=child_kind, port_directions=deepcopy(cell['port_directions']),
                    connections={pin: [wire(path, bit) for bit in bits]
                                 for pin, bits in cell['connections'].items()})
                owners[identity] = dict(module=kind, instance_path='.'.join(path), cell=name, type=child_kind)
            else:
                if name.startswith('$'):
                    raise ValueError('Private module instance is outside the hierarchy contract')
                instances[identity] = child_kind
                for pin, port in ports.items():
                    for inner, outer in zip(port['bits'], cell['connections'][pin]):
                        join(wire(child_path, inner), wire(path, outer))
                visit(child_kind, child_path, ancestors + (kind,))

    if top not in modules:
        raise ValueError('Missing hierarchy root')
    ports = deepcopy(modules[top]['ports'])
    for port in ports.values():
        if port['direction'] not in ('input', 'output'):
            raise ValueError('Unsupported root direction')
        port['bits'] = [wire((), bit) for bit in port['bits']]
    visit(top, (), ())
    numbers = {}

    def number(key):
        key = root(key)
        if isinstance(key, str):
            return key
        if key not in numbers:
            numbers[key] = len(numbers) + 2
        return numbers[key]

    for port in ports.values():
        port['bits'] = [number(key) for key in port['bits']]
    for cell in cells.values():
        cell['connections'] = {pin: [number(key) for key in bits]
                               for pin, bits in cell['connections'].items()}
    return dict(ports=ports, cells=cells), dict(sorted(instances.items())), dict(sorted(owners.items()))


def check_hierarchy(data, policy):
    flat, instances, _ = mapped_view(data)
    expected = dict(policy.retained_instances)
    if instances != expected:
        raise ValueError('Mapping hierarchy differs from policy: '
                         f'missing={sorted(set(expected) - set(instances))}, '
                         f'unexpected={sorted(set(instances) - set(expected))}, '
                         f'changed={sorted(p for p in expected.keys() & instances.keys() if expected[p] != instances[p])}')
    return dict(policy=policy.describe(), retained_instances=instances,
                leaf_cells=len(flat['cells']),
                leaf_cell_types=dict(sorted(Counter(c['type'] for c in flat['cells'].values()).items())))


def check_flattening(hierarchical, flattened, *, verilog_readback=False):
    """Require exact leaf identity, allowing only the declared export encoding.

    With write_verilog -norename, a private $name becomes an escaped public
    identifier. The pinned Yosys JSON writer represents its reread spelling as
    \\$name. This is a checked one-to-one name conversion, not a graph match
    that can silently accept arbitrary cell renaming.
    """
    before, _, owners = mapped_view(hierarchical)
    after, instances, _ = mapped_view(flattened)
    if instances:
        raise ValueError('Final equivalence view still contains hierarchy')
    if verilog_readback:
        names = {name: ('\\' + name if name.startswith('$') else name) for name in before['cells']}
        if len(set(names.values())) != len(names):
            raise ValueError('Ambiguous Verilog cell identity')
        before['cells'] = {names[name]: cell for name, cell in before['cells'].items()}
        owners = {names[name]: dict(owner, flattened_cell=name) for name, owner in owners.items()}
    identity = compare_connections(before, after)
    if identity['added_tie_cells']:
        raise ValueError('Flattening inserted physical tie cells')
    return dict(connection_identity=True, verilog_readback=verilog_readback,
                leaf_cells=identity['retained_cells'], leaf_owners=owners,
                scope='Exact named mapped cells and all leaf/package connections through flattening'
                      + (' and Verilog read-back' if verilog_readback else '') + '; '
                      'ownership provenance only, no placement or timing claim.')
