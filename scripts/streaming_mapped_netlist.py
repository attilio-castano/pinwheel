"""Strict single-clock Boolean graph interpreter for the selected mapped cells.

No equivalence claim is made. Liberty interpretation and JSON parsing remain
explicit trust boundaries until a later kernel certificate checks their graph.
Netname metadata never supplies functional logic or state.
"""
from collections import Counter, deque
from dataclasses import dataclass
import json
from pathlib import Path

from streaming_mapped_liberty import FF, Library, eval_boolean, require


def bit(value):
    require(type(value) is int and value >= 0 or type(value) is str and value in ('0', '1'),
        'Unsupported functional bit, X/Z or alias token')
    return value


@dataclass(frozen=True)
class Gate:
    name: str
    cell: str
    connections: dict
    output: int


@dataclass(frozen=True)
class FlipFlop:
    name: str
    cell: str
    d: int | str
    q: int
    clock: int
    reset_b: str = '1'


@dataclass(frozen=True)
class MappedGraph:
    top: str
    library: Library
    inputs: dict
    outputs: dict
    clock_bit: int | None
    gates: tuple
    flipflops: tuple
    cell_counts: dict
    metadata_cells: int

    @property
    def input_bits(self):
        return frozenset(value for name, values in self.inputs.items() if name != 'clk' for value in values)

    @property
    def state_bits(self): return frozenset(ff.q for ff in self.flipflops)


def expand_hierarchy(data, top, library):
    """Reconstruct every instantiated module, preserving actual port aliases.

    Module names and synthesis attributes never supply a Boolean function.
    Only selected pinned-library cells terminate expansion. This is a strict
    structural interpretation, not a claim that synthesis preserved a source.
    """
    require(type(data) is dict and type(data.get('modules')) is dict and top in data['modules'],
        'Missing selected mapped hierarchy')
    modules, parents, next_bit, cells = data['modules'], {}, 2, {}
    top_module = modules[top]
    require(type(top_module) is dict, 'Malformed mapped top module')
    def find(value):
        if value not in parents: parents[value] = value
        path = []
        while parents[value] != value: path.append(value); value = parents[value]
        for entry in path: parents[entry] = value
        return value
    def union(left, right):
        left, right = find(left), find(right)
        if left == right: return
        require(not (type(left) is str and type(right) is str), 'Hierarchy shorts opposite constants')
        if type(right) is str or type(left) is int and type(right) is int and right < left:
            left, right = right, left
        parents[right] = left
    def active_attribute(attributes, name):
        value = attributes.get(name, 0)
        require(type(value) in (int, str), 'Unsupported module attribute')
        if type(value) is str:
            require(value and set(value) <= {'0', '1'}, 'Unsupported module attribute encoding')
            value = int(value, 2)
        return value != 0
    def visit(name, path, bindings, ancestors):
        nonlocal next_bit
        require(name not in ancestors and name in modules, 'Recursive or unknown mapped module')
        module = modules[name]
        require(type(module) is dict and not module.get('processes') and not module.get('memories') and
            not module.get('parameter_default_values'), 'Behavioral or parameterized hierarchy module')
        attributes = module.get('attributes', {})
        require(type(attributes) is dict and not any(active_attribute(attributes, key)
            for key in ('blackbox', 'whitebox')), 'Uninterpreted blackbox or whitebox hierarchy')
        ports = module.get('ports')
        require(type(ports) is dict and ports, 'Missing hierarchy module ports')
        local = {}
        def wire(value):
            nonlocal next_bit
            value = bit(value)
            if type(value) is str: return value
            if value not in local:
                local[value] = value if not path else next_bit
                next_bit = max(next_bit + bool(path), value + 1 if not path else next_bit)
                find(local[value])
            return local[value]
        formal_inputs = []
        for pin, port in ports.items():
            require(type(pin) is str and type(port) is dict and port.get('direction') in ('input', 'output') and
                type(port.get('bits')) is list and port['bits'], 'Unsupported hierarchy port')
            values = [wire(value) for value in port['bits']]
            if port['direction'] == 'input':
                require(all(type(value) is int for value in values), 'Constant hierarchy input')
                formal_inputs.extend(values)
            if bindings is not None:
                require(pin in bindings and len(bindings[pin]) == len(values), 'Resized hierarchy port')
                for internal, external in zip(values, bindings[pin]): union(internal, external)
        require(len(formal_inputs) == len(set(formal_inputs)), 'Aliased hierarchy formal inputs')
        if bindings is not None: require(set(bindings) == set(ports), 'Missing or extra hierarchy pins')
        body = module.get('cells', {})
        require(type(body) is dict, 'Malformed hierarchy cell inventory')
        # Allocate all local IDs before descending so child allocation cannot
        # collide with a later parent wire whose JSON number is larger.
        for value in body.values():
            require(type(value) is dict and type(value.get('connections')) is dict, 'Malformed hierarchy instance')
            for values in value['connections'].values():
                require(type(values) is list and values, 'Empty hierarchy connection')
                for item in values: wire(item)
        for instance, value in body.items():
            require(type(instance) is str, 'Invalid hierarchy instance name')
            kind = value.get('type')
            connections = {pin: [wire(item) for item in values] for pin, values in value['connections'].items()}
            key = json.dumps((*path, instance), separators=(',', ':'))
            require(key not in cells, 'Ambiguous hierarchy instance path')
            if kind in library.cells or kind == '$scopeinfo':
                cells[key] = {**value, 'connections': connections}
            else:
                require(type(kind) is str and kind in modules and value.get('parameters') == {},
                    'Unknown or parameterized hierarchy instance')
                child_ports = modules[kind].get('ports', {})
                require(value.get('port_directions') == {pin: port.get('direction') for pin, port in child_ports.items()},
                    'Hierarchy instance directions differ from actual module')
                visit(kind, (*path, instance), connections, (*ancestors, name))
        return local
    # Reserve the entire top namespace before allocating any child-local wire.
    top_bits = [item for value in top_module.get('ports', {}).values() for item in value.get('bits', [])]
    top_bits += [item for value in top_module.get('cells', {}).values()
        for values in value.get('connections', {}).values() for item in values]
    next_bit = max([1, *(item for item in top_bits if type(item) is int)]) + 1
    local = visit(top, (), None, ())
    def resolved(value): return find(value) if type(value) is int else value
    flat_ports = {name: {**port, 'bits': [resolved(local[value]) if type(value) is int else bit(value)
        for value in port['bits']]} for name, port in top_module['ports'].items()}
    flat_cells = {name: {**value, 'connections': {pin: [resolved(item) for item in values]
        for pin, values in value['connections'].items()}} for name, value in cells.items()}
    netnames = {name: {**value, 'bits': [resolved(local[item]) if type(item) is int and item in local else item
        for item in value.get('bits', [])]} for name, value in top_module.get('netnames', {}).items()}
    return dict(modules={top: dict(ports=flat_ports, cells=flat_cells, netnames=netnames)})


def parse_mapped(data, top, library, *, combinational=False):
    require(type(library) is Library and type(data) is dict and type(top) is str,
        'Expected explicit mapped JSON, top and parsed Liberty')
    modules = data.get('modules', {})
    require(type(modules) is dict and top in modules, 'Missing selected mapped top')
    data = expand_hierarchy(data, top, library)
    module = data['modules'][top]
    require(type(module) is dict and not module.get('processes') and not module.get('memories'),
        'Unsupported behavioral process or memory in mapped top')
    ports = module.get('ports', {})
    require(type(ports) is dict and ports, 'Missing mapped public port inventory')
    inputs, outputs = {}, {}
    for name, port in ports.items():
        require(type(name) is str and type(port) is dict and port.get('direction') in ('input', 'output') and
            type(port.get('bits')) is list and port['bits'], 'Unsupported public port')
        values = tuple(bit(value) for value in port['bits'])
        (inputs if port['direction'] == 'input' else outputs)[name] = values
    require(type(combinational) is bool, 'Expected explicit graph kind')
    require(combinational or 'clk' in inputs and len(inputs['clk']) == 1 and type(inputs['clk'][0]) is int,
        'One direct scalar top-level clk is required')
    require(not combinational or 'clk' not in inputs, 'Combinational leaf cannot declare a clock')
    clock = None if combinational else inputs['clk'][0]
    primary = [value for values in inputs.values() for value in values]
    require(all(type(value) is int for value in primary) and len(primary) == len(set(primary)),
        'Aliased, constant or ambiguous primary input bits')
    primary = set(primary)
    cells = module.get('cells', {})
    require(type(cells) is dict and cells, 'Missing mapped cell inventory')
    gates, flops, drivers, counts, metadata = {}, [], {}, Counter(), 0
    for name, value in cells.items():
        require(type(value) is dict, 'Malformed mapped cell')
        kind = value.get('type')
        if kind == '$scopeinfo':
            require(value.get('connections') == {} and value.get('port_directions') == {},
                'Scope metadata has functional connections')
            metadata += 1
            continue
        require(kind in library.cells and value.get('parameters') == {},
            'Unsupported cell or functional parameter override')
        model = library.cells[kind]
        connections, directions = value.get('connections'), value.get('port_directions')
        require(type(connections) is dict and directions == model.directions and
            set(connections) == set(model.directions), 'Mapped pins/directions differ from actual Liberty')
        require(all(type(bits) is list and len(bits) == 1 for bits in connections.values()),
            'Mapped scalar cell has missing or resized pins')
        connections = {pin: bit(bits[0]) for pin, bits in connections.items()}
        out = connections[model.output]
        require(type(out) is int and out not in primary and out not in drivers,
            'Constant, input-alias or multiple functional output drivers')
        drivers[out] = name
        counts[kind] += 1
        if model.sequential:
            require(not combinational and kind == FF and connections['CLK'] == clock and connections['RESET_B'] == '1' and
                connections['D'] != clock, 'Unsupported FF clock, asynchronous reset or clock-as-data')
            flops.append(FlipFlop(name, kind, connections['D'], out, clock))
        else:
            require(clock not in connections.values(), 'Raw clock enters combinational logic')
            gates[name] = Gate(name, kind, connections, out)
    require(gates and (combinational or flops), 'Expected combinational logic and explicit FF state for a clocked graph')
    q_bits = {ff.q for ff in flops}
    require(len(q_bits) == len(flops), 'Aliased physical FF Q roots')
    known = primary | q_bits
    def supported_source(value):
        return value in ('0', '1') if type(value) is str else value in known or value in drivers
    for gate in gates.values():
        model = library.cells[gate.cell]
        require(all(supported_source(value) for pin, value in gate.connections.items()
            if model.directions[pin] == 'input'), 'Undriven combinational pin')
    require(all(supported_source(ff.d) for ff in flops), 'Undriven FF data')
    require(all(supported_source(value) and value != clock for values in outputs.values() for value in values),
        'Undriven or direct-clock public output')
    by_output = {gate.output: name for name, gate in gates.items()}
    successors, missing = {name: set() for name in gates}, {}
    for name, gate in gates.items():
        model = library.cells[gate.cell]
        parents = {by_output[value] for pin, value in gate.connections.items()
            if model.directions[pin] == 'input' and type(value) is int and value in by_output}
        missing[name] = len(parents)
        for parent in parents: successors[parent].add(name)
    ready, ordered = deque(sorted(name for name in gates if not missing[name])), []
    while ready:
        name = ready.popleft(); ordered.append(gates[name])
        for successor in sorted(successors[name]):
            missing[successor] -= 1
            if not missing[successor]: ready.append(successor)
    require(len(ordered) == len(gates), 'Combinational cycle in mapped graph')
    return MappedGraph(top, library, inputs, outputs, clock, tuple(ordered), tuple(flops),
        dict(sorted(counts.items())), metadata)


def load_mapped(path, top, library, *, combinational=False):
    """Read an exact regular JSON file, refusing duplicate object keys."""
    path = Path(path)
    require(path.is_file() and not path.is_symlink(), 'Expected a regular mapped JSON file')
    def pairs(items):
        result = {}
        for key, value in items:
            require(key not in result, 'Duplicate mapped JSON key')
            result[key] = value
        return result
    return parse_mapped(json.loads(path.read_text(), object_pairs_hook=pairs), top, library, combinational=combinational)


def evaluate_graph(graph, inputs, state):
    """One simultaneous positive clock edge; pins and FF Qs are explicit Booleans.

    Inputs are keyed by every nonclock primary bit ID; state by every physical
    Q bit ID. Outputs are pre-edge combinational vectors in JSON LSB-first order.
    The clock is an event, not a data input. No initialization is presumed.
    """
    require(type(graph) is MappedGraph and type(inputs) is dict and type(state) is dict and
        inputs.keys() == graph.input_bits and state.keys() == graph.state_bits,
        'Incomplete or extra mapped input/state bit assignment')
    require(all(type(value) is bool for value in [*inputs.values(), *state.values()]),
        'Mapped inputs and Q state must be explicit Booleans')
    values = {**inputs, **state, graph.clock_bit: True}
    def read(value): return value == '1' if type(value) is str else values[value]
    for gate in graph.gates:
        model = graph.library.cells[gate.cell]
        pins = {pin: read(value) for pin, value in gate.connections.items() if model.directions[pin] == 'input'}
        values[gate.output] = eval_boolean(model.function, pins)
    return dict(next_state={ff.q: read(ff.d) for ff in graph.flipflops},
        outputs={name: tuple(read(value) for value in bits) for name, bits in graph.outputs.items()})
