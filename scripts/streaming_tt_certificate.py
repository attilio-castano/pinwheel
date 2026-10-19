"""Post-physical Boolean/clock readback for the streaming TT candidate.

The final ODB-exported connectivity is the input.  Names propose a state/cell
pairing only; local functions, connected pins and all D/output roots must still
be checked.  This is a zero-delay model, separate from extracted physical STA.
"""
from collections import Counter, deque
from dataclasses import dataclass
from hashlib import sha256
from itertools import product
import json
from pathlib import Path

from streaming_mapped_liberty import (
    Cell, Library, LIBRARY_SHA256, Token, eval_boolean, group_name,
    parse_boolean, parse_document, require, scalar,
)
from streaming_mapped_netlist import Gate, bit, expand_hierarchy
from streaming_mapped_certificate import lean_expression, namespace_name, substitute, support


def read_json(path):
    path = Path(path)
    require(path.is_file() and not path.is_symlink(), 'Expected a regular actual connectivity JSON')
    before = path.read_bytes()
    def pairs(items):
        result = {}
        for key, value in items:
            require(key not in result, 'Duplicate actual connectivity JSON key')
            result[key] = value
        return result
    result = json.loads(before, object_pairs_hook=pairs)
    require(path.read_bytes() == before, 'Actual connectivity changed during read')
    return result


def read_library(path, used_cells, *, expected_sha256=LIBRARY_SHA256):
    """Interpret actual resized/tie cells from an independently selected pin.

    The old reader deliberately selected only mapping cells.  Physical tools
    may resize them or insert ties/buffers; their actual Liberty bodies are read
    here with the same strict Boolean and FF grammar, without a name-to-function
    table.  Physical-only masters are excluded from this signal model upstream.
    """
    path = Path(path)
    require(path.is_file() and not path.is_symlink(), 'Expected regular actual Liberty')
    data = path.read_bytes()
    digest = sha256(data).hexdigest()
    require(digest == expected_sha256, 'Actual physical Liberty differs from selected pin')
    roots = parse_document(data.decode('utf-8'))
    require(len(roots) == 1 and roots[0].name == 'library' and roots[0].kind == 'group',
        'Expected exactly one Liberty library')
    selected = set(used_cells)
    require(selected and all(type(name) is str and name.startswith('sg13cmos5l_') for name in selected),
        'Unsupported physical library family')
    candidates = {}
    for item in roots[0].children:
        if item.name == 'cell':
            name = group_name(item)
            require(name not in candidates, 'Duplicate Liberty cell')
            candidates[name] = item
    require(selected <= candidates.keys(), 'Actual physical cell missing from pinned Liberty')
    cells = {}
    for name in sorted(selected):
        item = candidates[name]
        require(all(child.name in ('pin', 'ff', 'leakage_power') for child in item.children
            if child.kind == 'group'), 'Unsupported functional physical Liberty group')
        pins, directions, functions = {}, {}, {}
        for pin in [child for child in item.children if child.name == 'pin']:
            pin_name = group_name(pin)
            require(pin_name not in pins, 'Duplicate physical Liberty pin')
            pins[pin_name] = pin
            direction = scalar(pin.children, 'direction')
            require(direction in ('input', 'output'), 'Unsupported physical signal pin')
            require(not any(child.name in ('three_state', 'state_function') for child in pin.children),
                'Unsupported three-state/state output')
            require(all(child.name in ('timing', 'internal_power') for child in pin.children
                if child.kind == 'group'), 'Unsupported physical pin functional group')
            directions[pin_name] = direction
            if direction == 'output': functions[pin_name] = scalar(pin.children, 'function')
            else: require(scalar(pin.children, 'function', required=False) is None,
                'Physical input has a function')
        ff = [child for child in item.children if child.name == 'ff']
        if not functions:
            require(not ff and directions and all(direction=='input' for direction in directions.values()) and
                all(scalar(pin.children,'clock',required=False) is None for pin in pins.values()),
                'A passive physical load may not hide state, a clock, or an output')
            cells[name]=Cell(name,directions,'','',('constant',False))
            continue
        require(len(functions) == 1, 'Exactly one actual Boolean output is required')
        output, function_text = next(iter(functions.items()))
        if ff:
            require(len(ff) == 1 and ff[0].kind == 'group' and ff[0].arguments ==
                ((Token('IQ'),), (Token('IQN'),)), 'Unsupported physical FF state')
            require(directions == dict(Q='output', CLK='input', D='input', RESET_B='input') and output == 'Q',
                'Unsupported physical FF pin inventory')
            require({child.name for child in ff[0].children} == {'clear', 'clocked_on', 'next_state'},
                'Unsupported physical sequential controls')
            clock = parse_boolean(scalar(ff[0].children, 'clocked_on'), {'CLK'})
            next_state = parse_boolean(scalar(ff[0].children, 'next_state'), {'D'})
            clear = parse_boolean(scalar(ff[0].children, 'clear'), {'RESET_B'})
            require(clock == ('variable', 'CLK') and next_state == ('variable', 'D') and
                clear == ('not', ('variable', 'RESET_B')) and function_text == 'IQ',
                'Changed physical FF edge/data/asynchronous behavior')
            require(scalar(pins['CLK'].children, 'clock') == 'true' and all(
                scalar(pin.children, 'clock', required=False) is None
                for key, pin in pins.items() if key != 'CLK'), 'Unsupported FF clock declaration')
            cells[name] = Cell(name, directions, output, function_text,
                parse_boolean(function_text, {'IQ'}), True, ('IQ', 'IQN'), clock, next_state, clear)
        else:
            require(all(scalar(pin.children, 'clock', required=False) is None for pin in pins.values()),
                'Combinational physical cell has clock/state behavior')
            inputs = {pin for pin, direction in directions.items() if direction == 'input'}
            cells[name] = Cell(name, directions, output, function_text, parse_boolean(function_text, inputs))
    require(path.read_bytes() == data, 'Actual physical Liberty changed during interpretation')
    return Library(digest, cells, True)


def read_corners(corners, used_cells, *, nominal='typ'):
    """Require the actual Boolean/sequential interpretation at every corner."""
    require(type(corners) is dict and set(corners)=={'slow','typ','fast'},
        'Exactly the three selected physical corners are required')
    libraries={};records={}
    for name,record in corners.items():
        require(type(record) is dict and set(record)=={'path','sha256'},'Unpinned physical corner')
        libraries[name]=read_library(record['path'],used_cells,expected_sha256=record['sha256'])
        records[name]=dict(path=str(Path(record['path']).resolve()),sha256=libraries[name].sha256)
    def signature(cell):
        return (cell.directions,cell.output,cell.function,cell.sequential,
            cell.state_names,cell.clocked_on,cell.next_state,cell.clear)
    require(nominal in libraries,'Missing nominal functional library')
    reference=libraries[nominal]
    for name,library in libraries.items():
        require(library.cells.keys()==reference.cells.keys() and all(signature(library.cells[cell])==
            signature(reference.cells[cell]) for cell in reference.cells),
            'Actual used-cell Boolean/sequential function changes across corners: '+name)
    return reference,dict(corners=records,used_cells=sorted(reference.cells),
        all_corner_functions_equal=True,
        boundary='Boolean/state functions only; capacitance, delays and electrical signoff are separate.')


@dataclass(frozen=True)
class PhysicalFF:
    name: str
    cell: str
    d: int | str
    q: int
    clock: int | str
    reset_b: int | str


@dataclass(frozen=True)
class PhysicalGraph:
    top: str
    library: Library
    inputs: dict
    outputs: dict
    clock: int
    gates: tuple
    flipflops: tuple
    counts: dict
    passive_loads: tuple = ()


def parse_graph(document, top, library):
    require(type(library) is Library and library.pinned, 'Selected actual Liberty is required')
    data = expand_hierarchy(document, top, library)
    module = data['modules'][top]
    require(not module.get('processes') and not module.get('memories'), 'Unlowered physical behavior')
    inputs, outputs = {}, {}
    for name, port in module.get('ports', {}).items():
        require(type(name) is str and port.get('direction') in ('input', 'output') and
            type(port.get('bits')) is list and port['bits'] and
            port.get('upto', 0) == 0 and port.get('offset', 0) == 0, 'Unsupported physical public port')
        (inputs if port['direction'] == 'input' else outputs)[name] = tuple(bit(wire) for wire in port['bits'])
    require('clk' in inputs and len(inputs['clk']) == 1 and type(inputs['clk'][0]) is int,
        'One scalar physical top clock is required')
    primary = [wire for wires in inputs.values() for wire in wires]
    require(all(type(wire) is int for wire in primary) and len(primary) == len(set(primary)),
        'Physical primary inputs are constant/aliased')
    primary, clock = set(primary), inputs['clk'][0]
    drivers, gates, flops, loads, counts = {}, {}, [], [], Counter()
    for name, cell in module.get('cells', {}).items():
        kind = cell.get('type')
        if kind == '$scopeinfo':
            require(cell.get('connections') == {} and cell.get('port_directions') == {},
                'Physical metadata has functional connections')
            continue
        require(kind in library.cells and cell.get('parameters') == {}, 'Unknown or parameterized physical cell')
        model = library.cells[kind]
        require(cell.get('port_directions') == model.directions and
            set(cell.get('connections', {})) == set(model.directions) and
            all(type(wires) is list and len(wires) == 1 for wires in cell['connections'].values()),
            'Physical cell pins differ from actual Liberty')
        connections = {pin: bit(wires[0]) for pin, wires in cell['connections'].items()}
        counts[kind] += 1
        if not model.output:
            require(not model.sequential and all(value=='input' for value in model.directions.values()),
                'Unclassified non-output physical cell')
            loads.append((name,kind,connections))
            continue
        out = connections[model.output]
        require(type(out) is int and out not in primary and out not in drivers,
            'Multiple/constant/input-alias physical driver')
        drivers[out] = name
        if model.sequential:
            flops.append(PhysicalFF(name, kind, connections['D'], out, connections['CLK'], connections['RESET_B']))
        else:
            gates[name] = Gate(name, kind, connections, out)
    require(gates and flops, 'Expected actual logic and full physical state')
    q = {ff.q for ff in flops}
    require(len(q) == len(flops), 'Aliased physical FF Q state')
    known = primary | q
    def driven(wire): return wire in ('0', '1') if type(wire) is str else wire in known or wire in drivers
    for gate in gates.values():
        model = library.cells[gate.cell]
        require(all(driven(wire) for pin, wire in gate.connections.items() if model.directions[pin] == 'input'),
            'Undriven physical cell input')
    require(all(driven(wire) for ff in flops for wire in (ff.d, ff.clock, ff.reset_b)),
        'Undriven physical FF pin')
    require(all(driven(wire) for _,_,connections in loads for wire in connections.values()),
        'Undriven actual passive-load pin')
    require(all(driven(wire) for wires in outputs.values() for wire in wires), 'Undriven physical public output')
    by_output = {gate.output: name for name, gate in gates.items()}
    missing, successors = {}, {name: set() for name in gates}
    for name, gate in gates.items():
        model = library.cells[gate.cell]
        parents = {by_output[wire] for pin, wire in gate.connections.items()
            if model.directions[pin] == 'input' and type(wire) is int and wire in by_output}
        missing[name] = len(parents)
        for parent in parents: successors[parent].add(name)
    ready, ordered = deque(sorted(name for name in gates if not missing[name])), []
    while ready:
        name = ready.popleft(); ordered.append(gates[name])
        for child in sorted(successors[name]):
            missing[child] -= 1
            if not missing[child]: ready.append(child)
    require(len(ordered) == len(gates), 'Physical combinational cycle')
    return PhysicalGraph(top, library, inputs, outputs, clock, tuple(ordered), tuple(flops),
        dict(sorted(counts.items())),tuple(loads))


def clock_cones(graph):
    """Read every FF CLK/reset cone, refusing data-driven or negative clocks."""
    by_output = {gate.output: gate for gate in graph.gates}
    memo, active = {}, set()
    def cone(wire):
        if type(wire) is str: return ('constant', wire == '1')
        if wire == graph.clock: return ('variable', 'clk')
        if wire in memo: return memo[wire]
        require(wire in by_output and wire not in active, 'FF clock/reset is data-driven, undriven or cyclic')
        active.add(wire)
        gate, cell = by_output[wire], graph.library.cells[by_output[wire].cell]
        value = substitute(cell.function, {pin: cone(source) for pin, source in gate.connections.items()
            if cell.directions[pin] == 'input'})
        active.remove(wire); memo[wire] = value
        return value
    dependent = {graph.clock}
    for gate in graph.gates:
        cell = graph.library.cells[gate.cell]
        if any(wire in dependent for pin, wire in gate.connections.items()
                if cell.directions[pin] == 'input'):
            dependent.add(gate.output)
    require(all(ff.d not in dependent for ff in graph.flipflops) and
        all(wire not in dependent for wires in graph.outputs.values() for wire in wires),
        'Physical clock enters data or public outputs')
    roots = {}
    for ff in graph.flipflops:
        expression, reset = cone(ff.clock), cone(ff.reset_b)
        require([eval_boolean(expression, {'clk': value}) for value in (False, True)] == [False, True],
            'Physical FF clock is not positive top-clock identity')
        require(all(eval_boolean(reset, {'clk': value}) for value in (False, True)),
            'Physical FF asynchronous reset is not inactive')
        require(not support(reset), 'Clock-dependent asynchronous reset is forbidden')
        roots[ff.name] = (expression, reset)
    return roots


def clock_source(graph, *, namespace, netlist_sha256, state_order=None):
    namespace_name(namespace)
    require(type(netlist_sha256) is str and len(netlist_sha256) == 64, 'Missing actual physical netlist hash')
    roots = clock_cones(graph)
    if state_order is None:state_order=tuple(sorted(roots))
    require(type(state_order) is tuple and len(state_order)==len(set(state_order)) and
        set(state_order)==set(roots),'Clock table does not cover every actual FF exactly once')
    expressions,indices,resets,reset_indices=[],{},[],{}
    for expression,reset in roots.values():
        if expression not in indices:indices[expression]=len(expressions);expressions.append(expression)
        if reset not in reset_indices:reset_indices[reset]=len(resets);resets.append(reset)
    lines=['import Pinwheel.Hardware.StreamingPhysical.Clock','',f'namespace {namespace}',
        'open Pinwheel.Hardware.StreamingMapped Pinwheel.Hardware.StreamingPhysical',
        'set_option maxRecDepth 100000', 'set_option maxHeartbeats 8000000',
        f'def netlistSHA256 : String := "{netlist_sha256}"',
        f'def libertySHA256 : String := "{graph.library.sha256}"']
    for index,expression in enumerate(expressions):
        lines += [f'def clock{index} : Expr 1 := {lean_expression(expression,("clk",))}',
            f'theorem clock{index}_positive : PositiveClock clock{index} :=',
            '  ⟨by decide +kernel, by decide +kernel⟩']
    for index,expression in enumerate(resets):
        lines += [f'def reset{index} : Expr 1 := {lean_expression(expression,("clk",))}',
            f'theorem reset{index}_inactive : InactiveReset reset{index} :=',
            '  ⟨by decide +kernel, by decide +kernel⟩']
    from streaming_tt_graph import lookup_source
    count=len(roots)
    for name,values in [('stateClock',['clock'+str(indices[roots[ff][0]]) for ff in state_order]),
            ('stateReset',['reset'+str(reset_indices[roots[ff][1]]) for ff in state_order])]:
        if len(set(values))==1:lines += [f'def {name} (_ : Fin {count}) : Expr 1 := '+values[0]]
        else:
            lines += [lookup_source(name+'Table',values,result_type='Expr 1',default=values[0]),
                f'def {name} (index : Fin {count}) : Expr 1 := {name}Table index.val']
    clock_levels='by intro index; exact ⟨rfl,rfl⟩' if len(expressions)==1 else 'by decide +kernel'
    reset_levels='by intro index; exact ⟨rfl,rfl⟩' if len(resets)==1 else 'by decide +kernel'
    lines += [f'theorem allClockLevels : ∀ index : Fin {count}, ClockLevel (stateClock index) false = false ∧ ClockLevel (stateClock index) true = true := {clock_levels}',
        f'theorem allResetLevels : ∀ index : Fin {count}, ClockLevel (stateReset index) false = true ∧ ClockLevel (stateReset index) true = true := {reset_levels}',
        f'def clocking : Clocking {count} := ⟨stateClock,stateReset,',
        '  (fun index => ⟨(allClockLevels index).1,(allClockLevels index).2⟩),',
        '  (fun index => ⟨(allResetLevels index).1,(allResetLevels index).2⟩)⟩',
        f'def stateClockCount : Nat := {count}',f'end {namespace}','']
    return '\n'.join(lines),dict(ff_clocks=count,distinct_clock_expressions=len(expressions),
        distinct_reset_expressions=len(resets),ff_order=state_order,
        ff_clock_indices={name:indices[roots[name][0]] for name in state_order},
        ff_reset_indices={name:reset_indices[roots[name][1]] for name in state_order},
        all_positive_top_clock=True,all_asynchronous_resets_inactive=True)


def instance_label(name):
    """A pairing hint only. Every proposed pair still has D/function checks."""
    try: parts=json.loads(name)
    except (ValueError,TypeError): parts=[name]
    if type(parts) is not list or not all(type(part) is str for part in parts): parts=[name]
    return '/'.join(parts).replace('.', '/')


def data_model(graph, *, state_labels=None, state_order=None):
    clock_cones(graph)
    flops={}
    for ff in graph.flipflops:
        label=instance_label(ff.name) if state_labels is None else state_labels[ff.name]
        require(type(label) is str and label and label not in flops,'Ambiguous physical state pairing')
        flops[label]=ff
    if state_order is None:state_order=tuple(sorted(flops))
    require(type(state_order) is tuple and len(state_order)==len(set(state_order)) and
        set(state_order)==set(flops),'Physical state order is not a complete bijection')
    labels=[('input',port,index) for port in sorted(graph.inputs) if port!='clk'
        for index in range(len(graph.inputs[port]))]
    labels += [('state',label) for label in state_order]
    wires={graph.inputs[port][index]:at for at,(_,port,index) in enumerate(labels[:len(labels)-len(flops)])}
    for at,label in enumerate(state_order,start=len(labels)-len(flops)):wires[flops[label].q]=at
    dependent={graph.clock};nodes=[]
    for gate in graph.gates:
        cell=graph.library.cells[gate.cell]
        pins=sorted(pin for pin,direction in cell.directions.items() if direction=='input')
        if any(gate.connections[pin] in dependent for pin in pins):
            dependent.add(gate.output);continue
        sources=tuple(dict.fromkeys(gate.connections[pin] for pin in pins if type(gate.connections[pin]) is int))
        require(all(source in wires for source in sources),'Physical data source unavailable after clock separation')
        expression=substitute(cell.function,{pin:('constant',gate.connections[pin]=='1')
            if type(gate.connections[pin]) is str else ('variable','p'+str(sources.index(gate.connections[pin])))
            for pin in pins})
        nodes.append(dict(name=gate.name,cell=gate.cell,sources=tuple(wires[source] for source in sources),
            expression=expression))
        wires[gate.output]=len(labels)+len(nodes)-1
    def root(wire):
        if type(wire) is str:return ('constant',wire=='1')
        require(wire in wires,'Missing final physical D/output root')
        return ('wire',wires[wire],False)
    return dict(labels=tuple(labels),nodes=tuple(nodes),
        next={label:root(flops[label].d) for label in state_order},
        outputs={port:tuple(root(wire) for wire in graph.outputs[port]) for port in sorted(graph.outputs)},
        clock_separated_nodes=len(graph.gates)-len(nodes))


def combinational_model(graph):
    require(graph.clock_bit is None and not graph.flipflops,'Expected actual combinational word body')
    labels=[('input',port,index) for port in sorted(graph.inputs) for index in range(len(graph.inputs[port]))]
    wires={graph.inputs[port][index]:at for at,(_,port,index) in enumerate(labels)};nodes=[]
    for gate in graph.gates:
        cell=graph.library.cells[gate.cell];pins=sorted(pin for pin,direction in cell.directions.items() if direction=='input')
        sources=tuple(dict.fromkeys(gate.connections[pin] for pin in pins if type(gate.connections[pin]) is int))
        require(all(source in wires for source in sources),'Unavailable actual word input')
        expression=substitute(cell.function,{pin:('constant',gate.connections[pin]=='1')
            if type(gate.connections[pin]) is str else ('variable','p'+str(sources.index(gate.connections[pin]))) for pin in pins})
        nodes.append(dict(name=gate.name,cell=gate.cell,sources=tuple(wires[source] for source in sources),expression=expression))
        wires[gate.output]=len(labels)+len(nodes)-1
    def root(wire):return ('constant',wire=='1') if type(wire) is str else ('wire',wires[wire],False)
    return dict(labels=tuple(labels),nodes=tuple(nodes),next={},outputs={port:tuple(root(wire) for wire in bits)
        for port,bits in graph.outputs.items()},clock_separated_nodes=0)


def atom_expression(atom):
    if atom[0]=='constant':return atom
    require(atom[0]=='wire' and type(atom[1]) is int and atom[1]>=0 and type(atom[2]) is bool,'Malformed wire atom')
    value=('variable','w'+str(atom[1]))
    return ('not',value) if atom[2] else value


def expression_signature(expression):
    names=tuple(sorted(support(expression),key=lambda name:int(name[1:])))
    require(len(names)<=6,'Local physical cell exceeds six independent Boolean sources')
    truth=tuple(eval_boolean(expression,dict(zip(names,values))) for values in product((False,True),repeat=len(names)))
    return names,truth


def projection(expression):
    names,truth=expression_signature(expression)
    if all(value==truth[0] for value in truth):return ('constant',truth[0])
    for at,name in enumerate(names):
        column=tuple(values[at] for values in product((False,True),repeat=len(names)))
        if truth==column:return ('wire',int(name[1:]),False)
        if truth==tuple(not value for value in column):return ('wire',int(name[1:]),True)
    return None


def normalized_expression(node,image):
    return substitute(node['expression'],{'p'+str(at):atom_expression(image[source])
        for at,source in enumerate(node['sources'])})


def rename_atom(atom,image):
    if atom[0]=='constant':return atom
    mapped=image[atom[1]]
    if not atom[2]:return mapped
    return ('constant',not mapped[1]) if mapped[0]=='constant' else ('wire',mapped[1],not mapped[2])


def canonical_model(model):
    """Propose only finite local identities; emitted Lean proves each rule."""
    base=len(model['labels']);image=[('wire',index,False) for index in range(base)]
    nodes,registry,rules=[],{},[]
    for node in model['nodes']:
        actual=normalized_expression(node,image);simple=projection(actual)
        if simple is not None:
            image.append(simple);rules.append(dict(kind='transport',actual=actual,expected=atom_expression(simple)))
            continue
        signature=expression_signature(actual)
        if signature not in registry:
            selected=len(nodes);registry[signature]=selected
            names=signature[0]
            nodes.append(dict(name=node['name'],cell=node['cell'],sources=tuple(int(name[1:]) for name in names),
                expression=substitute(actual,{name:('variable','p'+str(at)) for at,name in enumerate(names)})))
        selected=registry[signature]
        expected=substitute(nodes[selected]['expression'],{'p'+str(at):('variable','w'+str(source))
            for at,source in enumerate(nodes[selected]['sources'])})
        image.append(('wire',base+selected,False));rules.append(dict(kind='cell',selected=selected,
            actual=actual,expected=expected))
    return dict(labels=model['labels'],nodes=tuple(nodes),registry=registry,image=tuple(image),rules=tuple(rules),
        next={name:rename_atom(atom,image) for name,atom in model['next'].items()},
        outputs={name:tuple(rename_atom(atom,image) for atom in atoms) for name,atoms in model['outputs'].items()})


def contract_model(model,reference):
    require(model['labels']==reference['labels'],'Physical primary/full-state bijection changed')
    base=len(model['labels']);image=[('wire',index,False) for index in range(base)];rules=[]
    for node in model['nodes']:
        actual=normalized_expression(node,image);simple=projection(actual)
        if simple is not None:
            image.append(simple);rules.append(dict(kind='transport',actual=actual,expected=atom_expression(simple)))
            continue
        signature=expression_signature(actual)
        require(signature in reference['registry'],'Physical logic has no certified local reference function: '+node['name'])
        selected=reference['registry'][signature];target=reference['nodes'][selected]
        expected=substitute(target['expression'],{'p'+str(at):('variable','w'+str(source))
            for at,source in enumerate(target['sources'])})
        image.append(('wire',base+selected,False));rules.append(dict(kind='cell',selected=selected,
            actual=actual,expected=expected))
    require(model['next'].keys()==reference['next'].keys() and
        all(rename_atom(atom,image)==reference['next'][name] for name,atom in model['next'].items()),
        'Final physical FF D function/root changed')
    require(model['outputs'].keys()==reference['outputs'].keys() and
        all(tuple(rename_atom(atom,image) for atom in atoms)==reference['outputs'][name]
            for name,atoms in model['outputs'].items()),'Final physical public output function/root changed')
    return dict(image=tuple(image),rules=tuple(rules),full_state_bits=len(model['next']),
        all_d_roots_matched=True,all_public_roots_matched=True)
