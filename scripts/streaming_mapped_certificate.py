"""Kernel-checkable Boolean leaves from actual mapped JSON and Liberty.

The restricted parsers are explicit trust boundaries. These exports certify
the interpreted leaf, not preservation by ABC/Yosys or a whole RTL circuit.
No synthesis operation, solver result or module name supplies its function.
"""
from hashlib import sha256
import json
from pathlib import Path
import re

from streaming_mapped_liberty import Library, eval_boolean, require
from streaming_mapped_netlist import MappedGraph, load_mapped


def substitute(node, values):
    kind = node[0]
    if kind == 'constant': return node
    if kind == 'variable': return values[node[1]]
    if kind == 'not': return ('not', substitute(node[1], values))
    require(kind in ('*', '+', '^'), 'Unknown Boolean expression operation')
    return (kind, substitute(node[1], values), substitute(node[2], values))


def expressions(graph, input_order):
    """Inline a finite combinational leaf using its actual connected gates."""
    require(type(graph) is MappedGraph and graph.clock_bit is None and not graph.flipflops,
        'Expected a combinational mapped leaf')
    require(type(input_order) is tuple and len(input_order) == len(set(input_order)) and
        set(input_order) == set(graph.inputs), 'Incomplete or duplicated leaf input order')
    values, variables = {}, []
    for port in input_order:
        for index, wire in enumerate(graph.inputs[port]):
            name = f'{port}:{index}'
            variables.append(name); values[wire] = ('variable', name)
    def read(wire): return ('constant', wire == '1') if type(wire) is str else values[wire]
    for gate in graph.gates:
        cell = graph.library.cells[gate.cell]
        values[gate.output] = substitute(cell.function,
            {pin: read(wire) for pin, wire in gate.connections.items() if cell.directions[pin] == 'input'})
    return tuple(variables), {port: tuple(read(wire) for wire in bits) for port, bits in graph.outputs.items()}


def lean_expression(node, variables):
    kind = node[0]
    if kind == 'constant': return '.constant ' + str(node[1]).lower()
    if kind == 'variable':
        require(node[1] in variables, 'Unknown generated Lean expression variable')
        return f'.var ⟨{variables.index(node[1])}, by decide⟩'
    if kind == 'not': return f'.inv ({lean_expression(node[1], variables)})'
    require(kind in ('*', '+', '^'), 'Unknown generated Lean expression operation')
    constructor = {'*': 'conj', '+': 'disj', '^': 'xor'}[kind]
    return f'.{constructor} ({lean_expression(node[1], variables)}) ({lean_expression(node[2], variables)})'


def support(node):
    if node[0] == 'constant': return frozenset()
    if node[0] == 'variable': return frozenset((node[1],))
    if node[0] == 'not': return support(node[1])
    require(node[0] in ('*', '+', '^'), 'Unknown Boolean expression operation')
    return support(node[1]) | support(node[2])


def lean_bool(node, names):
    if node[0] == 'constant': return str(node[1]).lower()
    if node[0] == 'variable': return '(' + names[node[1]] + ')'
    if node[0] == 'not': return '(!' + lean_bool(node[1], names) + ')'
    require(node[0] in ('*', '+', '^'), 'Unknown Boolean expression operation')
    return '(' + lean_bool(node[1], names) + {'*': ' && ', '+': ' || ', '^': ' ^^ '}[node[0]] + lean_bool(node[2], names) + ')'


def namespace_name(value):
    require(type(value) is str and re.fullmatch(r'[A-Za-z_][A-Za-z0-9_]*(\.[A-Za-z_][A-Za-z0-9_]*)*', value),
        'Unsupported generated Lean namespace')
    return value


def full_adder_source(graph, *, namespace='Pinwheel.Artifact.StreamingMappedFA', netlist_sha256):
    """Actual A/B/CI/S/CO leaf; a wrong functional pin fails the kernel proof."""
    namespace_name(namespace)
    require(type(netlist_sha256) is str and re.fullmatch('[0-9a-f]{64}', netlist_sha256), 'Missing netlist identity')
    require(graph.library.pinned and set(graph.inputs) == {'A', 'B', 'CI'} and
        set(graph.outputs) == {'S', 'CO'} and all(len(bits) == 1
            for bits in (*graph.inputs.values(), *graph.outputs.values())), 'Full-adder physical interface differs')
    variables, outputs = expressions(graph, ('A', 'B', 'CI'))
    return f'''import Pinwheel.Hardware.StreamingMapped.Boolean

-- Generated from the actual five-cell (or otherwise explicitly interpreted)
-- mapped leaf and pinned Liberty. No synthesis equivalence premise is used.
namespace {namespace}
open Pinwheel.Hardware.StreamingMapped
def netlistSHA256 : String := "{netlist_sha256}"
def libertySHA256 : String := "{graph.library.sha256}"
def actualSum : Expr 3 := {lean_expression(outputs['S'][0], variables)}
def actualCarry : Expr 3 := {lean_expression(outputs['CO'][0], variables)}
def actual : FullAdderLeaf := .fromExpressions actualSum actualCarry
theorem actual_correct : actual.Correct := by
  exact ⟨by decide +kernel, by decide +kernel⟩
end {namespace}
'''


def generate_full_adder(path, library, *, module='pinwheel_mapped_fa', namespace='Pinwheel.Artifact.StreamingMappedFA'):
    path = Path(path)
    require(type(library) is Library and library.pinned and path.is_file() and not path.is_symlink(),
        'Expected pinned Liberty and regular actual mapped artifact')
    before = path.read_bytes()
    graph = load_mapped(path, module, library, combinational=True)
    require(path.read_bytes() == before, 'Mapped artifact changed while being interpreted')
    return full_adder_source(graph, namespace=namespace, netlist_sha256=sha256(before).hexdigest())


def bitwise_source(graph, operation, *, namespace, netlist_sha256):
    """A finite wiring certificate joins scalar truth to an arbitrary word.

    Global expressions retain every physical input index. Static renaming
    equality checks that each cone uses the correct bit and select wire; the
    bounded local truth check then proves the operation. No wide Boolean
    enumeration or native decision procedure is used.
    """
    namespace_name(namespace)
    require(graph.library.pinned and type(netlist_sha256) is str and re.fullmatch('[0-9a-f]{64}', netlist_sha256),
        'Missing pinned source identities')
    require(operation in ('$and', '$or', '$xor', '$not', '$mux'), 'Unsupported bitwise proof goal')
    ports = ('A',) if operation == '$not' else ('A', 'B', 'S') if operation == '$mux' else ('A', 'B')
    require(set(graph.inputs) == set(ports) and set(graph.outputs) == {'Y'}, 'Bitwise module physical interface differs')
    width = len(graph.outputs['Y'])
    require(width > 0 and all(len(bits) == (1 if pin == 'S' else width) for pin, bits in graph.inputs.items()),
        'Unsupported bitwise input resizing')
    variables, outputs = expressions(graph, ports)
    global_count, local_count = len(variables), len(ports)
    parameters = ' '.join(f'({pin} : BitVec {len(graph.inputs[pin])})' for pin in ports)
    arguments = ' '.join(ports)
    def lookup(name, values, result_type):
        if all(value == values[0] for value in values):
            return f'def {name} (_ : Fin {width}) : {result_type} := {values[0]}'
        cases = '\n'.join(f'  | {index} => {value}' for index, value in enumerate(values[:-1]))
        return f'def {name} (bit : Fin {width}) : {result_type} := match bit.val with\n{cases}\n  | _ => {values[-1]}'
    actual = [lean_expression(node, variables) for node in outputs['Y']]
    local = []
    for index, node in enumerate(outputs['Y']):
        # An unexpected cross-bit connection is still emitted in actualExpr.
        # Mapping it to local slot0 here makes static wiring equality false;
        # it cannot be silently omitted or accepted as the desired operation.
        known = {f'{pin}:{0 if pin == "S" else index}': position for position, pin in enumerate(ports)}
        def localize(value):
            if value[0] == 'variable': return ('variable', str(known.get(value[1], 0)))
            if value[0] == 'constant': return value
            return (value[0], *(localize(child) for child in value[1:]))
        local.append(lean_expression(localize(node), tuple(str(i) for i in range(local_count))))
    lines = ['import Pinwheel.Hardware.StreamingMapped.Ports', 'import Pinwheel.Hardware.StreamingMapped.Word',
        'import Init.Data.Fin.Lemmas',
        'set_option maxRecDepth 8192', 'set_option maxHeartbeats 4000000',
        'set_option linter.unusedSimpArgs false', 'set_option linter.unusedVariables false', '', f'namespace {namespace}',
        'open Pinwheel.Hardware.StreamingMapped', f'def netlistSHA256 : String := "{netlist_sha256}"',
        f'def libertySHA256 : String := "{graph.library.sha256}"',
        lookup('actualExpr', actual, f'Expr {global_count}'), lookup('localExpr', local, f'Expr {local_count}')]
    if local_count == 1:
        wiring = 'i.val'
        globals_expr = 'A.getLsbD pin.val'
        local_values = 'a'
    elif local_count == 2:
        wiring = f'if pin.val = 0 then i.val else {width} + i.val'
        globals_expr = f'if pin.val < {width} then A.getLsbD pin.val else B.getLsbD (pin.val-{width})'
        local_values = 'if pin.val = 0 then a else b'
    else:
        wiring = f'if pin.val = 0 then i.val else if pin.val = 1 then {width} + i.val else {2*width}'
        globals_expr = f'if pin.val < {width} then A.getLsbD pin.val else if pin.val < {2*width} then B.getLsbD (pin.val-{width}) else S.getLsbD 0'
        local_values = 'if pin.val = 0 then a else if pin.val = 1 then b else s'
    bound_proof = 'omega' if local_count == 1 else 'split <;> omega' if local_count == 2 else 'split <;> (try split) <;> omega'
    lines += [f'def wires (i : Fin {width}) (pin : Fin {local_count}) : Fin {global_count} := ⟨{wiring}, by {bound_proof}⟩',
        f'theorem wiring_correct : ∀ i, actualExpr i = (localExpr i).map (wires i) := by decide +kernel',
        f'def globalValues {parameters} (pin : Fin {global_count}) : Bool := {globals_expr}',
        f'def localValues ' + ('(a : Bool)' if local_count == 1 else '(a b : Bool)' if local_count == 2 else '(a b s : Bool)') +
        f' (pin : Fin {local_count}) : Bool := {local_values}']
    local_params = '(a : Bool)' if local_count == 1 else '(a b : Bool)' if local_count == 2 else '(a b s : Bool)'
    expected_local = {'$and': 'a && b', '$or': 'a || b', '$xor': 'a ^^ b', '$not': '!a', '$mux': 'if s then b else a'}[operation]
    local_args = 'a' if local_count == 1 else 'a b' if local_count == 2 else 'a b s'
    lines += [f'theorem scalar_correct : ∀ i {local_params}, (localExpr i).eval (localValues {local_args}) = ({expected_local}) := by decide +kernel',
        f'theorem wire_values {parameters} (i : Fin {width}) : globalValues {arguments} ∘ wires i = '
        f'localValues (A.getLsbD i.val)' + (f' (B.getLsbD i.val)' if local_count >= 2 else '') +
        (f' (S.getLsbD 0)' if local_count == 3 else '') + ' := by',
        '  funext pin']
    if local_count == 1:
        lines += ['  rfl']
    else:
        lines += [f'  have bounds := pin.isLt', f'  have low := i.isLt',
            f'  have high : {width} + i.val < {2*width} := by omega',
            f'  have outside : ¬ {width} + i.val < {width} := by omega',
            f'  have indices : ' + ' ∨ '.join(f'pin.val = {j}' for j in range(local_count)) + ' := by omega',
            '  rcases indices with ' + ' | '.join('index' for _ in range(local_count)),
            '  all_goals simp [globalValues,wires,localValues,Function.comp_apply,index,low,high,outside]',
            '  all_goals rfl']
    expected = {'$and': 'A &&& B', '$or': 'A ||| B', '$xor': 'A ^^^ B', '$not': '~~~A', '$mux': 'if S.getLsbD 0 then B else A'}[operation]
    bridge = {'$and': 'and_correct', '$or': 'or_correct', '$xor': 'xor_correct', '$not': 'not_correct', '$mux': 'mux_correct'}[operation]
    lines += [f'def actual {parameters} : BitVec {width} := Word.pack (fun i => (actualExpr i).eval (globalValues {arguments}))',
        f'theorem correct {parameters} : actual {arguments} = ({expected}) := by',
        f'  apply Word.{bridge}' + (' (S.getLsbD 0) B A' if operation == '$mux' else ''),
        '  intro i within', '  rw [actual,Word.pack_bit _ i within,wiring_correct,Expr.eval_map,wire_values]',
        f'  exact scalar_correct ⟨i,within⟩ (A.getLsbD i)' + (' (B.getLsbD i)' if local_count >= 2 else '') +
        (' (S.getLsbD 0)' if local_count == 3 else '')]
    if operation == '$mux':
        lines += [f'theorem raw_correct {parameters} : actual {arguments} = (if S = 1#1 then B else A) := by',
            '  have selector : S.getLsbD 0 = decide (S = 1#1) := by decide +kernel +revert',
            '  rw [correct,selector]', '  simp']
    else:
        lines += [f'theorem raw_correct {parameters} : actual {arguments} = ({expected}) := correct {arguments}']
    lines.append(f'end {namespace}')
    return '\n'.join(lines) + '\n'


def graph_source(graph, *, namespace='Pinwheel.Artifact.StreamingMappedGraph', netlist_sha256):
    """Explicit gate-linked Boolean recurrence, without an equivalence claim.

    Named functions retain DAG sharing instead of duplicating wide arithmetic
    cones. Q state and nonclock primary inputs are separate finite arguments.
    Actual FF D and public output connections select the next/observe bits.
    """
    require(type(graph) is MappedGraph and graph.library.pinned, 'Expected actual pinned mapped graph')
    namespace_name(namespace)
    require(type(netlist_sha256) is str and re.fullmatch('[0-9a-f]{64}', netlist_sha256), 'Missing netlist identity')
    input_ids, state_ids = sorted(graph.input_bits), sorted(graph.state_bits)
    names = {wire: f'i ⟨{index}, by decide⟩' for index, wire in enumerate(input_ids)}
    names.update({wire: f'q ⟨{index}, by decide⟩' for index, wire in enumerate(state_ids)})
    cell_names, lines = {}, ['import Pinwheel.Hardware.StreamingMapped.Boolean', '', f'namespace {namespace}',
        'open Pinwheel.Hardware.StreamingMapped', f'def netlistSHA256 : String := "{netlist_sha256}"',
        f'def libertySHA256 : String := "{graph.library.sha256}"',
        f'abbrev Inputs := Fin {len(input_ids)} → Bool', f'abbrev State := Fin {len(state_ids)} → Bool']
    for index, kind in enumerate(sorted({gate.cell for gate in graph.gates})):
        cell = graph.library.cells[kind]
        pins = tuple(sorted(pin for pin, direction in cell.directions.items() if direction == 'input'))
        cell_names[kind] = (f'cell{index}', pins)
        lines += [f'-- {kind}: actual output {cell.output}; ordered pins {json.dumps(pins)}',
            f'def cell{index} : Expr {len(pins)} := {lean_expression(cell.function, pins)}']
    def read(wire): return str(wire == '1').lower() if type(wire) is str else names[wire]
    for index, gate in enumerate(graph.gates):
        cell_name, pins = cell_names[gate.cell]
        args = [read(gate.connections[pin]) for pin in pins]
        cases = ' '.join(f'| {i} => {value}' for i, value in enumerate(args[:-1]))
        lines.append(f'def node{index} (i : Inputs) (q : State) : Bool := {cell_name}.eval '
            f'(fun pin => match pin.val with {cases} | _ => {args[-1]})')
        names[gate.output] = f'node{index} i q'
    next_bits = {ff.q: ff.d for ff in graph.flipflops}
    cases = '\n'.join(f'  | {index} => {read(next_bits[wire])}' for index, wire in enumerate(state_ids[:-1]))
    if state_ids:
        lines.append(f'def next (i : Inputs) (q : State) : State := fun bit => match bit.val with\n{cases}\n  | _ => {read(next_bits[state_ids[-1]])}')
    for index, (port, wires) in enumerate(sorted(graph.outputs.items())):
        cases = '\n'.join(f'  | {position} => {read(wire)}' for position, wire in enumerate(wires[:-1]))
        lines += [f'-- Actual output port {json.dumps(port)} in JSON LSB-first order.',
            f'def output{index} (i : Inputs) (q : State) : Fin {len(wires)} → Bool := fun bit => match bit.val with\n'
            f'{cases}\n  | _ => {read(wires[-1])}']
    lines.append(f'end {namespace}')
    return '\n'.join(lines) + '\n'
