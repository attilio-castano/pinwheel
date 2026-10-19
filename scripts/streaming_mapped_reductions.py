"""Kernel certificates for actual wide mapped reductions and equality.

The supplied operator chooses the proposition to prove, never the interpreted
function. Gate functions come from pinned Liberty and actual connected JSON.
De Morgan/XNOR clauses plus AC normalization avoid native SAT and exponential
truth enumeration over whole word inputs.
"""
from hashlib import sha256
import json
from pathlib import Path
import re

from streaming_mapped_certificate import namespace_name
from streaming_mapped_liberty import Library, require
from streaming_mapped_netlist import parse_mapped

REDUCTIONS = frozenset(('$eq', '$ne', '$logic_not', '$reduce_or', '$reduce_and'))


def _boolean(node, values):
    kind = node[0]
    if kind == 'constant': return str(node[1]).lower()
    if kind == 'variable': return '(' + values[node[1]] + ')'
    if kind == 'not': return '!(' + _boolean(node[1], values) + ')'
    require(kind in ('*', '+', '^'), 'Unsupported mapped reduction Boolean operation')
    return '(' + _boolean(node[1], values) + {'*': ' && ', '+': ' || ', '^': ' ^^ '}[kind] + _boolean(node[2], values) + ')'


def reduction_source(data, module, kind, library, *, namespace, netlist_sha256):
    """Return Lean plus inventory; only kernel acceptance certifies equivalence.

    `correct` exposes the actual Y port as BV1, matching the arithmetic/bitwise
    adapter API. `bool_correct` gives its one-bit Boolean function directly.
    Every actual gate receives an explicit named Boolean definition.
    """
    namespace_name(namespace)
    require(type(module) is str and re.fullmatch(r'[A-Za-z_][A-Za-z0-9_]*', module), 'Unsupported actual module name')
    require(type(kind) is str and kind in REDUCTIONS, 'Unsupported reduction operator')
    require(type(netlist_sha256) is str and re.fullmatch('[0-9a-f]{64}', netlist_sha256), 'Missing exact mapped identity')
    require(type(library) is Library and library.pinned, 'Expected pinned mapped-cell library')
    graph = parse_mapped(data, module, library, combinational=True)
    ports = ('A', 'B') if kind in ('$eq', '$ne') else ('A',)
    require(set(graph.inputs) == set(ports) and set(graph.outputs) == {'Y'} and len(graph.outputs['Y']) == 1,
        'Reduction formal interface differs')
    width = len(graph.inputs['A'])
    require(width > 0 and all(len(graph.inputs[port]) == width for port in ports), 'Reduction operand widths differ')
    parameters = ' '.join(f'({port} : BitVec {width})' for port in ports)
    arguments = ' '.join(ports)
    values = {}
    for port in ports:
        for index, wire in enumerate(graph.inputs[port]):
            require(type(wire) is int and wire not in values, 'Aliased reduction formal input')
            values[wire] = f'{port}.getLsbD {index}'
    def read(wire):
        if type(wire) is str:
            require(wire in ('0', '1'), 'Unsupported reduction constant')
            return str(wire == '1').lower()
        require(type(wire) is int and wire in values, 'Undriven reduction connection')
        return values[wire]
    lines = ['import Lean', 'import Pinwheel.Hardware.StreamingMapped.Clauses',
        f'namespace {namespace}', 'open Pinwheel.Hardware.StreamingMapped',
        'set_option maxHeartbeats 100000000', 'set_option maxRecDepth 100000',
        'set_option linter.unusedVariables false', 'set_option linter.unusedSimpArgs false',
        f'def netlistSHA256 : String := "{netlist_sha256}"', f'def libertySHA256 : String := "{library.sha256}"',
        f'def moduleName : String := "{module}"']
    for index, gate in enumerate(graph.gates):
        cell = library.cells[gate.cell]
        bindings = {pin: read(wire) for pin, wire in gate.connections.items() if cell.directions[pin] == 'input'}
        lines.append(f'def node{index} {parameters} : Bool := {_boolean(cell.function, bindings)}')
        values[gate.output] = f'node{index} {arguments}'
    lines += [f'def actualBool {parameters} : Bool := {read(graph.outputs["Y"][0])}',
        f'def actual {parameters} : BitVec 1 := BitVec.ofBool (actualBool {arguments})',
        f'def tree : Reduction.Tree {width} := ' + ''.join(f'.join (.leaf ⟨{index}, by decide⟩) (' for index in range(width)) + '.empty' + ')' * width]
    leaf_values = '(fun i => A.getLsbD i.val ^^ B.getLsbD i.val)' if kind in ('$eq', '$ne') else '(fun i => A.getLsbD i.val)'
    target = (f'(!tree.eval {leaf_values})' if kind in ('$eq', '$logic_not') else
        f'tree.evalAnd {leaf_values}' if kind == '$reduce_and' else f'tree.eval {leaf_values}')
    lines.append(f'private theorem actual_tree {parameters} : actualBool {arguments} = {target} := by')
    if kind in ('$ne', '$reduce_or'): lines.append('  apply Bool.not_inj')
    definitions = ['actualBool', *(f'node{index}' for index in reversed(range(len(graph.gates))))]
    lines += ['  simp only [' + ','.join(definitions) + ']',
        '  simp only [tree,Reduction.Tree.evalAnd,Reduction.Tree.eval]',
        '  simp only [Bool.not_and,Bool.not_or,Bool.not_not,Bool.not_xor,Bool.xor_not,Reduction.xnor_clause,Reduction.xnor_dnf_clause,Reduction.xnor_dnf_clause_swap,Bool.not_false,Bool.or_false,Bool.and_true]',
        '  all_goals ac_rfl', 'private theorem tree_complete : tree.Complete := by',
        f'  change ∀ i : Fin {width}, i ∈ tree.leaves', '  decide +kernel']
    expected = {'$eq': 'decide (A = B)', '$ne': 'decide (A ≠ B)', '$logic_not': f'decide (A = 0#{width})', '$reduce_or': f'decide (A ≠ 0#{width})', '$reduce_and': f'decide (A = BitVec.allOnes {width})'}[kind]
    proof = {'$eq': 'tree.word_eq tree_complete A B', '$ne': 'tree.word_ne tree_complete A B', '$logic_not': 'tree.logic_not tree_complete A', '$reduce_or': 'tree.reduce_or tree_complete A', '$reduce_and': 'tree.reduce_and tree_complete A'}[kind]
    lines += [f'theorem bool_correct {parameters} : actualBool {arguments} = {expected} := by',
        '  rw [actual_tree]', f'  exact {proof}',
        f'theorem correct {parameters} : actual {arguments} = BitVec.ofBool ({expected}) := by',
        '  unfold actual', '  rw [bool_correct]']
    raw_expected = (f'~~~BitVec.ofBool (decide (A = B))' if kind == '$ne' else
        f'~~~BitVec.ofBool (decide (A = 0#{width}))' if kind == '$reduce_or' else
        f'BitVec.ofBool (decide (A = {2**width-1}#{width}))' if kind == '$reduce_and' else
        f'BitVec.ofBool ({expected})')
    lines.append(f'theorem raw_correct {parameters} : actual {arguments} = {raw_expected} := by')
    if kind in ('$ne', '$reduce_or'):
        lines.append('  simpa only [BitVec.not_ofBool,← decide_not] using correct ' + arguments)
    else:
        lines.append('  exact correct ' + arguments)
    lines.append(f'end {namespace}')
    return '\n'.join(lines) + '\n', dict(module=module, kind=kind, width=width, result_width=1,
        actual_primitive_gates=len(graph.gates), netlist_sha256=netlist_sha256, liberty_sha256=library.sha256,
        module_sha256=sha256(json.dumps(data['modules'][module], sort_keys=True, separators=(',', ':')).encode()).hexdigest())


def generate_reduction(path, library, module, kind, *, namespace):
    path = Path(path)
    require(path.is_file() and not path.is_symlink(), 'Expected regular actual mapped JSON')
    def pairs(items):
        result = {}
        for key, value in items:
            require(key not in result, 'Duplicate mapped reduction JSON key')
            result[key] = value
        return result
    before = path.read_bytes()
    data = json.loads(before, object_pairs_hook=pairs)
    result = reduction_source(data, module, kind, library, namespace=namespace, netlist_sha256=sha256(before).hexdigest())
    require(path.read_bytes() == before, 'Mapped reduction artifact changed during interpretation')
    return result
