"""Actual mapped word DAGs and kernel ripple linkage certificates.

The expected operator chooses a proposition only. All output functions come
from real module ports, primitive Liberty functions and connected FA instances.
Carry netnames are candidate cuts: each scalar linkage equation is checked.
"""
from hashlib import sha256
import json
import re
from pathlib import Path

from streaming_mapped_certificate import namespace_name, expressions, lean_expression
from streaming_mapped_hierarchy import ARITHMETIC, FA
from streaming_mapped_liberty import require
from streaming_mapped_netlist import parse_mapped


def boolean(node, values):
    kind = node[0]
    if kind == 'constant': return str(node[1]).lower()
    if kind == 'variable': return values[node[1]]
    if kind == 'not': return f'(!({boolean(node[1], values)}))'
    require(kind in ('*', '+', '^'), 'Unsupported mapped Boolean function')
    return '(' + boolean(node[1], values) + {'*': ' && ', '+': ' || ', '^': ' ^^ '}[kind] + boolean(node[2], values) + ')'


def arithmetic_source(data, module, kind, library, *, namespace,
        fa_module='MappedFullAdder', fa_namespace='Pinwheel.Artifact.StreamingMappedFA', netlist_sha256):
    namespace_name(namespace); namespace_name(fa_namespace); namespace_name(fa_module)
    require(type(netlist_sha256) is str and re.fullmatch('[0-9a-f]{64}', netlist_sha256), 'Missing exact netlist identity')
    require(kind in ARITHMETIC and library.pinned, 'Expected pinned mapped arithmetic candidate')
    require(module in data.get('modules', {}) and FA in data['modules'], 'Missing actual arithmetic or FA module')
    graph = parse_mapped(data, module, library, combinational=True)
    require(set(graph.inputs) == {'A', 'B'} and set(graph.outputs) == {'Y'} and
        len(graph.inputs['A']) == len(graph.inputs['B']), 'Unsupported actual arithmetic port inventory')
    width, result_width = len(graph.inputs['A']), len(graph.outputs['Y'])
    require(width > 0 and result_width == (width if kind in ('$add', '$sub') else 1), 'Arithmetic result width differs')
    fa_graph = parse_mapped(data, FA, library, combinational=True)
    require(set(fa_graph.inputs) == {'A', 'B', 'CI'} and set(fa_graph.outputs) == {'S', 'CO'} and
        all(len(bits) == 1 for bits in (*fa_graph.inputs.values(), *fa_graph.outputs.values())),
        'Actual FA body has a different interface')
    fa_variables, fa_outputs = expressions(fa_graph, ('A', 'B', 'CI'))
    actual = data['modules'][module]
    ports = actual['ports']; values = {}
    for port in ('A', 'B'):
        require(len(ports[port]['bits']) == width, 'Changed arithmetic formal width')
        for index, wire in enumerate(ports[port]['bits']):
            require(type(wire) is int and wire not in values, 'Aliased actual arithmetic formal input')
            values[wire] = f'{port}.getLsbD {index}'
    lines = [f'import {fa_module}', 'import Pinwheel.Hardware.StreamingMapped.Comparison',
        'import Pinwheel.Hardware.StreamingMapped.Word', '', f'namespace {namespace}',
        'open Pinwheel.Hardware.StreamingMapped', 'set_option maxRecDepth 100000',
        'set_option linter.unusedVariables false', 'set_option linter.unusedSimpArgs false', f'def netlistSHA256 : String := "{netlist_sha256}"',
        f'def actualSum : Expr 3 := {lean_expression(fa_outputs["S"][0], fa_variables)}',
        f'def actualCarry : Expr 3 := {lean_expression(fa_outputs["CO"][0], fa_variables)}',
        'def leaf : FullAdderLeaf := .fromExpressions actualSum actualCarry',
        'theorem leaf_correct : leaf.Correct := by',
        f'  change {fa_namespace}.actual.Correct', f'  exact {fa_namespace}.actual_correct']
    def read(wire):
        if type(wire) is str:
            require(wire in ('0', '1'), 'Unknown arithmetic constant')
            return str(wire == '1').lower()
        require(type(wire) is int and wire in values, 'Undriven or cyclic arithmetic wire')
        return values[wire]
    pending = list(sorted(actual['cells'].items())); nodes, fa_instances = [], 0
    while pending:
        progressed = []
        for name, cell in pending:
            require(cell['parameters'] == {}, 'Unexpected mapped cell parameters')
            con, directions = cell['connections'], cell['port_directions']
            require(all(type(bits) is list and len(bits) == 1 for bits in con.values()), 'Non-scalar actual mapped gate')
            kind_cell = cell['type']
            if kind_cell == FA:
                require(directions == dict(A='input', B='input', CI='input', S='output', CO='output') and set(con) == set(directions),
                    'Actual FA instance interface differs')
                outputs = ('S', 'CO'); inputs = ('A', 'B', 'CI')
            else:
                require(kind_cell in library.cells and not library.cells[kind_cell].sequential, 'Unsupported arithmetic subcell')
                model = library.cells[kind_cell]
                require(directions == model.directions and set(con) == set(directions), 'Actual arithmetic primitive pins differ from Liberty')
                outputs = (model.output,); inputs = tuple(pin for pin in con if directions[pin] == 'input')
            if any(type(con[pin][0]) is int and con[pin][0] not in values for pin in inputs): continue
            arguments = {pin: read(con[pin][0]) for pin in inputs}
            for pin in outputs:
                wire = con[pin][0]
                require(type(wire) is int and wire not in values, 'Aliased or multiply driven arithmetic output')
                if kind_cell == FA:
                    operation = 'sum' if pin == 'S' else 'carry'
                    expression = f'leaf.{operation} ({arguments["A"]}) ({arguments["B"]}) ({arguments["CI"]})'
                else: expression = boolean(model.function, arguments)
                node = 'wire' + str(len(nodes)); nodes.append(node)
                lines.append(f'def {node} (A B : BitVec {width}) : Bool := {expression}')
                values[wire] = f'{node} A B'
            fa_instances += kind_cell == FA
            progressed.append((name, cell))
        require(progressed, 'Arithmetic module has a combinational cycle or undriven gate')
        pending = [entry for entry in pending if entry not in progressed]
    require(fa_instances == width, 'Arithmetic ripple must expose exactly one actual FA per bit')
    carry_bits = actual.get('netnames', {}).get('carry', {}).get('bits')
    require(type(carry_bits) is list and len(carry_bits) == width + 1, 'Missing proposed ripple carry cuts')
    sum_bits = actual.get('netnames', {}).get('sum_bits', {}).get('bits')
    require(type(sum_bits) is list and len(sum_bits) == width, 'Missing proposed ripple sum cuts')
    def packed(bits):
        cases = ' '.join(f'| {index} => {read(wire)}' for index, wire in enumerate(bits[:-1]))
        return f'Word.pack (fun bit => match bit.val with {cases} | _ => {read(bits[-1])})'
    lines += [f'def actual (A B : BitVec {width}) : BitVec {result_width} := {packed(ports["Y"]["bits"])}',
        f'def sums (A B : BitVec {width}) : BitVec {width} := {packed(sum_bits)}']
    cases = ' '.join(f'| {index} => {read(wire)}' for index, wire in enumerate(carry_bits))
    lines += [f'def carries (A B : BitVec {width}) (n : Nat) : Bool := match n with {cases} | _ => false']
    swapped = kind in ('$gt', '$le'); left = 'B' if swapped else 'A'; right = 'A' if swapped else 'B'
    subtract = kind != '$add'; complement = f'(~~~{right})' if subtract else right
    initial = 'true' if subtract else 'false'
    disjunction = ' ∨ '.join(f'i = {index}' for index in range(width))
    case_branches = ' | '.join('rfl' for _ in range(width))
    lines += [f'theorem linked (A B : BitVec {width}) : Ripple.Linked leaf {left} {complement} {initial} (carries A B) (sums A B) := by',
        '  constructor', '  · rfl', '  · intro i within', f'    have cases : {disjunction} := by omega',
        f'    rcases cases with {case_branches}',
        *(['    all_goals simp only [BitVec.getLsbD_not, Nat.reduceLT, decide_true, Bool.true_and]'] if subtract else []),
        '    all_goals rfl',
        '  · intro i within', '    unfold sums', '    rw [Word.pack_bit _ i within]', f'    have cases : {disjunction} := by omega',
        f'    rcases cases with {case_branches}',
        *(['    all_goals simp only [BitVec.getLsbD_not, Nat.reduceLT, decide_true, Bool.true_and]'] if subtract else []),
        '    all_goals rfl']
    if kind in ('$add', '$sub'):
        operation, target = ('add_correct', 'A+B') if kind == '$add' else ('sub_correct', 'A-B')
        lines += [f'theorem correct (A B : BitVec {width}) : actual A B = {target} :=',
            f'  Ripple.Linked.{operation} _ leaf_correct A B (carries A B) (sums A B) (linked A B)']
    else:
        comparison = {'$lt': 'A.toNat < B.toNat', '$gt': 'B.toNat < A.toNat', '$ge': 'B.toNat ≤ A.toNat', '$le': 'A.toNat ≤ B.toNat'}[kind]
        method = {'$lt': 'lt_word', '$gt': 'gt_word', '$ge': 'ge_word', '$le': 'le_word'}[kind]
        output_bit = f'(!carries A B {width})' if kind in ('$lt', '$gt') else f'(carries A B {width})'
        lines += [f'theorem output_bit (A B : BitVec {width}) : actual A B = BitVec.ofBool {output_bit} := by',
            '  apply BitVec.eq_of_getLsbD_eq', '  intro i within', '  have index : i = 0 := by omega', '  subst i',
            '  unfold actual', '  rw [Word.pack_bit _ 0 (by decide)]', '  simp only [BitVec.getLsbD_ofBool,decide_true,Bool.true_and]', '  rfl',
            f'theorem correct (A B : BitVec {width}) : actual A B = BitVec.ofBool (decide ({comparison})) := by',
            '  rw [output_bit]', f'  exact Ripple.Linked.{method} _ leaf_correct A B (carries A B) (sums A B) (linked A B)']
    if kind == '$ge':
        lines += [f'theorem raw_correct (A B : BitVec {width}) : actual A B = ~~~(BitVec.ofBool (decide (A.toNat < B.toNat))) := by',
            '  simpa only [BitVec.not_ofBool, ← decide_not, Nat.not_lt] using correct A B']
    else:
        raw_target = target if kind in ('$add', '$sub') else f'BitVec.ofBool (decide ({comparison}))'
        lines += [f'theorem raw_correct (A B : BitVec {width}) : actual A B = {raw_target} := correct A B']
    lines += [f'end {namespace}']
    return '\n'.join(lines) + '\n', dict(module=module, kind=kind, width=width, result_width=result_width,
        actual_fa_instances=fa_instances, named_bool_nodes=len(nodes), netlist_sha256=netlist_sha256,
        fa_module_sha256=sha256(json.dumps(data['modules'][FA],sort_keys=True,separators=(',',':')).encode()).hexdigest())


def generate_arithmetic(path, library, module, kind, *, namespace,
        fa_module='MappedFullAdder', fa_namespace='Pinwheel.Artifact.StreamingMappedFA'):
    path = Path(path)
    require(path.is_file() and not path.is_symlink(), 'Expected regular mapped JSON')
    def pairs(items):
        result = {}
        for key, value in items:
            require(key not in result, 'Duplicate mapped arithmetic JSON key')
            result[key] = value
        return result
    before = path.read_bytes(); data = json.loads(before, object_pairs_hook=pairs)
    result = arithmetic_source(data, module, kind, library, namespace=namespace, fa_module=fa_module,
        fa_namespace=fa_namespace, netlist_sha256=sha256(before).hexdigest())
    require(path.read_bytes() == before, 'Mapped arithmetic artifact changed during interpretation')
    return result
