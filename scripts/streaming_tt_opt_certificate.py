"""Kernel leaf certificates with explicit static constant-input premises.

Actual functions always come from mapped JSON/Liberty, including unused ports.
Only small comparisons use exhaustive kernel reduction (at most 256 inputs).
Wide muxes use the existing bounded scalar and exact bit-wiring proof.
"""
from hashlib import sha256
import json
from pathlib import Path
import re

from streaming_mapped_certificate import bitwise_source, expressions, lean_expression, namespace_name
from streaming_mapped_liberty import require
from streaming_mapped_netlist import MappedGraph, load_mapped


def load_leaf(path, module, library):
    """The historical reader rejects empty cones; handle only direct wires.

    Constant-specialized comparisons can have no gates at all. Such a leaf
    still retains every input port, and each output must be an actual input
    wire or literal. No missing driver or arbitrary module-name fallback.
    """
    def pairs(items):
        result = {}
        for key, value in items:
            require(key not in result, 'Duplicate specialization JSON key')
            result[key] = value
        return result
    data = json.loads(Path(path).read_bytes(), object_pairs_hook=pairs)
    body = data['modules'][module]
    if body.get('cells'):
        return load_mapped(path, module, library, combinational=True)
    require(body.get('cells') == {} and not body.get('processes') and not body.get('memories') and
        not body.get('parameter_default_values') and library.pinned,
        'Unsupported empty leaf behavior')
    for key in ('blackbox','whitebox'):
        require(not int(body.get('attributes', {}).get(key, '0'), 2), 'Uninterpreted empty leaf')
    ports = body['ports']
    require(set(ports) in ({'A','B','Y'}, {'A','B','S','Y'}) and
        all(port['direction'] == ('output' if pin == 'Y' else 'input') and port['bits'] and
            all(type(bit) is int and bit >= 0 or type(bit) is str and bit in ('0','1') for bit in port['bits'])
            for pin,port in ports.items()), 'Malformed empty leaf ports')
    inputs = {pin:tuple(port['bits']) for pin,port in ports.items() if pin != 'Y'}
    flat = [bit for bits in inputs.values() for bit in bits]
    require(all(type(bit) is int for bit in flat) and len(flat) == len(set(flat)) and
        all(bit in flat or bit in ('0','1') for bit in ports['Y']['bits']), 'Undriven or aliased empty leaf')
    return MappedGraph(module,library,inputs,{'Y':tuple(ports['Y']['bits'])},None,(),(),{},0)


def replace_once(text, old, new):
    require(text.count(old) == 1, 'Expected exact certificate seam: ' + old[:80])
    return text.replace(old, new)


def specialized_mux_source(graph, fixed, *, namespace, netlist_sha256):
    require(set(fixed) and set(fixed) <= {'A', 'B'}, 'Missing fixed mux operand')
    width = len(graph.outputs['Y'])
    require(all(type(bits) is str and len(bits) == width and set(bits) <= {'0', '1'}
        for bits in fixed.values()), 'Malformed fixed mux value')
    source = bitwise_source(graph, '$mux', namespace=namespace, netlist_sha256=netlist_sha256)
    values = {pin: str(int(fixed[pin], 2)) + '#' + str(width) if pin in fixed else pin for pin in ('A', 'B')}
    expected_scalar = 'if s then ' + (f'({values["B"]}).getLsbD i.val' if 'B' in fixed else 'b') + \
        ' else ' + (f'({values["A"]}).getLsbD i.val' if 'A' in fixed else 'a')
    source = replace_once(source, '= (if s then b else a) := by decide +kernel',
        '= (' + expected_scalar + ') := by decide +kernel')
    source = replace_once(source, '= (if S.getLsbD 0 then B else A) := by',
        f'= (if S.getLsbD 0 then {values["B"]} else {values["A"]}) := by')
    source = replace_once(source, 'apply Word.mux_correct (S.getLsbD 0) B A',
        f'apply Word.mux_correct (S.getLsbD 0) ({values["B"]}) ({values["A"]})')
    premises = ''.join(f' (fixed{pin} : {pin} = {values[pin]})' for pin in sorted(fixed))
    source = replace_once(source,
        f'theorem raw_correct (A : BitVec {width}) (B : BitVec {width}) (S : BitVec 1) :',
        f'theorem raw_correct (A : BitVec {width}) (B : BitVec {width}) (S : BitVec 1){premises} :')
    source = replace_once(source, '  rw [correct,selector]',
        '  rw [correct,selector' + ''.join(',← fixed' + pin for pin in sorted(fixed)) + ']')
    return source


def small_compare_source(graph, operation, fixed, *, namespace, netlist_sha256):
    namespace_name(namespace)
    require(operation in ('$lt', '$gt', '$ge', '$eq', '$ne') and set(fixed) and set(fixed) <= {'A', 'B'},
        'Unsupported specialized comparison')
    require(set(graph.inputs) == {'A', 'B'} and set(graph.outputs) == {'Y'} and len(graph.outputs['Y']) == 1,
        'Changed small comparison interface')
    width = len(graph.inputs['A'])
    require(1 <= width <= 8 and len(graph.inputs['B']) == width and
        all(type(bits) is str and len(bits) == width and set(bits) <= {'0', '1'} for bits in fixed.values()),
        'Small comparison is outside finite proof scope')
    variables, outputs = expressions(graph, ('A', 'B'))
    params = f'(A B : BitVec {width})'
    values = {pin: f'{int(bits, 2)}#{width}' for pin, bits in fixed.items()}
    premises = ''.join(f' (fixed{pin} : {pin} = {values[pin]})' for pin in sorted(fixed))
    expected = {'$lt':'BitVec.ofBool (A < B)', '$gt':'BitVec.ofBool (B < A)',
        '$ge':'~~~ (BitVec.ofBool (A < B))', '$eq':'BitVec.ofBool (A = B)',
        '$ne':'~~~ (BitVec.ofBool (A = B))'}[operation]
    # BitVec comparisons coerce to Bool in the typed expression notation, but
    # propositions need decide explicitly for the generated theorem statement.
    expected = expected.replace('(A < B)', '(decide (A < B))').replace('(B < A)', '(decide (B < A))').replace('(A = B)', '(decide (A = B))')
    return '\n'.join([
        'import Pinwheel.Hardware.StreamingMapped.Word',
        'import Pinwheel.Hardware.StreamingMapped.Boolean',
        'set_option maxRecDepth 16384', 'set_option maxHeartbeats 12000000',
        'set_option linter.unusedVariables false', f'namespace {namespace}',
        'open Pinwheel.Hardware.StreamingMapped',
        f'def netlistSHA256 : String := "{netlist_sha256}"',
        f'def libertySHA256 : String := "{graph.library.sha256}"',
        f'def actualExpr : Expr {2*width} := {lean_expression(outputs["Y"][0], variables)}',
        f'def values {params} (pin : Fin {2*width}) : Bool := if pin.val < {width} then A.getLsbD pin.val else B.getLsbD (pin.val-{width})',
        f'def actual {params} : BitVec 1 := BitVec.ofBool (actualExpr.eval (values A B))',
        f'theorem raw_correct {params}{premises} : actual A B = {expected} := by',
        *('  subst ' + pin for pin in sorted(fixed)),
        '  decide +kernel +revert', f'end {namespace}', ''])


def generate_specialized(path, library, module, descriptor, *, namespace):
    path = Path(path)
    before = path.read_bytes()
    graph = load_leaf(path, module, library)
    require(path.read_bytes() == before, 'Mapped leaf changed during interpretation')
    fixed = descriptor['fixed_operands']
    factory = specialized_mux_source if descriptor['kind'] == '$mux' else small_compare_source
    if descriptor['kind'] == '$mux':
        return factory(graph, fixed, namespace=namespace, netlist_sha256=sha256(before).hexdigest())
    return factory(graph, descriptor['kind'], fixed, namespace=namespace, netlist_sha256=sha256(before).hexdigest())


def add_static_premises(sources, specifications):
    """Append kernel proof terms only at exact generated per-word link calls.

    The original strict topology checker still compares every input wire.
    Each added rfl must prove the actual source expression is the literal
    promised by its leaf theorem. No Python Boolean acceptance replaces it.
    """
    result = {}
    for module, source in sources.items():
        for spec in specifications.values():
            fixed = spec.get('fixed_operands', {})
            if not fixed: continue
            prefix = '  exact ' + spec['namespace'] + '.raw_correct '
            lines = source.splitlines()
            source = '\n'.join(line + ''.join(' (by rfl)' for _ in fixed)
                if line.startswith(prefix) else line for line in lines) + '\n'
        result[module] = source
    return result
