"""Restricted artifact interface for the actual buffered SRAM controller.

The existing backend reader is loaded privately, with its complete port/state
contract replaced rather than relaxed.  MLIR and sampled signatures are proof
hints only: generated Lean must connect every endpoint to ``Sram.circuit``.
Yosys's SystemVerilog frontend/process lowering and this word-level adapter are
explicit interpretation boundaries; this module performs no synthesis mapping.
"""
from collections import Counter, defaultdict
import importlib.util
import json
from pathlib import Path
import random
import sys


ROOT = Path(__file__).resolve().parents[1]
TOP = 'pinwheel_buffered_shared_branches_sram_controller'
NAMESPACE = 'Pinwheel.Artifact.BufferedSram'

BASE_INPUTS = [
    ('initialize', 1, 'initialize'), ('command', 3, 'command'),
    ('address', 6, 'address'), ('word', 64, 'word'),
    ('control', 24, 'control'), ('branch', 56, 'branch'),
    ('count', 7, 'count'), ('virtual_span', 11, 'virtualSpan'),
    ('idle_levels', 3, 'idleLevels'), ('idle_enabled', 3, 'idleEnabled'),
    ('tx_data', 32, 'txData'), ('tx_length', 6, 'txLength'),
    ('rx_capacity', 6, 'rxCapacity'),
    ('expected_generation', 16, 'expectedGeneration'),
    ('expected_transfer', 16, 'expectedTransfer'),
    ('read_index', 5, 'readIndex'), ('raw_inputs', 2, 'rawInputs'),
]
CORE_REGISTERS = [
    ('written', 64, 'written'), ('pending', 1, 'pending'),
    ('valid', 1, 'valid'), ('count', 7, 'count'),
    ('idle_levels', 3, 'idleLevels'), ('idle_enabled', 3, 'idleEnabled'),
    ('generation', 16, 'generation'), ('transfer', 16, 'transfer'),
    ('phase', 3, 'phase'), ('retained', 1, 'retained'), ('pc', 7, 'pc'),
    ('virtual_pc', 10, 'virtualPC'), ('virtual_span', 11, 'virtualSpan'),
    ('current_control', 22, 'currentControl'),
    ('outer', 3, 'outer'), ('inner', 3, 'inner'), ('remaining', 8, 'remaining'),
    ('levels', 3, 'levels'), ('enabled', 3, 'enabled'),
    ('tx_data', 32, 'txData'), ('tx_length', 6, 'txLength'),
    ('tx_consumed', 6, 'txConsumed'), ('rx_data', 32, 'rxData'),
    ('rx_length', 6, 'rxLength'), ('rx_capacity', 6, 'rxCapacity'),
    ('stage1', 2, 'stage1'), ('stage2', 2, 'stage2'),
    ('wait_left', 8, 'waitLeft'), ('scratch', 16, 'scratch'),
    ('cached_duration', 8, 'cachedDuration'), ('cached_budget', 8, 'cachedBudget'),
    ('cached_check', 4, 'cachedCheck'), ('cached_wait', 2, 'cachedWait'),
    ('cached_terminal', 6, 'cachedTerminal'), ('cached_branch', 54, 'cachedBranch'),
]
BASE_OUTPUTS = [
    ('valid', 1, 'valid'), ('busy', 1, 'busy'), ('retained', 1, 'retained'),
    ('pending', 1, 'pending'), ('rejected', 1, 'rejected'), ('mode', 2, 'mode'),
    ('pc', 8, 'pc'), ('remaining', 8, 'remaining'), ('levels', 3, 'levels'),
    ('enabled', 3, 'enabled'), ('tx_consumed', 6, 'txConsumed'),
    ('rx_length', 6, 'rxLength'), ('rx_data', 32, 'rxData'),
    ('read_valid', 1, 'readValid'), ('read_bit', 1, 'readBit'),
    ('generation', 16, 'generation'), ('transfer', 16, 'transfer'),
    ('exhausted', 1, 'exhausted'), ('stage1', 2, 'stage1'), ('stage2', 2, 'stage2'),
    ('virtual_pc', 10, 'virtualPC'), ('env0', 3, 'env0'), ('env1', 3, 'env1'),
    ('phase', 3, 'phase'), ('wait_left', 8, 'waitLeft'), ('scratch', 16, 'scratch'),
]


def read_json(path):
    """Reject duplicate keys before the reused reader sees a JSON artifact."""
    def unique(items):
        result = {}
        for key, value in items:
            if key in result:
                raise ValueError('Duplicate JSON key: ' + key)
            result[key] = value
        return result
    return json.loads(Path(path).read_text(), object_pairs_hook=unique)


def backend():
    name = '_pinwheel_buffered_sram_readback'
    spec = importlib.util.spec_from_file_location(name, ROOT / 'scripts/backend_readback.py')
    rb = importlib.util.module_from_spec(spec)
    sys.modules[name] = rb
    spec.loader.exec_module(rb)
    rb.TOP = TOP
    rb.INPUTS = {name: (width, f'.base .{ctor}')
                 for name, width, ctor in BASE_INPUTS}
    rb.INPUTS.update({'mem_q0': (64, '.q false'), 'mem_q1': (64, '.q true')})
    rb.REGISTERS = {f'r_metadata{k}': (28, f'.metadata {k}#6') for k in range(64)}
    rb.REGISTERS.update({f'r_branch{k}': (56, f'.branch {k}#4') for k in range(16)})
    rb.REGISTERS['r_branch_written'] = (16, '.branchWritten')
    rb.REGISTERS.update({'r_' + name: (width, f'.core .{ctor}')
                         for name, width, ctor in CORE_REGISTERS})
    rb.REGISTERS['r_start_word'] = (64, '.startWord')
    rb.OUTPUTS = {name: (width, f'.base .{ctor}')
                  for name, width, ctor in BASE_OUTPUTS}
    rb.OUTPUTS.update({
        'mem_addr0': (6, '.port (.address false)'),
        'mem_addr1': (6, '.port (.address true)'),
        'mem_data': (64, '.port .data'),
        'mem_write': (1, '.port .write'),
        'mem_read': (1, '.port .read'),
    })
    rb.HEADER = f'''import Pinwheel.Hardware.Buffered.Sram
open Pinwheel.Hardware
open Pinwheel.Hardware.Buffered
namespace {NAMESPACE}
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
'''
    return rb


def adapt(text):
    return text.replace('Values Machine.Input', 'Values Sram.Input').replace(
        'Values Register', 'Values Sram.Register').replace(
        'Values Machine.Output', 'Values Sram.Output').replace(
        'Pinwheel.Artifact.Backend', NAMESPACE)


def check_interface(rb, interface):
    if type(interface.get('schema')) is not int or interface.get('schema') != 1 or interface.get('module') != TOP:
        raise ValueError('Changed buffered SRAM assembly module/schema')
    for name, expected in [('inputs', rb.INPUTS), ('registers', rb.REGISTERS),
                           ('outputs', rb.OUTPUTS)]:
        entries = interface.get(name)
        if not isinstance(entries, list) or any(not isinstance(e, dict) for e in entries):
            raise ValueError('Invalid interface entries: ' + name)
        actual = {e.get('name'): e.get('width') for e in entries}
        if len(actual) != len(entries) or any(type(e.get('width')) is not int for e in entries):
            raise ValueError('Invalid interface entries: ' + name)
        if actual != {n: w for n, (w, _) in expected.items()}:
            raise ValueError('Changed buffered SRAM interface: ' + name)
        if name == 'registers' and any(e.get('reference') != e['name'] for e in entries):
            raise ValueError('Changed buffered SRAM register references')


def validate_graph(rb, graph):
    """Check complete, width-consistent, acyclic endpoint graphs before printing Lean."""
    seen = set()
    unary = {'not', 'slice'}
    binary = {'and', 'or', 'xor', 'add', 'sub', 'eq', 'lt', 'concat'}
    for name, node in graph.nodes.items():
        if type(node.width) is not int or node.width <= 0:
            raise ValueError('Invalid graph width: ' + name)
        if any(arg not in seen for arg in node.args):
            raise ValueError('Forward or missing graph reference: ' + name)
        widths = [graph.nodes[arg].width for arg in node.args]
        if node.op in ('input', 'reg'):
            expected = rb.INPUTS if node.op == 'input' else rb.REGISTERS
            if name not in expected or node.value != name or node.args or node.width != expected[name][0]:
                raise ValueError('Changed graph leaf contract: ' + name)
        elif node.op == 'lit':
            if node.args or type(node.value) is not int or not 0 <= node.value < 2 ** node.width:
                raise ValueError('Invalid graph literal: ' + name)
        elif node.op in unary:
            if len(widths) != 1:
                raise ValueError('Invalid unary graph arity: ' + name)
            if node.op == 'slice':
                if type(node.value) is not int or not 0 <= node.value <= widths[0] - node.width:
                    raise ValueError('Invalid graph slice: ' + name)
            elif widths[0] != node.width:
                raise ValueError('Invalid graph inversion width: ' + name)
        elif node.op in binary:
            if len(widths) != 2:
                raise ValueError('Invalid binary graph arity: ' + name)
            if node.op == 'concat':
                valid = sum(widths) == node.width
            elif node.op in ('eq', 'lt'):
                valid = widths[0] == widths[1] and node.width == 1
            else:
                valid = widths[0] == widths[1] == node.width
            if not valid:
                raise ValueError('Invalid binary graph width: ' + name)
        elif node.op == 'mux':
            if widths != [1, node.width, node.width]:
                raise ValueError('Invalid graph mux width: ' + name)
        else:
            raise ValueError('Unsupported graph operation: ' + node.op)
        seen.add(name)
    for kind, roots, interface in [('state', graph.next, rb.REGISTERS),
                                    ('output', graph.outputs, rb.OUTPUTS)]:
        if set(roots) != set(interface):
            raise ValueError('Incomplete graph ' + kind + ' contract')
        for name, node in roots.items():
            if node not in graph.nodes or graph.nodes[node].width != interface[name][0]:
                raise ValueError('Invalid graph endpoint width: ' + name)
    return graph


def read_hints(rb, path):
    return validate_graph(rb, rb.read_hints(Path(path)))


def read_rtl(rb, path):
    read_json(path)
    return validate_graph(rb, rb.read_rtl(Path(path)))


def graph_source(rb, graph, namespace='RTL'):
    return adapt(rb.HEADER + graph.definitions(namespace) + f'end {NAMESPACE}\n')


def signatures(graph, samples=1024):
    """Untrusted matching hints with both arbitrary and guard-exercising samples.

    Uniform random coverage masks virtually never admit COMMIT.  Correlated
    examples expose that shared predicate without turning its truth into a
    premise: SMT suggests the resulting cuts and Lean proves them universally.
    """
    rng = random.Random(0x425546465352414D)
    values = {}
    def leaf(name, width, k):
        arbitrary = rng.getrandbits(width)
        profile = k % 8
        if profile < 4:
            return arbitrary
        word = [0, 1, (1 << 22) + 1, (1 << 22) + 2, 3, 5, 6, 4][k // 8 % 8]
        fields = {
            'initialize': 0, 'command': 2 if profile == 4 else 3 if profile == 5 else 0,
            'count': 1 if profile == 4 else 64, 'virtual_span': 1024,
            'expected_generation': 10, 'expected_transfer': 20,
            'tx_length': 32, 'rx_capacity': 32,
            'tx_data': arbitrary, 'raw_inputs': k // 8 % 4,
            'mem_q0': word, 'mem_q1': word,
            'r_written': (1 << 64) - 1, 'r_branch_written': 65535,
            'r_pending': 1, 'r_valid': 1, 'r_generation': 10, 'r_transfer': 20,
            'r_count': 64, 'r_virtual_span': 1024,
            'r_phase': 0 if profile in (4, 5) else 1 if profile == 6 else (k // 8 % 5) + 1,
            'r_remaining': 0, 'r_wait_left': k // 8 % 2,
            'r_pc': k // 8 % 63, 'r_virtual_pc': k // 8 % 64,
            'r_retained': 0, 'r_start_word': word,
            'r_tx_data': arbitrary, 'r_tx_length': 32, 'r_rx_capacity': 32,
            'r_tx_consumed': k // 8 % 33, 'r_rx_length': k // 8 % 33,
            'r_stage1': k // 8 % 4, 'r_stage2': k // 16 % 4,
            'r_cached_check': k // 8 % 16, 'r_cached_wait': k // 8 % 4,
        }
        return fields.get(name, 0) & (2 ** width - 1)
    for name, node in graph.nodes.items():
        mask = 2 ** node.width - 1
        if node.op in ('input', 'reg'):
            values[name] = tuple(leaf(name, node.width, k) for k in range(samples))
            continue
        if node.op == 'lit':
            values[name] = (node.value,) * samples
            continue
        arguments = [values[arg] for arg in node.args]
        def evaluate(k):
            x = [argument[k] for argument in arguments]
            if node.op == 'slice': return x[0] >> node.value
            if node.op == 'concat': return (x[0] << graph.nodes[node.args[1]].width) | x[1]
            if node.op == 'not': return ~x[0]
            if node.op == 'and': return x[0] & x[1]
            if node.op == 'or': return x[0] | x[1]
            if node.op == 'xor': return x[0] ^ x[1]
            if node.op == 'add': return x[0] + x[1]
            if node.op == 'sub': return x[0] - x[1]
            if node.op == 'eq': return int(x[0] == x[1])
            if node.op == 'lt': return int(x[0] < x[1])
            if node.op == 'mux': return x[1] if x[0] == 1 else x[2]
            raise ValueError('Unknown signature operation: ' + node.op)
        values[name] = tuple(evaluate(k) & mask for k in range(samples))
    return {name: (graph.nodes[name].width, data) for name, data in values.items()}


def partitions(rb, source, rtl, solver, *, forced_pairs=None, semantic_pairs=None):
    """Propose every useful acyclic shared cut, including narrow control muxes.

    The paired design's restricted cut heuristic leaves buffered prospective
    addresses as very large endpoints.  Here all nonconstant matching nodes may
    be cut.  The solver still supplies only a proposal: each local equality and
    every reconnection is reconstructed in Lean.
    """
    import paired_readback as pr
    oracle = rb.cut_oracle(solver)
    source_signatures = signatures(source)
    candidates = defaultdict(list)
    for name, signature in signatures(rtl).items():
        candidates[signature].append(name)
    forced = {source.next[name]: rtl.next[name] for name in rb.REGISTERS}
    forced.update({source.outputs[name]: rtl.outputs[name] for name in rb.OUTPUTS})
    forced.update(forced_pairs or {})
    semantic_pairs = semantic_pairs or {}
    for sn, (rn, _) in semantic_pairs.items():
        if sn not in source.nodes or rn not in rtl.nodes or source.nodes[sn].width != rtl.nodes[rn].width:
            raise ValueError('Invalid semantic cut interface: ' + sn)
    scuts, rcuts, pairs = {}, set(), []
    for sn, node in source.nodes.items():
        if node.op in ('lit', 'input', 'reg'):
            continue
        if sn in semantic_pairs:
            rn = semantic_pairs[sn][0]
        elif sn in forced:
            rn = forced[sn]
        else:
            if len(set(source_signatures[sn][1])) == 1:
                continue
            choices = candidates.get(source_signatures[sn], [])
            if not choices:
                continue
            rn = min(choices, key=lambda n: (rtl.nodes[n].op != node.op,
                                             rtl.nodes[n].op in ('reg', 'input')))
        allowed = set(rcuts)

        def variable(n):
            item = rtl.nodes[n]
            if item.op in ('input', 'reg'):
                key = (item.width, item.op, item.value)
            else:
                used.add(n)
                key = (item.width, 'rtl', n)
            if key not in variables:
                variables[key] = len(variables)
            return item.width, 'var', (), variables[key]

        def view(n, base):
            if n == base:
                return variable(base)
            item = rtl.nodes[n]
            definitions.add('RTL.' + n)
            return item.width, item.op, tuple(view(a, base) for a in item.args), item.value

        def expand(graph, n, namespace, root=False):
            key = namespace, n, root
            if key in memo:
                return memo[key]
            item = graph.nodes[n]
            if item.op in ('reg', 'input'):
                return variable(n)
            if not root and namespace == 'Source' and n in scuts:
                index, matching, base = scuts[n]
                if base in allowed:
                    dependencies.add(index)
                    result = view(matching, base)
                    memo[key] = result
                    return result
            if not root and namespace == 'RTL' and n in allowed:
                return variable(n)
            definitions.add(namespace + '.' + n)
            result = item.width, item.op, tuple(expand(graph, child, namespace)
                                                 for child in item.args), item.value
            memo[key] = result
            return result

        while True:
            variables, definitions, dependencies, memo, used = {}, set(), set(), {}, set()
            left = expand(source, sn, 'Source', root=True)
            left_cuts = set(used)
            used = set()
            right = expand(rtl, rn, 'RTL', root=rn not in rcuts)
            remove = left_cuts ^ used
            if not remove:
                break
            allowed -= remove
        sizes = {}
        def size(tree):
            if id(tree) not in sizes:
                sizes[id(tree)] = 1 + sum(size(a) for a in tree[2])
            return sizes[id(tree)]
        pair = {'source': sn, 'rtl': rn, 'left': left, 'right': right,
                'variables': tuple(variables), 'definitions': sorted(definitions),
                'dependencies': sorted(dependencies), 'size': size(left) + size(right)}
        if pair['size'] > 2000 and sn not in forced and sn not in semantic_pairs:
            continue
        if sn in semantic_pairs:
            pair['manual'] = semantic_pairs[sn][1]
        elif not oracle(pair):
            continue
        index = len(pairs)
        pairs.append(pair)
        base = rtl.views.get(rn, rn)
        scuts[sn] = index, rn, base
        rcuts.add(base)
        if len(pairs) % 500 == 0:
            print(f'partitioned SRAM {len(pairs)} ({sn})', flush=True)
    matches = {(pair['source'], pair['rtl']) for pair in pairs}
    endpoints = [(source.next[name], rtl.next[name]) for name in rb.REGISTERS]
    endpoints += [(source.outputs[name], rtl.outputs[name]) for name in rb.OUTPUTS]
    for sn, rn in endpoints:
        if (sn, rn) in matches:
            continue
        if source.nodes[sn].op in ('input', 'reg', 'lit') and sn == rn:
            continue
        pair = pr.constrained_pair(rb, source, rtl, pairs, sn, rn, oracle)
        pair = pr.expand_constraints(pr.minimize_constraints(rb, pair, solver))
        if not oracle(pair):
            raise ValueError('Expanded SRAM endpoint proposal is invalid: ' + sn)
        pairs.append(pair)
        matches.add((sn, rn))
    return pairs


def comparison_abstractions(rb, pairs, solver):
    """Suggest stronger local equalities over independent one-bit comparison atoms.

    No assertion is added. Lean proves the stronger equality for every fresh
    atom, then instantiates it with the original comparison expression.
    """
    oracle = rb.cut_oracle(solver)
    result = []
    for pair in pairs:
        atoms = {}
        def key(tree):
            return json.dumps(tree, separators=(',', ':'))
        def collect(tree):
            if tree[1] in ('eq', 'lt') and tree[2][0][0] > 1:
                atoms.setdefault(key(tree), tree)
            for child in tree[2]:
                collect(child)
        collect(pair['left'])
        collect(pair['right'])
        if not atoms:
            result.append(pair)
            continue
        def proposed(selected):
            indices = {name: len(pair['variables']) + k for k, name in enumerate(selected)}
            def replace(tree):
                name = key(tree)
                if name in indices:
                    return 1, 'var', (), indices[name]
                return tree[0], tree[1], tuple(replace(child) for child in tree[2]), tree[3]
            return {**pair, 'left': replace(pair['left']), 'right': replace(pair['right']),
                    'variables': [*pair['variables'], *((1, 'atom', k) for k in range(len(selected)))]}
        selected = list(atoms)
        candidate = proposed(selected)
        if not oracle(candidate):
            selected = []
            for name in atoms:
                trial = proposed([*selected, name])
                if oracle(trial):
                    selected.append(name)
            candidate = proposed(selected)
        if selected:
            result.append({**pair, 'abstract': {
                'left': candidate['left'], 'right': candidate['right'],
                'variables': candidate['variables'], 'atoms': [atoms[name] for name in selected]}})
        else:
            result.append(pair)
    return result


def model_source(rb, rtl, graph_module='SramArtifactGraphs'):
    """Lift the exact raw-state graph, with only the typed unused word ghosts zeroed."""
    value = lambda node: rb.graph_value(rtl, node, 'RTL')
    lines = [f'import {graph_module}\n' + rb.HEADER,
             'def rtlStep (i : Values Sram.Input) (s : Values Sram.Register) : Values Sram.Register']
    for family, count in [('metadata', 64), ('branch', 16)]:
        values = ', '.join('(' + value(rtl.next[f'r_{family}{k}']) + ')' for k in range(count))
        lines.append(f"  | _, .{family} k => (#[{values}])[k.toNat]'(by exact k.isLt)")
    lines.append(f"  | _, .branchWritten => {value(rtl.next['r_branch_written'])}")
    for name, _, ctor in CORE_REGISTERS:
        lines.append(f"  | _, .core .{ctor} => {value(rtl.next['r_' + name])}")
    # These constructors exist in the typed register family but are absent from
    # Sram.registers and every controller expression.  Actual coreNext is 0 too.
    lines.append('  | _, .core (.word _) => 0')
    lines.append(f"  | _, .startWord => {value(rtl.next['r_start_word'])}")
    lines.append('def rtlObserve (i : Values Sram.Input) (s : Values Sram.Register) : Values Sram.Output')
    for name, (_, ctor) in rb.OUTPUTS.items():
        lines.append(f'  | _, {ctor} => {value(rtl.outputs[name])}')
    lines.append(f'end {NAMESPACE}\n')
    return '\n'.join(lines)


def source_endpoints_source(rb, source, hints_module='SramArtifactHints', names=None):
    """First attempt: kernel conversion checks each full typed expression directly."""
    names = names or [('next', name) for name in rb.REGISTERS] + [
        ('output', name) for name in rb.OUTPUTS]
    lines = [f'import {hints_module}\n' + rb.HEADER]
    for kind, name in names:
        roots, interface, method = ((source.next, rb.REGISTERS, 'step') if kind == 'next'
                                    else (source.outputs, rb.OUTPUTS, 'observe'))
        lhs = rb.graph_value(source, roots[name], 'Source')
        lines.append(f'''theorem source_{kind}_{name} (i : Values Sram.Input) (s : Values Sram.Register) :
    {lhs} = Sram.circuit.{method} i s ({interface[name][1]}) := by
  rfl
''')
    lines.append(f'end {NAMESPACE}\n')
    return '\n'.join(lines)


def local_proofs_source(rb, pairs):
    """Only kernel-reconstructed arithmetic/bit proofs; SMT chooses cuts, never proofs."""
    prelude = '''private theorem inv_lt_zero (x : BitVec n) :
    (~~~(BitVec.ofBool (decide ((0#n).toNat < x.toNat)))) = BitVec.ofBool (decide (x = 0#n)) := by
  rw [BitVec.not_ofBool]
  apply congrArg BitVec.ofBool
  rw [← decide_not]
  simp only [BitVec.toNat_eq, BitVec.toNat_zero, Nat.not_lt, Nat.le_zero]

private theorem lt_zero (x : BitVec n) :
    BitVec.ofBool (decide ((0#n).toNat < x.toNat)) = ~~~(BitVec.ofBool (decide (x = 0#n))) := by
  simpa only [BitVec.not_not] using congrArg (fun v : BitVec 1 => ~~~v) (inv_lt_zero x)

private theorem gate_if : ∀ a b : BitVec 1, (if a = 1 then b else 0#1) = a &&& b := by
  decide +kernel

private theorem gate_if_else : ∀ a b : BitVec 1, (if a = 1 then 0#1 else b) = ~~~a &&& b := by
  decide +kernel

private theorem gate_if_one : ∀ a b : BitVec 1, (if a = 1 then 1#1 else b) = a ||| b := by
  decide +kernel

private theorem gate_if_else_one : ∀ a b : BitVec 1, (if a = 1 then b else 1#1) = ~~~a ||| b := by
  decide +kernel
'''
    proof_pairs = [{**pair, **{key: pair['abstract'][key] for key in ('left', 'right', 'variables')}}
                   if 'abstract' in pair else pair for pair in pairs]
    text = adapt(rb.helper_source(proof_pairs))
    wrappers = []
    for k, pair in enumerate(pairs):
        if 'abstract' not in pair:
            continue
        text = text.replace(f'theorem local_{k} ', f'private theorem abstract_local_{k} ', 1)
        params = ' '.join(f'(x{j} : BitVec {width})'
                          for j, (width, _, _) in enumerate(pair['variables']))
        actual = [f'x{j}' for j in range(len(pair['variables']))]
        actual += ['(' + rb.render_tree(atom) + ')' for atom in pair['abstract']['atoms']]
        wrappers.append(f'''theorem local_{k} {params} :
    {rb.render_tree(pair['left'])} = {rb.render_tree(pair['right'])} :=
  abstract_local_{k} {' '.join(actual)}
''')
    text = text.replace(f'end {NAMESPACE}\n', '\n'.join(wrappers) + f'\nend {NAMESPACE}\n')
    text = text.replace('set_option linter.unusedSimpArgs false',
                        'set_option linter.unusedSimpArgs false\n' + prelude)
    text = text.replace('  try simp only [BitVec.sub_eq_add_neg]',
                        '  try simp only [inv_lt_zero, lt_zero, BitVec.not_not, gate_if, gate_if_else, gate_if_one, gate_if_else_one, BitVec.and_assoc, BitVec.or_assoc]\n  try simp only [BitVec.sub_eq_add_neg]')
    text = text.replace(' | grind\n', ' | grind (splits := 128)\n')
    text = text.replace('all_goals grind)\n', 'all_goals grind (splits := 128))\n')
    return text.replace('  all_goals first\n  |\n', '''  all_goals first
  | (simp only [BitVec.not_ofBool, BitVec.not_not, Bool.not_not]
     apply congrArg BitVec.ofBool
     apply Bool.eq_iff_iff.mpr
     simp only [Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not,
       BitVec.toNat_eq, BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
     omega)
  | (apply BitVec.eq_of_toNat_eq
     simp only [BitVec.toNat_ofBool, Bool.toNat, Bool.cond_decide,
       BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
     first | omega | (split <;> omega))
  |
''')


def links_source(rb, source, rtl, pairs, hints_module='SramArtifactHints',
                 proofs_module='SramArtifactLocalProofs', graph_module='SramArtifactGraphs'):
    return f'import {hints_module}\n' + adapt(rb.links_source(
        source, rtl, pairs, proofs_module, graph_module))


def endpoints_source(rb, source, rtl, pairs, source_module='SramArtifactSources',
                     links_module='SramArtifactLinks', model_module='SramArtifactModel'):
    matches = {(p['source'], p['rtl']): k for k, p in enumerate(pairs)}
    lines = [f'import {source_module}\nimport {links_module}\nimport {model_module}\n' + rb.HEADER]
    for operation, roots, actual, interface in [('next', source.next, rtl.next, rb.REGISTERS),
                                               ('output', source.outputs, rtl.outputs, rb.OUTPUTS)]:
        method = 'Step' if operation == 'next' else 'Observe'
        action = 'step' if operation == 'next' else 'observe'
        for name, sn in roots.items():
            rn = actual[name]
            lines.append(f'''theorem rtl_{operation}_{name} (i : Values Sram.Input) (s : Values Sram.Register) :
    rtl{method} i s ({interface[name][1]}) = Sram.circuit.{action} i s ({interface[name][1]}) := by
  change ({rb.graph_value(rtl, rn, 'RTL')}) = _''')
            if (sn, rn) in matches:
                lines.append(f'  exact (link_{matches[(sn, rn)]} i s).symm.trans (source_{operation}_{name} i s)')
            elif sn == rn and source.nodes[sn].op in ('input', 'reg', 'lit'):
                lines.append(f'  exact source_{operation}_{name} i s')
            else:
                raise ValueError('Missing certified SRAM endpoint: ' + name)
    lines.append(f'end {NAMESPACE}\n')
    return '\n'.join(lines)


def proof_source(rb, endpoint_module='SramArtifactEndpoints', model_module='SramArtifactModel'):
    """Totality over the typed families, not just a checked list of chosen roots."""
    lines = [f'import {endpoint_module}\nimport {model_module}\n' + rb.HEADER,
             'theorem step_correct (i : Values Sram.Input) (s : Values Sram.Register)',
             '    (r : Sram.Register w) : rtlStep i s r = Sram.circuit.step i s r := by',
             '  cases r with']
    for family, count, width in [('metadata', 64, 6), ('branch', 16, 4)]:
        term = '(fun j => Fin.elim0 j)'
        for k in reversed(range(count)):
            term = f'(Fin.cases (rtl_next_r_{family}{k} i s) {term})'
        lines.extend([f'  | {family} k =>',
                      f'    have h : ∀ j : Fin {count}, rtlStep i s (.{family} (BitVec.ofFin j)) =',
                      f'        Sram.circuit.step i s (.{family} (BitVec.ofFin j)) := {term}',
                      '    exact h k.toFin'])
    lines.extend(['  | branchWritten => exact rtl_next_r_branch_written i s',
                  '  | startWord => exact rtl_next_r_start_word i s',
                  '  | core r =>', '    cases r with', '    | word _ => rfl'])
    for name, _, ctor in CORE_REGISTERS:
        lines.append(f'    | {ctor} => exact rtl_next_r_{name} i s')
    lines.extend(['', 'theorem observe_correct (i : Values Sram.Input) (s : Values Sram.Register)',
                  '    (o : Sram.Output w) : rtlObserve i s o = Sram.circuit.observe i s o := by',
                  '  cases o with', '  | base o =>', '    cases o with'])
    for name, _, ctor in BASE_OUTPUTS:
        lines.append(f'    | {ctor} => exact rtl_output_{name} i s')
    lines.extend(['  | port p =>', '    cases p with', '    | address b =>', '      cases b with',
                  '      | false => exact rtl_output_mem_addr0 i s',
                  '      | true => exact rtl_output_mem_addr1 i s',
                  '    | data => exact rtl_output_mem_data i s',
                  '    | write => exact rtl_output_mem_write i s',
                  '    | read => exact rtl_output_mem_read i s',
                  f'end {NAMESPACE}\n'])
    return '\n'.join(lines)


def hint_certificate_sources(rb, source, rtl, pairs):
    """A complete imported-RTL ↔ emitted-MLIR certificate, before typed linkage."""
    model = model_source(rb, source, 'SramArtifactHints').replace(
        'RTL.', 'Source.').replace('rtlStep', 'hintStep').replace('rtlObserve', 'hintObserve')
    lines = ['import SramArtifactLinks\nimport SramArtifactModel\nimport SramArtifactHintModel\n' + rb.HEADER]
    matches = {(pair['source'], pair['rtl']): k for k, pair in enumerate(pairs)}
    for kind, original, imported, interface in [('next', source.next, rtl.next, rb.REGISTERS),
                                                ('output', source.outputs, rtl.outputs, rb.OUTPUTS)]:
        method = 'Step' if kind == 'next' else 'Observe'
        for name, sn in original.items():
            rn = imported[name]
            lines.append(f'''theorem hint_rtl_{kind}_{name} (i : Values Sram.Input) (s : Values Sram.Register) :
    rtl{method} i s ({interface[name][1]}) = hint{method} i s ({interface[name][1]}) := by
  change ({rb.graph_value(rtl, rn, 'RTL')}) = ({rb.graph_value(source, sn, 'Source')})''')
            if (sn, rn) in matches:
                lines.append(f'  exact (link_{matches[(sn, rn)]} i s).symm')
            elif sn == rn and source.nodes[sn].op in ('input', 'reg', 'lit'):
                lines.append('  rfl')
            else:
                raise ValueError('Missing imported-RTL/MLIR endpoint: ' + name)
    lines.append(f'end {NAMESPACE}\n')
    proof = proof_source(rb, 'SramArtifactHintEndpoints')
    proof = proof.replace('Sram.circuit.step', 'hintStep').replace(
        'Sram.circuit.observe', 'hintObserve').replace('rtl_next_', 'hint_rtl_next_').replace(
        'rtl_output_', 'hint_rtl_output_').replace('theorem step_correct', 'theorem rtl_hint_step_correct').replace(
        'theorem observe_correct', 'theorem rtl_hint_observe_correct')
    return {'SramArtifactHintModel': model,
            'SramArtifactHintEndpoints': '\n'.join(lines), 'SramArtifactHintProof': proof}


def census(rb, graph):
    return {'module': TOP, 'inputs': len(rb.INPUTS), 'registers': len(rb.REGISTERS),
            'register_bits': sum(w for w, _ in rb.REGISTERS.values()),
            'outputs': len(rb.OUTPUTS), 'nodes': len(graph.nodes),
            'operations': dict(sorted(Counter(n.op for n in graph.nodes.values()).items()))}


def reference_partitions(rb, reference, mlir, solver):
    """Propose graph links with one separately reconstructed selection theorem.

    The two named scalar candidates are artifact-specific hints. The selection
    generator checks the entire tree shape and Lean discharges both prerequisites
    from earlier scalar links; no equality becomes an external premise.
    """
    pairs = partitions(rb, reference, mlir, solver,
        forced_pairs={'v117': 'v1576'},
        semantic_pairs={'p_v974': ('v1856', 'selection_entry')})
    ordinary = [pair for pair in pairs if 'manual' not in pair]
    abstract = iter(comparison_abstractions(rb, ordinary, solver))
    return [pair if 'manual' in pair else next(abstract) for pair in pairs]


def reference_certificate_sources(rb, reference, mlir, environment, pairs):
    """Ordered kernel reconstruction of the factored source→MLIR→RTL bridge.

    Requires the checked CompleteSources and original SramArtifactHint* stages.
    Python only proposes descriptions, cuts, and proof text. Every alias, local
    equality, selection prerequisite, and final endpoint is reconstructed by Lean.
    """
    import buffered_sram_selection as selection
    namespace = NAMESPACE + '.ReferenceLink'
    def rename(text):
        return text.replace(NAMESPACE, namespace)
    header = rename(adapt(rb.HEADER))
    modules = {}
    modules['ReferenceHints'] = rename(graph_source(rb, reference, 'Source'))
    modules['ReferenceGraphs'] = rename(graph_source(rb, mlir, 'RTL'))
    lines = ['import ReferenceHints\nimport CompleteSources\n' + header]
    for name, node in reference.nodes.items():
        if node.op in ('input', 'reg'):
            continue
        left = rb.graph_value(reference, name, 'Source')
        right = rb.graph_value(reference, name, 'Pinwheel.Artifact.SramReference.Composed')
        rules = ['Source.' + name, 'Pinwheel.Artifact.SramReference.Composed.' + name]
        if name in environment.nodes:
            rules += ['Pinwheel.Artifact.SramReference.Environment.' + name]
        rules += ['node_' + arg for arg in dict.fromkeys(node.args)
                  if reference.nodes[arg].op not in ('input', 'reg')]
        lines += [f'theorem node_{name} (i : Values Sram.Input) (s : Values Sram.Register) :',
                  f'    {left} = {right} := by',
                  '  simp only [' + ', '.join(rules) + ']', '  all_goals rfl']
    for kind, roots in [('next', reference.next), ('output', reference.outputs)]:
        for name, node in roots.items():
            ctor = (rb.REGISTERS if kind == 'next' else rb.OUTPUTS)[name][1]
            action = 'step' if kind == 'next' else 'observe'
            proof = f'Pinwheel.Artifact.SramReference.source_{kind}_{name} i s'
            if reference.nodes[node].op not in ('input', 'reg'):
                proof = f'(node_{node} i s).trans ({proof})'
            lines += [f'theorem source_{kind}_{name} (i : Values Sram.Input) (s : Values Sram.Register) :',
                      f'    {rb.graph_value(reference, node, "Source")} = Sram.circuit.{action} i s ({ctor}) := by',
                      '  exact ' + proof]
    modules['ReferenceSources'] = '\n'.join(lines) + '\nend ' + namespace + '\n'
    lines = ['import ReferenceGraphs\nimport SramArtifactHints\n' + header]
    for name, node in mlir.nodes.items():
        if node.op in ('input', 'reg'):
            continue
        rules = ['RTL.' + name, NAMESPACE + '.Source.' + name]
        rules += ['target_' + arg for arg in dict.fromkeys(node.args)
                  if mlir.nodes[arg].op not in ('input', 'reg')]
        lines += [f'theorem target_{name} (i : Values Sram.Input) (s : Values Sram.Register) :',
                  f'    {rb.graph_value(mlir, name, "RTL")} = {rb.graph_value(mlir, name, NAMESPACE + ".Source")} := by',
                  '  simp only [' + ', '.join(rules) + ']', '  all_goals rfl']
    modules['ReferenceTargetAliases'] = '\n'.join(lines) + '\nend ' + namespace + '\n'
    manuals = [(k, pair) for k, pair in enumerate(pairs) if 'manual' in pair]
    if len(manuals) != 1:
        raise ValueError('Expected one checked dictionary-selection cut')
    manual_index, manual = manuals[0]
    selection_text, metadata = selection.selection_source(rb, reference, mlir,
        manual['source'], manual['rtl'], namespace=namespace,
        hints_module='ReferenceHints', graphs_module='ReferenceGraphs')
    matches = {(pair['source'], pair['rtl']): k for k, pair in enumerate(pairs)}
    prerequisites = [matches[(metadata['source_' + key], metadata['target_' + key])]
                     for key in ('address', 'instruction')]
    if any(k >= manual_index for k in prerequisites):
        raise ValueError('Selection prerequisites must precede the selection cut')
    dummy = (1, 'lit', (), 0)
    proof_pairs = []
    for pair in pairs:
        if 'manual' in pair:
            proof_pairs.append({**{k: v for k, v in pair.items() if k != 'abstract'},
                                'left': dummy, 'right': dummy, 'variables': []})
        else:
            proof_pairs.append(pair)
    modules['ReferenceLocalProofs'] = rename(local_proofs_source(rb, proof_pairs))
    reconnect = rename(links_source(rb, reference, mlir, pairs,
        hints_module='ReferenceHints', proofs_module='ReferenceLocalProofs', graph_module='ReferenceGraphs'))
    prefix, rest = reconnect.split(f'theorem link_{manual_index} ', 1)
    _, rest = rest.split(f'theorem link_{manual_index + 1} ', 1)
    modules['ReferenceBaseLinks'] = prefix + 'end ' + namespace + '\n'
    modules['ReferenceSelection'] = selection_text
    modules['ReferenceLinks'] = ('import ReferenceBaseLinks\nimport ReferenceSelection\n' + header +
        f'theorem link_{manual_index} (i : Values Sram.Input) (s : Values Sram.Register) :\n'
        f'    Source.{manual["source"]} i s = RTL.{manual["rtl"]} i s := by\n'
        f'  exact selection_entry i s (link_{prerequisites[0]} i s) (link_{prerequisites[1]} i s)\n\n'
        f'theorem link_{manual_index + 1} ' + rest)
    modules['ReferenceModel'] = rename(model_source(rb, mlir, graph_module='ReferenceGraphs'))
    modules['ReferenceTypedEndpoints'] = rename(endpoints_source(rb, reference, mlir, pairs,
        source_module='ReferenceSources', links_module='ReferenceLinks', model_module='ReferenceModel'))
    lines = ['import ReferenceTypedEndpoints\nimport ReferenceTargetAliases\n'
             'import SramArtifactHintEndpoints\nimport SramArtifactModel\n' + adapt(rb.HEADER)]
    for kind, roots in [('next', mlir.next), ('output', mlir.outputs)]:
        for name, node in roots.items():
            ctor = (rb.REGISTERS if kind == 'next' else rb.OUTPUTS)[name][1]
            action = 'step' if kind == 'next' else 'observe'
            method = 'Step' if kind == 'next' else 'Observe'
            proof = f'{namespace}.rtl_{kind}_{name} i s'
            if mlir.nodes[node].op not in ('input', 'reg'):
                proof = f'({namespace}.target_{node} i s).symm.trans ({proof})'
            lines += [f'theorem rtl_{kind}_{name} (i : Values Sram.Input) (s : Values Sram.Register) :',
                      f'    rtl{method} i s ({ctor}) = Sram.circuit.{action} i s ({ctor}) := by',
                      f'  exact (hint_rtl_{kind}_{name} i s).trans ({proof})']
    modules['SramArtifactEndpoints'] = '\n'.join(lines) + '\nend ' + NAMESPACE + '\n'
    modules['SramArtifactProof'] = proof_source(rb)
    return modules
