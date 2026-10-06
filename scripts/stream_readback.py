"""Strict artifact interpretation for the additive paired stream supervisor.

Reuse the paired graph importer and partition generator in a private instance.
The extra register and its enclosing typed constructors are explicit. Neither
the retained interface nor its initialized-session theorem is widened.
"""
import hashlib
import random

import paired_readback as pr

read_json = pr.read_json
check_interface = pr.check_interface
check_cuts = pr.check_cuts
partitions = pr.partitions


def backend(kind):
    rb = pr.backend(kind)
    if kind == 'core':
        rb.REGISTERS = {n: (w, f'.inner ({ctor})') for n, (w, ctor) in rb.REGISTERS.items()}
        rb.REGISTERS['r_stream_enabled'] = (1, '.extra .enabled')
    else:
        for n, (w, ctor) in tuple(rb.REGISTERS.items()):
            if not n.startswith(('r_serial_', 'r_pin_', 'r_result_')):
                # The additional core wrapper sits below the unchanged adapters.
                rb.REGISTERS[n] = (w, ctor.replace('.inner (.inner (.inner (.inner (',
                    '.inner (.inner (.inner (.inner (.inner (') + ')')
        rb.REGISTERS['r_stream_enabled'] = (1, '.inner (.inner (.inner (.inner (.extra .enabled))))')
    rb.HEADER = rb.HEADER.replace('import Pinwheel.Hardware.Storage.PairedSession',
        'import Pinwheel.Hardware.Storage.PairedStream').replace('open PairedController\n',
        'open PairedController (Input GraphInput body bindings)\n'
        'open PairedStream (Register FullRegister)\n')
    return rb


def adapt(text, kind='core'):
    text = text.replace('Values Machine.Input', 'Values Input').replace(
        'namespace Pinwheel.Artifact.Backend', 'namespace Pinwheel.Artifact.Paired').replace(
        'end Pinwheel.Artifact.Backend', 'end Pinwheel.Artifact.Paired')
    if kind == 'chip':
        text = text.replace('Values Input', 'Values (SramController.Reads Chip.Pin)').replace(
            'Values Register', 'Values FullRegister')
    return text


def design_source(rb, kind):
    text = rb.HEADER + '''def validationGraph : PairedComposition.Component Input PairedController.Register (SramController.Out Loader.Machine.Output) where
  step := fun i s => body.step (PairedSemantics.inputs PairedValidation.bindings i s) s
  observe := fun i s => body.observe (PairedSemantics.inputs PairedValidation.bindings i s) s

theorem validation_graph_eq : validationGraph = PairedComposition.graph := by
  simp only [validationGraph, PairedComposition.graph, PairedSemantics.validation_inputs_eq]

def expressionInputs (i : Values Input) (s : Values Register) : Values Input :=
  fun p => (PairedStream.inputExpr p).eval i s
def expressionNext (i : Values Input) (s : Values Register) : Values PairedStream.SupervisorRegister :=
  fun r => (PairedStream.nextExpr r).eval i s
theorem expressionInputs_eq (i : Values Input) (s : Values Register) :
    (@expressionInputs i s : Values Input) = (@PairedStream.effectiveInputs i s : Values Input) := by
  funext w p
  exact PairedStream.inputExpr_correct i s p
theorem expressionNext_eq (i : Values Input) (s : Values Register) :
    (@expressionNext i s : Values PairedStream.SupervisorRegister) =
      (@PairedStream.nextValues i s : Values PairedStream.SupervisorRegister) := by
  funext w r
  exact PairedStream.nextExpr_correct i s r
def expressionWrapped (c : PairedComposition.Component Input PairedController.Register (SramController.Out Loader.Machine.Output)) :
    PairedComposition.Component Input Register (SramController.Out Loader.Machine.Output) where
  step := fun i s => Extended.values (c.step (expressionInputs i s) (Extended.innerValues s)) (expressionNext i s)
  observe := fun i s => c.observe (expressionInputs i s) (Extended.innerValues s)
theorem expressionWrapped_eq (c : PairedComposition.Component Input PairedController.Register (SramController.Out Loader.Machine.Output)) :
    expressionWrapped c = PairedStream.wrapped c := by
  simp only [expressionWrapped, PairedStream.wrapped, expressionInputs_eq, expressionNext_eq]
'''
    if kind == 'core':
        text += '''abbrev reference := expressionWrapped validationGraph
def coreState (s : Values Register) : Values PairedController.Register := Extended.innerValues s
def coreInputs (i : Values Input) (s : Values Register) : Values Input := expressionInputs i s
theorem reference_eq : reference = PairedStream.reference := by
  simp only [reference, expressionWrapped_eq, validation_graph_eq, PairedStream.reference]
'''
    else:
        text += '''def expressionOverlay (s : Values FullRegister) (o : Values (SramController.Out Chip.Output)) : Values (SramController.Out Chip.Output)
  | _, .base .uoOut => (PairedStream.overlayExpr (.input (.base .uoOut))).eval o s
  | _, p => o p
theorem expressionOverlay_eq (s : Values FullRegister) (o : Values (SramController.Out Chip.Output)) :
    (@expressionOverlay s o : Values (SramController.Out Chip.Output)) =
      (@PairedStream.overlay s o : Values (SramController.Out Chip.Output)) := by
  funext w p
  cases p with
  | port p => cases p <;> rfl
  | base p =>
    cases p <;> simp only [expressionOverlay, PairedStream.overlay, PairedStream.overlayExpr,
      PairedStream.enabledBits, Expr.eval, Bool.beq_eq_decide_eq, Reactive.bool_one]
    rfl
def expressionPackaged (c : PairedComposition.Component Input Register (SramController.Out Loader.Machine.Output)) :
    PairedComposition.Component (SramController.Reads Chip.Pin) FullRegister (SramController.Out Chip.Output) where
  step := (PairedStream.basePackaged c).step
  observe := fun i s => expressionOverlay s ((PairedStream.basePackaged c).observe i s)
theorem expressionPackaged_eq (c : PairedComposition.Component Input Register (SramController.Out Loader.Machine.Output)) :
    expressionPackaged c = PairedStream.packaged c := by
  simp only [expressionPackaged, PairedStream.packaged, expressionOverlay_eq]
abbrev reference := expressionPackaged (expressionWrapped validationGraph)
def streamState (s : Values FullRegister) : Values Register :=
  Extended.innerValues (Extended.innerValues (Extended.innerValues (Extended.innerValues s)))
def serialInputs (i : Values (SramController.Reads Chip.Pin)) (s : Values FullRegister) : Values Input :=
  (SramController.bypass Serial.receiver).feed
    ((SramController.bypass Feeder.sampler).feed
      ((SramController.bypass Chip.pinMap).feed i (Extended.extraValues (Extended.innerValues s)))
      (Extended.extraValues (Extended.innerValues (Extended.innerValues s))))
    (Extended.extraValues (Extended.innerValues (Extended.innerValues (Extended.innerValues s))))
def coreState (s : Values FullRegister) : Values PairedController.Register := Extended.innerValues (streamState s)
def coreInputs (i : Values (SramController.Reads Chip.Pin)) (s : Values FullRegister) : Values Input :=
  expressionInputs (serialInputs i s) (streamState s)
theorem reference_eq : reference = PairedStream.packaged PairedStream.reference := by
  simp only [reference, expressionPackaged_eq, expressionWrapped_eq, validation_graph_eq, PairedStream.reference]
'''
    return text + '\nend Pinwheel.Artifact.Paired\n'


def sources_source(rb, source, kind):
    itype = 'Input' if kind == 'core' else '(SramController.Reads Chip.Pin)'
    rtype = 'Register' if kind == 'core' else 'FullRegister'
    # A single unfolding template covers core, adapter and supervisor endpoints;
    # some definitions are unused for a particular projection.
    lines = ['import Equations\n' + rb.HEADER, 'set_option linter.unusedSimpArgs false']
    for operation, roots, interface in [('next', source.next, rb.REGISTERS),
                                        ('output', source.outputs, rb.OUTPUTS)]:
        action = 'step' if operation == 'next' else 'observe'
        for name, node in roots.items():
            lhs, ctor = rb.graph_value(source, node, 'Source'), interface[name][1]
            lines.append(f'theorem source_{operation}_{name} (i : Values {itype}) (s : Values {rtype}) :\n'
                f'    {lhs} = reference.{action} i s ({ctor}) := by\n'
                '  simp only [reference, expressionPackaged, expressionWrapped, PairedStream.basePackaged,\n'
                '    PairedComposition.observed, PairedComposition.fed, validationGraph]\n'
                '  have h := scope_correct i s\n'
                '  dsimp only [coreInputs, coreState, streamState, serialInputs] at h\n'
                '  try rw [h]\n'
                '  rfl')
    # Core Design has no package projections.
    text = '\n'.join(lines)
    if kind == 'core':
        text = text.replace(', streamState, serialInputs', '')
        text = text.replace('expressionPackaged, ', '')
    return text + '\nend Pinwheel.Artifact.Paired\n'


def model_source(rb, graph, kind):
    itype = 'Input' if kind == 'core' else '(SramController.Reads Chip.Pin)'
    rtype = 'Register' if kind == 'core' else 'FullRegister'
    otype = '(SramController.Out Loader.Machine.Output)' if kind == 'core' else '(SramController.Out Chip.Output)'
    lines = ['import Graphs\n' + rb.HEADER]
    def term(node):
        return rb.graph_value(graph, node, 'RTL')
    for operation, interface, roots, result in [('Step', rb.REGISTERS, graph.next, rtype),
                                               ('Observe', rb.OUTPUTS, graph.outputs, otype)]:
        lines.append(f'def rtl{operation} (i : Values {itype}) (s : Values {rtype}) : Values {result}')
        for name, (_, ctor) in interface.items():
            if name.startswith('r_parameter_') or (kind == 'core' and name.startswith('sample')):
                continue
            if name == 'mem_addr0':
                ctor = '.port (.address _)'
            lines.append(f'  | _, {ctor} => {term(roots[name])}')
        if operation == 'Step':
            pattern = '.inner (.parameter b k)' if kind == 'core' else '.inner (.inner (.inner (.inner (.inner (.parameter b k)))))'
            lines.append(f'  | _, {pattern} => if b then')
            for bank in (1, 0):
                values = ', '.join('(' + term(roots[f'r_parameter_b{bank}_w{k}']) + ')' for k in range(32))
                lines.append(f'      (#[{values}])[k.toNat]\'(by exact k.isLt)' + (' else' if bank else ''))
            if kind == 'chip':
                lines.append('  | _, .inner (.extra r) => nomatch r')
        elif kind == 'core':
            values = ', '.join('(' + term(roots[f'sample{k}']) + ')' for k in range(16))
            lines.append(f'  | _, .base (.core (.state (.sample k))) => (#[{values}])[k.val]\'(by exact k.isLt)')
    lines.append(f'def rtlComponent : PairedComposition.Component {itype} {rtype} {otype} := ⟨rtlStep, rtlObserve⟩')
    return '\n'.join(lines) + '\nend Pinwheel.Artifact.Paired\n'


def proof_source(rb, kind):
    # The unchanged exhaustive proof is extended by precisely one constructor.
    text = pr.proof_source(rb, kind)
    start, rest = text.split('theorem model_next', 1)
    step, output = rest.split('theorem model_output', 1)
    if kind == 'core':
        statement, cases = step.split('  cases r with', 1)
        step = statement + '  cases r with\n  | extra r => cases r; exact rtl_next_r_stream_enabled i s\n  | inner r =>\n    cases r with' + cases.replace('\n', '\n  ')
        for bank in ('true', 'false'):
            ctor = f'(.parameter {bank} (BitVec.ofFin j))'
            step = step.replace(ctor, f'(.inner {ctor})')
    else:
        prefix, cases = step.split('        | inner r =>\n          cases r with', 1)
        step = prefix + ('        | inner r =>\n          cases r with\n'
            '          | extra r => cases r; exact rtl_next_r_stream_enabled i s\n'
            '          | inner r =>\n            cases r with') + cases.replace('\n', '\n  ')
        for bank in ('true', 'false'):
            ctor = f'(.inner (.inner (.inner (.inner (.parameter {bank} (BitVec.ofFin j)))))'
            step = step.replace(ctor, f'(.inner {ctor})')
    # Indenting the final newline of the case tree must not indent the next
    # top-level declaration: its tactic body has the original two-space scope.
    text = start + 'theorem model_next' + step.rstrip() + '\n\n' + 'theorem model_output' + output
    text = text[:text.index('theorem component_correct')] + '''theorem component_correct
    (n : Netlist Register (SramController.Out Loader.Machine.Output) Input)
    (hn : PairedStream.core = .ok n) : rtlComponent = COMPONENT := by
  exact component_eq_reference.trans (reference_eq.trans (CORRECT n hn).symm)

#print axioms component_correct
end Pinwheel.Artifact.Paired
'''.replace('COMPONENT', 'n.component' if kind == 'core' else '(PairedStream.package n).component').replace(
        'CORRECT', 'PairedStream.emitted_core_correct' if kind == 'core' else 'PairedStream.emitted_package_correct')
    return text


def _helper_tree(tree):
    """Make the importer tree immutable without changing its expression."""
    return (tree[0], tree[1], tuple(_helper_tree(a) for a in tree[2]), tree[3])


def _helper_nodes(tree):
    yield tree
    for argument in tree[2]:
        yield from _helper_nodes(argument)


def _helper_guards(pair):
    left, right = (_helper_tree(pair[name]) for name in ('left', 'right'))
    predicates = set(_helper_nodes(left)) | set(_helper_nodes(right))
    # The supervisor's scalar data predicates feed Boolean policy only. Keeping
    # them as arbitrary one-bit atoms avoids eager closed-wide-literal reasoning.
    # Cursor predicates retain their numeric relationships in the engine proof.
    return sorted((t for t in predicates if t[1] == 'eq' and t[2][0][0] >= 16
        and all(a[1] in ('var', 'lit') for a in t[2])), key=repr)


_HELPER_ARITY = {'var': 0, 'lit': 0, 'slice': 1, 'not': 1, 'concat': 2,
    'and': 2, 'or': 2, 'xor': 2, 'add': 2, 'sub': 2, 'eq': 2, 'lt': 2, 'mux': 3}


def _helper_require(condition, message):
    if not condition:
        raise ValueError(message)


def _helper_parameters(entries):
    _helper_require(isinstance(entries, (tuple, list)), 'Invalid helper variables')
    variables = []
    for v in entries:
        _helper_require(isinstance(v, (tuple, list)) and len(v) == 3 and
            type(v[0]) is int and v[0] > 0 and type(v[1]) is str and type(v[2]) is str,
            'Invalid helper variables')
        variables.append(tuple(v))
    return tuple(variables)


def _helper_ast_fields(tree):
    _helper_require(isinstance(tree, (tuple, list)) and len(tree) == 4, 'Invalid helper AST')
    width, op, args, value = tree
    _helper_require(isinstance(args, (tuple, list)), 'Invalid helper operands')
    return width, op, args, value


def _helper_typed_node(node, child_widths, variables):
    width, op, children, value = node
    _helper_require(type(width) is int and width > 0, 'Invalid helper width')
    _helper_require(type(op) is str and op in _HELPER_ARITY, 'Invalid helper operator')
    _helper_require(len(children) == len(child_widths) == _HELPER_ARITY[op], 'Invalid helper arity')
    if op == 'var':
        _helper_require(type(value) is int and 0 <= value < len(variables) and
            width == variables[value][0], 'Helper variable changed')
    elif op in ('lit', 'slice'):
        _helper_require(type(value) is int and value >= 0, 'Invalid helper literal or slice')
    else:
        _helper_require(value is None, 'Invalid helper operator value')
        if op == 'concat':
            _helper_require(width == sum(child_widths), 'Helper concat width changed')
        elif op in ('eq', 'lt'):
            _helper_require(width == 1 and child_widths[0] == child_widths[1], 'Helper comparison width changed')
        elif op == 'mux':
            _helper_require(child_widths == (1, width, width), 'Helper mux width changed')
        else:
            _helper_require(all(w == width for w in child_widths), 'Helper operand width changed')


def _helper_dag(pair):
    """Share identical typed syntax only; no Boolean or arithmetic rewrites."""
    variables = _helper_parameters(pair['variables'])
    nodes, lookup, identities, visiting = [], {}, {}, set()

    def intern(tree):
        identity = id(tree)
        _helper_require(identity not in visiting, 'Cyclic helper AST')
        if identity in identities:
            return identities[identity]
        width, op, args, value = _helper_ast_fields(tree)
        visiting.add(identity)
        children = tuple(intern(a) for a in args)
        visiting.remove(identity)
        node = (width, op, children, value)
        _helper_typed_node(node, tuple(nodes[k][0] for k in children), variables)
        if node not in lookup:
            lookup[node] = len(nodes)
            nodes.append(node)
        identities[identity] = lookup[node]
        return lookup[node]

    roots = tuple(intern(pair[side]) for side in ('left', 'right'))
    dag = (variables, tuple(nodes), roots)
    _helper_verify_dag(dag, pair)
    return dag


def _helper_verify_dag(dag, pair):
    """Check topology and exact original AST expansion before emitting a proof.

    In particular, commuted operands and valid but changed literals or variable
    indices fail this check. Lean still checks the equality and its imported
    graph connection; this syntactic check does not accept a circuit.
    """
    variables, nodes, roots = dag
    _helper_require(_helper_parameters(variables) == _helper_parameters(pair['variables']),
        'Helper parameter table changed')
    _helper_require(type(nodes) is tuple and bool(nodes), 'Invalid helper DAG')
    seen = set()
    for index, node in enumerate(nodes):
        _helper_require(isinstance(node, tuple) and len(node) == 4 and type(node[2]) is tuple,
            'Invalid helper DAG node')
        _helper_require(all(type(k) is int and 0 <= k < index for k in node[2]), 'Forward helper DAG reference')
        _helper_typed_node(node, tuple(nodes[k][0] for k in node[2]), variables)
        _helper_require(node not in seen, 'Duplicate helper DAG node')
        seen.add(node)
    _helper_require(type(roots) is tuple and len(roots) == 2 and
        all(type(k) is int and 0 <= k < len(nodes) for k in roots), 'Invalid helper DAG roots')
    _helper_require(nodes[roots[0]][0] == nodes[roots[1]][0], 'Helper equality width changed')
    reachable, compared, visiting = set(), set(), set()

    def compare(tree, index):
        identity = id(tree)
        _helper_require(identity not in visiting, 'Cyclic helper AST')
        if (identity, index) in compared:
            return
        width, op, args, value = _helper_ast_fields(tree)
        node = nodes[index]
        _helper_typed_node((width, op, args, value), tuple(_helper_ast_fields(a)[0] for a in args), variables)
        _helper_require((width, op, value, len(args)) ==
            (node[0], node[1], node[3], len(node[2])), 'Helper DAG expansion changed')
        visiting.add(identity)
        reachable.add(index)
        for child, child_index in zip(args, node[2]):
            compare(child, child_index)
        visiting.remove(identity)
        compared.add((identity, index))

    for side, index in zip(('left', 'right'), roots):
        compare(pair[side], index)
    _helper_require(len(reachable) == len(nodes), 'Unreachable helper DAG node')


def _helper_dag_proposition(rb, dag):
    variables, nodes, roots = dag
    def ref(index):
        return f'x{nodes[index][3]}' if nodes[index][1] == 'var' else f'd{index}'
    lines = []
    for index, (width, op, children, value) in enumerate(nodes):
        if op == 'var':
            continue
        expression = (f'({value} : BitVec {width})' if op == 'lit' else
            rb.Graph.expression(None, rb.Node(width, op, children, value),
                lambda k: '(' + ref(k) + ')'))
        lines.append(f'    let d{index} : BitVec {width} := {expression}')
    lines.append(f'    {ref(roots[0])} = {ref(roots[1])}')
    return '\n'.join(lines)


def _helper_mux_cuts(dag):
    """Suggest branch-aligned data cuts; every selector remains a proof goal.

    Only mux guards are ignored when comparing tree shapes. Widths, branch
    order and leaf node identities must match exactly. Activation contexts are
    the branch conditions common to every dependency path from each root.
    """
    _, nodes, roots = dag
    shapes, counts, lookup = [], [], {}
    for index, (width, op, args, _) in enumerate(nodes):
        if op == 'mux' and width >= 8:
            key = ('mux', width, shapes[args[1]], shapes[args[2]])
            count = 1 + counts[args[1]] + counts[args[2]]
        else:
            key, count = ('leaf', index), 0
        if key not in lookup:
            lookup[key] = len(lookup)
        shapes.append(lookup[key])
        counts.append(count)
    classes = {}
    for index, count in enumerate(counts):
        if count >= 16:
            classes.setdefault(shapes[index], []).append(index)
    candidates = [(a, b) for group in classes.values()
        for offset, a in enumerate(group) for b in group[offset + 1:]]
    candidates.sort(key=lambda pair: (-counts[pair[0]], pair))
    covered, cuts = set(), []

    def branch_pairs(left, right, result):
        if left == right:
            return
        _helper_require(shapes[left] == shapes[right], 'Helper mux shape changed')
        a, b = nodes[left][2], nodes[right][2]
        branch_pairs(a[1], b[1], result)
        branch_pairs(a[2], b[2], result)
        result.append((left, right))

    def activation(root, target):
        paths = {root: set()}
        for index in range(root, -1, -1):
            if index not in paths:
                continue
            _, op, args, _ = nodes[index]
            for position, child in enumerate(args):
                context = set(paths[index])
                if op == 'mux' and position in (1, 2):
                    context.add((args[0], position == 1))
                if child in paths:
                    paths[child].intersection_update(context)
                else:
                    paths[child] = context
        return tuple(sorted(paths.get(target, set())))

    for left, right in candidates:
        if (left, right) in covered:
            continue
        pairs = []
        branch_pairs(left, right, pairs)
        covered.update(pairs)
        selectors = sorted({(nodes[a][2][0], nodes[b][2][0]) for a, b in pairs
            if nodes[a][2][0] != nodes[b][2][0]})
        cuts.append(dict(roots=(left, right), mux_pairs=tuple(pairs), selectors=tuple(selectors),
            contexts=(activation(roots[0], left), activation(roots[1], right))))
    return cuts



_DAG_SUPPORT_SOURCE = '''
theorem dag_mux_congr {w : Nat} (c c' : BitVec 1)
    (a a' b b' : BitVec w) (hc : c = c') (ha : a = a') (hb : b = b') :
    (if c = 1 then a else b) = (if c' = 1 then a' else b') := by
  subst c'
  subst a'
  subst b'
  rfl

theorem dag_bit_mux_one (c a b : BitVec 1) :
    (if c = 1 then a else b) = 1 ↔
      (c = 1 ∧ a = 1) ∨ (c ≠ 1 ∧ b = 1) := by
  rcases BitVec.eq_zero_or_eq_one c with rfl | rfl <;>
    rcases BitVec.eq_zero_or_eq_one a with rfl | rfl <;>
      rcases BitVec.eq_zero_or_eq_one b with rfl | rfl <;> decide +kernel

theorem dag_bit_or_one (a b : BitVec 1) :
    a ||| b = 1 ↔ a = 1 ∨ b = 1 := by
  rcases BitVec.eq_zero_or_eq_one a with rfl | rfl <;>
    rcases BitVec.eq_zero_or_eq_one b with rfl | rfl <;> decide +kernel

theorem dag_bit_xor_one (a b : BitVec 1) :
    a ^^^ b = 1 ↔ (a = 1 ∧ b ≠ 1) ∨ (a ≠ 1 ∧ b = 1) := by
  rcases BitVec.eq_zero_or_eq_one a with rfl | rfl <;>
    rcases BitVec.eq_zero_or_eq_one b with rfl | rfl <;> decide +kernel

theorem dag_extract_compose {w : Nat} (x : BitVec w)
    (s₁ len₁ s₂ len₂ : Nat) (h : s₂ + len₂ ≤ len₁) :
    (x.extractLsb' s₁ len₁).extractLsb' s₂ len₂ =
      x.extractLsb' (s₁ + s₂) len₂ := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  have hin : s₂ + k < len₁ := by omega
  simp only [BitVec.getLsbD_extractLsb', hk, hin, decide_true, Bool.true_and,
    Nat.add_assoc]
'''


def _helper_dag_ref(nodes, index):
    node = nodes[index]
    return f'x{node[3]}' if node[1] == 'var' else f'd{index}'


def _helper_dag_ancestors(nodes, roots):
    result = set()

    def visit(index):
        if index in result:
            return
        result.add(index)
        for child in nodes[index][2]:
            visit(child)

    for root in roots:
        visit(root)
    return result


def _helper_dag_facts(nodes, subset=None):
    """Return (hypothesis name, owner node, proof lines) for uniform local facts.

    Parent equations hdN must already exist with opaque children. All bounds are
    fully instantiated natural literals before their kernel-decide proofs.
    """
    selected = set(range(len(nodes))) if subset is None else set(subset)
    result = []
    for index, (width, operation, args, value) in enumerate(nodes):
        if index not in selected or operation == 'var':
            continue
        node = f'd{index}'
        children = [_helper_dag_ref(nodes, child) for child in args]
        goal = proof = None
        if width == 1:
            if operation == 'and':
                goal = f'{children[0]} = 1 ∧ {children[1]} = 1'
                proof = f'exact stream_bit_and_one {children[0]} {children[1]}'
            elif operation == 'or':
                goal = f'{children[0]} = 1 ∨ {children[1]} = 1'
                proof = f'exact dag_bit_or_one {children[0]} {children[1]}'
            elif operation == 'xor':
                a, b = children
                goal = f'({a} = 1 ∧ {b} ≠ 1) ∨ ({a} ≠ 1 ∧ {b} = 1)'
                proof = f'exact dag_bit_xor_one {a} {b}'
            elif operation == 'not':
                goal = f'{children[0]} ≠ 1'
                proof = f'exact stream_bit_not_one {children[0]}'
            elif operation == 'eq':
                goal = f'{children[0]} = {children[1]}'
                proof = f'exact stream_bit_ofBool_one ({goal})'
            elif operation == 'lt':
                goal = f'({children[0]}).toNat < ({children[1]}).toNat'
                proof = f'exact stream_bit_ofBool_one ({goal})'
            elif operation == 'mux':
                c, a, b = children
                goal = f'({c} = 1 ∧ {a} = 1) ∨ ({c} ≠ 1 ∧ {b} = 1)'
                proof = f'exact dag_bit_mux_one {c} {a} {b}'
        if goal is not None:
            name = f'hg{index}'
            lines = [f'  have {name} : {node} = 1 ↔ ({goal}) := by',
                     f'    rw [h{node}]', f'    {proof}']
            result.append((name, index, lines))
        if operation != 'slice':
            continue
        parent_width, parent_op, parent_args, parent_value = nodes[args[0]]
        proof = goal = None
        rewrites = [f'h{node}']
        if value == 0 and width == parent_width:
            goal = children[0]
            proof = "exact BitVec.extractLsb'_eq_self"
        elif parent_op == 'concat' and value + width <= nodes[parent_args[1]][0]:
            hi, lo = [_helper_dag_ref(nodes, child) for child in parent_args]
            rewrites.append(f'h{children[0]}')
            if value == 0 and width == nodes[parent_args[1]][0]:
                goal = lo
                proof = "exact BitVec.extractLsb'_append_eq_right"
            else:
                goal = f"{lo}.extractLsb' {value} {width}"
                proof = ("exact BitVec.extractLsb'_append_eq_of_add_le "
                         f'(xhi := {hi}) (xlo := {lo}) '
                         f'(start := {value}) (len := {width}) (by decide +kernel)')
        elif parent_op == 'slice' and value + width <= parent_width:
            original = _helper_dag_ref(nodes, parent_args[0])
            rewrites.append(f'h{children[0]}')
            goal = f"{original}.extractLsb' {value + parent_value} {width}"
            proof = (f'exact dag_extract_compose {original} {parent_value} '
                     f'{parent_width} {value} {width} (by decide +kernel)')
        if goal is not None:
            name = f'hs{index}'
            rendered_goal = goal if value == 0 and width == parent_width else f'({goal})'
            lines = [f'  have {name} : {node} = {rendered_goal} := by',
                     f"    rw [{', '.join(rewrites)}]", f'    {proof}']
            result.append((name, index, lines))
    return result


def _helper_dag_fact_lines(nodes, subset=None):
    return [line for _, _, lines in _helper_dag_facts(nodes, subset) for line in lines]


def _helper_dag_guardproof(nodes, roots, name, proposition, hypotheses,
                       extra_rules=(), splits=64, certified=(), opaque_scalar=True):
    """Emit a local proof; clear equations outside its actual ancestor cone.

    hypotheses is a sequence of (name, owner node). Any retained earlier cut
    must already have a kernel proof. No candidate becomes a theorem premise.
    """
    atoms = {j for j, (_, op, args, _) in enumerate(nodes)
        if opaque_scalar and op == 'eq' and nodes[args[0]][0] >= 16
        and all(nodes[a][1] in ('var', 'lit') for a in args)}
    stops = atoms | {endpoint for pair in certified for endpoint in pair}
    needed = _helper_dag_ancestors_until(nodes, roots, stops)
    remove = [hypothesis for hypothesis, owner in hypotheses
        if owner not in needed or owner in atoms or owner in stops - atoms]
    rules = ['stream_bit_and_one', 'stream_bit_not_one',
             'stream_bit_ofBool_one', 'BitVec.not_not', *extra_rules]
    lines = [f'  have {name} : {proposition} := by']
    if remove:
        lines.append('    clear ' + ' '.join(remove))
    lines += [f'    grind (zeta := false) (zetaDelta := false) (splits := {splits}) only',
              "      [" + ', '.join(rules) + ']']
    return lines

def _helper_dag_congruence(nodes, left, right, indent='    '):
    """Produce a linear proof DAG for syntactically aligned mux/concat cones.

    Leaves remain explicit kernel obligations. Matching output widths and ops
    are proposals only; no branch or value equality is assumed by this emitter.
    The return value is (proof lines, name of the final equality proof).
    """
    lines, proved = [], {}

    def prove(a, b):
        if a == b:
            return '(by rfl)'
        if (a, b) in proved:
            return proved[a, b]
        width_a, op_a, args_a, _ = nodes[a]
        width_b, op_b, args_b, _ = nodes[b]
        if width_a != width_b:
            raise ValueError('Structural equality has different widths')
        name = f'hp{a}_{b}'
        if (op_a == op_b and op_a not in ('var', 'lit')
                and nodes[a][3] == nodes[b][3] and len(args_a) == len(args_b)
                and all(nodes[x][0] == nodes[y][0] for x, y in zip(args_a, args_b))):
            children = [prove(x, y) for x, y in zip(args_a, args_b)]
            lines.append(f'{indent}have {name} : {_helper_dag_ref(nodes, a)} = {_helper_dag_ref(nodes, b)} := by')
            lines.append(f'{indent}  rw [hd{a}, hd{b}]')
            if op_a == 'mux':
                values = [item for x, y in zip(args_a, args_b)
                          for item in (_helper_dag_ref(nodes, x), _helper_dag_ref(nodes, y))]
                lines.append(f"{indent}  exact dag_mux_congr {' '.join(values + children)}")
            else:
                rewrites = [proof for x, y, proof in zip(args_a, args_b, children) if x != y]
                if rewrites:
                    lines.append(f"{indent}  rw [{', '.join(rewrites)}]")
                else:
                    lines.append(f'{indent}  rfl')
        else:
            lines.append(f'{indent}have {name} : {_helper_dag_ref(nodes, a)} = {_helper_dag_ref(nodes, b)} := by')
            lines.append(f'{indent}  grind (zeta := false) (zetaDelta := false) '
                         '(lia := false) (linarith := false) (ring := false) '
                         '(splitIte := false) only [BitVec.not_not]')
        proved[a, b] = name
        return name

    final = prove(left, right)
    return lines, final


def _helper_dag_ancestors_until(nodes, roots, stops=()):
    """Return exact _helper_dag_ancestors, stopping below already certified cut endpoints."""
    stops = set(stops)
    result = set()

    def visit(index):
        if index in result:
            return
        result.add(index)
        if index in stops:
            return
        for child in nodes[index][2]:
            visit(child)

    for root in roots:
        visit(root)
    return result


def _helper_dag_outerproof(nodes, roots, certified_pairs, hypotheses,
                       clear_cuts=(), splits=64):
    """Close original root equality from previously proved conditional cuts.

    Every cut and its activation guard proof remains in the local context.
    This emits no assumptions; the boundary only controls search visibility.
    hypotheses lists the defining and derived facts still available globally.
    """
    stops = {endpoint for pair in certified_pairs for endpoint in pair}
    needed = _helper_dag_ancestors_until(nodes, roots, stops)
    remove = [name for name, owner in hypotheses if owner not in needed]
    lines = []
    if remove:
        lines.append('  clear ' + ' '.join(remove))
    if clear_cuts:
        lines.append('  clear ' + ' '.join(clear_cuts))
    lines.append(f'  grind (zeta := false) (zetaDelta := false) '
                 f'(splits := {splits}) (lia := false) (linarith := false) '
                 '(ring := false) only [BitVec.not_not]')
    return lines

def _helper_dag_payloads(nodes, roots, certified_pairs=(), min_structure=8):
    """Propose aligned mux/concat payload cones after certified data cuts.

    Guard identities are ignored in mux shapes. Non-branch operation leaves
    with equal types and opcodes stay separate kernel equality obligations.
    Variables and literals retain exact identities unless already certified.
    """
    boundary = {}
    for number, (left, right) in enumerate(certified_pairs):
        if nodes[left][0] != nodes[right][0]:
            raise ValueError('Certified payload boundary widths differ')
        boundary[left] = boundary[right] = number
    shapes, sizes = [], []
    for index, (width, op, args, value) in enumerate(nodes):
        if index in boundary:
            shape, count = ('cut', width, boundary[index]), 0
        elif op == 'mux':
            shape = ('mux', width, shapes[args[1]], shapes[args[2]])
            count = 1 + sizes[args[1]] + sizes[args[2]]
        elif op == 'concat':
            shape = ('concat', width, shapes[args[0]], shapes[args[1]])
            count = 1 + sizes[args[0]] + sizes[args[1]]
        elif op in ('lit', 'var'):
            shape, count = ('exact', index), 0
        else:
            shape, count = ('obligation', width, op), 0
        shapes.append(shape)
        sizes.append(count)
    left_nodes, right_nodes = [_helper_dag_ancestors_until(nodes, [root], boundary) for root in roots]
    right_groups = {}
    for right in right_nodes:
        if nodes[right][0] >= 8 and nodes[right][1] in ('mux', 'concat'):
            right_groups.setdefault(shapes[right], []).append(right)
    result = []
    for left in left_nodes:
        if sizes[left] < min_structure or nodes[left][0] < 8:
            continue
        for right in right_groups.get(shapes[left], ()):
            if left != right:
                result.append(dict(roots=(left, right), structure=sizes[left]))
    result.sort(key=lambda item: (-item['structure'], item['roots']))
    return result

def _helper_dag_samples(nodes, count=2048, seed=0x53545245414d):
    rng = random.Random(seed)
    constants = {}
    for width, op, args, value in nodes:
        if op == 'lit':
            constants.setdefault(width, set()).add(value & ((1 << width) - 1))
    literal_boundaries = {max(0, value + delta) for _, op, _, value in nodes
                          if op == 'lit' for delta in (-1, 0, 1)}
    columns = [[] for _ in nodes]
    for _ in range(count):
        values, variables = [], {}
        for index, (width, op, args, literal) in enumerate(nodes):
            mask = (1 << width) - 1
            if op == 'var':
                if literal not in variables:
                    if width <= 6 or width in (16, 20, 32):
                        value = rng.getrandbits(width)
                    else:
                        choices = [0, 1, 2, 3, 7, mask, rng.getrandbits(width)]
                        choices += sorted(value for value in literal_boundaries if value <= mask)
                        value = rng.choice(choices)
                    variables[literal] = value
                value = variables[literal]
            elif op == 'lit':
                value = literal
            else:
                operands = [values[child] for child in args]
                if op == 'slice': value = operands[0] >> literal
                elif op == 'concat': value = (operands[0] << nodes[args[1]][0]) | operands[1]
                elif op == 'not': value = ~operands[0]
                elif op == 'and': value = operands[0] & operands[1]
                elif op == 'or': value = operands[0] | operands[1]
                elif op == 'xor': value = operands[0] ^ operands[1]
                elif op == 'add': value = operands[0] + operands[1]
                elif op == 'sub': value = operands[0] - operands[1]
                elif op == 'eq': value = int(operands[0] == operands[1])
                elif op == 'lt': value = int(operands[0] < operands[1])
                elif op == 'mux': value = operands[1] if operands[0] == 1 else operands[2]
                else: raise ValueError('Unsupported sample opcode: ' + op)
            value &= mask
            values.append(value)
            columns[index].append(value)
    return columns


def _helper_dag_context_rows(columns, context):
    return tuple(row for row in range(len(columns[0]))
                 if all((columns[guard][row] == 1) == truth for guard, truth in context))


def _helper_dag_signature_groups(nodes, columns, rows=None):
    """Hash complete typed value vectors; no sampled equivalence is accepted."""
    if rows is None:
        rows = range(len(columns[0]))
    if not rows:
        return []
    classes = {}
    for index, (width, _, _, _) in enumerate(nodes):
        size = (width + 7) // 8
        digest = hashlib.blake2b(digest_size=16)
        for row in rows:
            digest.update(columns[index][row].to_bytes(size, 'little'))
        key = width, digest.digest()
        classes.setdefault(key, []).append(index)
    return [group for group in classes.values() if len(group) > 1]


def _helper_dag_activation(nodes, root, target):
    paths = {root: set()}
    for index in range(root, -1, -1):
        if index not in paths:
            continue
        _, op, args, _ = nodes[index]
        for position, child in enumerate(args):
            context = set(paths[index])
            if op == 'mux' and position in (1, 2):
                context.add((args[0], position == 1))
            if child in paths:
                paths[child].intersection_update(context)
            else:
                paths[child] = context
    return tuple(sorted(paths.get(target, ())))


def _helper_dag_normalize_guard(nodes, guard, truth):
    """Strip exact one-bit negation and zero-padding/identity slices."""
    while True:
        width, op, args, value = nodes[guard]
        if width == 1 and op == 'not':
            guard, truth = args[0], not truth
        elif op == 'slice' and value == 0:
            parent = nodes[args[0]]
            if parent[0] == width:
                guard = args[0]
            elif parent[1] == 'concat' and nodes[parent[2][1]][0] == width:
                guard = parent[2][1]
            else:
                break
        else:
            break
    return guard, truth


def _helper_dag_plan(nodes, roots, mux_cuts, count=2048):
    columns = _helper_dag_samples(nodes, count=count)
    groups = _helper_dag_signature_groups(nodes, columns)
    class_of = {node: number for number, group in enumerate(groups) for node in group}
    left_ancestors, right_ancestors = [_helper_dag_ancestors(nodes, [root]) for root in roots]
    left_unique = left_ancestors - right_ancestors
    right_unique = right_ancestors - left_ancestors
    # Global aliases must be independent of the large data cones we will cut.
    # Otherwise this would propose the original theorem itself as a "cut".
    tainted = {endpoint for cut in mux_cuts for pair in cut['mux_pairs'] for endpoint in pair}
    for index, node in enumerate(nodes):
        if any(child in tainted for child in node[2]):
            tainted.add(index)
    ancestor_sizes = [len(_helper_dag_ancestors(nodes, [index])) for index in range(len(nodes))]
    globals_ = []
    for group in groups:
        if len(set(columns[group[0]])) <= 1:
            continue
        left = [i for i in group if i in left_unique and i not in tainted and nodes[i][1] != 'lit']
        right = [i for i in group if i in right_unique and i not in tainted and nodes[i][1] != 'lit']
        if not left or not right:
            continue
        # Prefer outermost aliases, reducing repeated deep controller proofs.
        pair = max(((a, b) for a in left for b in right),
                   key=lambda p: (min(ancestor_sizes[p[0]], ancestor_sizes[p[1]]), p))
        globals_.append(dict(roots=pair, width=nodes[pair[0]][0],
                             complexity=min(ancestor_sizes[pair[0]], ancestor_sizes[pair[1]])))
    globals_.sort(key=lambda cut: (-cut['width'], -cut['complexity'], cut['roots']))
    outer_stops = {endpoint for cut in mux_cuts for endpoint in cut['roots']}
    outer_nodes = _helper_dag_ancestors_until(nodes, roots, outer_stops)
    outer_guards = {nodes[index][2][0] for index in outer_nodes if nodes[index][1] == 'mux'}
    control_nodes = _helper_dag_ancestors(nodes, outer_guards)
    control_aliases = [item for item in globals_ if item['width'] > 1
                       and all(endpoint in control_nodes for endpoint in item['roots'])]
    data = []
    for cut in mux_cuts:
        contexts = [tuple(tuple(item) for item in context) for context in cut['contexts']]
        left_context, right_context = contexts
        normalized = [[_helper_dag_normalize_guard(nodes, guard, truth) for guard, truth in context]
                      for context in contexts]
        context_pairs = sorted({(a, b) for a, truth_a in normalized[0]
                                for b, truth_b in normalized[1]
                                if a != b and truth_a == truth_b
                                and class_of.get(a, -1) == class_of.get(b, -2)})
        rows = _helper_dag_context_rows(columns, left_context)
        conditional_groups = _helper_dag_signature_groups(nodes, columns, rows)
        conditional_class = {node: number for number, group in enumerate(conditional_groups)
                             for node in group}
        selectors = [tuple(pair) for pair in cut['selectors']
                     if conditional_class.get(pair[0], -1) == conditional_class.get(pair[1], -2)]
        zeros = [index for index, node in enumerate(nodes)
                 if node[0] == 1 and rows and all(columns[index][row] != 1 for row in rows)]
        selector_ancestors = _helper_dag_ancestors(nodes, [node for pair in cut['selectors'] for node in pair])
        selector_mux_guards = {nodes[index][2][0] for index in selector_ancestors
                               if nodes[index][1] == 'mux'}
        guard_zeros = [index for index in zeros if index in selector_mux_guards]
        old_values = [tuple(item['roots']) for item in globals_
                      if item['width'] == nodes[roots[0]][0]
                      and not all(endpoint in control_nodes for endpoint in item['roots'])]
        payloads = _helper_dag_payloads(nodes, roots,
                                      [tuple(cut['roots']), *old_values])
        data.append(dict(roots=tuple(cut['roots']), contexts=contexts,
                         context_pairs=context_pairs, active_rows=len(rows),
                         conditional_selectors=selectors, conditional_zero_nodes=zeros,
                         conditional_guard_zero_nodes=guard_zeros,
                         old_value_pairs=old_values, payload_candidates=payloads))
    return dict(scope='untrusted finite signature and syntactic proposals only',
                sample_count=count, global_aliases=globals_,
                global_control_aliases=control_aliases, data_cuts=data)


def _helper_dag_context_proposition(nodes, context):
    if not context:
        return 'True'
    terms = [f'{_helper_dag_ref(nodes, guard)} {"=" if truth else "≠"} 1'
             for guard, truth in context]
    return '(' + ' ∧ '.join(terms) + ')'



def _helper_dag_active_body(nodes, root, context):
    """Follow fixed mux branches through exact identity and low-pad slices."""
    context = dict(context)
    while True:
        width, op, args, value = nodes[root]
        if op == 'mux' and args[0] in context:
            root = args[1] if context[args[0]] else args[2]
        elif op == 'slice' and value == 0:
            parent = nodes[args[0]]
            if parent[0] == width:
                root = args[0]
            elif parent[1] == 'concat' and nodes[parent[2][1]][0] == width:
                root = parent[2][1]
            else:
                return root
        else:
            return root


def _helper_dag_context_proof(nodes, roots, name, proposition, hypotheses,
                              certified=(), context=(), pure=False):
    atoms = {j for j, (_, op, args, _) in enumerate(nodes)
        if op == 'eq' and nodes[args[0]][0] >= 16
        and all(nodes[a][1] in ('var', 'lit') for a in args)}
    stops = atoms | {endpoint for pair in certified for endpoint in pair}
    needed = _helper_dag_ancestors_until(nodes, roots, stops)
    remove = [hypothesis for hypothesis, owner in hypotheses
        if owner not in needed or owner in stops]
    lines = [f'  have {name} : {proposition} := by']
    if context:
        lines.append('    intro hactive')
    if remove:
        lines.append('    clear ' + ' '.join(remove))
    config = ' (lia := false) (linarith := false) (ring := false)' if pure else ''
    lines.append('    grind (zeta := false) (zetaDelta := false) (splits := 64)'+config+' only')
    lines.append("      [BitVec.not_not, dag_extract_compose, BitVec.extractLsb'_append_eq_right, "
                 "BitVec.extractLsb'_eq_self, BitVec.extractLsb'_extractLsb'_of_le]")
    return lines


def _helper_dag_proof(rb, dag):
    variables, nodes, roots = dag
    cuts = _helper_mux_cuts(dag)
    proposed = _helper_dag_plan(nodes, roots, cuts)
    lines, hypotheses, certified, names = [], [], [], {}
    for j, (width, op, args, value) in enumerate(nodes):
        if op == 'var':
            continue
        expression = (f'({value} : BitVec {width})' if op == 'lit' else
            rb.Graph.expression(None, rb.Node(width, op, args, value),
                lambda c: '(' + _helper_dag_ref(nodes, c) + ')'))
        lines += [f'  intro d{j}', f'  clear_value (hd{j} : d{j} = {expression})']
        hypotheses.append((f'hd{j}', j))
    facts = _helper_dag_facts(nodes)
    lines += [line for _, _, proof in facts for line in proof]
    hypotheses += [(name, owner) for name, owner, _ in facts]

    def global_cut(pair):
        pair = tuple(pair)
        if pair in names:
            return names[pair]
        name = f'hcut{len(names)}'
        proposition = ' = '.join(_helper_dag_ref(nodes, j) for j in pair)
        lines.extend(_helper_dag_context_proof(nodes, pair, name, proposition,
            hypotheses, certified=certified))
        names[pair] = name
        certified.append(pair)
        return name

    for proposal in proposed['global_control_aliases']:
        global_cut(proposal['roots'])
    for data in proposed['data_cuts']:
        for pair in data['context_pairs']:
            global_cut(pair)
        # Hold-data muxes may need start controls outside the active context.
        old_roots = [j for pair in data['old_value_pairs'] for j in pair]
        old_ancestors = _helper_dag_ancestors(nodes, old_roots)
        for proposal in proposed['global_aliases']:
            pair = proposal['roots']
            if proposal['width'] == 1 and all(j in old_ancestors for j in pair):
                global_cut(pair)
        for pair in data['old_value_pairs']:
            global_cut(pair)
        context = data['contexts'][0]
        predicate = _helper_dag_context_proposition(nodes, context)
        cut = next(cut for cut in cuts if tuple(cut['roots']) == tuple(data['roots']))
        selector_names = []
        for j, pair in enumerate(cut['selectors']):
            name = f'hselector{len(names)}_{j}'
            proposition = predicate+' → '+ ' = '.join(_helper_dag_ref(nodes, k) for k in pair)
            lines.extend(_helper_dag_context_proof(nodes,
                (*pair, *(guard for guard, _ in context)), name, proposition,
                hypotheses, context=context))
            selector_names.append(name)
        name = f'hword{len(names)}'
        a, b = data['roots']
        definitions = [f'hd{j}' for pair in cut['mux_pairs'] for j in pair]
        definitions += [f'{name} hactive' for name in selector_names]
        lines += [f'  have {name} : {predicate} → {_helper_dag_ref(nodes,a)} = {_helper_dag_ref(nodes,b)} := by',
                  '    intro hactive', '    simp only ['+', '.join(definitions)+']']
        bodies = tuple(_helper_dag_active_body(nodes, root, ctx)
                       for root, ctx in zip(roots, data['contexts']))
        body_name = f'hbody{len(names)}'
        body_prop = predicate+' → '+' = '.join(_helper_dag_ref(nodes,j) for j in bodies)
        lines += [f'  have {body_name} : {body_prop} := by',
                  '    intro hactive', f'    have hword := {name} hactive']
        stops = {endpoint for pair in (*certified, tuple(data['roots'])) for endpoint in pair}
        needed = _helper_dag_ancestors_until(nodes, bodies, stops)
        remove = [name for name, owner in hypotheses if owner not in needed or owner in stops]
        if remove:
            lines.append('    clear '+' '.join(remove))
        payload = data['payload_candidates']
        if payload and tuple(payload[0]['roots']) == bodies:
            proof, final = _helper_dag_congruence(nodes, *bodies)
            lines += proof+[f'    exact {final}']
        else:
            lines += ['    grind (zeta := false) (zetaDelta := false) (splits := 64) '
                      '(lia := false) (linarith := false) (ring := false) only [BitVec.not_not]']
        certified += [bodies]
    lines += _helper_dag_outerproof(nodes, roots, certified, hypotheses)
    return '\n'.join(lines)


def _helper_dag_expanded_size(dag):
    sizes = []
    for _, _, children, _ in dag[1]:
        sizes.append(1 + sum(sizes[child] for child in children))
    return sum(sizes[root] for root in dag[2])


def _helper_dag_compound_predicates(dag):
    nodes = dag[1]
    return any(op == 'eq' and nodes[args[0]][0] >= 16
               and any(nodes[child][1] not in ('var', 'lit') for child in args)
               for _, op, args, _ in nodes)


def _helper_dag_small_problem(dag):
    """Route expanded small-result predicates without promoting every field."""
    _, nodes, roots = dag
    if nodes[roots[0]][0] > 8 or _helper_dag_expanded_size(dag) < 1000:
        return False
    if _helper_dag_compound_predicates(dag):
        return True
    if nodes[roots[0]][0] != 1:
        return False
    literals = {}
    for _, op, args, _ in nodes:
        if op != 'eq' or nodes[args[0]][0] < 16:
            continue
        for variable, literal in (args, tuple(reversed(args))):
            if nodes[variable][1] == 'var' and nodes[literal][1] == 'lit':
                literals.setdefault(variable, set()).add(nodes[literal][3])
    return any(len(values) > 1 for values in literals.values())


def _helper_dag_field_zero_aliases(nodes, roots):
    """Propose zero-field cuts by exact bit support; Lean proves every cut.

    Masks, slices and concatenation select bits of the same typed DAG operands.
    Other operations remain distinct opaque bit sources. Padding and repeated
    selected bits may disappear from a zero test, but different words cannot
    become aliases merely because finite samples happened to agree.
    """
    cache = {}
    def bit(index, offset):
        key = index, offset
        if key in cache:
            return cache[key]
        width, op, args, value = nodes[index]
        if not 0 <= offset < width:
            result = False
        elif op == 'lit':
            result = bool(value >> offset & 1)
        elif op == 'slice':
            result = bit(args[0], value + offset)
        elif op == 'concat':
            low_width = nodes[args[1]][0]
            result = (bit(args[1], offset) if offset < low_width
                      else bit(args[0], offset - low_width))
        elif op == 'and':
            a, b = (bit(child, offset) for child in args)
            if a is False or b is False:
                result = False
            elif a is True:
                result = b
            elif b is True or a == b:
                result = a
            else:
                result = 'and', a, b
        else:
            result = 'opaque', index, offset
        cache[key] = result
        return result
    left, right = (_helper_dag_ancestors(nodes, [root]) for root in roots)
    classes = {}
    for index, (width, op, args, _) in enumerate(nodes):
        if width != 1 or op != 'eq':
            continue
        zero, word = (args if nodes[args[0]][1] == 'lit' else tuple(reversed(args)))
        if (nodes[zero][1] != 'lit' or nodes[word][0] < 2
                or nodes[zero][3] % (1 << nodes[zero][0]) != 0):
            continue
        bits = tuple(bit(word, k) for k in range(nodes[word][0]))
        if any(value is True for value in bits):
            continue
        support = frozenset(value for value in bits if value is not False)
        if support:
            classes.setdefault(support, []).append(index)
    proposals = []
    for support, members in classes.items():
        for a in (j for j in members if j in left - right):
            for b in (j for j in members if j in right - left):
                proposals.append(dict(roots=(a, b), support=sorted(support, key=repr),
                    complexity=len(_helper_dag_ancestors(nodes, [a, b]))))
    return sorted(proposals, key=lambda item: (item['complexity'], item['roots']))


def _helper_dag_small_boundaries(nodes, pairs):
    """Retain small numeric flag definitions and their mutual exclusion."""
    return [pair for pair in pairs if not any(nodes[index][1] == 'eq'
            and nodes[nodes[index][2][0]][0] < 16 for index in pair)]



def _helper_dag_small_proof(rb, dag):
    """Prove compact predicate wrappers using certified field/control cuts.

    Exact bit supports propose zero-field aliases; finite signatures propose
    other small aliases only when their variable supports and endpoint
    operations agree. Each proposed alias remains a mandatory kernel goal.
    Narrow numeric comparisons keep their definitions so mutually exclusive
    opcodes/pages cannot become independent Boolean assumptions.
    """
    _, nodes, roots = dag
    lines, hypotheses, certified, names = [], [], [], []
    for j, (width, op, args, value) in enumerate(nodes):
        if op == 'var':
            continue
        expression = (f'({value} : BitVec {width})' if op == 'lit' else
            rb.Graph.expression(None, rb.Node(width, op, args, value),
                lambda c: '(' + _helper_dag_ref(nodes, c) + ')'))
        lines += [f'  intro d{j}', f'  clear_value (hd{j} : d{j} = {expression})']
        hypotheses.append((f'hd{j}', j))
    facts = _helper_dag_facts(nodes)
    lines += [line for _, _, proof in facts for line in proof]
    hypotheses += [(name, owner) for name, owner, _ in facts]

    small_result = nodes[roots[0]][0] <= 2
    fields = _helper_dag_field_zero_aliases(nodes, roots)
    field_pairs = {tuple(item['roots']) for item in fields}
    def variables(root):
        return {nodes[j][3] for j in _helper_dag_ancestors(nodes, [root])
                if nodes[j][1] == 'var'}
    width_limit, complexity_limit = (2, 160) if small_result else (8, 200)
    aliases = sorted((item for item in _helper_dag_plan(nodes, roots, [])['global_aliases']
        if item['width'] <= width_limit and item['complexity'] < complexity_limit
        and variables(item['roots'][0]) == variables(item['roots'][1])
        and nodes[_helper_dag_active_body(nodes, item['roots'][0], ())][1]
            == nodes[_helper_dag_active_body(nodes, item['roots'][1], ())][1]
        and tuple(item['roots']) not in field_pairs),
        key=lambda item: (item['complexity'], item['roots']))

    for proposal in [*fields, *aliases]:
        pair, name = tuple(proposal['roots']), f'halias{len(names)}'
        boundaries = _helper_dag_small_boundaries(nodes, certified)
        common = (_helper_dag_ancestors(nodes, [pair[0]])
                  & _helper_dag_ancestors(nodes, [pair[1]]))
        isolated = [(j, j) for j in sorted(common)
                    if nodes[j][0] >= 16 and nodes[j][1] not in ('var', 'lit')]
        stops = {j for cut in [*boundaries, *isolated] for j in cut}
        needed = _helper_dag_ancestors_until(nodes, pair, stops)
        definitions = [f'hd{j}' for j in sorted(needed - stops) if nodes[j][1] != 'var']
        constants = [f'show ({k} : Fin {w}).val = {k} from rfl'
            for w in sorted({nodes[j][0] for j in needed if 0 < nodes[j][0] <= 64})
            for k in range(w)]
        constants += [f'show Nat.testBit {value} {k} = {str(bool(value >> k & 1)).lower()} from rfl'
            for j in sorted(needed) for width, op, _, value in [nodes[j]] if op == 'lit'
            for k in range(width)]
        bitwise = [
            '      try simp only ['+', '.join([*definitions, *names])+']',
            '      try simp only [BitVec.ofBool_eq_iff_eq, decide_eq_decide]',
            "      try simp only [Pinwheel.Hardware.Readback.eq_bits, Fin.forall_fin_succ, "
                "BitVec.getLsbD_and, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, BitVec.getLsbD_ofNat]",
            '      try simp [BitVec.getLsbD_append, BitVec.getLsbD_ofNat, '
                'BitVec.getElem_eq_testBit_toNat, BitVec.toNat_ofNat]',
            '      try simp only ['+', '.join(constants)+']',
            '      try simp only [Bool.true_eq_false, Bool.false_eq_true, Bool.eq_false_iff, '
                'true_implies, false_implies, and_true, and_false, Bool.and_true, Bool.and_false]',
            '      try simp [BitVec.getLsbD]', '      done']
        proposition = ' = '.join(_helper_dag_ref(nodes, j) for j in pair)
        proof = _helper_dag_context_proof(nodes, pair, name, proposition, hypotheses,
                                        certified=[*boundaries, *isolated])
        if small_result and 'support' in proposal:
            remove = [fact for fact, owner in hypotheses if owner not in needed or owner in stops]
            proof = [f'  have {name} : {proposition} := by']
            if remove:
                proof += ['    clear '+' '.join(remove)]
            # These fields are exact selected-bit zero tests. Prove them
            # directly instead of asking the arithmetic/control normalizer.
            bitwise[0] = '      try simp only ['+', '.join(definitions)+", BitVec.extractLsb'_append_eq_right, BitVec.extractLsb'_eq_self]"
            proof += [line[2:] for line in bitwise]
        elif small_result:
            at = next(index for index, line in enumerate(proof) if 'grind ' in line)
            proof.insert(at, '    try (bv_normalize; omega)')
            proof[at + 1] = '    all_goals '+proof[at + 1].lstrip()
            proof.append('    done')
        else:
            at = next(index for index, line in enumerate(proof) if 'grind ' in line)
            proof[at] = proof[at].replace('    grind ', '    all_goals grind ')
            proof[at:at] = ['    try (', *bitwise[:-1], '      done)']
        lines += proof
        certified.append(pair)
        names.append(name)

    boundaries = _helper_dag_small_boundaries(nodes, certified)
    outer = _helper_dag_outerproof(nodes, roots, boundaries, hypotheses)
    stops = {j for pair in boundaries for j in pair}
    needed = _helper_dag_ancestors_until(nodes, roots, stops)
    pages = [j for j in sorted(needed) if nodes[j][1] == 'var' and nodes[j][0] == 2]
    if not small_result and pages:
        # Exhaust the first surviving two-bit selector. The kernel proves the
        # four-value cover; each branch preserves all other original inputs.
        page = _helper_dag_ref(nodes, pages[0])
        definitions = [f'hd{j}' for j in sorted(needed - stops) if nodes[j][1] != 'var']
        lines += outer[:-1] + [
            f'  have hpage : {page} = 0 ∨ {page} = 1 ∨ {page} = 2 ∨ {page} = 3 := by',
            f'    have hlt := {page}.isLt', '    simp only [← BitVec.toNat_inj]',
            f'    change {page}.toNat = 0 ∨ {page}.toNat = 1 ∨ {page}.toNat = 2 ∨ {page}.toNat = 3',
            '    omega', '  rcases hpage with hpage | hpage | hpage | hpage',
            '  all_goals try simp only ['+', '.join([*definitions, *names])+', hpage, '
                'BitVec.not_and, BitVec.not_or, BitVec.not_not]',
            '  all_goals try rfl', '  all_goals '+outer[-1].lstrip()]
    else:
        lines += outer
    lines += ['  done']
    return '\n'.join(lines)


def helper_source(rb, pairs):
    """Keep imported equalities, compacting large and selected small predicates.

    The DAG expands to exactly the imported ordered typed AST. Its let-bound
    proposition is definitionally the original equality, with every original
    variable and no additional premises. Uniform local equations come from the
    lets; finite signatures only propose further cuts, all proved by the kernel.
    Large data muxes use linear congruence after proved selector equalities.
    Selected small predicate wrappers use kernel-proved field/control cuts;
    all other statements retain their original rendered equality text.

    Other statements keep their original text. Distinct scalar predicates may
    become arbitrary one-bit atoms in a stronger proof obligation. A failed
    small prepass falls back to the retained paired tactic. Every final module
    must also pass the standard-axiom audit and unchanged endpoint connections.
    """
    ending = '\nend Pinwheel.Artifact.Paired\n'
    prefix = pr.helper_source(rb, []).removesuffix(ending)
    prefix += '''
theorem stream_bit_append3 (a : BitVec 1) :
    (3#2) ++ a = (if a = 1 then (7#3) else (6#3)) := by
  rcases BitVec.eq_zero_or_eq_one a with rfl | rfl <;> rfl

theorem stream_bit_and_one (a b : BitVec 1) :
    a &&& b = 1 ↔ a = 1 ∧ b = 1 := by
  rcases BitVec.eq_zero_or_eq_one a with rfl | rfl <;>
    rcases BitVec.eq_zero_or_eq_one b with rfl | rfl <;> decide +kernel

theorem stream_bit_not_one (a : BitVec 1) :
    (~~~a) = 1 ↔ ¬a = 1 := by
  rcases BitVec.eq_zero_or_eq_one a with rfl | rfl <;> decide +kernel

theorem stream_bit_ofBool_one (p : Prop) [Decidable p] :
    BitVec.ofBool (decide p) = 1 ↔ p := by
  by_cases h : p <;> simp [h]
'''
    retained = '''try simp only [low_eight_sub]
try simp only [BitVec.sub_eq_add_neg, BitVec.extractLsb'_append_eq_right,
  BitVec.extractLsb'_append_extractLsb'_eq_extractLsb', BitVec.extractLsb'_eq_self,
  show (4#3).toNat = 4 from rfl, low_three_high, cursor_eq_288, cursor_eq_289, cursor_eq_290]
all_goals first
| (bv_normalize; first | omega | grind (splits := 64))
| (simp [Pinwheel.Hardware.Readback.eq_bits, Fin.forall_fin_succ,
    BitVec.getElem_append, BitVec.getElem_extractLsb']; all_goals grind (splits := 64))'''
    dags = [_helper_dag(pair) for pair in pairs]
    def compact(dag):
        return _helper_dag_expanded_size(dag) >= 20000 or _helper_dag_small_problem(dag)
    if any(compact(dag) for dag in dags):
        prefix += _DAG_SUPPORT_SOURCE
    lines = [prefix]
    for index, (pair, dag) in enumerate(zip(pairs, dags)):
        parameters = ' '.join(f'(x{j} : BitVec {w})' for j, (w, _, _) in enumerate(pair['variables']))
        if compact(dag):
            proof = (_helper_dag_small_proof(rb, dag) if _helper_dag_compound_predicates(dag)
                and _helper_dag_expanded_size(dag) < 20000 else _helper_dag_proof(rb, dag))
            lines.append(f'theorem local_{index} {parameters} :\n'+
                _helper_dag_proposition(rb, dag)+' := by\n'+proof)
            if index % 100 == 0:
                lines.append(f'run_cmd IO.eprintln "checked local {index}"')
            continue
        lines.append(f'theorem local_{index} {parameters} :\n'
            f"    {rb.render_tree(pair['left'])} = {rb.render_tree(pair['right'])} := by\n"
            '  first\n  | rfl')
        guards = _helper_guards(pair)
        if guards:
            prepass = [f'generalize {rb.render_tree(t)} = xstream_guard{j}' for j, t in enumerate(guards)]
            prepass.append("try simp only [BitVec.extractLsb'_append_eq_right]")
            prepass.append("try simp only [stream_bit_and_one, stream_bit_not_one, stream_bit_ofBool_one,\n"
                "  BitVec.and_assoc, BitVec.not_not, show (4#3).toNat = 4 from rfl, low_three_high,\n"
                "  cursor_eq_288, cursor_eq_289, cursor_eq_290, ite_not, stream_bit_append3]")
            prepass.append("first\n| (congr 5 <;> simp [Pinwheel.Hardware.Readback.eq_bits, Fin.forall_fin_succ] <;> omega)\n"
                "| (simp [Pinwheel.Hardware.Readback.eq_bits, Fin.forall_fin_succ,\n"
                "    BitVec.getElem_append, BitVec.getElem_extractLsb']; all_goals grind (splits := 64))\n"
                "| (\n" + '\n'.join('  ' + line for line in retained.splitlines()) + '\n  )')
            lines.append('  | (\n' + '\n'.join('    ' + line for line in '\n'.join(prepass).splitlines()) + '\n    )')
        lines.append('  | (\n' + '\n'.join('    ' + line for line in retained.splitlines()) + '\n    )')
        if index % 100 == 0:
            lines.append(f'run_cmd IO.eprintln "checked local {index}"')
    return '\n'.join(lines) + ending


def generate(rb, source, rtl, cuts, pairs, kind):
    texts = {
        'Design': design_source(rb, kind),
        'Hints': rb.HEADER + source.definitions('Source') + 'end Pinwheel.Artifact.Paired\n',
        'Graphs': 'import Hints\n' + rb.HEADER + rtl.definitions('RTL') + 'end Pinwheel.Artifact.Paired\n',
        'HintEquations': pr.hint_equations_source(rb, source, cuts, kind),
        'Equations': pr.equations_source(rb, cuts, kind),
        'Sources': sources_source(rb, source, kind),
        'LocalProofs': helper_source(rb, pairs),
        'Links': pr.links_source(rb, source, rtl, pairs),
        'Model': model_source(rb, rtl, kind),
        'Endpoints': pr.endpoints_source(rb, source, rtl, pairs, kind),
        'Proof': proof_source(rb, kind),
    }
    return {name: adapt(text, kind) if name in ('Hints', 'Graphs', 'Links') else text for name, text in texts.items()}
