"""Checked leaf-environment and DAG composition hints for SRAM interpretation.

Python chooses descriptions and proof boundaries. Every generated leaf/root
equation and substitution is reconstructed by Lean before artifact use.
"""
import buffered_sram_readback as sram

NAMESPACE = 'Pinwheel.Artifact.SramReference'


def environment_roots():
    return ([('instruction', 64, 'Sram.instruction')] +
            [('input_' + n, w, 'SramArtifactReference.input (.' + ctor + ')')
             for n, w, ctor in sram.BASE_INPUTS] +
            [(f'register_word{k}', 144, f'SramArtifactReference.register (.word {k}#6)')
             for k in range(64)] +
            [('register_' + n, w, 'SramArtifactReference.register (.' + ctor + ')')
             for n, w, ctor in sram.CORE_REGISTERS] + control_roots())


def control_roots():
    return ([('control_row_writing', 1, 'Sram.rowWriting'),
             ('control_table_writing', 1, 'Sram.tableWriting'),
             ('control_committing', 1, 'Sram.committing'),
             ('control_next_written', 64, 'Sram.next_written'),
             ('control_next_branch_written', 16, 'Sram.next_branchWritten')] +
            [(f'control_next_metadata{k}', 28, f'Sram.next (.metadata {k}#6)')
             for k in range(64)] +
            [(f'control_next_branch{k}', 56, f'Sram.next (.branch {k}#4)')
             for k in range(16)] +
            [('control_next_start_word', 64, 'Sram.next (.startWord)')])


def environment_backend():
    rb = sram.backend()
    rb.TOP = 'pinwheel_buffered_artifact_sram_environment'
    rb.OUTPUTS = {name: (width, '.' + name) for name, width, _ in environment_roots()}
    rb.HEADER = f'''import Pinwheel.Hardware.Buffered.SramArtifactReference
open Pinwheel.Hardware Pinwheel.Hardware.Buffered
namespace {NAMESPACE}
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
'''
    return rb


def environment_emitter():
    roots = environment_roots()
    lines = ['import Pinwheel.Hardware.Buffered.SramArtifactReference',
             'open Pinwheel.Hardware Pinwheel.Hardware.Buffered',
             'namespace Pinwheel.Artifact.SramReference.Emit',
             'inductive Root : Nat → Type where']
    lines += [f'  | {name} : Root {width}' for name, width, _ in roots]
    lines += ['def expression : {w : Nat} → Root w → Sram.E w']
    lines += [f'  | _, .{name} => {term}' for name, _, term in roots]
    lines += ['def label : {w : Nat} → Root w → String']
    lines += [f'  | _, .{name} => "{name}"' for name, _, _ in roots]
    lines += ['def outputs : Array (Sigma Root) := #[']
    lines += [f'  ⟨{width}, .{name}⟩' + (',' if k + 1 < len(roots) else '')
              for k, (name, width, _) in enumerate(roots)]
    lines += [']', 'def circuit : Circuit Sram.Input Sram.Register Root :=',
              '  ⟨fun r => .reg r, expression⟩', 'end Pinwheel.Artifact.SramReference.Emit',
              'def main (args : List String) : IO Unit := do',
              '  let path := args.headD "build/sram-reference-environment.mlir"',
              '  let text ← IO.ofExcept (MemoEmit.moduleText',
              '    "pinwheel_buffered_artifact_sram_environment"',
              '    Pinwheel.Artifact.SramReference.Emit.circuit',
              '    Sram.inputs Sram.registers Pinwheel.Artifact.SramReference.Emit.outputs',
              '    Sram.inputLabel Sram.registerLabel Pinwheel.Artifact.SramReference.Emit.label)',
              '  IO.FS.writeFile path text',
              '  IO.println "SRAM leaf environment emitted; kernel checks remain required."']
    return '\n'.join(lines) + '\n'


def adapt(text):
    return sram.adapt(text).replace(sram.NAMESPACE, NAMESPACE)


def environment_hints(rb, graph):
    return adapt(rb.HEADER + graph.definitions('Environment') + f'end {NAMESPACE}\n')


def environment_sources(rb, graph, selected=None):
    if set(graph.outputs) != {name for name, _, _ in environment_roots()}:
        raise ValueError('Incomplete SRAM leaf-environment endpoints')
    lines = ['import EnvironmentHints\nimport Lean.Elab.Command\n' + rb.HEADER]
    for name, _, term in environment_roots():
        if selected is not None and name not in selected:
            continue
        root = rb.graph_value(graph, graph.outputs[name], 'Environment')
        lines += [f'theorem source_{name} (i : Values Sram.Input) (s : Values Sram.Register) :',
                  f'    {root} = ({term}).eval i s := by']
        if name == 'instruction' or name.startswith('control_'):
            lines += ['  rfl']
        else:
            lines += ['  conv =>', '    rhs',
                      '    simp only [SramArtifactReference.input, SramArtifactReference.register,',
                      '      MemoBind.eval_bind, SharedBranches.registerExpr, SharedBranches.inputExpr,',
                      '      SharedBranches.expandRow, SharedBranches.branchAt, Sram.registerExpr, Sram.rowExpr,',
                      '      Execution.readTree, Expr.eval, ← source_instruction]',
                      '  all_goals rfl']
        lines += [f'run_cmd IO.eprintln "checked SRAM environment {name}"']
    return '\n'.join(lines) + f'\nend {NAMESPACE}\n'


def compose_environment(environment, reactive):
    """Substitute checked leaf DAGs into the checked Reactive description.

    This graph remains a proof hint. Per-node substitution theorems below make
    the connection to the original typed expressions in the kernel.
    """
    import buffered_reactive_reference as ref
    rb = sram.backend()
    graph = rb.Graph()
    graph.nodes.update(environment.nodes)
    mapping = {}
    for name, node in reactive.nodes.items():
        if node.op in ('input', 'reg'):
            key = ('input_' + name if node.op == 'input' else
                   'register_' + name.removeprefix('r_'))
            if key not in environment.outputs:
                raise ValueError('Missing environment substitution: ' + key)
            mapping[name] = environment.outputs[key]
        else:
            mapped = 'p_' + name
            if mapped in graph.nodes:
                raise ValueError('Ambiguous composition node: ' + mapped)
            graph.nodes[mapped] = rb.Node(node.width, node.op,
                tuple(mapping[arg] for arg in node.args), node.value)
            mapping[name] = mapped
    graph.next = {name: name for name in rb.REGISTERS}
    graph.outputs = {name: mapping[node] for name, node in reactive.outputs.items()}
    return graph, mapping


def composition_hints(rb, graph, environment, reactive, mapping):
    """Environment aliases share checked constants; other nodes are operators."""
    lines = ['import EnvironmentHints\n' + adapt(rb.HEADER), 'namespace Composed']
    for name, node in graph.nodes.items():
        if node.op in ('input', 'reg'):
            continue
        if name in environment.nodes:
            body = f'Environment.{name} i s'
        else:
            def value(arg):
                return '(' + rb.graph_value(graph, arg, 'Composed') + ')'
            body = graph.expression(node, value)
        lines += [f'def {name} (i : Values Sram.Input) (s : Values Sram.Register) : BitVec {node.width} := {body}']
    return adapt('\n'.join(lines)) + '\nend Composed\n' + f'end {NAMESPACE}\n'


def composition_sources(rb, graph, environment, reactive, mapping, selected=None):
    import buffered_reactive_reference as ref
    lines = ['import ComposedHints\nimport EnvironmentSources\nimport ReactiveSources\nimport Lean.Elab.Command\n' + adapt(rb.HEADER),
        'set_option linter.unusedSimpArgs false',
        'def mappedInput (i : Values Sram.Input) (s : Values Sram.Register) : Values Reactive.Input :=',
        '  fun p => (SramArtifactReference.input p).eval i s',
        'def mappedState (i : Values Sram.Input) (s : Values Sram.Register) : Values Reactive.Register :=',
        '  fun r => (SramArtifactReference.register r).eval i s']
    reactive_backend = ref.backend()
    def source_value(name):
        return ref.adapt(reactive_backend.graph_value(reactive, name,
            ref.NAMESPACE + '.Source', '(mappedInput i s)', '(mappedState i s)'))
    for name, node in reactive.nodes.items():
        lhs = rb.graph_value(graph, mapping[name], 'Composed')
        rhs = source_value(name)
        lines += [f'theorem subst_{name} (i : Values Sram.Input) (s : Values Sram.Register) :',
                  f'    {lhs} = {rhs} := by']
        if node.op in ('input', 'reg'):
            key = ('input_' + name if node.op == 'input' else
                   'register_' + name.removeprefix('r_'))
            lines += [f'  exact source_{key} i s']
        else:
            rules = ['Composed.' + mapping[name], ref.NAMESPACE + '.Source.' + name]
            rules += ['subst_' + arg for arg in dict.fromkeys(node.args)]
            lines += ['  simp only [' + ', '.join(rules) + ']']
            lines += ['  all_goals rfl']
        if name in reactive.outputs.values():
            lines += [f'run_cmd IO.eprintln "checked composition node {name}"']
    for name, width, term in ref.endpoints():
        if selected is not None and name not in selected:
            continue
        original = reactive.outputs[name]
        root = rb.graph_value(graph, mapping[original], 'Composed')
        lines += [f'theorem composed_{name} (i : Values Sram.Input) (s : Values Sram.Register) :',
                  f'    {root} = (SramArtifactReference.adapt ({term})).eval i s := by',
                  '  rw [SramArtifactReference.adapt, MemoBind.eval_bind]',
                  f'  exact (subst_{original} i s).trans ({ref.NAMESPACE}.source_{name} (mappedInput i s) (mappedState i s))',
                  f'run_cmd IO.eprintln "checked composed endpoint {name}"']
    return '\n'.join(lines) + f'\nend {NAMESPACE}\n'


def complete_reference(environment, reactive):
    """Full 117/31 interface description, assembled only from checked DAGs."""
    graph, mapping = compose_environment(environment, reactive)
    rb = sram.backend()
    post = {}
    candidate_names = [reactive.outputs['candidate_false'], reactive.outputs['candidate_true']]
    required = set()
    def visit(name):
        if name in required:
            return
        for arg in reactive.nodes[name].args:
            visit(arg)
        required.add(name)
    for name in candidate_names:
        visit(name)
    for name, node in reactive.nodes.items():
        if name not in required:
            continue
        if node.op == 'reg':
            field = name.removeprefix('r_')
            post[name] = (environment.outputs['control_next_written'] if field == 'written'
                          else mapping[reactive.outputs['next_' + field]])
        elif node.op == 'input':
            literal = 'a_zero_' + str(node.width)
            graph.nodes[literal] = rb.Node(node.width, 'lit', value=0)
            post[name] = literal
        else:
            literal = 'a_' + name
            graph.nodes[literal] = rb.Node(node.width, node.op,
                tuple(post[arg] for arg in node.args), node.value)
            post[name] = literal
    graph.next = {}
    for name in rb.REGISTERS:
        if name == 'r_written':
            graph.next[name] = environment.outputs['control_next_written']
        elif name in {'r_' + field for field, _, _ in sram.CORE_REGISTERS}:
            graph.next[name] = mapping[reactive.outputs['next_' + name.removeprefix('r_')]]
        else:
            graph.next[name] = environment.outputs['control_next_' + name.removeprefix('r_')]
    graph.outputs = {name: mapping[reactive.outputs['output_' + name]]
                     for name, _, _ in sram.BASE_OUTPUTS}
    for bit, label in [(False, 'false'), (True, 'true')]:
        name = 'read_address_' + label
        graph.nodes[name] = rb.Node(6, 'slice', (post[reactive.outputs['candidate_' + label]],), 0)
        output = 'memory_address_' + label
        graph.nodes[output] = rb.Node(6, 'mux',
            (environment.outputs['control_row_writing'], 'address', name))
        graph.outputs['mem_addr' + str(int(bit))] = output
    graph.nodes['memory_read'] = rb.Node(1, 'not', (environment.outputs['control_row_writing'],))
    graph.outputs.update(mem_data='word', mem_write=environment.outputs['control_row_writing'],
                         mem_read='memory_read')
    return graph, mapping, post


def complete_sources(rb, graph, environment, reactive, mapping, post):
    import buffered_reactive_reference as ref
    rrb = ref.backend()
    lines = ['import ComposedSources\n' + adapt(rb.HEADER),
             'set_option linter.unusedSimpArgs false',
             'def postInput (i : Values Sram.Input) (s : Values Sram.Register) : Values Reactive.Input :=',
             '  fun _ => 0',
             'def postState (i : Values Sram.Input) (s : Values Sram.Register) : Values Reactive.Register :=',
             '  fun r => (SramArtifactReference.coreNext r).eval i s']
    for name, node in reactive.nodes.items():
        if name not in post:
            continue
        lhs = rb.graph_value(graph, post[name], 'Composed')
        rhs = ref.adapt(rrb.graph_value(reactive, name, ref.NAMESPACE + '.Source',
                                      '(postInput i s)', '(postState i s)'))
        lines += [f'theorem post_{name} (i : Values Sram.Input) (s : Values Sram.Register) :',
                  f'    {lhs} = {rhs} := by']
        if node.op == 'reg':
            field = name.removeprefix('r_')
            proof = 'source_control_next_written' if field == 'written' else 'composed_next_' + field
            lines += [f'  exact {proof} i s']
        elif node.op == 'input':
            lines += ['  rfl']
        else:
            rules = ['Composed.' + post[name], ref.NAMESPACE + '.Source.' + name]
            rules += ['post_' + arg for arg in dict.fromkeys(node.args)]
            lines += ['  simp only [' + ', '.join(rules) + ']', '  all_goals rfl']
    for label in ['false', 'true']:
        original = reactive.outputs['candidate_' + label]
        lines += [f'theorem composed_read_address_{label} (i : Values Sram.Input) (s : Values Sram.Register) :',
                  f'    Composed.read_address_{label} i s = (SramArtifactReference.readAddress {label}).eval i s := by',
                  '  simp only [SramArtifactReference.readAddress, MemoBind.eval_bind, Expr.eval]',
                  f'  exact congrArg (fun x : BitVec 7 => x.extractLsb\' 0 6)',
                  f'    ((post_{original} i s).trans ({ref.NAMESPACE}.source_candidate_{label} (postInput i s) (postState i s)))']
    for name, (_, ctor) in rb.REGISTERS.items():
        root = rb.graph_value(graph, graph.next[name], 'Composed')
        lines += [f'theorem source_next_{name} (i : Values Sram.Input) (s : Values Sram.Register) :',
                  f'    {root} = Sram.circuit.step i s ({ctor}) := by']
        if name == 'r_written':
            lines += ['  exact source_control_next_written i s']
        elif name in {'r_' + field for field, _, _ in sram.CORE_REGISTERS}:
            field = name.removeprefix('r_')
            lines += [f'  exact (composed_next_{field} i s).trans (SramArtifactReference.coreNext_correct (.{dict((n,c) for n,_,c in sram.CORE_REGISTERS)[field]}) i s)']
        else:
            lines += ['  exact source_control_next_' + name.removeprefix('r_') + ' i s']
    for name, (_, ctor) in rb.OUTPUTS.items():
        root = rb.graph_value(graph, graph.outputs[name], 'Composed')
        lines += [f'theorem source_output_{name} (i : Values Sram.Input) (s : Values Sram.Register) :',
                  f'    {root} = Sram.circuit.observe i s ({ctor}) := by']
        if name in {n for n, _, _ in sram.BASE_OUTPUTS}:
            lines += [f'  exact (composed_output_{name} i s).trans (SramArtifactReference.output_correct ({ctor}) i s)']
        elif name.startswith('mem_addr'):
            label = 'true' if name.endswith('1') else 'false'
            lines += [f'  simp only [Composed.memory_address_{label}, Sram.circuit, Circuit.observe, Sram.output, Sram.request, Expr.eval,',
                      f'    composed_read_address_{label}, SramArtifactReference.readAddress_correct]',
                      '  rfl']
        else:
            lines += ['  rfl']
    return '\n'.join(lines) + f'\nend {NAMESPACE}\n'
