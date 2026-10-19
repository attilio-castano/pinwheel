"""Actual controller-Verilog negative controls with kernel-checked witnesses.

Python evaluates only the reimported graph to propose a literal reduction. Lean
checks that literal against the actual candidate graph and attempts the original
universal component certificate at the same closed input/state.
"""
import re
import buffered_sram_readback as controller


def mutation_specs():
    return [
        ('unchanged', None, None, 'next', 'r_phase'),
        ('cold-phase', r'(r_phase\s*<=\s*)([^;]+);', r'\1~(\2);', 'next', 'r_phase'),
        ('full-start-payload', r'(r_tx_data\s*<=\s*)([^;]+);',
         r"\1(\2) & 32'h1;", 'next', 'r_tx_data'),
        ('sampler-latency', r"(r_stage2\s*<=\s*[^;]*\?\s*2'h0\s*:\s*)r_stage1;",
         r'\1raw_inputs;', 'next', 'r_stage2'),
        ('prospective-address', r'(assign mem_addr0\s*=\s*)([^;]+);',
         r'\1~(\2);', 'output', 'mem_addr0'),
        ('memory-write', r'(assign mem_write\s*=\s*)([^;]+);',
         r'\1~(\2);', 'output', 'mem_write'),
        ('coverage-reset', r'(r_written\s*<=\s*)([^;]+);',
         r"\1(\2) | 64'h1;", 'next', 'r_written'),
    ]


FIXTURES = {
    'r_phase': ({'initialize': 1}, {'r_phase': 3}),
    'r_tx_data': ({'command': 3, 'tx_data': 0x80000001, 'tx_length': 1},
                  {'r_valid': 1, 'r_count': 1, 'r_virtual_span': 1}),
    'r_stage2': ({'raw_inputs': 3}, {'r_stage1': 0}),
    'mem_addr0': ({}, {}),
    'mem_write': ({}, {}),
    'r_written': ({'initialize': 1}, {'r_written': 0xffffffffffffffff}),
}


def graph_values(graph, inputs, registers):
    values = {}
    for name, node in graph.nodes.items():
        args = [values[a] for a in node.args]
        if node.op == 'input': value = inputs.get(node.value, 0)
        elif node.op == 'reg': value = registers.get(node.value, 0)
        elif node.op == 'lit': value = node.value
        elif node.op == 'slice': value = args[0] >> node.value
        elif node.op == 'concat': value = args[0] << graph.nodes[node.args[1]].width | args[1]
        elif node.op == 'not': value = ~args[0]
        elif node.op == 'and': value = args[0] & args[1]
        elif node.op == 'or': value = args[0] | args[1]
        elif node.op == 'xor': value = args[0] ^ args[1]
        elif node.op == 'add': value = args[0] + args[1]
        elif node.op == 'sub': value = args[0] - args[1]
        elif node.op == 'eq': value = int(args[0] == args[1])
        elif node.op == 'lt': value = int(args[0] < args[1])
        elif node.op == 'mux': value = args[1] if args[0] == 1 else args[2]
        else: raise ValueError('Unsupported candidate operation: ' + node.op)
        values[name] = value & ((1 << node.width) - 1)
    return values


def mutation_sources(rb, graph, operation, port, baseline=None):
    if operation not in ('next', 'output') or port not in FIXTURES:
        raise ValueError('Missing distinguishing controller witness')
    interface = rb.REGISTERS if operation == 'next' else rb.OUTPUTS
    if port not in interface:
        raise ValueError('Changed controller witness endpoint')
    if baseline is None:
        raise ValueError('An original certified graph is required for controller controls')
    inputs, registers = FIXTURES[port]
    root = (graph.next if operation == 'next' else graph.outputs)[port]
    original_root = (baseline.next if operation == 'next' else baseline.outputs)[port]
    values = graph_values(graph, inputs, registers)
    original_values = graph_values(baseline, inputs, registers)
    value, expected = values[root], original_values[original_root]
    graphs = controller.graph_source(rb, graph).replace('namespace RTL\n', 'namespace Mutant\n').replace(
        'end RTL\n', 'end Mutant\n')
    model = controller.model_source(rb, graph).replace('import SramArtifactGraphs\n',
        'import SramMutantGraphs\n').replace('RTL.', 'Mutant.').replace(
        'rtlStep', 'mutantStep').replace('rtlObserve', 'mutantObserve')
    fixture = ['def faultInputs : Values Sram.Input']
    fixture += [f'  | _, {rb.INPUTS[name][1]} => {number}' for name, number in inputs.items()]
    fixture += ['  | _, _ => 0', 'def faultState : Values Sram.Register']
    fixture += [f'  | _, {rb.REGISTERS[name][1]} => {number}' for name, number in registers.items()]
    fixture += ['  | _, _ => 0']
    method, action, theorem = ('Step', 'step', 'step_correct') if operation == 'next' else (
        'Observe', 'observe', 'observe_correct')
    width, ctor = interface[port]
    def closed_lemmas(candidate, namespace, prefix, root, table):
        needed = set()
        def visit(name):
            if name in needed:
                return
            for arg in candidate.nodes[name].args:
                visit(arg)
            needed.add(name)
        visit(root)
        lines = []
        for name, node in candidate.nodes.items():
            if name not in needed or node.op in ('input', 'reg'):
                continue
            rules = [namespace + '.' + name]
            rules += [prefix + '_' + arg for arg in dict.fromkeys(node.args)
                      if candidate.nodes[arg].op not in ('input', 'reg')]
            lines += [f'private theorem {prefix}_{name} :',
                f'    {namespace}.{name} faultInputs faultState = {table[name]}#{node.width} := by',
                '  simp only [' + ', '.join(rules) + ']', '  all_goals rfl']
        endpoint = (f'{prefix}_{root}' if candidate.nodes[root].op not in ('input', 'reg') else 'by rfl')
        return '\n'.join(lines), endpoint
    candidate_lemmas, candidate_endpoint = closed_lemmas(graph, 'Mutant', 'candidate_value', root, values)
    original_lemmas, original_endpoint = closed_lemmas(baseline, 'RTL', 'original_value', original_root, original_values)
    # Each closed DAG node is normalized once. The final source value uses the
    # original universal theorem, avoiding conversion through its large AST.
    rejection = ('import SramArtifactProof\nimport SramMutantModel\n' + rb.HEADER +
        'set_option linter.unusedSimpArgs false\n' + '\n'.join(fixture) + '\n' +
        candidate_lemmas + '\n' + original_lemmas + '\n' +
        f'theorem candidate_correct : mutant{method} faultInputs faultState ({ctor}) =\n'
        f'    Sram.circuit.{action} faultInputs faultState ({ctor}) := by\n'
        f'  have candidate : mutant{method} faultInputs faultState ({ctor}) = {value}#{width} := {candidate_endpoint}\n'
        f'  have original : rtl{method} faultInputs faultState ({ctor}) = {expected}#{width} := {original_endpoint}\n'
        f'  have source : Sram.circuit.{action} faultInputs faultState ({ctor}) = {expected}#{width} :=\n'
        f'    ({theorem} faultInputs faultState ({ctor})).symm.trans original\n'
        f'  exact candidate.trans ((show {value}#{width} = {expected}#{width} from Eq.refl ({expected}#{width})).trans source.symm)\n'
        f'end {controller.NAMESPACE}\n')
    return {'SramMutantGraphs': graphs, 'SramMutantModel': model, 'SramReject': rejection}
