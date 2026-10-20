"""Restricted artifact interpretation for the buffered serial frontend.

The shared importer is loaded privately with an exact replacement interface.
Emitted MLIR is only a proof hint: Sources connects every root to Serial.circuit
in Lean. Actual RTL equations are separately imported from Yosys JSON.
"""
import importlib.util
import json
from pathlib import Path
import re
import sys
from collections import defaultdict

import paired_readback as decomposition

ROOT = Path(__file__).resolve().parents[1]
NAMESPACE = 'Pinwheel.Artifact.Buffered.Serial'

RAW_INPUTS = [('initialize', 1, 'initialize'), ('sck', 1, 'sck'),
              ('mosi', 1, 'mosi'), ('csn', 1, 'csn'), ('raw_inputs', 2, 'rawInputs')]
STATUS = [
    ('valid', 1, 'valid'), ('busy', 1, 'busy'), ('retained', 1, 'retained'),
    ('pending', 1, 'pending'), ('rejected', 1, 'rejected'), ('mode', 2, 'mode'),
    ('pc', 8, 'pc'), ('remaining', 8, 'remaining'), ('levels', 3, 'levels'),
    ('enabled', 3, 'enabled'), ('tx_consumed', 6, 'txConsumed'),
    ('rx_length', 6, 'rxLength'), ('rx_data', 32, 'rxData'),
    ('read_valid', 1, 'readValid'), ('read_bit', 1, 'readBit'),
    ('generation', 16, 'generation'), ('transfer', 16, 'transfer'),
    ('exhausted', 1, 'exhausted'), ('stage1', 2, 'stage1'), ('stage2', 2, 'stage2'),
    ('virtual_pc', 10, 'virtualPC'), ('env0', 3, 'env0'), ('env1', 3, 'env1'),
    ('phase', 3, 'phase'), ('wait_left', 8, 'waitLeft'), ('scratch', 16, 'scratch')]
REGISTERS = [
    ('sck_prev', 1, 'sckPrev'), ('csn_prev', 1, 'csnPrev'), ('active', 1, 'active'),
    ('reading', 1, 'reading'), ('count', 9, 'count'), ('request', 160, 'request'),
    ('dispatch', 1, 'dispatch'), ('capture', 1, 'capture'), ('code', 4, 'code'),
    ('sequence', 16, 'sequence'), ('rejected', 1, 'rejected'),
    ('response', 192, 'response'), ('ready', 1, 'ready')]
CORE_OUTPUTS = [
    ('initialize', 1, 'initialize'), ('command', 3, 'command'),
    ('address', 6, 'address'), ('word', 64, 'word'), ('control', 24, 'control'),
    ('branch', 56, 'branch'), ('count', 7, 'count'), ('virtual_span', 11, 'virtualSpan'),
    ('idle_levels', 3, 'idleLevels'), ('idle_enabled', 3, 'idleEnabled'),
    ('tx_data', 32, 'txData'), ('tx_length', 6, 'txLength'),
    ('rx_capacity', 6, 'rxCapacity'), ('expected_generation', 16, 'expectedGeneration'),
    ('expected_transfer', 16, 'expectedTransfer'), ('read_index', 5, 'readIndex'),
    ('raw_inputs', 2, 'rawInputs')]


def backend():
    name = '_buffered_serial_readback'
    spec = importlib.util.spec_from_file_location(name, ROOT / 'scripts/backend_readback.py')
    rb = importlib.util.module_from_spec(spec)
    sys.modules[name] = rb
    spec.loader.exec_module(rb)
    rb.TOP = 'pinwheel_buffered_sram_serial_frontend'
    rb.INPUTS = {n: (w, '.' + ctor) for n, w, ctor in RAW_INPUTS}
    rb.INPUTS.update({'status_' + n: (w, '.status .' + ctor) for n, w, ctor in STATUS})
    rb.REGISTERS = {'r_' + n: (w, '.' + ctor) for n, w, ctor in REGISTERS}
    rb.OUTPUTS = {'core_' + n: (w, '.core .' + ctor) for n, w, ctor in CORE_OUTPUTS}
    rb.OUTPUTS.update({'miso': (1, '.miso'), 'ready': (1, '.ready')})
    rb.HEADER = '''import Pinwheel.Hardware.Buffered.Serial
open Pinwheel.Hardware Pinwheel.Hardware.Buffered
namespace Pinwheel.Artifact.Buffered.Serial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
'''
    return rb


def adapt(text):
    return (text.replace('Values Machine.Input', 'Values Serial.Input')
            .replace('Values Register', 'Values Serial.Register')
            .replace('Pinwheel.Artifact.Backend', NAMESPACE))


def check_interface(rb, path):
    interface = decomposition.read_json(path)
    if interface.get('schema') != 1 or interface.get('module') != rb.TOP:
        raise ValueError('Changed frontend assembly contract')
    decomposition.check_interface(rb, interface)


def hints_source(rb, source):
    return adapt(rb.HEADER + source.definitions('Source') + 'end ' + NAMESPACE + '\n')


def graphs_source(rb, rtl):
    return adapt('import Hints\n' + rb.HEADER + rtl.definitions('RTL') + 'end ' + NAMESPACE + '\n')


def sources_source(rb, source, select=None):
    """All typed root equations, discharged by kernel definitional equality."""
    lines = ['import Hints\nimport Lean.Elab.Command\n' + rb.HEADER]
    for operation, roots, interface in [('next', source.next, rb.REGISTERS),
                                         ('output', source.outputs, rb.OUTPUTS)]:
        for name, node in roots.items():
            if select is not None and (operation, name) not in select:
                continue
            ctor = interface[name][1]
            lines.append(f'theorem source_{operation}_{name} (i : Values Serial.Input) '
                         f'(s : Values Serial.Register) :\n'
                         f'    {rb.graph_value(source, node, "Source")} = '
                         f'(Serial.circuit.{operation} ({ctor})).eval i s := by\n  rfl\n')
            lines.append(f'run_cmd IO.eprintln "checked source {operation}.{name}"')
    return '\n'.join(lines) + '\nend ' + NAMESPACE + '\n'


def helper_source(rb, pairs):
    lines = ['import Lean.Elab.Command\nimport Pinwheel.Hardware.Readback.Boolean\n' + rb.HEADER,
             'set_option linter.unusedSimpArgs false']
    for k, pair in enumerate(pairs):
        params = ' '.join(f'(x{j} : BitVec {w})' for j, (w, _, _) in enumerate(pair['variables']))
        if pair['left'] == pair['right']:
            lines.append(f'theorem local_{k} {params} :\n'
                         f'    {rb.render_tree(pair["left"])} = {rb.render_tree(pair["right"])} := by\n'
                         '  rfl\n')
            continue
        lines.append(f'theorem local_{k} {params} :\n'
                     f'    {rb.render_tree(pair["left"])} = {rb.render_tree(pair["right"])} := by\n'
                     '  try simp only [BitVec.append_assoc, BitVec.cast_eq]\n'
                     '  try simp only [BitVec.sub_eq_add_neg, BitVec.extractLsb\'_append_eq_right,\n'
                     '    BitVec.extractLsb\'_append_extractLsb\'_eq_extractLsb\', BitVec.extractLsb\'_eq_self]\n'
                     '  all_goals first\n'
                     '  | (bv_normalize; first | omega | grind (splits := 64))\n'
                     '  | (simp [Pinwheel.Hardware.Readback.eq_bits, Fin.forall_fin_succ,\n'
                     '      BitVec.getElem_append, BitVec.getElem_extractLsb\']; all_goals grind (splits := 64))\n')
        if k % 100 == 0:
            lines.append(f'run_cmd IO.eprintln "checked local {k}"')
    return '\n'.join(lines) + '\nend ' + NAMESPACE + '\n'


def links_source(rb, source, rtl, pairs):
    return adapt(rb.links_source(source, rtl, pairs, 'LocalProofs', 'Graphs'))


def partitions(rb, source, rtl, solver):
    """Retain one-bit mux cutpoints, including the 192-bit MISO selector.

    Random signatures and SMT propose boundaries only. Every local equality and
    its reconnection to the actual gates is independently kernel checked.
    """
    oracle = rb.cut_oracle(solver)
    base = decomposition._suggest_partitions(rb, source, rtl, oracle=oracle)
    selected = {p['source']: p['rtl'] for p in base}
    signatures = defaultdict(list)
    # The 9-bit selector needs enough proposals to distinguish adjacent narrow
    # muxes; fewer samples often miss an individual count. This is still only
    # a decomposition heuristic, never an acceptance test.
    for name, sig in rtl.signatures(4096).items():
        signatures[sig].append(name)
    for name, sig in source.signatures(4096).items():
        node = source.nodes[name]
        if node.op == 'mux' and node.width == 1 and name not in selected:
            choices = signatures.get(sig, [])
            if choices:
                selected[name] = min(choices, key=lambda n: (rtl.nodes[n].op != 'mux',
                    rtl.nodes[n].op in ('input', 'reg')))
    endpoints = [(source.next[n], rtl.next[n]) for n in rb.REGISTERS]
    endpoints += [(source.outputs[n], rtl.outputs[n]) for n in rb.OUTPUTS]
    selected.update(endpoints)
    pairs = []
    forced = set(endpoints)
    for sn in source.nodes:
        if sn not in selected or source.nodes[sn].op in ('input', 'reg', 'lit'):
            continue
        rn = selected[sn]
        try:
            pair = decomposition.constrained_pair(rb, source, rtl, pairs, sn, rn, oracle)
            pair = decomposition.expand_constraints(pair)
            if not oracle(pair):
                raise ValueError('Invalid expanded cutpoint: ' + sn)
        except ValueError:
            if (sn, rn) in forced:
                raise
            continue
        pairs.append(pair)
    matches = {(p['source'], p['rtl']) for p in pairs}
    for sn, rn in endpoints:
        if (sn, rn) not in matches and not (
                source.nodes[sn].op in ('input', 'reg', 'lit') and sn == rn):
            raise ValueError('Missing frontend endpoint: ' + sn)
    return pairs


def model_source(rb, rtl):
    lines = ['import Graphs\n' + rb.HEADER]
    for method, interface, roots, result in [('Step', rb.REGISTERS, rtl.next, 'Serial.Register'),
                                            ('Observe', rb.OUTPUTS, rtl.outputs, 'Serial.Output')]:
        lines.append(f'def rtl{method} (i : Values Serial.Input) (s : Values Serial.Register) : Values {result}')
        for name, (_, ctor) in interface.items():
            lines.append(f'  | _, {ctor} => {rb.graph_value(rtl, roots[name], "RTL")}')
    return '\n'.join(lines) + '\nend ' + NAMESPACE + '\n'


def endpoints_source(rb, source, rtl, pairs):
    matches = {(p['source'], p['rtl']): k for k, p in enumerate(pairs)}
    lines = ['import Sources\nimport Links\nimport Model\n' + rb.HEADER]
    for operation, roots, actual, interface in [('next', source.next, rtl.next, rb.REGISTERS),
                                               ('output', source.outputs, rtl.outputs, rb.OUTPUTS)]:
        method, action = ('Step', 'step') if operation == 'next' else ('Observe', 'observe')
        for name, sn in roots.items():
            rn, ctor = actual[name], interface[name][1]
            lines.append(f'theorem rtl_{operation}_{name} (i : Values Serial.Input) (s : Values Serial.Register) :\n'
                         f'    rtl{method} i s ({ctor}) = Serial.circuit.{action} i s ({ctor}) := by\n'
                         f'  change ({rb.graph_value(rtl, rn, "RTL")}) = _')
            if (sn, rn) in matches:
                lines.append(f'  exact (link_{matches[(sn,rn)]} i s).symm.trans (source_{operation}_{name} i s)')
            else:
                lines.append(f'  exact source_{operation}_{name} i s')
    return '\n'.join(lines) + '\nend ' + NAMESPACE + '\n'


def proof_source(rb):
    lines = ['import Endpoints\nimport Pinwheel.Hardware.Buffered.ArtifactPackage\n' + rb.HEADER,
             'theorem next_correct (i : Values Serial.Input) (s : Values Serial.Register) '
             '(r : Serial.Register w) :\n    rtlStep i s r = Serial.circuit.step i s r := by\n  cases r']
    lines.append('  all_goals first | ' + ' | '.join(f'exact rtl_next_{n} i s' for n in rb.REGISTERS))
    lines.append('theorem output_correct (i : Values Serial.Input) (s : Values Serial.Register) '
                 '(o : Serial.Output w) :\n    rtlObserve i s o = Serial.circuit.observe i s o := by\n'
                 '  cases o with\n  | miso => exact rtl_output_miso i s\n'
                 '  | ready => exact rtl_output_ready i s\n  | core p =>\n    cases p')
    lines.append('    all_goals first | ' + ' | '.join(f'exact rtl_output_core_{n} i s' for n, _, _ in CORE_OUTPUTS))
    lines.append('def behavior : ArtifactPackage.Behavior Serial.Input Serial.Register Serial.Output :=\n'
                 '  ⟨rtlStep, rtlObserve⟩')
    return '\n'.join(lines) + '\nend ' + NAMESPACE + '\n'


def mutation_specs():
    """Actual-Verilog fault controls; each changes one exact statement/use."""
    return [
        ('unchanged', None, None, 'next', 'r_capture'),
        ('capture-delay', r'r_capture\s*<=\s*[^;]+;',
         'r_capture <= ~initialize & r_capture;', 'next', 'r_capture'),
        ('response-snapshot', r'(\s+)status_valid\}',
         r'\1~status_valid}', 'next', 'r_response'),
        ('request-order', r'\{r_request\[158:0\], mosi\}',
         '{mosi, r_request[159:1]}', 'next', 'r_request'),
        ('miso-last-bit', r'\? r_response\[0\]',
         '? ~r_response[0]', 'output', 'miso'),
        ('dispatch-command', r'(assign core_command\s*=\s*)([^;]+);',
         r'\1~(\2);',
         'output', 'core_command')]


FAULT_STATES = {
    'r_capture': [('dispatch', 1)],
    'r_response': [('capture', 1)],
    'r_request': [('active', 1)],
    'miso': [('active', 1), ('reading', 1), ('count', 191)],
    'core_command': [('dispatch', 1)],
}
FAULT_EXPECTED = {'r_capture': 1, 'r_response': 0x5A1 << 180,
                  'r_request': 1, 'miso': 0, 'core_command': 0}


def rejection_source(rb, operation, port, prefix=None, candidate_value=None):
    """Reuse the universal theorem at an independent distinguishing raw state.

    A closed witness avoids spending time unfolding unequal open 160-bit shift
    expressions during definitional equality. The positive certificate itself
    still quantifies over every input and register value.
    """
    interface = rb.REGISTERS if operation == 'next' else rb.OUTPUTS
    ctor = interface[port][1]
    method, action, theorem = ('Step', 'step', 'next_correct') if operation == 'next' else (
        'Observe', 'observe', 'output_correct')
    if port not in FAULT_STATES:
        raise ValueError('No distinguishing frontend witness: ' + port)
    fixture = ('def faultInputs : Values Serial.Input\n'
               '  | _, .sck => 1\n  | _, .mosi => 1\n  | _, _ => 0\n'
               'def faultState : Values Serial.Register\n')
    fixture += ''.join(f'  | _, .{field} => {value}\n' for field, value in FAULT_STATES[port])
    fixture += '  | _, _ => 0\n'
    text = ('import Proof\nimport MutantModel\n' + rb.HEADER + fixture +
            f'theorem candidate_correct :\n'
            f'    mutant{method} faultInputs faultState ({ctor}) =\n'
            f'      Serial.circuit.{action} faultInputs faultState ({ctor}) := by\n')
    if candidate_value is not None:
        width = interface[port][0]
        # Both values are kernel-checked against the actual expressions by
        # `change`. The Python evaluation supplies only a reduction hint.
        text += f'  change {candidate_value}#{width} = {FAULT_EXPECTED[port]}#{width}\n'
    text += f'  exact {theorem} faultInputs faultState ({ctor})\nend ' + NAMESPACE + '\n'
    return prefix_imports(text, prefix)


MODULES = ('Hints', 'Graphs', 'Sources', 'LocalProofs', 'Links', 'Model',
           'Endpoints', 'Proof', 'MutantGraphs', 'MutantModel', 'Reject')


def prefix_imports(text, prefix):
    """Give independently generated component certificates unique module IDs."""
    if not prefix:
        return text
    if not re.fullmatch(r'[A-Za-z][A-Za-z0-9_]*', prefix):
        raise ValueError('Invalid Lean module prefix')
    for name in MODULES:
        text = re.sub(r'(?m)^import ' + name + r'$', 'import ' + prefix + name, text)
    return text


def mutation_sources(rb, rtl, operation, port, prefix=None):
    graphs = graphs_source(rb, rtl).replace('namespace RTL\n', 'namespace Mutant\n').replace(
        'end RTL\n', 'end Mutant\n')
    model = model_source(rb, rtl).replace('import Graphs\n', 'import MutantGraphs\n').replace(
        'RTL.', 'Mutant.').replace('rtlStep', 'mutantStep').replace('rtlObserve', 'mutantObserve')
    values = {}
    states = {'r_' + next(n for n, _, ctor in REGISTERS if ctor == field): value
              for field, value in FAULT_STATES[port]}
    for name, node in rtl.nodes.items():
        args = [values[a] for a in node.args]
        if node.op == 'input': value = int(node.value in ('sck', 'mosi'))
        elif node.op == 'reg': value = states.get(node.value, 0)
        elif node.op == 'lit': value = node.value
        elif node.op == 'slice': value = args[0] >> node.value
        elif node.op == 'concat': value = args[0] << rtl.nodes[node.args[1]].width | args[1]
        elif node.op == 'not': value = ~args[0]
        elif node.op == 'and': value = args[0] & args[1]
        elif node.op == 'or': value = args[0] | args[1]
        elif node.op == 'xor': value = args[0] ^ args[1]
        elif node.op == 'add': value = args[0] + args[1]
        elif node.op == 'sub': value = args[0] - args[1]
        elif node.op == 'eq': value = int(args[0] == args[1])
        elif node.op == 'lt': value = int(args[0] < args[1])
        elif node.op == 'mux': value = args[1] if args[0] == 1 else args[2]
        else: raise ValueError('Unsupported fixture operation: ' + node.op)
        values[name] = value & ((1 << node.width) - 1)
    candidate_value = values[(rtl.next if operation == 'next' else rtl.outputs)[port]]
    texts = {'MutantGraphs': graphs, 'MutantModel': model,
             'Reject': rejection_source(rb, operation, port, candidate_value=candidate_value)}
    return {(prefix or '') + name: prefix_imports(text, prefix) for name, text in texts.items()}


def generate(rb, source, rtl, pairs, prefix=None):
    texts = {'Hints': hints_source(rb, source), 'Graphs': graphs_source(rb, rtl),
            'Sources': sources_source(rb, source), 'LocalProofs': helper_source(rb, pairs),
            'Links': links_source(rb, source, rtl, pairs), 'Model': model_source(rb, rtl),
            'Endpoints': endpoints_source(rb, source, rtl, pairs), 'Proof': proof_source(rb)}
    return {(prefix or '') + name: prefix_imports(text, prefix) for name, text in texts.items()}
