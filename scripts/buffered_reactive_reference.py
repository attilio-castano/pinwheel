"""Untrusted named-DAG hints for the unadapted buffered semantic reference.

Every helper and endpoint is connected back to the actual typed expression by
Lean. Source parsing only chooses proof boundaries; it discharges no equality.
"""
from pathlib import Path
import re

import buffered_sram_readback as sram

ROOT = Path(__file__).resolve().parents[1]
NAMESPACE = 'Pinwheel.Artifact.ReactiveReference'


def named_roots():
    text = (ROOT / 'Pinwheel/Hardware/Buffered/Reactive.lean').read_text()
    return [(m[1], int(m[2])) for m in re.finditer(r'^def (\w+) : E (\d+) :=', text, re.M)]


def proof_rules(name, term, previous):
    text = (ROOT / 'Pinwheel/Hardware/Buffered/Reactive.lean').read_text()
    matches = list(re.finditer(r'^def (\w+)\b', text, re.M))
    definitions = {m[1]: text[m.end():matches[k + 1].start() if k + 1 < len(matches) else len(text)]
                   for k, m in enumerate(matches)}
    helpers = {n for n, _ in named_roots()}
    if name.startswith('helper_'):
        current = name.removeprefix('helper_')
        body = definitions[current]
        unfold = {'Reactive.' + current}
    elif name.startswith('next_'):
        ctor = term.split('(.', 1)[1].split(')', 1)[0]
        body = definitions['next']
        clauses = list(re.finditer(r'\| _,\s*\.(\w+)\b', body))
        chosen = next(k for k, m in enumerate(clauses) if m[1] == ctor)
        body = body[clauses[chosen].end():clauses[chosen + 1].start() if chosen + 1 < len(clauses) else len(body)]
        current, unfold = None, {'Reactive.next'}
    elif name.startswith('candidate_'):
        return ['SramCandidates.candidate', 'SramCandidates.selectedEndpoint',
                'SramCandidates.sequential', 'Reactive.isPhase', 'Reactive.both',
                'Reactive.innerStart', 'Reactive.outerStart', 'Reactive.increment',
                'Expr.eval'] + ['← source_helper_' + n for n in
                    ('finish', 'currentControl', 'innerAgain', 'outerAgain')]
    else:
        ctor = term.split('(.', 1)[1].split(')', 1)[0]
        body = definitions['circuit']
        clauses = list(re.finditer(r'\|\s*\.(\w+)\s*=>', body))
        chosen = next(k for k, m in enumerate(clauses) if m[1] == ctor)
        body = body[clauses[chosen].end():clauses[chosen + 1].start() if chosen + 1 < len(clauses) else len(body)]
        current, unfold = None, {'Reactive.circuit'}
    cuts, visited = set(), set()
    def visit(fragment):
        for word in re.findall(r'\b\w+\b', fragment):
            if word == current or word in visited or word not in definitions:
                continue
            visited.add(word)
            if word in helpers:
                if 'helper_' + word in previous:
                    cuts.add('helper_' + word)
            else:
                unfold.add('Reactive.' + word)
                visit(definitions[word])
    visit(body)
    return sorted(unfold) + ['Execution.readTree', 'Expr.eval'] + [
        '← source_' + p for p in previous if p in cuts]


def endpoints():
    return ([('helper_' + name, width, 'Reactive.' + name) for name, width in named_roots()] +
            [('next_' + name, width, 'Reactive.next (.' + ctor + ')')
             for name, width, ctor in sram.CORE_REGISTERS] +
            [('output_' + name, width, 'Reactive.circuit.output (.' + ctor + ')')
             for name, width, ctor in sram.BASE_OUTPUTS] +
            [('candidate_false', 7, 'SramCandidates.candidate false'),
             ('candidate_true', 7, 'SramCandidates.candidate true')])


def backend():
    rb = sram.backend()
    rb.TOP = 'pinwheel_buffered_artifact_reactive_reference'
    rb.INPUTS = {n: (w, '.' + ctor) for n, w, ctor in sram.BASE_INPUTS}
    rb.REGISTERS = {f'r_word{k}': (144, f'.word {k}#6') for k in range(64)}
    rb.REGISTERS.update({'r_' + n: (w, '.' + ctor) for n, w, ctor in sram.CORE_REGISTERS})
    rb.OUTPUTS = {name: (width, '.' + name) for name, width, _ in endpoints()}
    rb.HEADER = f'''import Pinwheel.Hardware.Buffered.SramCandidates
open Pinwheel.Hardware Pinwheel.Hardware.Buffered
namespace {NAMESPACE}
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
'''
    return rb


def adapt(text):
    return text.replace('Values Machine.Input', 'Values Reactive.Input').replace(
        'Values Register', 'Values Reactive.Register').replace('Pinwheel.Artifact.Backend', NAMESPACE)


def emitter_source():
    roots = endpoints()
    lines = ['import Pinwheel.Hardware.Buffered.SramCandidates',
             'open Pinwheel.Hardware Pinwheel.Hardware.Buffered',
             'namespace Pinwheel.Artifact.ReactiveReference.Emit',
             'inductive Root : Nat → Type where']
    lines += [f'  | {name} : Root {width}' for name, width, _ in roots]
    lines += ['def expression : {w : Nat} → Root w → Reactive.E w']
    lines += [f'  | _, .{name} => {term}' for name, _, term in roots]
    lines += ['def label : {w : Nat} → Root w → String']
    lines += [f'  | _, .{name} => "{name}"' for name, _, _ in roots]
    lines += ['def outputs : Array (Sigma Root) := #[']
    lines += [f'  ⟨{width}, .{name}⟩' + (',' if k + 1 < len(roots) else '')
              for k, (name, width, _) in enumerate(roots)]
    lines += [']',
              'def circuit : Circuit Reactive.Input Reactive.Register Root :=',
              '  ⟨fun r => .reg r, expression⟩',
              'end Pinwheel.Artifact.ReactiveReference.Emit',
              'def main (args : List String) : IO Unit := do',
              '  let path := args.headD "build/reactive-reference.mlir"',
              '  let text ← IO.ofExcept (MemoEmit.moduleText',
              '    "pinwheel_buffered_artifact_reactive_reference"',
              '    Pinwheel.Artifact.ReactiveReference.Emit.circuit',
              '    Reactive.inputs Reactive.registers Pinwheel.Artifact.ReactiveReference.Emit.outputs',
              '    Reactive.inputLabel Reactive.registerLabel Pinwheel.Artifact.ReactiveReference.Emit.label)',
              '  IO.FS.writeFile path text',
              '  IO.println "Named reactive reference emitted; all roots require kernel checks."']
    return '\n'.join(lines) + '\n'


def hints_source(rb, graph):
    return adapt(rb.HEADER + graph.definitions('Source') + f'end {NAMESPACE}\n')


def sources_source(rb, graph, prefix='Reactive'):
    expected = {name for name, _, _ in endpoints()}
    if set(graph.outputs) != expected:
        raise ValueError('Incomplete named reactive reference endpoints')
    lines = [f'import {prefix}Hints\nimport Lean.Elab.Command\n' + rb.HEADER]
    previous = []
    for name, width, term in endpoints():
        root = rb.graph_value(graph, graph.outputs[name], 'Source')
        lines += [f'theorem source_{name} (i : Values Reactive.Input) (s : Values Reactive.Register) :',
                  f'    {root} = ({term}).eval i s := by']
        rules = ', '.join(proof_rules(name, term, previous))
        lines += ['  conv =>', '    rhs', f'    simp only [{rules}]', '  all_goals rfl',
                  f'run_cmd IO.eprintln "checked reference {name}"']
        if name.startswith('helper_'):
            previous.append(name)
    return '\n'.join(lines) + f'\nend {NAMESPACE}\n'
