#!/usr/bin/env python3
"""Shared reactive-buffer execution, compact schedules and independent wire fixtures.

This validates the reference target. It does not emit or qualify buffered RTL.
"""
import argparse
import importlib.util
import json
from pathlib import Path
import re
import shutil
import sys

from buffered_engine import (BufferedBlock, BufferedEngine, BufferedInstruction,
                             BufferedProgram, BufferedRepeat, BufferedSequence)
from pinwheel_buffers import TransferSlot
from validation_run import Commands, fresh_directory, sha

ROOT = Path(__file__).resolve().parents[1]


def decode_schedule(code):
    kind = code.get('kind')
    if kind == 'emit' and set(code) == {'kind', 'instruction'}:
        fields = dict(code['instruction'])
        for name in ('entry_capture', 'terminal_capture', 'finish'):
            if isinstance(fields.get(name), list):
                fields[name] = tuple(fields[name])
        return BufferedBlock((BufferedInstruction(**fields),))
    if kind == 'seq' and set(code) == {'kind', 'first', 'rest'}:
        return BufferedSequence((decode_schedule(code['first']), decode_schedule(code['rest'])))
    if kind == 'repeat' and set(code) == {'kind', 'count', 'body'}:
        return BufferedRepeat(code['count'], decode_schedule(code['body']))
    raise ValueError('Unknown or malformed exported counted schedule')


def projection(engine):
    stopped = engine.done
    reason = ('complete' if engine.mode == 'completed' else engine.mode) if stopped else None
    slot = engine.slot
    return dict(control='stopped' if stopped else engine.mode, stop_reason=reason,
        pc=None if stopped else engine.pc, remaining=None if stopped else engine.remaining,
        wait_left=engine.wait_left if engine.mode == 'qualifying' else None,
        samples=list(engine.samples), levels=engine.levels, enabled=engine.enabled,
        sampler_first=engine._first, sampler_second=engine._second,
        phase=slot.state, tx_consumed_bits=slot._tx_consumed, rx_bits=list(slot._rx),
        outcome=slot.peek(engine.identity).outcome if slot.state == 'completed' else None)


def bind_i2c_factory(case, program):
    """Bind the typed frontend to the independently wire-checked factory.

    Compare every virtual instruction, including untaken fault cleanup, plus
    compact geometry and admission metadata. AST grouping may differ between
    languages; stored descriptors and decoded leaves must agree.
    """
    if not case['name'].startswith('i2c-'):
        return 0
    from buffered_i2c import buffered_i2c_read
    reference = buffered_i2c_read(byte_count=4)
    if (program.storage() != reference.storage() or
            (program.idle_levels, program.idle_enabled, program.tx_bits, program.rx_bits,
             program.rx_reservation_bits) !=
            (reference.idle_levels, reference.idle_enabled, reference.tx_bits, reference.rx_bits,
             reference.rx_reservation_bits)):
        raise RuntimeError('Lean/Python I2C factory geometry or admission mismatch')
    for pc in range(program.span):
        if program.fetch(pc) != reference.fetch(pc):
            raise RuntimeError(f'Lean/Python I2C factory instruction mismatch at virtual PC {pc}')
    return program.span


def differential(vectors):
    if vectors.get('schema') != 'pinwheel-buffered-reactive-vectors-v1':
        raise ValueError('Unknown buffered reactive vector schema')
    cases = vectors.get('cases')
    if type(cases) is not list or not cases:
        raise ValueError('Buffered reactive vectors must contain cases')
    edges = initial_states = completed = faults = timeouts = 0
    factory_bindings = factory_positions = 0
    for case_index, case in enumerate(cases):
        definition = case['program']
        schedule = decode_schedule(definition['schedule'])
        metrics = dict(virtual_span=schedule.span, stored_words=schedule.words,
                       stored_nodes=schedule.nodes, loop_count=schedule.loops,
                       nesting=schedule.nesting)
        for name, actual in metrics.items():
            if actual != definition[name]:
                raise RuntimeError(f'Lean/Python counted geometry mismatch: {case_index}/{name}')
        program = BufferedProgram((), schedule=schedule,
            idle_levels=definition['idle_levels'], idle_enabled=definition['idle_enabled'],
            declared_tx_bits=case['tx_demand'], declared_rx_bits=case['rx_demand'],
            max_rx_bits=case.get('rx_max', case['rx_demand']))
        positions = bind_i2c_factory(case, program)
        factory_bindings += positions > 0
        factory_positions += positions
        slot = TransferSlot(tx_capacity_bits=case['tx_capacity_bits'],
                            rx_capacity_bits=case['rx_capacity_bits'])
        identity = slot.begin(program.key, tuple(case['tx_bits']), case['rx_limit'])
        engine = BufferedEngine(slot, identity, program)
        actual = projection(engine)
        if actual != case['initial_state']:
            raise RuntimeError(f'Lean/Python buffered initial-state mismatch in case {case_index}: '
                               f'expected {case["initial_state"]}, observed {actual}')
        initial_states += 1
        incoming, states = case['incoming'], case['states']
        if len(incoming) != len(states):
            raise ValueError('Buffered vectors must pair every input edge with a state')
        for edge, (pads, expected) in enumerate(zip(incoming, states, strict=True)):
            engine.step(pads)
            actual = projection(engine)
            if actual != expected:
                raise RuntimeError(f'Lean/Python buffered execution mismatch in case {case_index}, '
                                   f'edge {edge}: expected {expected}, observed {actual}')
            edges += 1
        completed += engine.mode == 'completed'
        faults += engine.mode == 'fault'
        timeouts += engine.mode == 'timeout'
    return dict(cases=len(cases), initial_states=initial_states, edges=edges,
                completed=completed, faults=faults, timeouts=timeouts,
                i2c_factory_bindings=factory_bindings,
                i2c_factory_instruction_positions=factory_positions,
                scope='Finite actual Lean/Python execution and schedule differential; '
                      'not universal Python refinement')


def legacy_gate():
    spec = importlib.util.spec_from_file_location('buffered_ownership_gate',
                                                ROOT / 'scripts/check-buffered-transfers.py')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--tag', required=True)
    args = parser.parse_args()
    if sys.version_info < (3, 12):
        raise RuntimeError('Python 3.12+ is required')
    lake = shutil.which('lake')
    if not lake:
        raise RuntimeError('The pinned Lean toolchain must be on PATH')
    out = fresh_directory(ROOT / 'build/buffered-reactive', args.tag)
    paths = [ROOT / name for name in ('Pinwheel.lean', 'lean-toolchain', 'lakefile.toml',
                                    'lake-manifest.json')]
    paths += sorted((ROOT / 'Pinwheel').rglob('*.lean'))
    paths += sorted((ROOT / 'test').glob('*.lean'))
    paths += sorted((ROOT / 'scripts').glob('*.py')) + sorted((ROOT / 'test').glob('test_*.py'))
    hashes = {str(path.relative_to(ROOT)): sha(path) for path in paths}
    commands = Commands(ROOT, out, default_timeout=1800)
    version = commands([lake, 'env', 'lean', '--version'], 'lean-version').strip()
    expected = (ROOT / 'lean-toolchain').read_text().strip().split(':v')[-1]
    if not re.search(r'Lean \(version ' + re.escape(expected) + r'(?:,|\s)', version):
        raise RuntimeError('Compiler differs from the repository pin')
    commands([lake, 'build'], 'build')
    commands([lake, 'env', 'lean', '-DwarningAsError=true', 'test/ProofAudit.lean'], 'axioms')
    lean = [lake, 'env', 'lean', '-DwarningAsError=true', '--run']
    commands([*lean, 'test/Transfer.lean'], 'lean-ownership')
    commands([*lean, 'test/Buffered.lean'], 'lean-buffered-reactive')
    ownership = legacy_gate().differential(json.loads(commands(
        [*lean, 'test/TransferExport.lean'], 'ownership-vectors')))
    exported = commands([*lean, 'test/BufferedExport.lean'], 'execution-vectors')
    execution = differential(json.loads(exported))
    if any(execution[name] == 0 for name in ('completed', 'faults', 'timeouts')):
        raise RuntimeError('Execution vectors omit a required terminal outcome')
    if execution['i2c_factory_bindings'] < 7:
        raise RuntimeError('Execution vectors omit the required typed I2C frontend bindings')
    tests = {}
    for label, optimization in (('python', []), ('python-optimized', ['-O'])):
        log = commands([sys.executable, *optimization, '-B', '-m', 'unittest', 'discover',
                        '-s', 'test', '-p', 'test_*.py'], label)
        count = re.search(r'Ran (\d+) tests?', log)
        skipped = re.search(r'OK \(skipped=(\d+)\)', log)
        if not count:
            raise RuntimeError('Missing Python suite summary')
        tests[label] = dict(total=int(count[1]), skipped=int(skipped[1]) if skipped else 0)
    from buffered_i2c import witnesses
    existing = legacy_gate().witnesses()
    i2c = witnesses()
    i2c_outcomes = {outcome: sum(case['outcome'] == outcome for case in i2c)
                    for outcome in ('complete', 'fault', 'timeout')}
    if any(count == 0 for count in i2c_outcomes.values()):
        raise RuntimeError('Independent I2C fixtures omit a required terminal outcome')
    cases = existing + i2c
    (out / 'wire-cases.json').write_text(json.dumps(cases, indent=2) + '\n')
    for path in paths:
        if sha(path) != hashes[str(path.relative_to(ROOT))]:
            raise RuntimeError(f'Source changed during validation: {path}')
    report = dict(schema='pinwheel-buffered-reactive-evidence-v1',
        target='buffered-reference-v1', lean=version, ownership=ownership,
        execution=execution, python=tests, legacy_wire_cases=len(existing),
        i2c_wire_cases=len(i2c), wire_cases=len(cases),
        i2c_outcomes=i2c_outcomes,
        model_wire_edges=sum(case['engine_edges'] if 'engine_edges' in case
                             else case['execution_edges'] for case in cases),
        wire_cases_sha256=sha(out / 'wire-cases.json'), source_sha256=hashes,
        commands=commands.records,
        boundary='Shared Lean Reactive/Fetch and counted schedule semantics composed with finite '
                 'buffer ownership; finite Python execution differential; independent digital '
                 'SPI/JTAG/I2C fixtures. No new circuit, buffered RTL interpretation, hardware '
                 'image/transport encoding, mapped cost or physical qualification.')
    (out / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    print(f'Buffered reactive model gate passed: {out / "report.json"}', flush=True)


if __name__ == '__main__':
    main()
