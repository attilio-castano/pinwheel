#!/usr/bin/env python3
"""Owned finite SPI datapath through typed circuit, emitted RTL and saved gates.

This opt-in linear parallel target has no paired SRAM/serial package integration,
counted/reactive execution, routed timing or physical qualification.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import sys
import time

from buffered_engine import BufferedEngine, BufferedInstruction, BufferedProgram, buffered_spi
from buffered_hardware import (BufferedHardwareHost, BufferedHardwareWaitTimeout,
                               encode_instruction, lower_buffered, pack_wire_bits)
from buffered_hardware_rtl import BufferedRTL, COMMAND_FIELDS, replay_vectors
from buffered_hardware_synthesis import CAD, compile_rtl, stage_pdk, synthesize
from buffered_peers import BufferedSPIPeer
from pad_io import PadDrive
from pinwheel_buffers import TransferError, TransferSlot
from validation_run import Commands, fresh_directory, sha

ROOT = Path(__file__).resolve().parents[1]
CIRCT = ROOT / 'build/tools/firtool-1.159.0/bin/circt-opt'
TARGET = 'pinwheel-buffered-linear32-v1'
STATE_WIDTHS = dict(valid=1, busy=1, retained=1, pending=1, rejected=1, mode=2,
    pc=8, remaining=8, levels=3, enabled=3, tx_consumed=6, rx_length=6, rx_data=32,
    read_valid=1, read_bit=1, generation=16, transfer=16, exhausted=1, stage1=2, stage2=2)


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def command_cases():
    """Directed independent command expectations, plus all 4^3 raw histories."""
    cases = []

    def case(name):
        vectors = []
        checks = []
        def edge(raw=3, expect=None, **command):
            vectors.append(dict(command=command, raw_inputs=raw))
            if expect is not None:
                checks.append(dict(edge=len(vectors)-1, state=expect))
        def load(words, idle=4):
            for address, word in enumerate(words):
                edge(command=1, address=address, word=word)
            edge(command=2, count=len(words), idle_levels=idle, idle_enabled=7,
                 expect=dict(valid=1, pending=0, rejected=0))
        edge(initialize=1, expect=dict(generation=0, transfer=0, retained=0, busy=0))
        return edge, load, vectors, checks

    def finish(name, vectors, checks):
        cases.append(dict(name=name, vectors=vectors, checks=checks))

    e, load, vs, cs = case('coverage-and-count-admission')
    e(command=2, count=1, expect=dict(rejected=1, valid=0, generation=0))
    e(command=1, address=0, word=3)
    for count in (0, 2, 129, 255):
        e(command=2, count=count, expect=dict(rejected=1, valid=0, generation=0))
    e(command=2, count=1, idle_levels=4, idle_enabled=7,
      expect=dict(rejected=0, valid=1, generation=1))
    e(command=3, expected_generation=0, expect=dict(rejected=1, transfer=0))
    for tx, rx in ((33, 0), (0, 33), (63, 63)):
        e(command=3, expected_generation=1, tx_length=tx, rx_capacity=rx,
          expect=dict(rejected=1, transfer=0))
    e(command=3, expected_generation=1,
      expect=dict(rejected=0, mode=2, retained=1, transfer=1))
    for command in (1, 2, 3):
        e(command=command, expected_generation=1, count=1, word=4,
          expect=dict(rejected=1, mode=2, retained=1, generation=1, transfer=1))
    e(command=4, expected_generation=1, expected_transfer=2,
      expect=dict(rejected=1, retained=1))
    e(command=4, expected_generation=0, expected_transfer=1,
      expect=dict(rejected=1, retained=1))
    e(command=4, expected_generation=1, expected_transfer=1,
      expect=dict(rejected=0, retained=0, mode=0))
    finish('coverage-and-count-admission', vs, cs)

    shift = encode_instruction(BufferedInstruction('shift', append_input=0, shift_pin=0))
    for name, words, tx_len, rx_cap, expected in (
        ('underflow-before-rx', [shift, shift, 3], 1, 2, dict(tx_consumed=1, rx_length=1)),
        ('overflow-after-tx', [shift, shift, 3], 2, 1, dict(tx_consumed=2, rx_length=1)),
        ('zero-tx-underflow', [shift, 3], 0, 1, dict(tx_consumed=0, rx_length=0)),
        ('malformed-before-effects', [shift | (1 << 24), 3], 1, 1,
         dict(tx_consumed=0, rx_length=0)),
        ('malformed-retains-prefix', [shift, shift | (1 << 24), 3], 2, 2,
         dict(tx_consumed=1, rx_length=1)),
        ('terminal-canonical', [3 | (1 << 22)], 0, 1,
         dict(tx_consumed=0, rx_length=0)),
        ('unknown-kind', [5], 0, 0, dict(tx_consumed=0, rx_length=0)),
        ('explicit-fault', [4], 0, 0, dict(tx_consumed=0, rx_length=0)),
    ):
        e, load, vs, cs = case(name)
        load(words)
        e(command=3, expected_generation=1, tx_data=3, tx_length=tx_len, rx_capacity=rx_cap)
        for _ in range(len(words)+1): e()
        e(expect=dict(mode=3, retained=1, levels=4, enabled=7, **expected))
        for index in range(expected['rx_length']):
            e(read_index=index, expect=dict(read_valid=1, read_bit=1))
        e(command=4, expected_generation=1, expected_transfer=1,
          expect=dict(retained=0, tx_consumed=0, rx_length=0))
        finish(name, vs, cs)

    e, load, vs, cs = case('busy-and-warm-reset')
    load([encode_instruction(BufferedInstruction('shift', 256, shift_pin=0)), 3])
    e(command=3, expected_generation=1, tx_data=1, tx_length=1,
      expect=dict(mode=1, remaining=255, tx_consumed=1, transfer=1))
    for command in (1, 2, 3, 4):
        e(command=command, expected_generation=1, expected_transfer=1, count=2,
          expect=dict(rejected=1, busy=1, generation=1, transfer=1, tx_consumed=1))
    e(command=7, expect=dict(mode=0, retained=0, valid=0, generation=2,
                            transfer=1, tx_consumed=0, rx_length=0))
    load([3])
    e(command=3, expected_generation=1, expect=dict(rejected=1, transfer=1))
    e(command=3, expected_generation=3, expect=dict(mode=2, retained=1, transfer=2))
    e(command=4, expected_generation=1, expected_transfer=1,
      expect=dict(rejected=1, retained=1))
    e(command=4, expected_generation=3, expected_transfer=2,
      expect=dict(rejected=0, retained=0))
    finish('busy-and-warm-reset', vs, cs)

    e, load, vs, cs = case('dispatch-past-row127')
    load([encode_instruction(BufferedInstruction('drive'))] * 128)
    e(command=3, expected_generation=1, expect=dict(pc=0, busy=1))
    for _ in range(127): e()
    e(expect=dict(mode=3, retained=1, pc=0, tx_consumed=0, rx_length=0))
    finish('dispatch-past-row127', vs, cs)

    e, load, vs, cs = case('first-entry-uses-primed-low-sampler')
    e(raw=0, command=1, address=0,
      word=encode_instruction(BufferedInstruction('drive', append_input=0)))
    e(raw=0, command=1, address=1, word=3)
    e(raw=0, command=2, count=2, idle_levels=4, idle_enabled=7)
    e(raw=3, command=3, expected_generation=1, rx_capacity=1,
      expect=dict(mode=1, rx_length=1, rx_data=0))
    e(expect=dict(mode=2, rx_length=1, rx_data=0, retained=1))
    e(read_index=0, expect=dict(read_valid=1, read_bit=0))
    finish('first-entry-uses-primed-low-sampler', vs, cs)

    for history in range(64):
        e, load, vs, cs = case(f'sampler-history-{history}')
        sources = [0, 1, 0, 1, 0, 1]
        load([encode_instruction(BufferedInstruction('drive', append_input=source))
              for source in sources] + [3])
        raw = [(history >> (2*k)) & 3 for k in range(3)] + [0, 2, 1]
        sampled = [3, 3] + raw[:-2]
        expected_bits = [(pads >> source) & 1 for pads, source in zip(sampled, sources)]
        e(raw=raw[0], command=3, expected_generation=1, rx_capacity=6)
        for pads in raw[1:]: e(raw=pads)
        e(expect=dict(mode=2, rx_length=6, retained=1,
                      rx_data=sum(bit << k for k, bit in enumerate(expected_bits))))
        for index, bit in enumerate(expected_bits):
            e(read_index=index, expect=dict(read_valid=1, read_bit=bit))
        e(read_index=6, expect=dict(read_valid=0, read_bit=0))
        e(command=4, expected_generation=1, expected_transfer=1)
        finish(f'sampler-history-{history}', vs, cs)
    return dict(schema='pinwheel-buffered-hardware-input-v1', cases=cases)


def check_export(request, exported):
    require(type(exported) is dict and set(exported) == {'schema', 'cases'},
            'Wrong exported hardware vector envelope')
    require(exported.get('schema') == 'pinwheel-buffered-hardware-vectors-v1',
            'Wrong exported hardware vector schema')
    actual = exported.get('cases')
    require(type(actual) is list and len(actual) == len(request['cases']),
            'Truncated hardware command cases')
    edges = checks = 0
    for expected, case in zip(request['cases'], actual, strict=True):
        require(type(case) is dict and set(case) == {'name', 'vectors'} and
                type(case['name']) is str and type(case['vectors']) is list,
                'Wrong exported hardware case schema')
        require(case['name'] == expected['name'], 'Changed hardware command case identity')
        require(len(case['vectors']) == len(expected['vectors']), 'Truncated hardware command edges')
        for given, vector in zip(expected['vectors'], case['vectors'], strict=True):
            require(type(vector) is dict and set(vector) == {'command', 'raw_inputs', 'state'},
                    'Wrong exported hardware edge schema')
            command, raw, state = vector['command'], vector['raw_inputs'], vector['state']
            require(type(command) is dict and set(command) <= set(COMMAND_FIELDS) and
                    all(type(value) is int and 0 <= value < 2**COMMAND_FIELDS[key]
                        for key, value in command.items()),
                    'Wrong exported command field type or width')
            require(type(raw) is int and 0 <= raw < 4, 'Wrong exported raw input type or width')
            require(type(state) is dict and set(state) == set(STATE_WIDTHS) and
                    all(type(value) is int and 0 <= value < 2**STATE_WIDTHS[key]
                        for key, value in state.items()),
                    'Wrong exported public state field type or width')
            require(vector['command'] == given['command'] and
                    vector['raw_inputs'] == given['raw_inputs'], 'Changed hardware input transcript')
        for check in expected['checks']:
            state = case['vectors'][check['edge']]['state']
            require(all(state.get(key) == value for key, value in check['state'].items()),
                    f'Independent command expectation differs: {case["name"]}/{check}')
            checks += 1
        edges += len(case['vectors'])
    return dict(cases=len(actual), edges=edges, independent_state_checks=checks,
                raw_input_histories=64)


class ReferenceTransport:
    """Compare timed execution to the preexisting buffered reference on every edge."""
    def __init__(self, rtl):
        self.rtl, self.program = rtl, None
        self.engine = None
        self.compared_edges = self.starts = 0

    def edge(self, **command):
        actual = self.rtl.edge(**command)
        if command.get('initialize') or command.get('command') == 7:
            self.engine = None
        elif command.get('command') == 3 and not actual.rejected:
            require(self.program is not None, 'Reference requires the selected canonical source')
            length = command['tx_length']
            bits = tuple(bool(command['tx_data'] & (1 << k)) for k in range(length))
            slot = TransferSlot(tx_capacity_bits=32, rx_capacity_bits=32)
            identity = slot.begin(self.program.key, bits, command['rx_capacity'])
            self.engine = BufferedEngine(slot, identity, self.program)
            # SPI starts with SHIFT, which has no input capture. Hardware sampler
            # registers have advanced throughout upload and must be bound here.
            require(self.program.instructions[0].append_input is None,
                    'Start sampler binding requires a first instruction without RX')
            self.engine._first, self.engine._second = actual.stage1, actual.stage2
            self.starts += 1
        elif self.engine is not None and not self.engine.done:
            self.engine.step(actual.stage1)
        if self.engine is not None and command.get('command') != 4:
            model = self.engine
            mode = 2 if model.mode == 'completed' else 3 if model.done else 1
            expected = dict(mode=mode, pc=model.pc, remaining=model.remaining,
                levels=model.levels, enabled=model.enabled,
                tx_consumed=model.slot._tx_consumed, rx_length=len(model.slot._rx),
                rx_data=sum(int(bit) << k for k, bit in enumerate(model.slot._rx)))
            require(all(getattr(actual, key) == value for key, value in expected.items()),
                    'Emitted execution differs from the buffered reference: ' + repr(expected))
            if not model.done:
                require((actual.stage1, actual.stage2) == (model._first, model._second),
                        'Emitted sampler age differs from the buffered reference')
            self.compared_edges += 1
        if command.get('command') == 4 and not actual.rejected:
            self.engine = None
        return actual


def wire_cases(full):
    cases = []
    values = range(256) if full else (0, 1, 0x96, 255)
    for lane in range(4):
        for value in values:
            tx = bytearray(b'\x96\xa5\x3c\xc3')
            rx = bytearray(b'\xa6\x9b\x42\xe1')
            tx[lane], rx[lane] = value, value ^ 255
            cases.append((bytes(tx), bytes(rx)))
    return cases


def wire_gate(executable, full=False):
    results = []
    with BufferedRTL(CAD / 'vvp', executable) as rtl:
        reference = ReferenceTransport(rtl)
        host = BufferedHardwareHost(reference)
        host.initialize()
        loaded, configuration, uploads, images = None, None, 0, []
        fixtures = [(4, 4, 1, tx, rx) for tx, rx in wire_cases(full)]
        fixtures += [(n, half, tco, b'\x96\xa5\x3c\xc3'[:n], b'\xa6\x9b\x42\xe1'[:n])
                     for n, half, tco in ((1, 3, 0), (2, 7, 1), (4, 256, 1))]
        for n, half, tco, tx, rx in fixtures:
            if configuration != (n, half):
                reference.program = buffered_spi(n, half)
                loaded = host.load(reference.program)
                uploads += len(loaded.image.words)
                images.append(dict(bytes=n, half_cycles=half, image_key=loaded.image.key,
                                   words=len(loaded.image.words)))
                configuration = n, half
            peer = BufferedSPIPeer(tx, rx, half, tco)
            rtl.device = peer
            pending = loaded.submit(tx=tx)
            try:
                pending.wait(timeout_cycles=0)
            except BufferedHardwareWaitTimeout as error:
                require(error.pending is pending, 'Host wait timeout lost its hardware owner')
            else:
                raise RuntimeError('Zero host wait budget unexpectedly completed a four-byte transfer')
            pending.wait(timeout_cycles=(16*n+1)*half+2)
            first = pending.read()
            require(first.payload == rx and first.outcome == 'complete',
                    'Indexed hardware RX differs from the independent reply')
            require(first == pending.read(), 'Nondestructive indexed hardware result changed')
            require(rtl.snapshot.retained == 1, 'Indexed read released hardware ownership')
            peer_result = peer.check(first.raw_rx_bits)
            before = host.edges
            try:
                loaded.submit(tx=tx)
            except TransferError:
                pass
            else:
                raise RuntimeError('Public host overwrote a retained hardware result')
            require(host.edges == before, 'Owned host rejection sent a hardware edge')
            pending.release()
            rtl.device = None
            require(rtl.snapshot.retained == 0, 'Matching hardware release failed')
            results.append(peer_result)
        require(sum(record['command']['command'] == 1 for record in rtl.records) == uploads,
                'Repeated data transfers uploaded their program again')
        return dict(cases=len(results), starts=reference.starts,
            reference_edges=reference.compared_edges, circuit_edges=rtl.cycle,
            uploaded_program_words=uploads, program_images=images,
            indexed_reads_retained_twice=True,
            host_wait_timeout_recovered=True, cases_sha256=hashlib.sha256(
                json.dumps(results, sort_keys=True).encode()).hexdigest())


def replay_gate(executable, exported):
    edges = 0
    for case in exported['cases']:
        with BufferedRTL(CAD / 'vvp', executable) as rtl:
            edges += replay_vectors(rtl, case['vectors'])['edges']
    return dict(cases=len(exported['cases']), edges=edges, public_state_fields=20)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--tag', required=True)
    parser.add_argument('--pdk-root', type=Path)
    args = parser.parse_args()
    out = fresh_directory(ROOT / 'build/buffered-hardware', args.tag)
    run = Commands(ROOT, out, default_timeout=1800)
    started = time.monotonic()
    report = dict(schema='pinwheel-buffered-hardware-results-v1', target=TARGET,
                  status='running', commands=run.records)
    try:
        pdk = stage_pdk(pdk_root=args.pdk_root)
        sources = [ROOT / name for name in ('Pinwheel.lean', 'lean-toolchain',
                    'lakefile.toml', 'lake-manifest.json', 'tools/technology-library.json',
                    'tools/hardware-toolchain.json', 'test/buffered_hardware_tb.sv')]
        sources += sorted((ROOT / 'Pinwheel').rglob('*.lean'))
        sources += sorted((ROOT / 'test').glob('*.lean')) + sorted((ROOT / 'test').glob('test_*.py'))
        sources += sorted((ROOT / 'scripts').glob('*.py'))
        sources += [CIRCT, *[CAD / name for name in ('yosys', 'yosys-abc', 'iverilog', 'vvp')],
                    *[CAD.parent / 'libexec' / name for name in
                      ('yosys', 'yosys-abc', 'iverilog', 'vvp', 'ivl', 'ivlpp', 'realpath')],
                    Path(pdk['library']), *map(Path, pdk['models']),
                    ROOT / 'build/tools/oss-cad-suite/share/yosys/simcells.v']
        source_hashes = {str(path.relative_to(ROOT)): sha(path) for path in sources}
        report['source_sha256'] = source_hashes
        version = run(['lake', 'env', 'lean', '--version'], 'lean-version').strip()
        expected = (ROOT / 'lean-toolchain').read_text().strip().split(':v')[-1]
        require(bool(re.search(r'Lean \(version ' + re.escape(expected) + r'(?:,|\s)', version)),
                'Lean version differs from its repository pin')
        report['lean'] = version
        report['tools'] = {
            'circt': run([CIRCT, '--version'], 'circt-version').strip(),
            'yosys': run([CAD / 'yosys', '-V'], 'yosys-version').strip(),
            'iverilog': run([CAD / 'iverilog', '-V'], 'iverilog-version').strip(),
        }
        run(['lake', 'build'], 'build')
        audit = run(['lake', 'env', 'lean', '-DwarningAsError=true', 'test/ProofAudit.lean'], 'axioms')
        counts = re.search(r'Pinwheel audit: (\d+) declarations, (\d+) theorems;', audit)
        require(counts is not None, 'Missing whole-library axiom audit')
        report['audit'] = dict(declarations=int(counts[1]), theorems=int(counts[2]))
        audit_text = (ROOT / 'test/ProofAudit.lean').read_text().removesuffix('#audit_pinwheel\n')
        mutant = out / 'RejectAxiom.lean'
        mutant.write_text(audit_text + 'axiom Pinwheel.CI.untrusted : False\n#audit_pinwheel\n')
        run(['lake', 'env', 'lean', mutant], 'axiom-negative',
            reject='Unapproved axioms in Pinwheel.CI.untrusted')
        lean = ['lake', 'env', 'lean', '-DwarningAsError=true', '--run']
        run([*lean, 'test/BufferedHardware.lean'], 'lean-hardware')
        run([*lean, 'test/Buffered.lean'], 'lean-reference')
        request = command_cases()
        (out / 'input.json').write_text(json.dumps(request, indent=2) + '\n')
        run([*lean, 'test/BufferedHardwareExport.lean', out / 'input.json', out], 'emit-vectors')
        exported = json.loads((out / 'vectors.json').read_text())
        report['command_expectations'] = check_export(request, exported)
        assembly = json.loads((out / 'assembly.json').read_text())
        report['declared_register_bits'] = sum(slot['width'] for slot in assembly['registers'])
        sv = run([CIRCT, out / 'core.mlir', '--canonicalize', '--lower-seq-to-sv',
                  '--lower-hw-to-sv', '--hw-legalize-modules', '--export-verilog',
                  '-o', '/dev/null'], 'circt-export')
        (out / 'core.sv').write_text(sv)
        executable = compile_rtl(run, out, out / 'core.sv', 'emitted')
        report['emitted_control'] = replay_gate(executable, exported)
        report['emitted_spi'] = wire_gate(executable, full=True)
        changed = sv.replace('r_stage2[0]', 'r_stage1[0]').replace('r_stage2[1]', 'r_stage1[1]')
        require(changed != sv, 'Missing emitted RX sampler negative-control anchor')
        (out / 'capture-negative.sv').write_text(changed)
        negative = compile_rtl(run, out, out / 'capture-negative.sv', 'capture-negative')
        try:
            replay_gate(negative, exported)
        except RuntimeError as error:
            require('Buffered RTL public state mismatch' in str(error),
                    'Capture negative failed outside its represented execution state')
        else:
            raise RuntimeError('One-stage RX capture mutant was accepted')
        report['capture_negative_rejected'] = True
        report['synthesis'] = synthesize(run, out, out / 'core.sv', pdk_root=args.pdk_root)
        for variant, artifact in report['synthesis']['variants'].items():
            gate = Path(artifact['executable'])
            artifact['control_replay'] = replay_gate(gate, exported)
            artifact['spi_replay'] = wire_gate(gate)
        report['python'] = {}
        for label, optimization in (('python', []), ('python-optimized', ['-O'])):
            output = run([sys.executable, *optimization, '-B', '-m', 'unittest', 'discover',
                          '-s', 'test', '-p', 'test_*.py'], label)
            totals = re.search(r'Ran (\d+) tests', output)
            require(totals is not None, 'Missing Python regression count')
            skips = re.search(r'skipped=(\d+)', output)
            report['python'][label] = dict(total=int(totals[1]),
                skipped=int(skips[1]) if skips else 0)
        preservation = json.loads((ROOT / 'build/buffered-hardware/baseline-preservation.json').read_text())
        for name, digest in preservation['prior_sha256'].items():
            require(sha(ROOT / name) == digest, 'Prior hardware/physical artifact changed: ' + name)
        report['preservation'] = dict(base=preservation['base'],
            previous_files=len(preservation['prior_sha256']), unchanged=True,
            baseline_map_sha256=sha(ROOT / 'build/buffered-hardware/baseline-preservation.json'))
        for name, digest in source_hashes.items():
            require(sha(ROOT / name) == digest, 'Source changed during hardware validation: ' + name)
        report.update(status='passed', inputs_unchanged=True,
            elapsed_seconds=round(time.monotonic()-started, 3),
            boundary='Opt-in reloadable linear parallel hardware target, finite directed Lean/RTL '
                     'and reference SPI traces, saved generic/typical CMOS5L state-cut equivalence '
                     'and indexed result ownership. No counted/reactive hardware, paired SRAM, '
                     'serial package, reset reconnection, physical pads, routing or timing qualification.')
        report['artifact_sha256'] = {str(path.relative_to(out)): sha(path)
            for path in out.rglob('*') if path.is_file() and path.name != 'report.json'}
    except BaseException as error:
        report.update(status='failed', error=str(error))
        raise
    finally:
        (out / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    print('Buffered hardware gate passed: ' + str(out / 'report.json'), flush=True)


if __name__ == '__main__':
    main()
