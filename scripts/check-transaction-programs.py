#!/usr/bin/env python3
"""Exercise the public transaction workflow on one actual paired-stream package."""
import argparse
from dataclasses import asdict, replace
import json
from pathlib import Path

from i2c_read_peers import I2CReadPeer
from jtag_peers import JTAGPeer, TAP
from pad_peers import SPIPeer, require
from pinwheel_transactions import (CapabilityError, compile_transaction, uart_tx,
    spi_transfer, i2c_register_read, jtag_scan)
from resident_peers import ResidentUARTPeer, ResidentSPIPeer
from transaction_package import paired_package
from validation_run import sha

ROOT = Path(__file__).resolve().parents[1]


def record(runtime, case):
    with (runtime.out/'case-progress.jsonl').open('a') as stream:
        stream.write(json.dumps(case) + '\n')
    return case


def transfer(runtime, loaded, peer, *, payload=0, expected=(), outcome='success', wire_options=None):
    runtime.simulation.device = peer
    frames = runtime.host.frames
    result = loaded.run(payload=payload)
    require((result.outcome, result.payload, result.overrun, result.rejected) ==
            (outcome, expected, False, False), 'Public decoded result differs from independent reply')
    wire = peer.check(**(wire_options or {}))
    require(runtime.host.frames - frames == 1, 'Transfer issued a command beyond one START')
    runtime.simulation.device = None
    return dict(result=asdict(result), wire=wire, serial_command_frames=1)


def resident_cases(runtime):
    cases = []
    definitions = [('uart', uart_tx()), ('spi', spi_transfer()), ('jtag', jtag_scan())]
    states = tuple(TAP)
    for name, spec in definitions:
        transaction = runtime.compile(spec, name)
        loaded = transaction.load(runtime.host)
        upload_frames = runtime.host.frames
        for payload in range(256):
            reply = (payload * 73 + 0x96) & 255
            if name == 'uart':
                peer, expected, options = ResidentUARTPeer(payload), (), None
            elif name == 'spi':
                peer, expected, options = ResidentSPIPeer(payload, reply), (reply,), None
            else:
                peer = JTAGPeer(payload, reply, initial_state=states[payload % len(states)])
                expected, options = (reply,), dict(samples=reply)
            result = transfer(runtime, loaded, peer, payload=payload, expected=expected, wire_options=options)
            cases.append(record(runtime, dict(name=name, payload=payload, **result)))
        require(runtime.host.frames - upload_frames == 256, 'Resident image was replaced between payloads')
    return cases


def fixed_cases(runtime):
    cases = []
    for mode in range(4):
        for count in (1, 2):
            sent, reply = (0xa6, 0x53)[:count], (0x96, 0x3c)[:count]
            name = f'spi-mode{mode}-{count}byte'
            transaction = runtime.compile(spi_transfer(sent, mode=mode), name)
            loaded = transaction.load(runtime.host)
            peer = SPIPeer(mode, sent, reply, 4, 1)
            result = transfer(runtime, loaded, peer, expected=reply)
            cases.append(record(runtime, dict(name=name, **result)))
    for count in (1, 2):
        reply = (0x96, 0x3c)[:count]
        transaction = runtime.compile(i2c_register_read(0x50, 0x17, byte_count=count), f'i2c-{count}byte')
        loaded = transaction.load(runtime.host)
        scenarios = [(None, 0, False, False), (None, 3, False, False),
                     *((stage, 0, False, False) for stage in range(3)),
                     (None, 0, True, False), (None, 0, False, True)]
        for nack, stretch, stuck, fault in scenarios:
            ack = tuple(int(n == nack) for n in range(3))
            peer = I2CReadPeer(0x50, 0x17, reply, ack, stretch_cycles=stretch,
                              scl_stuck=stuck, fault_after_rises=30 if fault else None)
            outcome = 'timeout' if stuck else 'nack_or_bus_fault' if nack is not None or fault else 'success'
            result = transfer(runtime, loaded, peer,
                expected=reply if outcome == 'success' else None, outcome=outcome,
                wire_options=dict(timeout=stuck, fault=fault))
            require(runtime.simulation.pins.enabled == 0, 'I2C terminal outputs remained driven')
            cases.append(record(runtime, dict(name=f'i2c-{count}byte', nack_stage=nack,
                stretch_cycles=stretch, stuck_clock=stuck, guard_fault=fault, **result)))
    return cases


def before_io_controls(runtime):
    host = runtime.host
    controls = []
    for name, factory in [('32-bit-jtag-operand', lambda: jtag_scan(outgoing_bits=32)),
                          ('32-bit-jtag-result', lambda: jtag_scan(captured_bits=32)),
                          ('four-byte-i2c-result', lambda: i2c_register_read(0x50, 0x17, byte_count=4))]:
        before = (host.edges, host.frames)
        try:
            factory()
        except CapabilityError as error:
            controls.append(dict(name=name, rejected_before_io=True, reason=str(error)))
        else:
            raise RuntimeError('Unsupported capacity was accepted')
        require((host.edges, host.frames) == before, 'Capacity rejection touched chip pins')
    transaction = runtime.compile(jtag_scan(), 'ownership-jtag')
    loaded = transaction.load(host)
    before = (host.edges, host.frames)
    try:
        loaded.run(payload=256)
    except ValueError as error:
        controls.append(dict(name='invalid-start-payload', rejected_before_io=True, reason=str(error)))
    else:
        raise RuntimeError('Invalid START payload was accepted')
    require((host.edges, host.frames) == before, 'Invalid START payload touched chip pins')
    fixed = runtime.compile(spi_transfer((0xa6,)), 'ownership-fixed-spi').load(host)
    before = (host.edges, host.frames)
    try:
        fixed.run(payload=1)
    except CapabilityError as error:
        controls.append(dict(name='nonzero-fixed-payload', rejected_before_io=True, reason=str(error)))
    else:
        raise RuntimeError('Fixed transaction accepted a dynamic payload')
    require((host.edges, host.frames) == before, 'Fixed-payload rejection touched chip pins')
    replacement_uart = runtime.compile(uart_tx(), 'ownership-uart')
    for replacement in ('identical-reload', 'different-reload', 'reset'):
        loaded = transaction.load(host)
        if replacement == 'identical-reload':
            transaction.load(host)
        elif replacement == 'different-reload':
            replacement_uart.load(host)
        else:
            host.reset()
        before = (host.edges, host.frames)
        try:
            loaded.run(payload=0x53)
        except RuntimeError as error:
            require('lost its committed program' in str(error), 'Unexpected stale-session rejection')
            controls.append(dict(name=replacement, rejected_before_io=True, reason=str(error)))
        else:
            raise RuntimeError('Stale transaction session executed')
        require((host.edges, host.frames) == before, 'Stale session touched chip pins')
    return controls


def semantic_controls(runtime):
    original = compile_transaction(jtag_scan())
    source = original.program
    words = list(source.words)
    wrong_order = tuple(word ^ (1 << 31) if word & 7 == 5 else word for word in words)
    # Five reset pulses must carry TMS=1; mutate every copy of the first low record.
    wrong_reset = tuple(word ^ (1 << 5) if word == words[0] else word for word in words)
    # First KEEP's slot zero is redirected to slot eight; canonical grammar stays valid.
    first_keep = next(word for word in words if word & 7 == 6)
    wrong_capture = tuple(word | (8 << 31) if word == first_keep else word for word in words)
    controls = []
    for name, changed in [('jtag-wrong-bit-order', wrong_order), ('jtag-wrong-reset-tms', wrong_reset),
                          ('jtag-wrong-capture-slot', wrong_capture)]:
        program = replace(source, words=changed)
        runtime.evidence.certify(name, program, runtime.run)
        program.write(runtime.out/(name+'.json'))
        runtime.evidence.freeze_generated(runtime.out/(name+'.json'))
        runtime.simulation.device = None
        runtime.host.reset()
        # This deliberate mutant bypasses artifact rebinding to exercise the wire/result oracles.
        loaded = replace(original, program=program).load(runtime.host)
        peer = JTAGPeer(0x53, 0xa5)
        runtime.simulation.device = peer
        try:
            loaded.run(payload=0x53)
            peer.check()
        except (ValueError, RuntimeError) as error:
            reason = str(error)
            require('JTAG' in reason or 'outside its declared result layout' in reason,
                    'Canonical mutant failed for an unrelated reason')
        else:
            raise RuntimeError('Canonical JTAG mutation escaped its independent oracle')
        if name.endswith('capture-slot'):
            raw = runtime.host.read_result(timeout_cycles=0, consume=False)
            require(raw.samples & 256 and raw.outcome == 5, 'Capture mutant did not reach expected complete packet')
            require(raw == runtime.host.read_result(timeout_cycles=0, consume=False), 'Decode failure lost mailbox')
            peer.check()
            runtime.host.consume()
        runtime.simulation.device = None
        controls.append(record(runtime, dict(name=name, canonical_certificate_passed=True,
            rejected_by='independent package wire or declared capture layout', reason=reason,
            unread_packet_preserved=name.endswith('capture-slot'))))
    runtime.host.reset()
    return controls


def run_gate(tag):
    with paired_package(tag) as runtime:
        baseline = runtime.evidence.capture(ROOT/'physical/experiments/reusable-protocol-results.json',
                                            'baseline-results.json')
        prior = json.loads(baseline)['artifact_identity']
        runtime.host.reset()
        residents = resident_cases(runtime)
        fixed = fixed_cases(runtime)
        controls = before_io_controls(runtime) + semantic_controls(runtime)
        counts = dict(uart_payloads=256, spi_payloads=256, jtag_payloads=256,
            initial_jtag_tap_states=16, fixed_spi_cases=8, i2c_cases=14)
        edges, frames = runtime.host.edges, runtime.host.frames
        identical = (sha(runtime.out/'chip.mlir') == prior['stream_mlir'] and
                     sha(runtime.out/'design.sv') == prior['stream_rtl'])
        require(identical, 'Transaction workflow changed the previously accepted chip artifact')
    report = dict(runtime.receipt, action='unified-transaction-demo', accepted=True,
        **counts, edges=edges, frames=frames, resident_cases=residents, fixed_cases=fixed,
        controls=controls, existing_chip_bytes_identical=identical,
        boundary='One unchanged paired-stream RTL package with supervisor disabled. Public compile/load/run/decode '
            'API and independent resolved-pad peers. JTAG is an eight-bit DR selected by reset, with no IR/chain '
            'or IDCODE claim. No board frequency, analog sampling or physical qualification claim.')
    (runtime.out/'report.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(dict(**counts, edges=edges, frames=frames, existing_chip_bytes_identical=identical), indent=2))
    print(runtime.out/'report.json')
    return report


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--tag', required=True)
    run_gate(parser.parse_args().tag)
