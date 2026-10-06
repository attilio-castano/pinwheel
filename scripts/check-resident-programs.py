#!/usr/bin/env python3
"""Kernel-certified resident UART/SPI programs on one unchanged RTL package.

UART sends all 256 START payloads without a code upload between transfers.
SPI does the same with delayed replies and deliberately wrong off-edge inputs.
Independent resolved-wire peers own waveform expectations; this gate imports
no execution model to derive the expected pin traces or captured replies.
"""
import argparse
from dataclasses import asdict, replace
import json
from pathlib import Path
import re
import time

from capability_receipt import CapabilityEvidence
from pad_io import PAD_MAP
from pad_peers import require, spi_result_bytes
from pinwheel_host import Command, Host, PAIRED_FORMAT
from pinwheel_program import resident_spi, resident_uart, resource_report
from pinwheel_sim import Simulation
from protocol_tool_closure import ProtocolToolClosure
from resident_peers import ResidentSPIPeer, ResidentUARTPeer
from validation_run import Commands, fresh_directory, sha

ROOT = Path(__file__).resolve().parents[1]


class ResidentCommands(Commands):
    """Retain command identities even when a later probe fails."""
    def __call__(self, *args, **kwargs):
        try:
            return super().__call__(*args, **kwargs)
        finally:
            (self.out/'commands.json').write_text(json.dumps(self.records, indent=2) + '\n')


def save_program(evidence, run, name, program):
    """Certify once, then reuse exactly these captured program bytes."""
    evidence.certify(name, program, run)
    path = evidence.out / (name + '.json')
    require(not path.exists(), 'Preserve existing resident program snapshot')
    program.write(path)
    evidence.freeze_generated(path)
    return dict(name=name, snapshot=path.name, sha256=sha(path), **resource_report(program))


def finish_peer(simulation, host, peer, *, limit=4000):
    """Keep the externally visible busy page stable through completion."""
    host.page(0)
    end = simulation.cycle + limit
    while peer.finished_at is None if isinstance(peer, ResidentUARTPeer) else not peer.finished:
        require(simulation.cycle < end, 'Resident program exceeded independent peer horizon')
        host.advance()
    require(not simulation.pins.status & 1, 'Resident waveform ended before package execution completed')
    return peer.check()


def retained_result(host, expected, *, rejected=False, overrun=False, consume=True):
    result = host.read_result(timeout_cycles=16, consume=False)
    require((result.samples, result.outcome, result.rejected, result.overrun) ==
            (expected, 5, rejected, overrun), 'Resident raw result/ownership differs from independent expectation')
    require(result == host.read_result(timeout_cycles=0, consume=False), 'Resident unread result changed')
    if consume:
        host.consume()
        require(not host.result_status() & 1, 'Resident result consumption failed')
    return asdict(result)


def one_uart(simulation, host, payload, period=4):
    peer = ResidentUARTPeer(payload, period)
    simulation.device = peer
    before = host.frames
    host.start(payload=payload)
    wire = finish_peer(simulation, host, peer)
    result = retained_result(host, 0)
    require(host.frames - before == 1, 'Resident UART repeated transfer reuploaded code')
    simulation.device = None
    return dict(payload=payload, wire=wire, result=result, retained_twice=True,
                serial_command_frames=1)


def one_spi(simulation, host, payload, reply, *, consume=True):
    peer = ResidentSPIPeer(payload, reply, 4, 1)
    simulation.device = peer
    before = host.frames
    host.start(payload=payload)
    wire = finish_peer(simulation, host, peer)
    expected = sum(((reply >> (7 - bit)) & 1) << bit for bit in range(8))
    result = retained_result(host, expected, consume=consume)
    require(spi_result_bytes(result['samples'], 1) == (reply,), 'Resident SPI reply/wire-order decode')
    require(host.frames - before == 1, 'Resident SPI repeated transfer reuploaded code')
    simulation.device = None
    return dict(payload=payload, reply=reply, wire=wire, result=result,
                retained_twice=True, serial_command_frames=1)


def spi_ownership_control(simulation, host):
    first = one_spi(simulation, host, 0xa6, 0x96, consume=False)
    frames = host.frames
    try:
        host.start(payload=0x53)
    except RuntimeError as error:
        require('Consume the previous result' in str(error), 'Resident unread API rejection reason')
    else:
        raise RuntimeError('Resident public API overwrote an unread result')
    require(host.frames == frames, 'Rejected resident API start sent a serial frame')
    peer = ResidentSPIPeer(0x53, 0x3c, 4, 1)
    simulation.device = peer
    host.command(Command.START, 0x53)
    wire = finish_peer(simulation, host, peer)
    expected = first['result']['samples']
    result = retained_result(host, expected, overrun=True)
    host.clear_flags()
    require(not host.result_status() & 6, 'Resident overrun failed to clear after consumption')
    simulation.device = None
    return dict(name='unread-result-ownership', api_start_refused_before_command=True,
                raw_second_start_completed=True, old_samples_retained=expected,
                result=result, wire=wire, sticky_overrun_observed=True)


def send_partial_start(host, payload, bits):
    if type(bits) is not int or not 0 <= bits < 72:
        raise ValueError('Partial START must contain fewer than 72 bits')
    frame = (int(Command.START) << 64) | payload
    host.ui &= ~7
    if bits == 0:
        host.advance(host.phase_cycles)
    for shift in range(71, 71 - bits, -1):
        host.ui = (host.ui & ~7) | (((frame >> shift) & 1) << 1)
        host.advance(host.phase_cycles)
        host.ui |= 1
        host.advance(host.phase_cycles)
    host.ui = (host.ui & ~7) | 4
    host.advance(4)


def serial_controls(simulation, host, uart):
    simulation.device = None
    host.upload(uart)
    require(host.page(0) & 3 == 2, 'Resident UART did not become ready')
    host.advance(80)
    require(host.page(0) & 1 == 0 and host.result_status() & 1 == 0,
            'Resident program began without an accepted START')
    controls = [dict(name='absent-start', idle_edges=80, no_execution_or_result=True)]
    for bits in (0, 7, 8, 64, 71):
        send_partial_start(host, 0x53, bits)
        require(host.page(0) & 3 == 2 and host.result_status() & 1 == 0,
                'Truncated START executed or damaged the committed program')
        recovered = one_uart(simulation, host, 0xa6)
        controls.append(dict(name='truncated-start', delivered_bits=bits,
            no_execution_or_result=True, recovery=recovered))
    host.command(Command.BEGIN)
    host.command(Command.PUSH, 1 << 63)
    require(host.result_status() & 4 and host.page(0) & 7 == 6,
            'Malformed upload failed to reject the push/preserve active and staged ownership')
    # The paired loader retains its staging cursor on a rejected push. The
    # ordinary Host.upload path sends ABORT; reproduce that explicit policy.
    host.command(Command.ABORT)
    require(host.page(0) & 7 == 2, 'Resident malformed-upload ABORT failed to preserve committed image')
    recovered = one_uart(simulation, host, 0x53)
    controls.append(dict(name='malformed-upload', rejected_reserved_parameter=True,
                         explicit_staging_abort=True, old_program_preserved=True, recovery=recovered))
    return controls


def busy_start_control(simulation, host, slow_uart):
    simulation.device = None
    host.upload(slow_uart)
    peer = ResidentUARTPeer(0xa6, 64)
    simulation.device = peer
    host.start(payload=0xa6)
    host.page(0)
    require(simulation.pins.status & 1, 'Resident busy-start control did not find active UART')
    before = simulation.cycle
    host.command(Command.START, 0x53)
    require(simulation.cycle - before == 292, 'Resident busy START framing budget changed')
    wire = finish_peer(simulation, host, peer)
    result = retained_result(host, 0, rejected=True)
    simulation.device = None
    host.clear_flags()
    return dict(name='busy-start-payload-snapshot', initial_payload=0xa6, rejected_payload=0x53,
                busy_command_edges=292, execution_owned_payload_preserved=True,
                wire=wire, result=result)


def reset_controls(simulation, host, slow_uart):
    controls = []
    for symbol in range(10):
        simulation.device = None
        host.reset()
        host.upload(slow_uart)
        peer = ResidentUARTPeer(0xa6, 64)
        simulation.device = peer
        host.start(payload=0xa6)
        target = peer.started_at + symbol * 64 + 32
        require(simulation.cycle < target, 'Resident reset control missed its symbol midpoint')
        host.advance(target - simulation.cycle)
        require(peer.finished_at is None, 'Resident reset control unexpectedly completed')
        simulation.device = None  # The interrupted frame is deliberately incomplete.
        host.reset()
        require(host.page(0) & 7 == 0 and host.result_status() & 7 == 0,
                'Resident external reset retained execution/image/result ownership')
        require(simulation.pins.enabled == 0, 'Resident reset left a protocol driver enabled')
        controls.append(dict(name='reset-during-symbol', symbol=symbol,
            observed_frame_edges=target - peer.started_at, frame_aborted=True,
            committed_image_invalidated=True, mailbox_flushed=True, outputs_released=True))
    return controls


def semantic_negative_controls(simulation, host, evidence, run, uart, spi):
    negatives = []
    # Toggle the source SHIFT bit-order selector (entry bit 2), retaining a
    # canonical resident program whose upload certificate is expected to pass.
    wrong_uart = replace(uart, words=tuple(word ^ (1 << 31) if word & 7 == 5 else word
                                          for word in uart.words))
    save_program(evidence, run, 'resident-uart-wrong-bit-order', wrong_uart)
    simulation.device = None
    host.upload(wrong_uart)
    simulation.device = ResidentUARTPeer(0x53, 4)
    try:
        host.start(payload=0x53)
        finish_peer(simulation, host, simulation.device)
    except RuntimeError as error:
        require('Resident UART pin waveform' in str(error), 'Resident UART mutation failed for another reason')
        reason = str(error)
    else:
        raise RuntimeError('Resident UART canonical bit-order mutation escaped the independent peer')
    simulation.device = None
    host.advance(100)
    retained_result(host, 0)
    negatives.append(dict(name='uart-wrong-bit-order', canonical_certificate_passed=True,
                         refused_by='independent resolved TX waveform', reason=reason))

    # Redirect every KEEP capture to slot zero while retaining its input
    # selector, capture enable and pin-preservation mask.
    wrong_spi = replace(spi, words=tuple(word & ~(15 << 31) if word & 7 == 6 else word
                                        for word in spi.words))
    save_program(evidence, run, 'resident-spi-wrong-capture-slots', wrong_spi)
    host.upload(wrong_spi)
    peer = ResidentSPIPeer(0xa6, 0x96, 4, 1)
    simulation.device = peer
    host.start(payload=0xa6)
    wire = finish_peer(simulation, host, peer)
    packet = host.read_result(timeout_cycles=16, consume=False)
    require(packet.outcome == 5 and packet.samples != 0x69,
            'Resident SPI capture mutation escaped the independent raw-result oracle')
    require(packet == host.read_result(timeout_cycles=0, consume=False), 'Resident mutation unread result changed')
    host.consume()
    simulation.device = None
    negatives.append(dict(name='spi-wrong-capture-slots', canonical_certificate_passed=True,
        refused_by='independent reply/wire-order expectation', intended_samples=0x69,
        observed=asdict(packet), wire=wire))
    return negatives


def demonstrate(simulation, evidence, run):
    host = Host(simulation, image_format=PAIRED_FORMAT)
    host.reset()
    uart, spi, slow_uart = resident_uart(), resident_spi(), resident_uart(64)
    programs = [save_program(evidence, run, name, program) for name, program in
        [('resident-uart', uart), ('resident-spi', spi), ('resident-uart-controls', slow_uart)]]
    def progress(name, detail):
        with (evidence.out/'case-progress.jsonl').open('a') as output:
            output.write(json.dumps(dict(case=name, detail=detail)) + '\n')

    host.upload(uart)
    uart_cases = []
    for payload in range(256):
        case = one_uart(simulation, host, payload)
        uart_cases.append(case)
        progress('resident-uart', case)
    host.upload(spi)
    spi_cases = []
    for payload in range(256):
        case = one_spi(simulation, host, payload, payload ^ 255)
        spi_cases.append(case)
        progress('resident-spi', case)
    controls = [spi_ownership_control(simulation, host)]
    progress('unread-result-ownership', controls[-1])
    controls += serial_controls(simulation, host, uart)
    progress('serial-controls', controls[1:])
    controls.append(busy_start_control(simulation, host, slow_uart))
    progress('busy-start-control', controls[-1])
    controls += reset_controls(simulation, host, slow_uart)
    progress('reset-controls', controls[-10:])
    negatives = semantic_negative_controls(simulation, host, evidence, run, uart, spi)
    progress('semantic-negative-controls', negatives)
    return dict(programs=programs, uart=uart_cases, spi=spi_cases,
                controls=controls, semantic_negative_controls=negatives,
                uart_payloads=256, spi_payloads=256, uart_edges_per_transfer=40,
                spi_edges_per_transfer=68, edges=host.edges, frames=host.frames,
                resident_repeat_command_frames=1, pad_map=PAD_MAP)


def execute_gate(out, backend):
    emitter = 'test/PairedStreamEmit.lean' if backend == 'paired-stream' else 'test/PairedChipEmit.lean'
    sources = [ROOT/'Pinwheel.lean', *sorted((ROOT/'Pinwheel').rglob('*.lean')),
        *[ROOT/name for name in ('lakefile.toml', 'lake-manifest.json', 'lean-toolchain', emitter,
            'test/host_bridge.sv', 'test/paired_chip.sv', 'tools/hardware-toolchain.json',
            'tools/storage-macros.json')],
        *[ROOT/'scripts'/name for name in ('check-resident-programs.py', 'resident_peers.py',
            'pinwheel_program.py', 'pinwheel_host.py', 'pinwheel_sim.py', 'pad_io.py',
            'pad_peers.py', 'paired_execution.py', 'execution-vectors.py',
            'capability_receipt.py', 'resident_image_certificate.py', 'paired_image_certificate.py',
            'protocol_tool_closure.py', 'validation_run.py', 'process_group.py')]]
    cad = ROOT/'build/tools/oss-cad-suite/bin'
    circt = ROOT/'build/tools/firtool-1.159.0/bin/circt-opt'
    closure = ProtocolToolClosure(ROOT, circt, cad/'iverilog', cad/'vvp')
    models = [ROOT/'build/storage/macros'/name for name in
        ('RM_IHPSG13_1P_512x64_c2_bm_bist.v', 'RM_IHPSG13_1P_core_behavioral_bm_bist.v')]
    locked = json.loads((ROOT/'tools/storage-macros.json').read_text())['files_sha256']
    require(all(sha(path) == locked['verilog/' + path.name] for path in models), 'Resident unpinned SRAM models')
    evidence = CapabilityEvidence(ROOT, out, sources, closure.files, models)
    (out/'attempt-inputs.json').write_text(json.dumps(dict(status='initial-input-inventory',
        accepted=False, **evidence.identity()), indent=2) + '\n')
    started = time.monotonic()
    run = ResidentCommands(ROOT, out, default_timeout=600)
    lean_version = run(['lake', 'env', 'lean', '--version'], 'lean-version').strip()
    version = (ROOT/'lean-toolchain').read_text().strip().split(':v')[-1]
    require(re.search(r'Lean \(version ' + re.escape(version) + r'(?:,|\s)', lean_version),
            'Resident Lean toolchain differs from pinned version')
    run(['lake', 'build', 'Pinwheel'], 'build')
    run(['lake', 'env', 'lean', '-DwarningAsError=true', '--run', emitter, out], 'emit')
    for path in out.glob('*.mlir'):
        evidence.freeze_generated(path)
    if (out/'assembly.json').exists():
        evidence.freeze_generated(out/'assembly.json')
    rtl = run([circt, out/'chip.mlir', '--canonicalize', '--lower-seq-to-sv', '--lower-hw-to-sv',
               '--hw-legalize-modules', '--export-verilog', '-o', '/dev/null'], 'export')
    design = out/'design.sv'
    design.write_text(rtl)
    evidence.freeze_generated(design)
    executable = out/'host.vvp'
    run([cad/'iverilog', '-B', closure.backend, '-g2012', '-DFUNCTIONAL', '-s', 'host_bridge', '-o', executable,
        design, ROOT/'test/host_bridge.sv', ROOT/'test/paired_chip.sv', *models], 'compile-simulation')
    evidence.freeze_generated(executable)
    closure.check_executable(executable)
    with Simulation(cad/'vvp', executable) as simulation:
        result = demonstrate(simulation, evidence, run)
    require(run(['lake', 'env', 'lean', '--version'], 'lean-version-closeout').strip() == lean_version,
            'Resident Lean version changed during run')
    closure.closeout()
    evidence.closeout()
    report = dict(backend=backend, action='resident-demo', **result, **evidence.identity(),
        rtl_sha256=sha(design), mlir_sha256=sha(out/'chip.mlir'), executable_sha256=sha(executable),
        commands=run.records, bundled_tool_closure=closure.identity(), lean_version=lean_version,
        lean_version_unchanged=True, elapsed_seconds=round(time.monotonic() - started, 3),
        boundary='One unchanged emitted RTL package, resolved five-pad fixtures, certified resident source images '
            'and actual serial START payloads. The UART/SPI peers inspect only package wires and edge counts. '
            'Supervisor disabled. No board frequency, analog sampling, new hardware or physical qualification claim.')
    (out/'report.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({name: report[name] for name in
        ('backend', 'uart_payloads', 'spi_payloads', 'uart_edges_per_transfer', 'spi_edges_per_transfer',
         'edges', 'frames', 'elapsed_seconds')}, indent=2))
    print(out/'report.json')
    return report


def run_gate(tag, backend='paired-stream'):
    if backend not in ('paired', 'paired-stream'):
        raise ValueError('Resident demonstration requires paired or paired-stream hardware')
    out = fresh_directory(ROOT/'build/host', tag)
    try:
        return execute_gate(out, backend)
    except BaseException as error:
        # A failed/interrupted probe remains reviewable without publishing a
        # report.json that could be mistaken for an accepted capability gate.
        (out/'failed-attempt.json').write_text(json.dumps(dict(status='failed', accepted=False,
            backend=backend, error_type=type(error).__name__, error=str(error),
            boundary='Incomplete capability attempt. Retained command logs and case-progress.jsonl '
                'are diagnostic evidence; source/tool custody and complete gate acceptance are unverified.'),
            indent=2) + '\n')
        raise


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--tag', required=True)
    parser.add_argument('--backend', choices=('paired', 'paired-stream'), default='paired-stream')
    args = parser.parse_args()
    run_gate(args.tag, args.backend)


if __name__ == '__main__':
    main()
