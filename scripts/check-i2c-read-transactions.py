#!/usr/bin/env python3
"""Certify and run compact I2C register reads on resolved emitted package pins."""
import argparse
from dataclasses import asdict, replace
import json
from pathlib import Path
import re
import time

from capability_receipt import CapabilityEvidence
from host_demo import compiler_images
from i2c_read_peers import I2CReadPeer, I2CReadWireError
from pad_io import PAD_MAP
from pad_peers import require
from pinwheel_host import Host, PAIRED_FORMAT
from pinwheel_sim import Simulation
from protocol_results import i2c_read_result
from protocol_tool_closure import ProtocolToolClosure
from validation_run import Commands, fresh_directory, sha

ROOT = Path(__file__).resolve().parents[1]
FIELDS = {'name', 'address', 'register', 'payload_bytes', 'byte_count', 'ack_bits',
          'phase_cycles', 'wait_cycles', 'stretch_cycles', 'scl_stuck',
          'expected_samples', 'expected_outcome', 'expected_clock_count'}


class ReadCheckError(RuntimeError):
    def __init__(self, category, message, case):
        self.category, self.case = category, case
        super().__init__(message)


def metadata(data, images):
    entries = json.loads(data)
    require(isinstance(entries, list) and bool(entries), 'Read fixtures must be a nonempty list')
    names = set()
    for item in entries:
        require(isinstance(item, dict) and set(item) == FIELDS and
                isinstance(item['name'], str) and re.fullmatch(r'[A-Za-z0-9_-]+', item['name']),
                'Unsupported I2C read fixture schema/name')
        require(isinstance(item['payload_bytes'], list) and isinstance(item['ack_bits'], list),
                'Read payload and ACK metadata must use lists')
        peer = peer_for(item)
        require(type(item['byte_count']) is int and item['byte_count'] == len(peer.payload_bytes),
                'Read byte count differs from peer')
        require(type(item['wait_cycles']) is int and 16 <= item['wait_cycles'] <= 256 and
                3 <= peer.phase_cycles <= 256, 'Package peer requires H>=3 and wait budget16..256')
        outcome = 6 if peer.scl_stuck else 7 if peer.nack_stage is not None else 5
        samples = (0 if peer.scl_stuck else 1 << peer.nack_stage if peer.nack_stage is not None else
                   sum(((byte >> (7-bit)) & 1) << (8*n+bit)
                       for n, byte in enumerate(peer.payload_bytes) for bit in range(8)))
        count = 0 if peer.scl_stuck else peer.stop_after
        require(all(type(item[k]) is int for k in
                    ('expected_samples', 'expected_outcome', 'expected_clock_count')) and
                (item['expected_samples'], item['expected_outcome'], item['expected_clock_count']) ==
                (samples, outcome, count), 'Read expected result disagrees with independent peer')
        require(item['name'] not in names, 'Duplicate I2C read fixture')
        names.add(item['name'])
    require(names == set(images), 'Read image/metadata names differ')
    return entries


def peer_for(item):
    return I2CReadPeer(item['address'], item['register'], item['payload_bytes'], item['ack_bits'],
        phase_cycles=item['phase_cycles'], stretch_cycles=item['stretch_cycles'],
        scl_stuck=item['scl_stuck'], fault_after_rises=item.get('fault_after_rises'),
        fault_delay_cycles=item.get('fault_delay_cycles', 2))


def run_cases(simulation, images, entries, out, certify, *, host=None, reset=True):
    simulation.device = None
    host = Host(simulation, image_format=PAIRED_FORMAT) if host is None else host
    if reset:
        host.reset()
    cases = []
    for item in entries:
        name = item['name']
        source = replace(images[name], image_format=PAIRED_FORMAT)
        simulation.device = None
        certify(name, source)
        source.write(out / (name + '.json'))
        host.upload(source)
        peer = peer_for(item)
        simulation.device = peer
        try:
            host.start()
            raw = host.read_result(timeout_cycles=100_000, consume=False)
        except I2CReadWireError as error:
            # Peers run on every chip edge, including host command/status edges.
            # A malformed waveform can fail before there is a terminal packet.
            raise ReadCheckError(error.category, str(error),
                dict(name=name, scenario=item, partial_wire=dict(clock_count=len(peer.bits),
                     starts=peer.starts, stopped=peer.stopped))) from error
        require(host.read_result(timeout_cycles=0, consume=False) == raw, name + ': retained result changed')
        decoded = i2c_read_result(raw, byte_count=item['byte_count'])
        host.consume()
        require(not host.result_status() & 1, name + ': consumption did not clear result')
        case = dict(name=name, result=asdict(raw), protocol_result=asdict(decoded),
                    retained_twice=True, consumed=True, scenario={k: v for k, v in item.items() if k != 'name'})
        try:
            wire = peer.check(timeout=item['expected_outcome'] == 6,
                              fault=item.get('fault_after_rises') is not None)
        except RuntimeError as error:
            raise ReadCheckError('wire-order', str(error), case) from error
        if wire['clock_count'] != item['expected_clock_count']:
            raise ReadCheckError('wire-order', name + ': wrong clock count', case)
        require(simulation.pins.enabled == 0, name + ': terminal outputs not released')
        case.update(wire=wire, outputs_released=True)
        if raw.outcome != item['expected_outcome'] or raw.overrun or raw.rejected:
            raise ReadCheckError('status', name + ': unexpected outcome/flags', case)
        if raw.samples != item['expected_samples']:
            raise ReadCheckError('capture', name + ': raw capture mismatch', case)
        expected_payload = tuple(item['payload_bytes']) if raw.outcome == 5 else None
        require(decoded.payload == expected_payload, name + ': decoded payload mismatch')
        simulation.device = None
        cases.append(case)
        with (out / 'case-progress.jsonl').open('a') as stream:
            stream.write(json.dumps(case) + '\n')
    return dict(cases=cases, edges=host.edges, frames=host.frames)


def changed_capture(source):
    # First payload bit is the checked high phase at PC116. Move its capture
    # to slot1, which the next received bit later overwrites; wire behavior stays.
    words = list(source.words)
    require(words[116] & 7 == 2 and words[116] >> 35 & 63 == 3, 'Read capture layout changed')
    original = words[116]
    # Replace every instance of this record, including the early address ACK,
    # so the canonical 32-record capacity stays valid for the negative upload.
    changed = original & ~(63 << 35) | 7 << 35
    words = [changed if word == original else word for word in words]
    return replace(source, words=tuple(words))


def changed_nack_status(source):
    words = list(source.words)
    require(words[195] == 0, 'Read NACK terminal layout changed')
    words[195] = 4
    return replace(source, words=tuple(words))


def missing_nack_stop(source):
    words = list(source.words)
    words[191] = 4
    return replace(source, words=tuple(words))


def unsafe_sda(source):
    words = list(source.words)
    original = words[1]
    words = [word | 2 << 3 if word == original else word for word in words]
    return replace(source, words=tuple(words))


def reset_control(simulation, images, entries, out, certify):
    item = next(x for x in entries if x['byte_count'] == 2 and x['expected_outcome'] == 5 and
                x['stretch_cycles'] == 0 and x['phase_cycles'] == 4)
    simulation.device = None
    host = Host(simulation, image_format=PAIRED_FORMAT)
    host.reset()
    source = replace(images[item['name']], image_format=PAIRED_FORMAT)
    certify('i2c-read-active-reset', source)
    host.upload(source)
    peer = peer_for(item)
    simulation.device = peer
    host.start()
    for _ in range(128):
        if peer.bits:
            break
        host.advance()
    require(host.page(0) & 1 and peer.starts and 0 < len(peer.bits) < 45,
            'Reset must interrupt a running incomplete read')
    before = dict(clock_count=len(peer.bits), starts=peer.starts)
    simulation.device = None
    host.reset()
    require(not host.page(0) & 1 and host.result_status() == 0x10 and
            host.page(1) == host.page(2) == 0 and simulation.pins.enabled == 0,
            'Read reset did not clear engine/mailbox/output state')
    name = 'i2c-read-after-reset'
    recovery = run_cases(simulation, {name: source}, [dict(item, name=name)], out, certify,
                         host=host, reset=False)
    return dict(interrupted=before, mailbox_cleared=True, outputs_released=True,
                boundary='External rst_n; interrupted framing exempt; explicit reload before recovery',
                recovery=recovery)


def run_gate(out):
    sources = [ROOT / 'Pinwheel.lean', *sorted((ROOT / 'Pinwheel').rglob('*.lean')),
        *[ROOT / n for n in ('lakefile.toml', 'lake-manifest.json', 'lean-toolchain',
            'test/I2CReadTransactions.lean', 'test/PairedValidationEmit.lean', 'test/paired_chip.sv',
            'test/host_bridge.sv', 'tools/storage-macros.json', 'tools/hardware-toolchain.json')],
        *[ROOT / 'scripts' / n for n in ('check-i2c-read-transactions.py', 'capability_receipt.py',
            'i2c_read_peers.py', 'protocol_results.py', 'pad_io.py', 'pad_peers.py', 'pinwheel_host.py',
            'pinwheel_sim.py', 'host_demo.py', 'paired_execution.py', 'paired_image_certificate.py',
            'execution-vectors.py', 'validation_run.py', 'process_group.py', 'protocol_tool_closure.py')]]
    cad = ROOT / 'build/tools/oss-cad-suite/bin'
    circt = ROOT / 'build/tools/firtool-1.159.0/bin/circt-opt'
    models = [ROOT / 'build/storage/macros' / n for n in
        ('RM_IHPSG13_1P_512x64_c2_bm_bist.v', 'RM_IHPSG13_1P_core_behavioral_bm_bist.v')]
    lock = json.loads((ROOT / 'tools/storage-macros.json').read_text())
    for path in models:
        require(sha(path) == lock['files_sha256']['verilog/' + path.name], 'Unpinned SRAM model')
    closure = ProtocolToolClosure(ROOT, circt, cad / 'iverilog', cad / 'vvp')
    evidence = CapabilityEvidence(ROOT, out, sources, closure.files, models)
    (out / 'attempt-inputs.json').write_text(json.dumps(evidence.identity(), indent=2) + '\n')
    started = time.monotonic()
    run = Commands(ROOT, out, default_timeout=600)
    try:
        lean_version = run(['lake', 'env', 'lean', '--version'], 'lean-version').strip()
        expected = (ROOT / 'lean-toolchain').read_text().strip().split(':v')[-1]
        require(re.search(r'Lean \(version ' + re.escape(expected) + r'(?:,|\s)', lean_version), 'Wrong Lean version')
        run(['lake', 'build', 'Pinwheel', 'Pinwheel.Compile.I2CReadTransactionProofs'], 'build')
        generated = out / 'compiled-read'
        run(['lake', 'env', 'lean', '-DwarningAsError=true', '--run', 'test/I2CReadTransactions.lean', generated], 'compile-read')
        images = compiler_images(evidence.capture(generated / 'images.txt', 'read-images.txt'))
        entries = metadata(evidence.capture(generated / 'metadata.json', 'read-metadata.json'), images)
        coverage = {(x['byte_count'], next((i for i, bit in enumerate(x['ack_bits']) if bit), None))
                    for x in entries if not x['scl_stuck']}
        require({(count, nack) for count in (1, 2) for nack in (None, 0, 1, 2)} <= coverage,
                'Both read sizes need success and every first-NACK stage')
        require(any(x['stretch_cycles'] > 0 for x in entries) and any(x['scl_stuck'] for x in entries),
                'Reads need clock stretching and initial timeout')
        run(['lake', 'env', 'lean', '-DwarningAsError=true', '--run', 'test/PairedValidationEmit.lean', out], 'emit')
        mlir_digest = evidence.freeze_generated(out / 'chip.mlir')
        rtl = run([circt, out / 'chip.mlir', '--canonicalize', '--lower-seq-to-sv', '--lower-hw-to-sv',
                   '--hw-legalize-modules', '--export-verilog', '-o', '/dev/null'], 'export')
        design = out / 'design.sv'
        design.write_text(rtl)
        rtl_digest = evidence.freeze_generated(design)
        executable = out / 'host.vvp'
        run([cad / 'iverilog', '-B', closure.backend, '-g2012', '-DFUNCTIONAL', '-s', 'host_bridge',
             '-o', executable, design, ROOT / 'test/host_bridge.sv', ROOT / 'test/paired_chip.sv', *models], 'compile-simulation')
        executable_digest = evidence.freeze_generated(executable)
        closure.check_executable(executable)
        certify = lambda name, source: evidence.certify(name, source, run)
        baseline = next(x for x in entries if x['byte_count'] == 2 and x['expected_outcome'] == 5 and
                        x['stretch_cycles'] == 0 and x['phase_cycles'] == 4)
        nack = next(x for x in entries if x['byte_count'] == 2 and x['ack_bits'] == [0, 0, 1])
        with Simulation(cad / 'vvp', executable) as simulation:
            reads = run_cases(simulation, images, entries, out, certify)
            reset = reset_control(simulation, images, entries, out, certify)
            name = 'i2c-read-guard-loss'
            guard = dict(baseline, name=name, expected_outcome=7, expected_samples=0,
                         expected_clock_count=1, fault_after_rises=1, fault_delay_cycles=2)
            guards = run_cases(simulation, {name: images[baseline['name']]}, [guard], out, certify)
        negatives = []
        for suffix, item, mutate, category in [
                ('wrong-capture', baseline, changed_capture, 'capture'),
                ('wrong-nack-status', nack, changed_nack_status, 'status'),
                ('missing-nack-stop', nack, missing_nack_stop, 'wire-order'),
                ('push-pull-sda', baseline, unsafe_sda, 'open-drain')]:
            name = 'i2c-read-' + suffix
            source = mutate(images[item['name']])
            try:
                with Simulation(cad / 'vvp', executable) as simulation:
                    run_cases(simulation, {name: source}, [dict(item, name=name)], out, certify)
            except ReadCheckError as error:
                require(error.category == category, 'Wrong read negative rejection category: ' + suffix)
                negatives.append(dict(reason=suffix, category=category, diagnostic=str(error),
                                      observation=error.case, status='rejected_as_expected'))
            except RuntimeError as error:
                require(category == 'open-drain' and
                        ('only low/release' in str(error) or 'I2C board links require open-drain' in str(error)),
                        'Unexpected negative failure: ' + str(error))
                negatives.append(dict(reason=suffix, category=category, diagnostic=str(error), status='rejected_as_expected'))
            else:
                raise RuntimeError('Read negative unexpectedly passed: ' + suffix)
        require(run(['lake', 'env', 'lean', '--version'], 'lean-version-closeout').strip() == lean_version,
                'Lean version changed during read gate')
        closure.closeout()
        evidence.closeout()
        report = dict(schema=1, status='passed', backend='paired-validation', candidate='five-pad-digital',
            A_accepted=False, physical_evidence_reused=False, cad_seconds=0, pad_map=PAD_MAP,
            clock_assumption_ns=20, lean_version=lean_version, lean_version_unchanged=True,
            mlir_sha256=mlir_digest, rtl_sha256=rtl_digest, executable_sha256=executable_digest,
            reads=reads, reset_control=reset, guard_control=guards, negatives=negatives,
            bundled_tool_closure=closure.identity(), commands=run.records,
            elapsed_seconds=round(time.monotonic() - started, 3), **evidence.identity(),
            boundary='Resolved digital package wires with pinned behavioral SRAM. One/two-byte compact reads; '
                'NACK and guard fault share terminal fault and discard captures; no automatic retry, analog '
                'I2C compliance, board timing, SRAM qualification or physical acceptance claim.')
        (out / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
        return report
    except BaseException as error:
        (out / 'failed-attempt.json').write_text(json.dumps(dict(status='failed', accepted=False,
            error=type(error).__name__, diagnostic=str(error), commands=run.records, **evidence.identity()), indent=2) + '\n')
        raise


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--tag', required=True)
    args = parser.parse_args()
    out = fresh_directory(ROOT / 'build/host', args.tag)
    report = run_gate(out)
    print(json.dumps(dict(status='passed', reads=len(report['reads']['cases']),
                          negatives=len(report['negatives']), certificates=len(report['image_certificates'])), indent=2))
    print(out / 'report.json')


if __name__ == '__main__':
    main()
