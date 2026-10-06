#!/usr/bin/env python3
"""Check bounded I2C writes and nine-attempt bus clear on resolved package wires."""
import argparse
from dataclasses import asdict, replace
import json
from pathlib import Path
import re
import time

from capability_receipt import CapabilityEvidence
from host_demo import compiler_images
from i2c_peers import I2CBusClearPeer, I2CWritePeer
from pad_io import PAD_MAP
from pad_peers import require
from pinwheel_host import Host, PAIRED_FORMAT
from pinwheel_sim import Simulation
from protocol_tool_closure import ProtocolToolClosure
from validation_run import Commands, fresh_directory, sha

ROOT = Path(__file__).resolve().parents[1]
WRITE_FIELDS = {'name', 'address', 'payload_bytes', 'ack_bits', 'phase_cycles', 'wait_cycles',
                'stretch_cycles', 'scl_stuck', 'expected_samples', 'expected_outcome', 'expected_clock_count'}
CLEAR_FIELDS = {'name', 'phase_cycles', 'timeout_cycles', 'recovery_policy', 'capture_slot',
                'release_after_pulses', 'stretch_cycles', 'scl_stuck', 'expected_pulses',
                'expected_sda_sample', 'expected_outcome'}


class I2CCheckError(RuntimeError):
    def __init__(self, category, message, case):
        self.category, self.case = category, case
        super().__init__(message)


def metadata(kind, data, images):
    entries = json.loads(data)
    fields = WRITE_FIELDS if kind == 'write' else CLEAR_FIELDS
    if not isinstance(entries, list) or not entries:
        raise ValueError('I2C metadata must be a nonempty list')
    names = set()
    for item in entries:
        if not isinstance(item, dict) or set(item) != fields or not isinstance(item['name'], str) or not re.fullmatch(r'[A-Za-z0-9_-]+', item['name']):
            raise ValueError('Unsupported I2C fixture schema/name')
        for key in ('phase_cycles', 'stretch_cycles', 'expected_outcome'):
            if type(item[key]) is not int:
                raise ValueError('I2C configuration fields must use integers')
        budget = item['wait_cycles' if kind == 'write' else 'timeout_cycles']
        if type(budget) is not int or not 1 <= budget <= 256 or not 1 <= item['phase_cycles'] <= 256 or item['stretch_cycles'] < 0 or type(item['scl_stuck']) is not bool:
            raise ValueError('I2C phase/budget/peer configuration out of range')
        if kind == 'write':
            if not isinstance(item['payload_bytes'], list) or not isinstance(item['ack_bits'], list):
                raise ValueError('I2C payload/ACK metadata must use lists')
            peer = I2CWritePeer(item['address'], item['payload_bytes'], item['ack_bits'], phase_cycles=item['phase_cycles'], stretch_cycles=item['stretch_cycles'], scl_stuck=item['scl_stuck'])
            count = 0 if item['scl_stuck'] else 9 * peer.completed_bytes
            samples = 0 if item['scl_stuck'] else sum(bit << index for index, bit in enumerate(peer.ack_bits[:peer.completed_bytes]))
            if any(type(item[k]) is not int for k in ('expected_samples', 'expected_clock_count')) or item['expected_clock_count'] != count or item['expected_samples'] != samples:
                raise ValueError('I2C ACK/capture/count metadata inconsistent')
        else:
            I2CBusClearPeer(item['release_after_pulses'], phase_cycles=item['phase_cycles'], stretch_cycles=item['stretch_cycles'], scl_stuck=item['scl_stuck'])
            if item['recovery_policy'] != 'nine_rises_release_only' or type(item['capture_slot']) is not int or item['capture_slot'] != 0:
                raise ValueError('Unsupported bus-clear policy/capture slot')
            if type(item['expected_pulses']) is not int or item['expected_pulses'] != (0 if item['scl_stuck'] else 9) or type(item['expected_sda_sample']) is not bool or item['expected_sda_sample'] != (not item['scl_stuck'] and item['release_after_pulses'] is not None):
                raise ValueError('Bus-clear pulse/result metadata inconsistent')
        if item['expected_outcome'] != (6 if item['scl_stuck'] else 5):
            raise ValueError('I2C fixture outcome disagrees with peer scenario')
        if item['name'] in names:
            raise ValueError('Duplicate I2C fixture name')
        names.add(item['name'])
    if names != set(images):
        raise ValueError('I2C image/metadata names differ')
    return entries


def peer_for(kind, item):
    options = dict(phase_cycles=item['phase_cycles'], stretch_cycles=item['stretch_cycles'],
                   scl_stuck=item['scl_stuck'], fault_after_rises=item.get('fault_after_rises'),
                   fault_delay_cycles=item.get('fault_delay_cycles', 2))
    if kind == 'write':
        return I2CWritePeer(item['address'], item['payload_bytes'], item['ack_bits'], **options)
    return I2CBusClearPeer(item['release_after_pulses'], **options)


def run_cases(simulation, kind, images, entries, out, certify, *, host=None, reset=True):
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
        peer = peer_for(kind, item)
        simulation.device = peer
        host.start()
        result = host.read_result(timeout_cycles=100_000, consume=False)
        retained = host.read_result(timeout_cycles=0, consume=False)
        require(retained == result, name + ': retained result changed')
        host.consume()
        require(not host.result_status() & 1, name + ': consumption did not clear result')
        case = dict(name=name, result=asdict(result), retained_twice=True, consumed=True,
                    scenario={k: v for k, v in item.items() if k != 'name'})
        try:
            wire = peer.check(timeout=item['expected_outcome'] == 6, fault=item['expected_outcome'] == 7)
        except RuntimeError as error:
            raise I2CCheckError('wire-order', str(error), case) from error
        count = wire['clock_count'] if kind == 'write' else wire['pulse_rises']
        if count != item['expected_clock_count' if kind == 'write' else 'expected_pulses']:
            raise I2CCheckError('wire-order', name + ': I2C pulse/byte count mismatch', case)
        require(simulation.pins.enabled == 0, name + ': terminal I2C outputs not released')
        case.update(wire=wire, outputs_released=True)
        if result.outcome != item['expected_outcome'] or result.overrun or result.rejected:
            raise I2CCheckError('status', name + ': unexpected I2C outcome/flags', case)
        expected_samples = item['expected_samples'] if kind == 'write' else int(item['expected_sda_sample'])
        if result.samples != expected_samples:
            raise I2CCheckError('capture', name + ': I2C captured result differs from independent reply', case)
        if kind == 'write':
            ack_count = len(wire['observed_ack_bits'])
            case['decoded_ack_bits'] = [(result.samples >> index) & 1 for index in range(ack_count)]
            case['protocol_result'] = ('timeout' if result.outcome == 6 else 'bus-fault' if result.outcome == 7 else
                next(('address-nack' if index == 0 else 'data' + str(index) + '-nack'
                      for index, bit in enumerate(case['decoded_ack_bits']) if bit), 'success'))
        else:
            case['protocol_result'] = ('timeout' if result.outcome == 6 else 'bus-fault' if result.outcome == 7 else
                                       'recovered' if result.samples else 'still-stuck')
        simulation.device = None
        cases.append(case)
    return dict(cases=cases, edges=host.edges, frames=host.frames)


def wrong_ack_slot(source):
    changed, words = 0, []
    for word in source.words:
        for offset in (29, 35):
            field = (word >> offset) & 63
            if field & 1 and field >> 2 == 2:
                word &= ~(15 << (offset + 2))
                changed += 1
        words.append(word)
    require(changed > 0, 'ACK mutation found no slot2 capture')
    return replace(source, words=tuple(words))


def wrong_status(source):
    words = list(source.words)
    require(words[source.last] == 4, 'Status mutation requires a final halt')
    words[source.last] = 1  # Canonical wait for low SCL, one-edge budget, released pins.
    return replace(source, words=tuple(words))


def push_pull_sda(source):
    words = list(source.words)
    index = next((k for k, word in enumerate(words) if word & 7 != 4 and word & (2 << 6)), None)
    require(index is not None, 'Drive mutation found no enabled SDA')
    words[index] |= 2 << 3
    return replace(source, words=tuple(words))


def swap_address_data(source):
    # Exchange the eight outgoing address bits with the second payload's bits;
    # leave ACK destinations, guards, phase durations and successors unchanged.
    words, mask = list(source.words), 63 << 3
    for bit in range(8):
        for phase in range(4):
            a, b = 2 + 4 * bit + phase, 2 + 4 * (18 + bit) + phase
            words[a], words[b] = ((words[a] & ~mask) | (words[b] & mask),
                                  (words[b] & ~mask) | (words[a] & mask))
    require(tuple(words) != source.words, 'Order mutation requires unequal address/data bytes')
    return replace(source, words=tuple(words))


def reset_control(simulation, images, entries, out, certify):
    item = next(x for x in entries if len(x['payload_bytes']) == 2 and not any(x['ack_bits']) and
                x['phase_cycles'] == 4 and x['stretch_cycles'] == 0 and not x['scl_stuck'])
    source = replace(images[item['name']], image_format=PAIRED_FORMAT)
    simulation.device = None
    host = Host(simulation, image_format=PAIRED_FORMAT)
    host.reset()
    name = 'i2c-write-active-rst-n'
    certify(name, source)
    host.upload(source)
    peer = peer_for('write', item)
    simulation.device = peer
    host.start()
    for _ in range(128):
        if peer.bits:
            break
        host.advance()
    require(host.page(0) & 1 and peer.started and 0 < len(peer.bits) < 27,
            'Reset must interrupt an active incomplete I2C write')
    before = dict(started=peer.started, clock_count=len(peer.bits))
    simulation.device = None
    host.reset()
    require(not host.page(0) & 1, 'rst_n did not stop I2C execution')
    require(host.result_status() == 0x10 and host.page(1) == 0 and host.page(2) == 0,
            'rst_n did not clear I2C mailbox and flags')
    require(simulation.pins.enabled == 0, 'rst_n did not release I2C outputs')
    recovery_name = 'i2c-write-after-rst-n'
    recovery = run_cases(simulation, 'write', {recovery_name: source},
                         [dict(item, name=recovery_name)], out, certify)
    return dict(boundary='external rst_n through Host.reset; interrupted framing exempt',
        interrupted=before, engine_stopped=True, mailbox_cleared=True, outputs_released=True,
        recovery=recovery)


def recovery_then_write(simulation, clear_images, clears, write_images, writes, out, certify):
    clear = next(x for x in clears if x['release_after_pulses'] == 9 and not x['scl_stuck'] and x['stretch_cycles'] == 0)
    write = next(x for x in writes if len(x['payload_bytes']) == 2 and not any(x['ack_bits']) and
                 not x['scl_stuck'] and x['stretch_cycles'] == 0 and x['phase_cycles'] == 4)
    simulation.device = None
    host = Host(simulation, image_format=PAIRED_FORMAT)
    host.reset()
    clear_name, write_name = 'i2c-sequence-clear', 'i2c-sequence-write'
    recovered = run_cases(simulation, 'clear', {clear_name: clear_images[clear['name']]},
                          [dict(clear, name=clear_name)], out, certify, host=host, reset=False)
    written = run_cases(simulation, 'write', {write_name: write_images[write['name']]},
                        [dict(write, name=write_name)], out, certify, host=host, reset=False)
    return dict(boundary='same Host and Simulation; explicit cooperating peer replacement',
                intervening_chip_resets=0, automatic_retry=False,
                steps=['clear', 'read-twice', 'consume', 'replace-peer', 'upload-write',
                       'start-write', 'read-twice', 'consume'], recovered=recovered, written=written)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--tag', required=True)
    args = parser.parse_args()
    out = fresh_directory(ROOT / 'build/host', args.tag)
    sources = [ROOT / 'Pinwheel.lean', *sorted((ROOT / 'Pinwheel').rglob('*.lean')),
        *[ROOT / n for n in ('lakefile.toml', 'lake-manifest.json', 'lean-toolchain',
            'test/I2CWriteTransactions.lean', 'test/I2CRecovery.lean', 'test/PairedValidationEmit.lean',
            'test/paired_chip.sv', 'test/host_bridge.sv', 'tools/storage-macros.json',
            'tools/hardware-toolchain.json')],
        *[ROOT / 'scripts' / n for n in ('check-i2c-capabilities.py', 'capability_receipt.py',
            'i2c_peers.py', 'pad_io.py', 'pad_peers.py', 'pinwheel_host.py', 'pinwheel_sim.py',
            'host_demo.py', 'paired_execution.py', 'paired_image_certificate.py',
            'execution-vectors.py', 'validation_run.py', 'process_group.py', 'protocol_tool_closure.py')]]
    cad = ROOT / 'build/tools/oss-cad-suite/bin'
    circt = ROOT / 'build/tools/firtool-1.159.0/bin/circt-opt'
    models = [ROOT / 'build/storage/macros' / n for n in
        ('RM_IHPSG13_1P_512x64_c2_bm_bist.v', 'RM_IHPSG13_1P_core_behavioral_bm_bist.v')]
    lock = json.loads((ROOT / 'tools/storage-macros.json').read_text())
    for path in models:
        require(sha(path) == lock['files_sha256']['verilog/' + path.name], 'Unpinned SRAM model: ' + path.name)
    closure = ProtocolToolClosure(ROOT, circt, cad / 'iverilog', cad / 'vvp')
    evidence = CapabilityEvidence(ROOT, out, sources, closure.files, models)
    started = time.monotonic()
    run = Commands(ROOT, out, default_timeout=600)
    lean_version = run(['lake', 'env', 'lean', '--version'], 'lean-version').strip()
    expected_version = (ROOT / 'lean-toolchain').read_text().strip().split(':v')[-1]
    require(re.search(r'Lean \(version ' + re.escape(expected_version) + r'(?:,|\s)', lean_version),
            'Actual Lean version does not match lean-toolchain: ' + lean_version)
    run(['lake', 'build', 'Pinwheel', 'Pinwheel.Compile.I2CWriteTransactionProofs',
         'Pinwheel.Compile.I2CRecoveryProofs'], 'build')
    fixtures = {}
    for kind, fixture in [('write', 'I2CWriteTransactions.lean'), ('clear', 'I2CRecovery.lean')]:
        generated = out / ('compiled-' + kind)
        run(['lake', 'env', 'lean', '-DwarningAsError=true', '--run', ROOT / 'test' / fixture, generated], 'compile-' + kind)
        images = compiler_images(evidence.capture(generated / 'images.txt', kind + '-images.txt'))
        entries = metadata(kind, evidence.capture(generated / 'metadata.json', kind + '-metadata.json'), images)
        fixtures[kind] = images, entries
    write_images, writes = fixtures['write']
    clear_images, clears = fixtures['clear']
    coverage = {(len(x['payload_bytes']), next((i for i, bit in enumerate(x['ack_bits']) if bit), None))
                for x in writes if not x['scl_stuck']}
    require({(1, None), (1, 0), (1, 1), (2, None), (2, 0), (2, 1), (2, 2)} <= coverage,
            'Write fixtures must cover every first-NACK position and both successes')
    require(set(range(1, 10)) <= {x['release_after_pulses'] for x in clears if not x['scl_stuck']} and
            any(x['release_after_pulses'] is None and not x['scl_stuck'] for x in clears),
            'Bus-clear fixtures must cover releases1..9 and still-stuck SDA')
    require(all(any(x['scl_stuck'] for x in entries) and any(x['stretch_cycles'] > 0 for x in entries)
                for entries in (writes, clears)), 'Both I2C tracks need stretching and SCL-stuck timeout cases')
    require(all(x['phase_cycles'] >= 3 and x['wait_cycles' if kind == 'write' else 'timeout_cycles'] >= 16
                for kind, (_, entries) in fixtures.items() for x in entries),
            'Physical peer fixtures require H>=3 and a declared wait budget>=16; shorter model configurations remain separate')
    run(['lake', 'env', 'lean', '-DwarningAsError=true', '--run', 'test/PairedValidationEmit.lean', out], 'emit')
    mlir = out / 'chip.mlir'
    mlir_digest = evidence.freeze_generated(mlir)
    rtl = run([circt, mlir, '--canonicalize', '--lower-seq-to-sv', '--lower-hw-to-sv',
               '--hw-legalize-modules', '--export-verilog', '-o', '/dev/null'], 'export')
    design = out / 'design.sv'
    design.write_text(rtl)
    rtl_digest = evidence.freeze_generated(design)
    executable = out / 'host.vvp'
    run([cad / 'iverilog', '-B', closure.backend, '-g2012', '-DFUNCTIONAL', '-s', 'host_bridge', '-o', executable,
         design, ROOT / 'test/host_bridge.sv', ROOT / 'test/paired_chip.sv', *models], 'compile-simulation')
    executable_digest = evidence.freeze_generated(executable)
    closure.check_executable(executable)
    certify = lambda name, source: evidence.certify(name, source, run)
    with Simulation(cad / 'vvp', executable) as simulation:
        write_result = run_cases(simulation, 'write', write_images, writes, out, certify)
        clear_result = run_cases(simulation, 'clear', clear_images, clears, out, certify)
        reset = reset_control(simulation, write_images, writes, out, certify)
        sequence = recovery_then_write(simulation, clear_images, clears, write_images, writes, out, certify)
        guards = []
        for kind, images, entries in [('write', write_images, writes), ('clear', clear_images, clears)]:
            item = next(x for x in entries if not x['scl_stuck'] and x['stretch_cycles'] == 0 and
                        (not any(x['ack_bits']) if kind == 'write' else x['release_after_pulses'] == 9))
            name = 'i2c-' + kind + '-guard-loss'
            control = dict(item, name=name, expected_outcome=7, fault_after_rises=1, fault_delay_cycles=2)
            if kind == 'write':
                control.update(expected_samples=0, expected_clock_count=1)
            else:
                control.update(expected_sda_sample=False, expected_pulses=1)
            guards.append(run_cases(simulation, kind, {name: images[item['name']]}, [control], out, certify))
    negatives = []
    baseline = next(x for x in writes if len(x['payload_bytes']) == 2 and not any(x['ack_bits']) and
                    x['stretch_cycles'] == 0 and not x['scl_stuck'])
    nack = next(x for x in writes if x['ack_bits'] == [0, 0, 1] and x['stretch_cycles'] == 0)
    for suffix, item, mutate, expected_category in [
            ('wrong-ack-slot', nack, wrong_ack_slot, 'capture'),
            ('wrong-terminal-status', baseline, wrong_status, 'status'),
            ('push-pull-sda', baseline, push_pull_sda, 'open-drain'),
            ('swapped-address-data', baseline, swap_address_data, 'wire-order')]:
        name = 'i2c-' + suffix
        program = mutate(write_images[item['name']])
        try:
            with Simulation(cad / 'vvp', executable) as simulation:
                run_cases(simulation, 'write', {name: program}, [dict(item, name=name)], out, certify)
        except I2CCheckError as error:
            require(error.category == expected_category, 'Wrong negative rejection category: ' + suffix)
            negatives.append(dict(status='rejected_as_expected', reason=suffix,
                                  category=error.category, observation=error.case, diagnostic=str(error)))
        except RuntimeError as error:
            require(expected_category == 'open-drain' and 'open-drain' in str(error),
                    'Unexpected I2C negative failure: ' + str(error))
            negatives.append(dict(status='rejected_as_expected', reason=suffix,
                                  category='open-drain', diagnostic=str(error)))
        else:
            raise RuntimeError('I2C negative unexpectedly passed: ' + suffix)
    require(run(['lake', 'env', 'lean', '--version'], 'lean-version-closeout').strip() == lean_version,
            'Lean version changed during capability run')
    closure.closeout()
    evidence.closeout()
    report = dict(schema=1, status='passed', candidate='five-pad-digital', backend='paired-validation',
        A_accepted=False, physical_evidence_reused=False, cad_seconds=0, pad_map=PAD_MAP,
        clock_assumption_ns=20, lean_version=lean_version,
        lean_version_unchanged=True, mlir_sha256=mlir_digest, rtl_sha256=rtl_digest,
        executable_sha256=executable_digest, writes=write_result, bus_clear=clear_result,
        bundled_tool_closure=closure.identity(),
        reset_control=reset, recovery_then_write=sequence,
        guard_controls=guards, negatives=negatives, commands=run.records,
        elapsed_seconds=round(time.monotonic() - started, 3), **evidence.identity(),
        boundary='Resolved digital wires with declared I2C board joins and pinned behavioral SRAM. '
            'Bounded one/two-payload-byte writes and nine release-only recovery attempts; no automatic retry, '
            'analog I2C compliance, board timing, SRAM qualification or physical acceptance claim.')
    (out / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(dict(status='passed', write_cases=len(write_result['cases']),
                         bus_clear_cases=len(clear_result['cases']), negatives=len(negatives),
                         certificates=len(evidence.image_certificates)), indent=2))
    print(out / 'report.json')


if __name__ == '__main__':
    main()
