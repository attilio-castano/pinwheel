#!/usr/bin/env python3
"""Finite ownership differential checks and independent buffered wire witnesses.

This gate exercises a reference model, not the existing package/RTL or new data
storage circuitry. It requires only the pinned Lean toolchain and Python 3.12+.
"""
import argparse
import json
from pathlib import Path
import re
import shutil
import sys

from buffered_engine import buffered_jtag, buffered_spi
from buffered_peers import BufferedJTAGPeer, BufferedSPIPeer
from jtag_peers import TAP
from pinwheel_buffers import BufferFault, BufferedModelHost, TransferError, TransferId, TransferSlot
from validation_run import Commands, fresh_directory, sha

ROOT = Path(__file__).resolve().parents[1]


def projection(slot):
    """Validation observation; slot-internal UUID adds cross-device admission.

    Lean models one slot and uses its local epoch/sequence pair. This projection
    omits Python's namespace, not the local identity or retained data.
    """
    descriptor = slot.descriptor
    identity = descriptor.identity if descriptor else None
    return dict(phase=slot.state, epoch=slot._epoch, next_sequence=slot._next_sequence,
        identity=[identity.epoch, identity.sequence] if identity else None,
        program_generation=descriptor.program_generation if descriptor else None,
        tx_bits=list(slot._tx), tx_consumed_bits=slot._tx_consumed,
        rx_limit=slot.rx_limit, rx_bits=list(slot._rx),
        outcome=slot.peek(identity).outcome if slot.state == 'completed' else None)


def apply_command(slot, command):
    kind = command['kind']
    if type(kind) is not str or kind not in ('prepare', 'start', 'consume', 'append',
                                             'finish', 'read', 'release', 'reset'):
        raise ValueError('Unknown exported ownership command')
    identity = None if kind in ('prepare', 'reset') else TransferId(
        command['epoch'], command['sequence'], slot._owner)
    reply = dict(accepted=True, reason=None, tx_bit=None)
    try:
        if kind == 'prepare':
            slot.prepare('differential-program', tuple(command['tx_bits']), command['rx_limit'],
                         program_generation=command['program_generation'])
        elif kind == 'start':
            slot.start(identity, program_generation=command['program_generation'])
        elif kind == 'consume':
            reply['tx_bit'] = slot.take_tx(identity)
        elif kind == 'append':
            slot.append_rx(identity, command['bit'])
        elif kind == 'finish':
            slot.complete(identity, command['outcome'])
        elif kind == 'read':
            slot.peek(identity)
        elif kind == 'release':
            slot.release(identity)
        elif kind == 'reset':
            slot.reset()
        else:
            raise ValueError('Unknown exported ownership command')
    except BufferFault as error:
        reply.update(accepted=False, reason='tx_exhausted' if 'TX buffer' in str(error) else 'rx_full')
    except TransferError as error:
        message = str(error)
        if 'identity' in message:
            reason = 'wrong_identity'
        elif 'generation' in message:
            reason = 'program_generation'
        else:
            reason = 'wrong_phase'
        reply.update(accepted=False, reason=reason)
    except ValueError as error:
        if 'exceeds buffer capacity' not in str(error):
            raise
        reply.update(accepted=False, reason='capacity')
    return dict(projection(slot), reply=reply)


def differential(vectors):
    if vectors.get('schema') != 'pinwheel-transfer-vectors-v1':
        raise ValueError('Unknown ownership vector schema')
    edges = rejected = 0
    cases = vectors['cases']
    if not cases:
        raise ValueError('Ownership vectors must contain cases')
    for case_index, case in enumerate(cases):
        slot = TransferSlot(tx_capacity_bits=case['tx_capacity_bits'],
                            rx_capacity_bits=case['rx_capacity_bits'])
        commands, states = case['commands'], case['states']
        if not commands or len(commands) != len(states):
            raise ValueError('Ownership vectors must pair every command with a state')
        for edge, (command, expected) in enumerate(zip(commands, states, strict=True)):
            actual = apply_command(slot, command)
            if actual != expected:
                raise RuntimeError(f'Lean/Python ownership mismatch in case {case_index}, edge {edge}: '
                                   f'expected {expected}, observed {actual}')
            edges += 1
            rejected += not actual['reply']['accepted']
    return dict(cases=len(cases), edges=edges, rejected_edges=rejected,
                scope='Finite differential execution; not universal Python refinement')


def witnesses():
    cases = []
    # Reuse one loaded program; vary every possible byte in each of four lanes.
    host = BufferedModelHost()
    program = buffered_spi()
    loaded = host.load(program)
    for lane in range(4):
        for byte in range(256):
            tx = bytearray(b'\xa6\x53\x81\x00')
            tx[lane] = byte
            tx = bytes(tx)
            rx = bytes(value ^ 0x96 for value in tx)
            peer = BufferedSPIPeer(tx, rx)
            result = loaded.run(tx=tx, peer=peer)
            wire = peer.check(result.raw_rx_bits)
            if result.outcome != 'complete' or result.payload != rx:
                raise RuntimeError('SPI host result differs from independent wire reply')
            cases.append(dict(protocol='spi', lane=lane, byte=byte,
                tx=tx.hex(), rx=rx.hex(), program_key=program.key,
                engine_edges=program.execution_edges, wire=wire))
    for width in (1, 7, 13, 32):
        program = buffered_jtag(bit_count=width)
        loaded = host.load(program)
        mask = (1 << width) - 1
        for state in TAP:
            for value in (0, mask, 0xa6531289 & mask):
                received = value ^ (0x963cc35a & mask)
                peer = BufferedJTAGPeer(value, received, bit_count=width, initial_state=state)
                result = loaded.run(tx=value.to_bytes((width + 7) // 8, 'little'), peer=peer)
                wire = peer.check(result.raw_rx_bits)
                if result.outcome != 'complete' or int.from_bytes(result.payload, 'little') != received:
                    raise RuntimeError('JTAG host result differs from independent wire reply')
                cases.append(dict(protocol='jtag', width=width, initial_state=state,
                    tx=value, rx=received, program_key=program.key,
                    engine_edges=program.execution_edges, wire=wire))
    return cases


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--tag', required=True)
    args = parser.parse_args()
    if sys.version_info < (3, 12):
        raise RuntimeError('Python 3.12+ is required')
    lake = shutil.which('lake')
    if not lake:
        raise RuntimeError('The pinned Lean toolchain must be on PATH')
    out = fresh_directory(ROOT / 'build/buffered-transfers', args.tag)
    paths = [ROOT / name for name in ('Pinwheel.lean', 'lean-toolchain', 'lakefile.toml', 'lake-manifest.json')]
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
    commands([lake, 'env', 'lean', '-DwarningAsError=true', '--run', 'test/Transfer.lean'], 'lean-ownership')
    exported = commands([lake, 'env', 'lean', '-DwarningAsError=true', '--run', 'test/TransferExport.lean'],
                        'ownership-vectors')
    ownership = differential(json.loads(exported))
    tests = {}
    for label, optimization in (('python', []), ('python-optimized', ['-O'])):
        log = commands([sys.executable, *optimization, '-B', '-m', 'unittest',
                        'discover', '-s', 'test', '-p', 'test_*.py'], label)
        count = re.search(r'Ran (\d+) tests?', log)
        skipped = re.search(r'OK \(skipped=(\d+)\)', log)
        if not count:
            raise RuntimeError('Missing Python suite summary')
        tests[label] = dict(total=int(count[1]), skipped=int(skipped[1]) if skipped else 0)
    cases = witnesses()
    (out / 'wire-cases.json').write_text(json.dumps(cases, indent=2) + '\n')
    for path in paths:
        if sha(path) != hashes[str(path.relative_to(ROOT))]:
            raise RuntimeError(f'Source changed during validation: {path}')
    report = dict(schema='pinwheel-buffered-transfer-evidence-v1', target='buffered-reference-v1',
        lean=version, ownership=ownership, python=tests,
        wire_cases=len(cases), spi_cases=sum(case['protocol'] == 'spi' for case in cases),
        jtag_cases=sum(case['protocol'] == 'jtag' for case in cases),
        model_wire_edges=sum(case['engine_edges'] for case in cases),
        model_capacity=dict(tx_bits=32, rx_bits=32, data_storage_bits=64),
        wire_cases_sha256=sha(out / 'wire-cases.json'), source_sha256=hashes,
        commands=commands.records,
        boundary='Lean ownership safety and finite Python differential; independent digital resolved-pin '
                 'SPI/JTAG reference-model witnesses. No buffered circuit, emitted RTL, SRAM integration, '
                 'host serial transport, physical area, timing qualification, or initialized package proof.')
    (out / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    print(f'Buffered transfer model gate passed: {out / "report.json"}')


if __name__ == '__main__':
    main()
