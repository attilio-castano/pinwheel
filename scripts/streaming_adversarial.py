"""Additional actual-pin adversarial controls for streaming-quad-v1.

Kept separate from the immutable first 16-case producer. Every physical case
uses the actual public compiled bridge and a fresh cold session. Expected bits
come from independent peers. The sequence-exhaustion check is explicitly a
host-only refusal, not a simulated 65536-transaction endpoint history.
"""
from dataclasses import asdict, replace
import json
from pathlib import Path
import re
import time

from streaming_compile import Instruction, lower, spi_image, validate_image
from streaming_peers import StreamingSPIPeer
from streaming_rtl import QuadRTL
from streaming_transport import (Code, Flags, Opcode, QuadTransport, StreamHost,
    StreamProtocolError, StreamTransportError, byte_bits, command, decode_request)
from streaming_wire_cases import EdgeTrace, FaultLink, payloads, require


class FrameFaultLink(FaultLink):
    def arm(self, kind):
        if kind not in ('partial_request', 'overlong_request', 'overlong_response'):
            raise ValueError('Unsupported additional frame fault')
        if self.armed is not None:
            raise ValueError('One link fault may be pending')
        self.armed = kind

    def tick(self, *, csn, sck, mosi):
        mode = self.mode
        rising = not csn and sck and not self.sck
        injected = None
        # The44th host sample is physically suppressed. Closing CS therefore
        # delivers exactly43 request nibbles; the immutable host request is kept.
        if self.armed == 'partial_request' and mode == 'request' and rising and self.count == 43:
            sck, injected = 0, self.armed
        result = super().tick(csn=csn, sck=sck, mosi=mosi)
        if (self.armed == 'overlong_request' and mode == 'request' and rising and self.count == 44 or
                self.armed == 'overlong_response' and mode == 'read' and rising and self.count == 52):
            injected = self.armed
            self.rtl.tick(csn=0, sck=0, mosi=0)
            self.rtl.tick(csn=0, sck=1, mosi=0)
        if injected is not None:
            self.triggered.append(dict(kind=injected, physical_edge=self.cycle))
            self.armed = None
        return result


def physical_case(vvp, executable, directory, operation):
    directory = Path(directory)
    directory.mkdir(parents=True, exist_ok=False)
    trace, started = EdgeTrace(directory / 'wire.bin'), time.monotonic()
    try:
        with QuadRTL(vvp, executable, record_sink=trace) as rtl:
            result = operation(rtl)
            result.update(passed=True, physical_edges=rtl.cycle)
    except Exception as error:
        result = dict(passed=False, error=repr(error))
    finally:
        record = trace.close()
    result.update(trace=record, physical_edges=record['edges'], elapsed_seconds=time.monotonic() - started)
    (directory / 'report.json').write_text(json.dumps(result, indent=2) + '\n')
    return result


def recover_frames(rtl, *, depth, kind):
    link = FrameFaultLink(rtl)
    transport = QuadTransport(link)
    host = StreamHost(transport, depth=depth)
    host.initialize()
    loaded = host.load(spi_image())
    tx, rx, tx_bits, rx_bits = payloads('spi', 32)
    peer = StreamingSPIPeer(tx, rx)
    rtl.device = peer
    pending = loaded.submit(tx_bits)
    link.arm(kind)
    try:
        pending.pump()
    except StreamTransportError as error:
        require(error.pending is pending, 'Framing failure lost its original owner')
    else:
        raise RuntimeError('Specified malformed frame did not force explicit recovery')
    original = transport.inflight
    require(original is not None and original.opcode is Opcode.EXCHANGE32,
        'Framing error did not retain the exact original exchange')
    first_sequence, first_bytes = original.sequence, original.bytes
    for _ in range(3):
        try:
            recovered = pending.recover()
            break
        except StreamTransportError:
            require(transport.inflight == original, 'Recovery changed the original request')
    else:
        raise RuntimeError('Exact framing recovery failed')
    require(recovered.sequence == first_sequence and recovered.tx_accepted == 32,
        'Malformed/replayed request changed the accepted prefix or sequence')
    pending.wait(max_exchanges=30)
    require(pending.rx_bits == rx_bits and pending.tag == 65537, 'Frame recovery changed owner or RX prefix')
    peer_result = peer.check(pending.rx_bits)
    released = pending.release()
    require(not released.busy and not released.retained, 'Recovered transfer did not release')
    require([value['kind'] for value in link.triggered] == [kind], 'Physical frame fault was not exercised once')
    return dict(kind=kind, depth=depth, original_sequence=first_sequence,
        original_request_hex=first_bytes.hex(), recovery_sequence=recovered.sequence,
        recoveries=transport.recoveries, same_sequence_recovery=True,
        exact_tx_prefix_once=True, owner_tag=pending.tag, peer=peer_result,
        faults=link.triggered, ready_retention_checked=kind == 'overlong_response')


def changed_sequence(rtl, *, depth):
    transport = QuadTransport(rtl)
    host = StreamHost(transport, depth=depth)
    host.initialize()
    loaded = host.load(spi_image())
    peer = StreamingSPIPeer(b'\x96', b'\xa5')
    rtl.device = peer
    pending = loaded.submit(byte_bits(b'\x96'))
    pending.wait(max_exchanges=20)
    require(pending.last.rx_valid == 8 and pending.last.retained,
        'Changed-sequence fixture lacks an unacknowledged exported interval')
    # This would be a valid new ACK, but deliberately reuses the completed
    # request sequence with changed payload bytes. It must not retire custody.
    altered = command(pending.last.sequence, Opcode.EXCHANGE0, tag=pending.tag,
        tx_offset=8, rx_ack=8, data=0)
    transport._send(altered)
    rejected = transport._read(altered.sequence)
    require(rejected.code is Code.BAD_PAYLOAD and rejected.tag == pending.tag and rejected.tx_accepted == 8,
        'Changed bytes with the old sequence were not rejected without TX/owner changes')
    release_request = command(transport._sequence, Opcode.RELEASE, tag=pending.tag)
    held = transport.request(Opcode.RELEASE, tag=pending.tag)
    require(held.code is Code.REJECTED and held.retained,
        'Invalid-sequence request retired unacknowledged RX custody')
    transport._send(release_request)
    replayed = transport._read(release_request.sequence)
    require(replayed.packet == held.packet, 'Exact cached rejected request did not replay its frozen response')
    pending.release()
    return dict(kind='changed_bytes_same_sequence', depth=depth, owner_tag=pending.tag,
        changed_sequence=altered.sequence, changed_request_rejected=True,
        unacknowledged_release_still_rejected=True, rejected_cache_replayed_exactly=True,
        peer=peer.check(pending.rx_bits), changed_reply=asdict(rejected), held_reply=asdict(held))


def rejected_credit(rtl, *, depth):
    transport = QuadTransport(rtl)
    host = StreamHost(transport, depth=depth)
    host.initialize()
    loaded = host.load(spi_image())
    tx, rx, tx_bits, rx_bits = payloads('spi', 512)
    peer = StreamingSPIPeer(tx, rx)
    rtl.device = peer
    pending = loaded.submit(tx_bits)
    for _ in range(8):
        bits = tx_bits[pending.tx_accepted:pending.tx_accepted + 64]
        require(len(bits) == 64, 'Credit fixture exhausted TX before finding a bounded queue rejection')
        request = command(transport._sequence, Opcode.EXCHANGE64, tag=pending.tag,
            tx_offset=pending.tx_accepted, rx_ack=len(pending.rx_bits),
            data=int(''.join('1' if bit else '0' for bit in bits), 2))
        reply = transport.exchange(pending.tag, pending.tx_accepted, len(pending.rx_bits), bits,
            validate=pending._validate_received)
        if reply.code is Code.ACCEPTED:
            pending._received(reply)
        else:
            require(reply.code is Code.REJECTED and reply.tx_accepted == pending.tx_accepted,
                'Credit rejection applied a TX prefix')
            break
    else:
        raise RuntimeError('Credit case never filled its bounded TX queue')
    rejected_prefix = pending.tx_accepted
    transport.idle(4096)
    transport._send(request)
    replay = transport._read(request.sequence)
    require(replay.packet == reply.packet, 'Cached credit rejection was reevaluated instead of replayed')
    probe = transport.request(Opcode.RELEASE, tag=pending.tag)
    require(probe.code is Code.REJECTED and probe.flags & Flags.WAIT_RX,
        'Delayed host service did not expose actual RX backpressure')
    fresh = transport.exchange(pending.tag, pending.tx_accepted, len(pending.rx_bits), bits,
        validate=pending._validate_received)
    require(fresh.code is Code.ACCEPTED and fresh.tx_accepted == rejected_prefix + 64,
        'Fresh sequence failed to reevaluate restored TX credits exactly once')
    pending._received(fresh)
    pending.wait(max_exchanges=100)
    require(pending.rx_bits == rx_bits and pending.tx_accepted == 512,
        'Credit recovery skipped or duplicated protocol data')
    peer_result = peer.check(pending.rx_bits, require_stall=True)
    pending.release()
    return dict(kind='rejected_credit_fresh_sequence', depth=depth, owner_tag=pending.tag,
        rejected_sequence=request.sequence, rejected_tx_prefix=rejected_prefix,
        cached_rejected_replay_exact=True, fresh_sequence=fresh.sequence,
        fresh_sequence_accepted=True, rx_backpressure_observed=True,
        probe=asdict(probe), peer=peer_result)


def retained_tx_ack(rtl, *, depth):
    # The generic compiler/low-level link support receive-only images. The
    # convenience StreamHost intentionally refuses them before any I/O.
    base = spi_image()
    instructions = list(base.source.instructions)
    instructions[1] = Instruction('stream', replace(instructions[1].cell, transmit=False))
    image = lower(tuple(instructions), idle_levels=4, idle_enabled=7)
    validate_image(image)
    transport = QuadTransport(rtl)
    transport.cold_reset()
    for address, word in enumerate(image.words):
        require(transport.request(Opcode.WRITE, address=address, word=word).code is Code.ACCEPTED,
            'Generic receive-only upload failed')
    commit = transport.request(Opcode.COMMIT, count=len(image.words), idle_levels=4, idle_enabled=7)
    require(commit.code is Code.ACCEPTED and commit.valid, 'Generic receive-only COMMIT failed')
    peer = StreamingSPIPeer(b'\x00', b'\xa5')
    rtl.device = peer
    start = transport.request(Opcode.START, expected_generation=commit.generation, bit_count=8)
    require(start.code is Code.ACCEPTED, 'Receive-only START failed')
    exported = transport.exchange(start.tag, 0, 0)
    require(exported.code is Code.ACCEPTED and exported.retained and exported.rx_bits == byte_bits(b'\xa5') and
        exported.tx_accepted == 0 and not exported.rx_queued, 'Fixture lacks retained RX and unused TX room')
    before = transport.request(Opcode.RELEASE, tag=start.tag)
    require(before.code is Code.REJECTED, 'Unacknowledged receive-only export was released')
    offered = transport.exchange(start.tag, 0, 8, byte_bits(b'\x00'))
    require(offered.code is Code.REJECTED and offered.tx_accepted == 0,
        'Retained core admitted nonzero TX')
    after = transport.request(Opcode.RELEASE, tag=start.tag)
    require(after.code is Code.REJECTED and after.retained,
        'Rejected retained TX+ACK retired exported RX custody')
    acknowledged = transport.exchange(start.tag, 0, 8)
    require(acknowledged.code is Code.ACCEPTED and not acknowledged.rx_valid,
        'Explicit zero-TX ACK did not retire exactly the exported interval')
    release = transport.request(Opcode.RELEASE, tag=start.tag)
    require(release.code is Code.ACCEPTED and not release.retained and not release.busy,
        'Matching RELEASE after admitted ACK failed')
    return dict(kind='retained_tx_ack', depth=depth, owner_tag=start.tag,
        retained_tx_offer_rejected=True, rejected_ack_preserved_custody=True,
        explicit_zero_tx_ack_accepted=True, matching_release_accepted=True,
        peer=peer.check(exported.rx_bits), image_words=list(image.words), offered=asdict(offered))


def host_sequence_refusal():
    class NoIO:
        cycle = 0
        def tick(self, **pins):
            self.cycle += 1
            raise RuntimeError('Exhausted host sequence unexpectedly touched I/O')
    maximum = command(65535, Opcode.START, expected_generation=1, bit_count=0)
    require(decode_request(maximum.packet) == maximum, 'Maximum wire sequence does not round-trip')
    backend = NoIO()
    transport = QuadTransport(backend)
    transport._sequence = 65536
    try:
        transport.request(Opcode.START, expected_generation=1, bit_count=0)
    except StreamProtocolError:
        pass
    else:
        raise RuntimeError('Exhausted sequence silently wrapped')
    require(backend.cycle == 0 and transport.inflight is None, 'Exhaustion refusal touched link or captured a request')
    return dict(kind='maximum_sequence_host_only', passed=True, maximum_sequence=65535,
        exhausted_sequence=65536, refused_before_io=True, physical_edges=0,
        scope='Codec and host refusal only; no 65536-transaction device history was simulated')


def run_adversarial(vvp, executable, directory, *, depth):
    directory = Path(directory)
    directory.mkdir(parents=True, exist_ok=False)
    cases = []
    for kind in ('overlong_response', 'partial_request', 'overlong_request'):
        result = physical_case(vvp, executable, directory / kind,
            lambda rtl, kind=kind: recover_frames(rtl, depth=depth, kind=kind))
        result['case'] = kind
        cases.append(result)
    for kind, operation in [('changed_bytes_same_sequence', changed_sequence),
            ('rejected_credit_fresh_sequence', rejected_credit), ('retained_tx_ack', retained_tx_ack)]:
        result = physical_case(vvp, executable, directory / kind, lambda rtl, operation=operation: operation(rtl, depth=depth))
        result['case'] = kind
        cases.append(result)
    cases.append(host_sequence_refusal())
    result = dict(schema='pinwheel.streaming-quad-adversarial.v1', depth=depth,
        passed=all(case.get('passed') is True for case in cases), cases=cases,
        physical_edges=sum(case.get('physical_edges', 0) for case in cases))
    if result['passed']:
        check_adversarial(result)
    (directory / 'report.json').write_text(json.dumps(result, indent=2) + '\n')
    return result


def check_adversarial(result):
    expected = ['overlong_response', 'partial_request', 'overlong_request',
        'changed_bytes_same_sequence', 'rejected_credit_fresh_sequence', 'retained_tx_ack',
        'maximum_sequence_host_only']
    cases = result.get('cases', [])
    if (result.get('schema') != 'pinwheel.streaming-quad-adversarial.v1' or
            result.get('depth') not in (2, 4) or result.get('passed') is not True or
            [case.get('case', case.get('kind')) for case in cases] != expected):
        raise ValueError('Incomplete additional adversarial corpus')
    for index, case in enumerate(cases):
        if case.get('passed') is not True:
            raise ValueError('Failed adversarial control')
        if index == 6:
            if (case.get('maximum_sequence') != 65535 or case.get('exhausted_sequence') != 65536 or
                    case.get('refused_before_io') is not True or case.get('physical_edges') != 0):
                raise ValueError('Maximum sequence must be a host-only refusal before I/O')
            continue
        trace = case.get('trace', {})
        edges = case.get('physical_edges', 0)
        if (edges <= 0 or edges != trace.get('edges') or trace.get('bytes') != edges * 20 or
                not re.fullmatch(r'[0-9a-f]{64}', trace.get('sha256', '')) or case.get('owner_tag') != 65537):
            raise ValueError('Adversarial physical trace/owner is missing or inconsistent')
        peer = case.get('peer', {})
        bits = 32 if index < 3 else 512 if index == 4 else 8
        if (peer.get('bits') != bits or peer.get('clock_edges') != bits * 2 or
                peer.get('high_phase_edges') != [4] or peer.get('continuous_cs') is not True):
            raise ValueError('Independent peer did not establish the requested physical transfer')
        if index < 3:
            if (case.get('same_sequence_recovery') is not True or case.get('exact_tx_prefix_once') is not True or
                    case.get('original_sequence') != case.get('recovery_sequence') or
                    case.get('recoveries', 0) <= 0 or
                    [fault.get('kind') for fault in case.get('faults', [])] != [expected[index]]):
                raise ValueError('Malformed frame did not recover the same request exactly once')
            if index == 0 and case.get('ready_retention_checked') is not True:
                raise ValueError('Overlong read did not exercise retained READY')
        elif index == 3:
            if any(case.get(field) is not True for field in ('changed_request_rejected',
                    'unacknowledged_release_still_rejected', 'rejected_cache_replayed_exactly')):
                raise ValueError('Changed-sequence/cached-rejection controls missing')
        elif index == 4:
            if (any(case.get(field) is not True for field in ('cached_rejected_replay_exact',
                    'fresh_sequence_accepted', 'rx_backpressure_observed')) or
                    case.get('fresh_sequence', 0) <= case.get('rejected_sequence', 65535) or
                    not case.get('probe', {}).get('flags', 0) & Flags.WAIT_RX or
                    peer.get('low_extra_edges', 0) <= 0):
                raise ValueError('Credit case did not distinguish replay, retry and actual RX stalls')
        elif any(case.get(field) is not True for field in ('retained_tx_offer_rejected',
                'rejected_ack_preserved_custody', 'explicit_zero_tx_ack_accepted', 'matching_release_accepted')):
            raise ValueError('Retained rejected TX+ACK custody boundary missing')
    if result.get('physical_edges') != sum(case['physical_edges'] for case in cases):
        raise ValueError('Adversarial aggregate physical edge count differs')
