"""Finite public-pin streaming RTL corpus, separate from source execution.

Expected protocol bits come from independent deterministic peer payloads. The
host accesses the chip only through the sampled quad link. Binary edge traces
record each pre-edge MISO/raw-input sample and post-edge pads/status; no private
RTL hierarchy, queue model or source execution result is used as an oracle.
"""
from dataclasses import asdict
import hashlib
from pathlib import Path
import struct
import time

from streaming_compile import jtag_image, spi_image
from streaming_peers import StreamingJTAGPeer, StreamingSPIPeer
from streaming_rtl import QuadRTL
from streaming_transport import (Code, Flags, Opcode, QuadTransport, StreamHost,
    StreamProtocolError, StreamTransportError, byte_bits, jtag_bits)


def require(value, message):
    if not value:
        raise RuntimeError(message)


class FaultLink:
    """Inject specified link errors above the real public-pin RTL backend.

    Errors occur after actual sampled edges. A response-bit corruption changes
    only the host's received observation. Request corruption changes one real
    MOSI CRC nibble. Neither reads engine state nor changes the peer stimulus.
    """
    def __init__(self, rtl):
        self.rtl = rtl
        self.mode, self.count = None, 0
        self.csn, self.sck = 1, 0
        self.armed, self.triggered = None, []

    @property
    def cycle(self): return self.rtl.cycle

    def cold_reset(self):
        self.rtl.cold_reset()
        self.mode, self.count, self.csn, self.sck, self.armed = None, 0, 1, 0, None

    def arm(self, kind):
        if self.armed is not None or kind not in ('request_crc', 'response_crc', 'partial_read', 'request_close'):
            raise ValueError('Expected one supported pending link fault')
        self.armed = kind

    def tick(self, *, csn, sck, mosi):
        if self.csn and not csn:
            ready = self.rtl.snapshot.ready if self.rtl.snapshot is not None else False
            self.mode, self.count = ('read' if ready else 'request'), 0
        rising = not csn and sck and not self.sck
        closing = not self.csn and csn
        mode = self.mode
        injected = None
        if self.armed == 'request_crc' and mode == 'request' and rising and self.count == 43:
            mosi ^= 1
            injected = self.armed
        result = self.rtl.tick(csn=csn, sck=sck, mosi=mosi)
        if rising:
            self.count += 1
        self.csn, self.sck = csn, sck
        if closing:
            self.mode = None
        if self.armed == 'response_crc' and mode == 'read' and rising and self.count == 11:
            result['miso'] ^= 1
            injected = self.armed
        if self.armed == 'partial_read' and mode == 'read' and rising and self.count == 7:
            injected = self.armed
        if self.armed == 'request_close' and closing and mode == 'request':
            injected = self.armed
        if injected is not None:
            self.triggered.append(dict(kind=injected, physical_edge=self.cycle))
            self.armed = None
            if injected in ('partial_read', 'request_close'):
                raise OSError('Injected link acknowledgement loss after an actual edge: ' + injected)
        return result


class EdgeTrace:
    """Little-endian uint32 edge number then16 uint8 public fields per edge."""
    FORMAT = 'u32 cycle; u8 initialize,csn,sck,mosi,peerLevels,peerEnabled,links,pullups,' \
        'preMiso,postReady,postBusy,postLevels,postEnabled,postWires,postKnown,preRaw'

    def __init__(self, path):
        self.stream = Path(path).open('xb')
        self.hash, self.edges = hashlib.sha256(), 0

    def __call__(self, record):
        p, d, o = record['pins'], record['drive'], record['observation']
        values = [p[name] for name in ('initialize', 'csn', 'sck', 'mosi')]
        values += [d[name] for name in ('levels', 'enabled', 'links', 'pullups')]
        values += [o[name] for name in ('miso', 'ready', 'busy', 'levels', 'enabled', 'wires', 'known', 'edge_inputs')]
        block = struct.pack('<I16B', record['cycle'], *values)
        self.stream.write(block)
        self.hash.update(block)
        self.edges += 1

    def close(self):
        self.stream.close()
        return dict(edges=self.edges, sha256=self.hash.hexdigest(), bytes=self.edges * 20,
            format=self.FORMAT)


def payloads(protocol, bits):
    size = (bits + 7) // 8
    tx = bytes(((k * 73 + 19) ^ (k >> 3)) & 255 for k in range(size))
    rx = bytes(((k * 151 + 165) ^ (k >> 2)) & 255 for k in range(size))
    if protocol == 'spi':
        if bits % 8:
            raise ValueError('SPI corpus transfers whole bytes')
        return tx, rx, byte_bits(tx), byte_bits(rx)
    if protocol != 'jtag' or not 1 <= bits <= 65535:
        raise ValueError('Expected SPI or a positive finite JTAG scan')
    if bits % 8:
        mask = (1 << (bits % 8)) - 1
        tx, rx = tx[:-1] + bytes([tx[-1] & mask]), rx[:-1] + bytes([rx[-1] & mask])
    return tx, rx, jtag_bits(tx, bits), jtag_bits(rx, bits)


def packed_bits(bits, *, msb_first):
    output = bytearray((len(bits) + 7) // 8)
    for index, bit in enumerate(bits):
        output[index // 8] |= int(bit) << (7 - index % 8 if msb_first else index % 8)
    return bytes(output)


def recover_owned(pending, operation):
    try:
        return operation()
    except StreamTransportError as error:
        require(error.pending is pending, 'Uncertain operation lost its original stream owner')
        for _ in range(3):
            try:
                return pending.recover()
            except StreamTransportError:
                pass
        raise RuntimeError('Exact in-flight recovery did not converge within the specified fault case') from error


def run_stream(vvp, executable, directory, *, protocol, bits, depth, fault=None, delays=True):
    directory = Path(directory)
    directory.mkdir(parents=True, exist_ok=False)
    tx, rx, tx_bits, rx_bits = payloads(protocol, bits)
    (directory / 'tx.bin').write_bytes(tx)
    (directory / 'rx-expected.bin').write_bytes(rx)
    trace = EdgeTrace(directory / 'wire.bin')
    started = time.monotonic()
    receipts, peer, pending = [], None, None
    try:
        with QuadRTL(vvp, executable, record_sink=trace) as rtl:
            link = FaultLink(rtl)
            transport = QuadTransport(link)
            host = StreamHost(transport, depth=depth)
            host.initialize()
            image = spi_image() if protocol == 'spi' else jtag_image()
            loaded = host.load(image)
            peer = (StreamingSPIPeer(tx, rx) if protocol == 'spi' else
                StreamingJTAGPeer(int.from_bytes(tx, 'little'), int.from_bytes(rx, 'little'), bits))
            rtl.device = peer
            if fault == 'request_close': link.arm(fault)
            try:
                pending = loaded.submit(tx_bits)
            except StreamTransportError as error:
                pending = error.pending
                require(pending is not None, 'START acknowledgement loss lost its owner handle')
                pending.recover()
            receipts.append(asdict(pending.last))
            if delays and bits:
                transport.idle(512)
                receipts.append(asdict(pending.pump(max_bits=0)))
                require(pending.last.flags & Flags.WAIT_TX, 'Initial starvation did not expose WAIT_TX')
            if fault in ('request_crc', 'response_crc', 'partial_read'): link.arm(fault)
            maximum = max(20, (bits + 31) // 32 * 3 + 20)
            for index in range(maximum):
                if pending.last.retained and not pending.last.rx_queued and len(pending.rx_bits) == bits:
                    break
                recover_owned(pending, pending.pump)
                receipts.append(asdict(pending.last))
                if delays and index == 2 and bits > 128:
                    # No protocol-specific scheduler: delayed host service can
                    # exhaust either bounded queue while physical SCK stays LOW.
                    transport.idle(4096)
            else:
                raise RuntimeError('Finite public-wire exchange budget expired')
            require(not pending.last.fault, 'Certified image ended in a fault')
            require(pending.tx_accepted == bits, 'Host did not submit the complete TX prefix')
            require(pending.rx_bits == rx_bits, 'Independent expected RX differs from host prefix')
            require(all(r['rx_valid'] <= 32 for r in receipts), 'Frontend exported more than one queued RX word')
            peer_result = peer.check(pending.rx_bits, require_stall=delays and bits > 128)
            before_tag = pending.tag
            released = pending.release()
            require(released.tag == before_tag and not released.busy and not released.retained,
                'Matching RELEASE did not restore the free slot')
            require(transport.transactions == transport._sequence, 'Host sequence count differs from allocated requests')
            (directory / 'rx-actual.bin').write_bytes(packed_bits(pending.rx_bits, msb_first=protocol == 'spi'))
            require((directory / 'rx-actual.bin').read_bytes() == rx, 'RX byte packing differs')
            if fault is not None:
                require([x['kind'] for x in link.triggered] == [fault], 'Specified real-wire fault was not exercised exactly once')
                require(transport.recoveries > 0, 'Fault case did not perform exact in-flight recovery')
            result = dict(passed=True, protocol=protocol, bits=bits, depth=depth, fault=fault,
                owner_tag=before_tag, start_count=transport.opcode_counts[Opcode.START],
                opcode_counts={op.name: count for op, count in transport.opcode_counts.items()}, image_words=list(image.words),
                tx_sha256=hashlib.sha256(tx).hexdigest(), rx_sha256=hashlib.sha256(rx).hexdigest(),
                peer=peer_result, physical_edges=rtl.cycle, requests=transport.transactions,
                request_frames=transport.request_frames, response_frames=transport.response_frames,
                recoveries=transport.recoveries, faults=link.triggered,
                exchange_rx_max=max(r['rx_valid'] for r in receipts), receipts=receipts,
                release=asdict(released))
    except Exception as error:
        result = dict(passed=False, protocol=protocol, bits=bits, depth=depth, fault=fault,
            error=repr(error), receipts=receipts)
    finally:
        record = trace.close()
    result.update(trace=record, elapsed_seconds=time.monotonic() - started)
    return result


def run_custody(vvp, executable, directory, *, depth):
    """Retained exported RX survives rejected commands and exact replays.

    This uses actual RELEASE admission to distinguish cached receipt custody
    from an empty core RX FIFO. A second START reuses the same loaded program,
    generation, host and hardware transfer allocator.
    """
    directory = Path(directory)
    directory.mkdir(parents=True, exist_ok=False)
    trace = EdgeTrace(directory / 'wire.bin')
    started, receipts = time.monotonic(), []
    try:
        with QuadRTL(vvp, executable, record_sink=trace) as rtl:
            transport = QuadTransport(rtl)
            host = StreamHost(transport, depth=depth)
            host.initialize()
            loaded = host.load(spi_image())
            tags, peer_results = [], []
            for round_index in range(2):
                tx, rx = bytes([0x96 ^ round_index]), bytes([0xa5 ^ round_index])
                peer = StreamingSPIPeer(tx, rx)
                rtl.device = peer
                pending = loaded.submit(byte_bits(tx))
                pending.wait(max_exchanges=20)
                require(pending.last.retained and pending.last.rx_valid == 8 and not pending.last.rx_queued,
                    'Custody fixture must have exported RX and an empty retained core FIFO')
                tags.append(pending.tag)
                peer_results.append(peer.check(pending.rx_bits))
                if round_index == 0:
                    # Empty core queues are insufficient: the frontend still
                    # owns an exported interval that the next request must ACK.
                    unacked = transport.request(Opcode.RELEASE, tag=pending.tag)
                    receipts.append(asdict(unacked))
                    require(unacked.code is Code.REJECTED and unacked.retained,
                        'RELEASE incorrectly discarded unacknowledged exported RX')
                    wrong = transport.exchange(pending.tag, 7, 8)
                    receipts.append(asdict(wrong))
                    require(wrong.code is Code.REJECTED, 'Wrong TX offset was admitted')
                    wrong_ack = transport.exchange(pending.tag, 8, 0)
                    receipts.append(asdict(wrong_ack))
                    require(wrong_ack.code is Code.REJECTED, 'Old RX acknowledgement was admitted')
                    again = transport.request(Opcode.RELEASE, tag=pending.tag)
                    receipts.append(asdict(again))
                    require(again.code is Code.REJECTED and again.retained,
                        'Rejected requests silently acknowledged exported RX')
                    pending.pump(max_bits=0)
                    require(not pending.last.rx_valid and pending.last.rx_start == 8,
                        'Final RX acknowledgement did not retire exactly the exported interval')
                    stale = transport.request(Opcode.RELEASE, tag=pending.tag ^ 1)
                    receipts.append(asdict(stale))
                    require(stale.code is Code.REJECTED, 'Stale owner RELEASE was admitted')
                release = pending.release()
                receipts.append(asdict(release))
                require(not release.retained and not release.busy, 'Final ACK and matching RELEASE did not free owner')
            require(tags[1] == tags[0] + 1 and tags[1] >> 16 == tags[0] >> 16,
                'Repeated START did not preserve generation and increment the one transfer allocator')
            before = rtl.cycle
            try:
                pending.pump()
            except StreamProtocolError:
                pass
            else:
                raise RuntimeError('Released host handle was reused')
            require(rtl.cycle == before, 'Stale local owner refusal touched the wire')
            host.warm_reset()
            before = rtl.cycle
            try:
                loaded.submit(byte_bits(b'\x96'))
            except StreamProtocolError:
                pass
            else:
                raise RuntimeError('Pre-reset image handle was reused')
            require(rtl.cycle == before, 'Stale image refusal touched the wire')
            result = dict(passed=True, depth=depth, tags=tags, peer_results=peer_results,
                receipts=receipts, unacknowledged_release_rejected=True,
                rejected_request_custody_preserved=True, stale_owner_rejected=True,
                same_image_two_starts=True, stale_local_owner_no_io=True, stale_image_no_io=True,
                physical_edges=rtl.cycle, requests=transport.transactions)
    except Exception as error:
        result = dict(passed=False, depth=depth, error=repr(error), receipts=receipts)
    finally:
        record = trace.close()
    result.update(trace=record, elapsed_seconds=time.monotonic() - started)
    return result
