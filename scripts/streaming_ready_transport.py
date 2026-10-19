"""Host ownership and I2C slot packing for the separate sampled-ready target.

The quad framing implementation is shared unchanged. Ready images have their
own validator, and a START carries the total stream-cell count independently of
whether that stream transmits, receives, or does both.
"""
from dataclasses import dataclass

from streaming_transport import (Code, MAX_BITS, Opcode, PendingStream, StreamHost,
    StreamProtocolError, StreamRejected, StreamTransportError, require_accepted, uint)


@dataclass(frozen=True)
class LoadedReady:
    host: object
    image: object
    epoch: int
    generation: int

    def submit(self, tx_bits=(), *, bit_count=None):
        return self.host._submit(self, tx_bits, bit_count=bit_count)


class ReadyHost(StreamHost):
    def load(self, image):
        from streaming_ready_compile import validate_image
        validate_image(image)  # Revalidate before even checking/opening the link.
        if self._pending is not None:
            raise StreamProtocolError('Release or explicitly reset the current Ready owner before loading')
        self._epoch += 1
        for address, word in enumerate(image.words):
            self._last = require_accepted(self.transport.request(Opcode.WRITE, address=address, word=word))
        self._last = require_accepted(self.transport.request(Opcode.COMMIT, count=len(image.words),
            idle_levels=image.idle_levels, idle_enabled=image.idle_enabled))
        if not self._last.valid:
            raise StreamProtocolError('Ready COMMIT did not establish a valid image')
        return LoadedReady(self, image, self._epoch, self._last.generation)

    def _submit(self, loaded, bits=(), *, bit_count=None):
        if loaded.host is not self or loaded.epoch != self._epoch or self._pending is not None:
            raise StreamProtocolError('Stale Ready image or unreleased stream owner')
        if type(bits) is not tuple or any(type(bit) is not bool for bit in bits):
            raise ValueError('Ready TX bits must be an immutable Boolean tuple')
        image = loaded.image
        from streaming_ready_compile import validate_image
        validate_image(image)
        cell = image.source.instructions[image.certificate.stream_row].cell
        total = len(bits) if bit_count is None else uint(bit_count, 16, 'Ready cell count')
        if not 0 <= total <= MAX_BITS:
            raise ValueError('Ready cell count exceeds the wire bound')
        if (cell.transmit and len(bits) != total) or (not cell.transmit and bits):
            raise ValueError('Ready TX payload does not match the stream transmit mode and cell count')
        if bit_count is None and not cell.transmit:
            raise ValueError('A stream without TX requires an explicit cell count')
        pending = ReadyPending(self, loaded, bits, total=total,
            transmit=cell.transmit, receive=cell.receive)
        self._pending = pending
        try:
            receipt = self.transport.request(Opcode.START, expected_generation=loaded.generation,
                bit_count=total, validate=pending._validate_started)
            pending._started(require_accepted(receipt))
        except StreamTransportError as error:
            raise StreamTransportError(error.cause, pending) from error
        except Exception:
            self._pending = None
            raise
        return pending


class ReadyPending(PendingStream):
    def __init__(self, host, loaded, bits, *, total, transmit, receive):
        super().__init__(host, loaded, bits)
        self.total_bits = total
        self.expected_tx = total if transmit else 0
        self.expected_rx = total if receive else 0
        self.terminal_retries = []
        self._offered = 0

    def _validate_received(self, receipt):
        if receipt.tag != self.tag or not self.tx_accepted <= receipt.tx_accepted <= self.expected_tx:
            raise StreamProtocolError('Ready receipt has a stale owner or invalid TX accepted offset')
        if receipt.tx_accepted != self.tx_accepted + self._offered:
            raise StreamProtocolError('Ready receipt differs from the complete admitted TX reservation')
        if receipt.tx_free > self.host.depth or receipt.rx_queued > self.host.depth:
            raise StreamProtocolError('Ready queue counts exceed the configured depth')
        if receipt.rx_start != len(self.rx_bits) or receipt.rx_end > self.expected_rx:
            raise StreamProtocolError('Ready receipt duplicates, skips or exceeds the expected RX interval')

    def _terminal_retry(self, error, offered):
        """One fresh empty exchange after a demonstrable terminal TX rejection.

        The rejected offer is never treated as accepted. Its reply must retain
        this exact owner and accepted TX prefix. Its RX presentation must be
        either the unchanged cached interval or a canonical empty diagnostic
        at the collected end. An empty request can then acknowledge the held
        export and learn/drain terminal RX; rejected data is never appended.
        """
        reply, old = error.receipt, self.last
        if not (offered and old is not None and old.busy and reply.code is Code.REJECTED and
                reply.tag == self.tag and reply.retained and reply.fault and
                reply.tx_accepted == self.tx_accepted and
                (reply.rx_start, reply.rx_valid, reply.data) in (
                    (old.rx_start, old.rx_valid, old.data), (len(self.rx_bits), 0, 0)) and
                reply.tx_free <= self.host.depth and reply.rx_queued <= self.host.depth):
            raise error
        before_tx, before_rx = self.tx_accepted, len(self.rx_bits)
        self._offered = 0
        receipt = super().pump(max_bits=0)
        self.terminal_retries.append(dict(rejected_sequence=reply.sequence, empty_sequence=receipt.sequence,
            owner_tag=self.tag, unchanged_tx_accepted=before_tx, acknowledged_rx_end=before_rx))
        if receipt.tx_accepted != before_tx:
            raise StreamProtocolError('Empty terminal retry unexpectedly accepted TX')
        return receipt

    def pump(self, *, max_bits=64):
        offered = (min(len(self.tx_bits) - self.tx_accepted, max_bits,
            64 if self.last.tx_free >= 2 else 32 if self.last.tx_free else 0)
            if self.last is not None and self.last.busy and type(max_bits) is int and max_bits in (0, 32, 64) else 0)
        self._offered = offered
        try:
            return super().pump(max_bits=max_bits)
        except StreamRejected as error:
            return self._terminal_retry(error, offered)

    def wait(self, *, max_exchanges=100000):
        if type(max_exchanges) is not int or max_exchanges < 0:
            raise ValueError('Ready exchange budget must be a nonnegative integer')
        self._local()
        for _ in range(max_exchanges):
            if self.last is not None and self.last.retained and not self.last.rx_queued:
                if self.last.fault:
                    return self.last
                if len(self.rx_bits) == self.expected_rx:
                    if self.tx_accepted != self.expected_tx:
                        raise StreamProtocolError('Completed Ready stream has an incomplete accepted TX prefix')
                    return self.last
            self.pump()
        raise TimeoutError('Ready exchange budget expired; owner remains live')

    def release(self):
        try:
            return super().release()
        except StreamRejected:
            self._operation = None
            raise

    def recover(self):
        request, operation = self.host.transport.inflight, self._operation
        try:
            return super().recover()
        except StreamRejected as error:
            self._operation = None
            offered = 0
            if operation == 'exchange' and request is not None:
                requested = {Opcode.EXCHANGE32: 32, Opcode.EXCHANGE64: 64}.get(request.opcode, 0)
                offered = min(requested, self.expected_tx - self.tx_accepted)
            return self._terminal_retry(error, offered)


def byte_bits(byte):
    return tuple(bool((byte >> bit) & 1) for bit in range(7, -1, -1))


@dataclass(frozen=True)
class I2cPlan:
    address: int
    direction: str
    length: int
    write_data: bytes = b''

    def __post_init__(self):
        uint(self.address, 7, 'I2C address')
        if self.direction not in ('read', 'write') or type(self.length) is not int or not 1 <= self.length <= MAX_BITS // 9 - 1:
            raise ValueError('I2C needs a positive byte count within the START cell bound')
        if type(self.write_data) is not bytes or (
                len(self.write_data) != self.length if self.direction == 'write' else bool(self.write_data)):
            raise ValueError('I2C write payload differs from the declared direction/length')

    @property
    def tx_bits(self):
        result = list(byte_bits((self.address << 1) | (self.direction == 'read')))
        result.append(True)  # Target owns the address acknowledgment.
        if self.direction == 'write':
            for value in self.write_data:
                result.extend(byte_bits(value))
                result.append(True)
        else:
            for index in range(self.length):
                result.extend((True,) * 8)
                result.append(index == self.length - 1)  # ACK0, final NACK1.
        return tuple(result)

    @property
    def bit_count(self): return (self.length + 1) * 9


def pack_write(address, data):
    if type(data) is not bytes:
        raise ValueError('I2C write data must be bytes')
    return I2cPlan(address, 'write', len(data), data)


def pack_read(address, length): return I2cPlan(address, 'read', length)


@dataclass(frozen=True)
class I2cResult:
    raw_bits: tuple
    address_ack: bool | None
    data: bytes
    acknowledgements: tuple
    partial_data_bits: tuple
    complete: bool
    fault: bool
    payload_valid: bool


def project(plan, raw_prefix, *, fault=False):
    """Project complete bytes while preserving the exact unmodified RX prefix.

    Address NACK invalidates payload, even if a read observed sixty-four FFs.
    A fault can expose complete preceding bytes and an explicit partial byte;
    it never becomes a successful completed transaction.
    """
    if type(plan) is not I2cPlan or type(raw_prefix) is not tuple or type(fault) is not bool or (
            any(type(bit) is not bool for bit in raw_prefix) or len(raw_prefix) > plan.bit_count):
        raise ValueError('I2C projection requires a bounded immutable Boolean RX prefix')
    tx = plan.tx_bits
    for index, value in enumerate(raw_prefix):
        master = index < 8 or (index >= 9 and ((index - 9) % 9 == 8 if plan.direction == 'read' else
            (index - 9) % 9 < 8))
        if master and value != tx[index]:
            raise StreamProtocolError('I2C sampled echo differs from a master-owned slot')
    address_ack = not raw_prefix[8] if len(raw_prefix) >= 9 else None
    acknowledgements = tuple(not raw_prefix[index] for index in range(8, len(raw_prefix), 9))
    data, partial = bytearray(), ()
    for index in range(plan.length):
        bits = raw_prefix[9 + index * 9:17 + index * 9]
        if len(bits) < 8:
            partial = bits
            break
        data.append(sum(int(bit) << (7 - offset) for offset, bit in enumerate(bits)))
    complete = len(raw_prefix) == plan.bit_count
    accepted = address_ack is True and (plan.direction == 'read' or all(acknowledgements))
    return I2cResult(raw_prefix, address_ack, bytes(data) if address_ack else b'', acknowledgements,
        partial if address_ack else (), complete, fault, bool(complete and not fault and accepted))
