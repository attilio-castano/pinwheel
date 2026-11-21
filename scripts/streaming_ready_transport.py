"""Shared host ownership and I2C slot packing for the sampled-ready target.

The quad framing implementation is shared unchanged. Ready images have their
own validator, and a START carries the total stream-cell count independently of
whether that stream transmits, receives, or does both.
"""
from dataclasses import dataclass

from streaming_transport import (Code, MAX_BITS, Opcode, PendingStream, Receipt, StreamHost,
    StreamProtocolError, StreamRejected, StreamTransportError, require_accepted, uint)


REGISTER_READ_SCHEMA = 'pinwheel.ready-register-read.v1'
REGISTER_READ_NACKS = ('write-address-nack', 'register-nack', 'read-address-nack')
REGISTER_READ_EXITS = frozenset({('complete', 36, 36), ('discard', 27, 27),
                                ('discard', 18, 18), ('discard', 9, 9)})


@dataclass(frozen=True)
class CombinedI2cResult:
    outcome: str
    byte: int | None = None


@dataclass(frozen=True)
class CombinedI2cRead:
    """Inputs to an already checked Lean image.

    The source gate binds the image words and exits to the Lean checker.
    This reader validates the transport metadata and request plan.
    """
    words: tuple[int, ...]
    address: int
    register: int
    tx_bits: tuple[bool, ...]
    exits: tuple[tuple[str, int, int], ...]
    tx_budget: int
    wait_budget: int
    idle_levels: int
    idle_enabled: int

    @classmethod
    def from_manifest(cls, manifest):
        if type(manifest) is not dict or manifest.get('schema') != REGISTER_READ_SCHEMA:
            raise ValueError('Unsupported Ready register read manifest')
        try:
            exits = manifest['exits']
            if type(exits) is not list or any(type(exit_) is not dict for exit_ in exits):
                raise ValueError('Expected Ready register read exit records')
            image = cls(tuple(manifest['words']), manifest['address'], manifest['register'],
                       tuple(manifest['tx_bits']), tuple((exit_['kind'], exit_['tx'], exit_['rx']) for exit_ in exits),
                       manifest['tx_budget'], manifest['wait_budget'], manifest['idle_levels'], manifest['idle_enabled'])
        except (KeyError, TypeError) as error:
            raise ValueError('Malformed Ready register read manifest') from error
        image.validate()
        return image

    def validate(self):
        uint(self.address, 7, 'Register read address')
        uint(self.register, 8, 'Register read register')
        uint(self.tx_budget, 16, 'Register read TX budget')
        uint(self.wait_budget, 8, 'Register read wait budget')
        if not self.wait_budget or uint(self.idle_levels, 3, 'Idle levels') or uint(self.idle_enabled, 3, 'Idle enables'):
            raise ValueError('Register read requires bounded guards and released idle pads')
        if type(self.words) is not tuple or not 1 <= len(self.words) <= 64:
            raise ValueError('Register read requires 1..64 immutable image words')
        for word in self.words:
            uint(word, 64, 'Register read word')
        expected = tuple(bit for byte in (self.address << 1, self.register, (self.address << 1) | 1)
                         for bit in (*byte_bits(byte), True)) + (True,) * 9
        if (type(self.tx_bits) is not tuple or any(type(bit) is not bool for bit in self.tx_bits) or
                self.tx_bits != expected or self.tx_budget != len(expected)):
            raise ValueError('Register read TX plan differs from the declared request')
        if (type(self.exits) is not tuple or len(self.exits) != 4 or any(
                type(exit_) is not tuple or len(exit_) != 3 or type(exit_[0]) is not str or
                type(exit_[1]) is not int or type(exit_[2]) is not int for exit_ in self.exits) or
                set(self.exits) != REGISTER_READ_EXITS):
            raise ValueError('Register read exits differ from the declared protocol')

    def project(self, rx, accepted, *, fault):
        """Decode chronological captures and account for accepted TX at a checked exit."""
        for index, bit in enumerate(rx):
            if ((index < 27 and index % 9 < 8) or index == 35) and bit != self.tx_bits[index]:
                raise StreamProtocolError('Register read sampled echo differs from a master-owned slot')
        nack = next(((index, outcome) for index, outcome in zip((8, 17, 26), REGISTER_READ_NACKS)
                     if index < len(rx) and rx[index]), None)
        extent = nack[0] + 1 if nack else self.tx_budget
        if len(rx) > extent or len(rx) > accepted:
            raise StreamProtocolError('Register read RX extends beyond accepted TX or a NACK boundary')
        if fault:
            return CombinedI2cResult('deadline'), None
        kind = 'discard' if nack else 'complete'
        exit_ = next((tx for mode, tx, captured in self.exits if mode == kind and captured == len(rx)), None)
        if len(rx) != extent or exit_ is None or accepted < exit_:
            raise StreamProtocolError('Register read completed with an invalid RX prefix or TX count')
        if nack:
            return CombinedI2cResult(nack[1]), exit_
        byte = sum(int(bit) << (7 - index) for index, bit in enumerate(rx[27:35]))
        return CombinedI2cResult('read', byte), exit_


@dataclass(frozen=True)
class ReadyCompletion:
    terminal: Receipt
    release: Receipt | None
    rx_bits: tuple[bool, ...]
    result: CombinedI2cResult | tuple[bool, ...] | None
    tx_consumed: int | None
    tx_cancelled: int | None


def validate_ready_image(image):
    if type(image) is CombinedI2cRead:
        image.validate()
    else:
        from streaming_ready_compile import validate_image
        validate_image(image)


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
        validate_ready_image(image)  # Revalidate before even checking/opening the link.
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
        validate_ready_image(image)
        if type(image) is CombinedI2cRead:
            if bits or bit_count is not None:
                raise ValueError('A compiled register read supplies its own TX plan and cell count')
            plan = dict(bits=image.tx_bits, total=image.tx_budget, transmit=True, receive=True)
        else:
            plan = self._stream_plan(image, bits, bit_count)
        pending = ReadyPending(self, loaded, **plan)
        self._pending = pending
        try:
            receipt = self.transport.request(Opcode.START, expected_generation=loaded.generation,
                bit_count=pending.total_bits, validate=pending._validate_started)
            pending._started(require_accepted(receipt))
        except StreamTransportError as error:
            raise StreamTransportError(error.cause, pending) from error
        except Exception:
            self._pending = None
            raise
        return pending

    def _stream_plan(self, image, bits, bit_count):
        cell = image.source.instructions[image.certificate.stream_row].cell
        total = len(bits) if bit_count is None else uint(bit_count, 16, 'Ready cell count')
        if not 0 <= total <= MAX_BITS:
            raise ValueError('Ready cell count exceeds the wire bound')
        if (cell.transmit and len(bits) != total) or (not cell.transmit and bits):
            raise ValueError('Ready TX payload does not match the stream transmit mode and cell count')
        if bit_count is None and not cell.transmit:
            raise ValueError('A stream without TX requires an explicit cell count')
        return dict(bits=bits, total=total, transmit=cell.transmit, receive=cell.receive)


class ReadyPending(PendingStream):
    def __init__(self, host, loaded, bits, *, total, transmit, receive):
        super().__init__(host, loaded, bits)
        self.total_bits = total
        self.expected_tx = total if transmit else 0
        self.expected_rx = total if receive else 0
        self.terminal_retries = []
        self._offered = 0

    def _validate_started(self, receipt):
        super()._validate_started(receipt)
        if receipt.rx_start or not (receipt.busy or receipt.retained):
            raise StreamProtocolError('START must establish an owner with an empty RX prefix')

    def _validate_received(self, receipt):
        if receipt.tag != self.tag or not self.tx_accepted <= receipt.tx_accepted <= self.expected_tx:
            raise StreamProtocolError('Ready receipt has a stale owner or invalid TX accepted offset')
        if not receipt.valid or not (receipt.busy or receipt.retained):
            raise StreamProtocolError('Ready exchange receipt must retain an installed owner')
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
        can_end_early = type(self.loaded.image) is CombinedI2cRead
        if not (offered and old is not None and old.busy and reply.code is Code.REJECTED and
                reply.tag == self.tag and reply.valid and reply.retained and (reply.fault or can_end_early) and
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
        self._local()
        if self._operation is not None or self.host.transport.inflight is not None:
            raise StreamProtocolError('Recover the uncertain Ready operation first')
        offered = (min(len(self.tx_bits) - self.tx_accepted, max_bits,
            64 if self.last.tx_free >= 2 else 32 if self.last.tx_free else 0)
            if self.last is not None and self.last.busy and type(max_bits) is int and max_bits in (0, 32, 64) else 0)
        self._offered = offered
        try:
            return super().pump(max_bits=max_bits)
        except StreamRejected as error:
            return self._terminal_retry(error, offered)

    def _outcome(self, receipt):
        image = self.loaded.image
        if type(image) is CombinedI2cRead:
            return image.project(self.rx_bits, self.tx_accepted, fault=receipt.fault)
        if receipt.fault:
            return None, None
        if self.tx_accepted != self.expected_tx or len(self.rx_bits) != self.expected_rx:
            raise StreamProtocolError('Completed Ready stream has an incomplete TX or RX prefix')
        return self.rx_bits, self.expected_tx

    def wait(self, *, max_exchanges=100000):
        if type(max_exchanges) is not int or max_exchanges < 0:
            raise ValueError('Ready exchange budget must be a nonnegative integer')
        self._local()
        for used in range(max_exchanges + 1):
            if self.last is not None and self.last.retained and not self.last.rx_queued:
                self._outcome(self.last)
                return self.last
            if used == max_exchanges:
                break
            self.pump()
        raise TimeoutError('Ready exchange budget expired; owner remains live')

    def _acknowledge_terminal(self):
        self._local()
        if self.last is None or not self.last.retained or self.last.rx_queued:
            raise StreamProtocolError('Expected a drained retained Ready owner')
        self._outcome(self.last)
        fault = self.last.fault
        receipt = self.pump(max_bits=0)
        if not receipt.retained or receipt.fault != fault or receipt.rx_queued or receipt.rx_valid:
            raise StreamProtocolError('Final acknowledgement did not settle the Ready owner')
        return receipt

    def _release_acknowledged(self):
        try:
            return super()._release_acknowledged()
        except StreamRejected:
            self._operation = None
            raise

    def _validate_released(self, receipt):
        super()._validate_released(receipt)
        if (not receipt.valid or receipt.tx_accepted or receipt.tx_free != self.host.depth or
                receipt.rx_start or receipt.rx_valid or receipt.rx_queued):
            raise StreamProtocolError('RELEASE did not preserve installation and clear Ready custody')

    def release(self):
        self._acknowledge_terminal()
        return self._release_acknowledged()

    def finish(self, *, max_exchanges=100000):
        """Drain once, decode the result, and release a successful owner.

        A device fault retains the acknowledged RX prefix and owner. The
        caller can explicitly cancel it after inspecting the outcome.
        """
        self.wait(max_exchanges=max_exchanges)
        terminal = self._acknowledge_terminal()
        result, consumed = self._outcome(terminal)
        release = None if terminal.fault else self._release_acknowledged()
        cancelled = None if consumed is None else terminal.tx_accepted - consumed
        return ReadyCompletion(terminal, release, self.rx_bits, result, consumed, cancelled)

    def _validate_cancelled(self, receipt):
        if (receipt.tag != self.tag or receipt.valid or receipt.busy or receipt.retained or
                receipt.tx_accepted or receipt.tx_free != self.host.depth or receipt.rx_start or
                receipt.rx_valid or receipt.rx_queued):
            raise StreamProtocolError('Warm cancellation did not empty the matching owner')

    def _cancelled(self, receipt):
        self.host._epoch += 1
        self.host._pending, self.host._last, self._operation = None, receipt, None

    def cancel(self):
        self._local()
        if (self._operation is not None or self.host.transport.inflight is not None or self.last is None or
                not self.last.fault or self.last.rx_queued or self.last.rx_valid):
            raise StreamProtocolError('Cancel requires an acknowledged fault owner with no uncertain operation')
        self._operation = 'cancel'
        try:
            receipt = require_accepted(self.host.transport.request(Opcode.WARM_RESET,
                validate=self._validate_cancelled))
        except StreamTransportError as error:
            raise StreamTransportError(error.cause, self) from error
        except StreamRejected:
            self._operation = None
            raise
        self._cancelled(receipt)
        return receipt

    def recover(self):
        request, operation = self.host.transport.inflight, self._operation
        try:
            if operation == 'cancel':
                self._local()
                receipt = require_accepted(self.host.transport.recover())
                self._validate_cancelled(receipt)
                self._cancelled(receipt)
                return receipt
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
