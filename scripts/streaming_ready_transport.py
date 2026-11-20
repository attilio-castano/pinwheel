"""Shared host ownership and protocol decoding for the sampled-ready target.

The quad framing implementation is shared unchanged. Ready images have their
own validator. Fixed streams use the START cell count, while a branching
image supplies separate TX, RX, and terminal path bounds.
"""
from dataclasses import dataclass

from streaming_transport import (Code, MAX_BITS, Opcode, PendingStream, Receipt, StreamHost,
    StreamProtocolError, StreamRejected, StreamTransportError, require_accepted, uint)


REGISTER_READ_SCHEMA = 'pinwheel.ready-register-read.v1'
REGISTER_READ_NACKS = ('write-address-nack', 'register-nack', 'read-address-nack')
REGISTER_READ_EXITS = frozenset({('complete', 36, 36), ('discard', 27, 27),
                                ('discard', 18, 18), ('discard', 9, 9)})
SWD_READ_SCHEMA = 'pinwheel.ready-swd-read.v1'
SWD_READ_EXITS = frozenset({('complete', 0, 3), ('complete', 0, 36)})
SWD_ACK_OUTCOMES = {
    (True, False, False): 'ok',
    (False, True, False): 'wait',
    (False, False, True): 'fault',
}


def _manifest_exits(records):
    if type(records) is not list or any(type(record) is not dict for record in records):
        raise ValueError('Expected Ready exit records')
    return tuple((record['kind'], record['tx'], record['rx']) for record in records)


@dataclass(frozen=True)
class ReadyPathPlan:
    """Bounds for a checked branching image, independent of its wire decoder."""
    start_count: int
    tx_bits: tuple[bool, ...]
    exits: tuple[tuple[str, int, int], ...]

    def __post_init__(self):
        uint(self.start_count, 16, 'Ready START count')
        if (type(self.tx_bits) is not tuple or any(type(bit) is not bool for bit in self.tx_bits) or
                len(self.tx_bits) > self.start_count):
            raise ValueError('Ready TX plan must fit its START count')
        if type(self.exits) is not tuple or not self.exits:
            raise ValueError('Ready path plan requires immutable exit records')
        for exit_ in self.exits:
            if type(exit_) is not tuple or len(exit_) != 3:
                raise ValueError('Invalid Ready path exit record')
            kind, tx, rx = exit_
            if (type(kind) is not str or kind not in ('complete', 'discard') or
                    uint(tx, 16, 'Ready exit TX count') > len(self.tx_bits) or
                    (kind == 'complete' and tx != len(self.tx_bits))):
                raise ValueError('Ready path exit is inconsistent with its TX plan')
            uint(rx, 16, 'Ready exit RX count')

    @property
    def rx_capacity(self):
        return max(rx for _, _, rx in self.exits)

    @property
    def can_end_tx_early(self):
        return any(tx < len(self.tx_bits) for _, tx, _ in self.exits)

    def consumed(self, kind, received, accepted):
        """Select a single TX disposition for the decoded terminal path."""
        matches = {tx for mode, tx, rx in self.exits if mode == kind and rx == received}
        if len(matches) != 1:
            raise StreamProtocolError('Ready completed with an invalid RX prefix or ambiguous terminal path')
        (tx,) = matches
        if not tx <= accepted <= len(self.tx_bits):
            raise StreamProtocolError('Ready completed with an invalid TX count')
        return tx


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
            image = cls(tuple(manifest['words']), manifest['address'], manifest['register'],
                       tuple(manifest['tx_bits']), _manifest_exits(manifest['exits']),
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
        if len(self.path_plan.exits) != 4 or set(self.exits) != REGISTER_READ_EXITS:
            raise ValueError('Register read exits differ from the declared protocol')

    @property
    def path_plan(self):
        return ReadyPathPlan(self.tx_budget, self.tx_bits, self.exits)

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
        if len(rx) != extent:
            raise StreamProtocolError('Register read completed with an invalid RX prefix or TX count')
        consumed = self.path_plan.consumed(kind, len(rx), accepted)
        if nack:
            return CombinedI2cResult(nack[1]), consumed
        byte = sum(int(bit) << (7 - index) for index, bit in enumerate(rx[27:35]))
        return CombinedI2cResult('read', byte), consumed


@dataclass(frozen=True)
class BranchingSwdResult:
    outcome: str
    word: int | None = None


@dataclass(frozen=True)
class BranchingSwdRead:
    """Transport metadata for an ACK-branching, receive-only SWD image."""
    words: tuple[int, ...]
    exits: tuple[tuple[str, int, int], ...]
    tx_bits: tuple[bool, ...]
    tx_budget: int
    start_count: int
    idle_levels: int
    idle_enabled: int

    @classmethod
    def from_manifest(cls, manifest):
        if type(manifest) is not dict or manifest.get('schema') != SWD_READ_SCHEMA:
            raise ValueError('Unsupported Ready SWD read manifest')
        try:
            image = cls(tuple(manifest['words']), _manifest_exits(manifest['exits']),
                        tuple(manifest['tx_bits']), manifest['tx_budget'], manifest['start_count'],
                        manifest['idle_levels'], manifest['idle_enabled'])
        except (KeyError, TypeError) as error:
            raise ValueError('Malformed Ready SWD read manifest') from error
        image.validate()
        return image

    @property
    def path_plan(self):
        return ReadyPathPlan(self.start_count, self.tx_bits, self.exits)

    def validate(self):
        plan = self.path_plan
        if uint(self.tx_budget, 16, 'SWD TX budget') or plan.tx_bits or plan.start_count:
            raise ValueError('SWD read requires no host TX and uses image-local slot counts')
        if set(plan.exits) != SWD_READ_EXITS:
            raise ValueError('SWD read exits differ from the declared ACK and data phases')
        if uint(self.idle_levels, 3, 'Idle levels') or uint(self.idle_enabled, 3, 'Idle enables') != 1:
            raise ValueError('SWD idle requires low SWCLK and released SWDIO')
        if type(self.words) is not tuple or not 1 <= len(self.words) <= 64:
            raise ValueError('SWD read requires 1..64 immutable image words')
        for word in self.words:
            uint(word, 64, 'SWD read word')

    def project(self, rx, accepted, *, fault):
        outcome = SWD_ACK_OUTCOMES.get(rx[:3], 'invalid-ack')
        extent = 36 if outcome == 'ok' else 3
        if len(rx) > extent:
            raise StreamProtocolError('SWD RX extends beyond its ACK-selected path')
        if fault:
            return BranchingSwdResult('deadline'), None
        if len(rx) != extent:
            raise StreamProtocolError('SWD completed with an invalid RX prefix for its ACK')
        consumed = self.path_plan.consumed('complete', len(rx), accepted)
        if outcome != 'ok':
            return BranchingSwdResult(outcome), consumed
        if sum(rx[3:]) % 2:
            return BranchingSwdResult('bad-parity'), consumed
        word = sum(int(bit) << index for index, bit in enumerate(rx[3:-1]))
        return BranchingSwdResult('ok', word), consumed


_BRANCHING_IMAGES = (CombinedI2cRead, BranchingSwdRead)


@dataclass(frozen=True)
class ReadyCompletion:
    terminal: Receipt
    release: Receipt | None
    rx_bits: tuple[bool, ...]
    result: CombinedI2cResult | BranchingSwdResult | tuple[bool, ...] | None
    tx_consumed: int | None
    tx_cancelled: int | None


def validate_ready_image(image):
    if type(image) in _BRANCHING_IMAGES:
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
        if type(image) in _BRANCHING_IMAGES:
            if bits or bit_count is not None:
                raise ValueError('A checked branching image supplies its own TX plan and START count')
            path_plan = image.path_plan
            plan = dict(bits=path_plan.tx_bits, total=path_plan.start_count,
                        transmit=bool(path_plan.tx_bits), receive=bool(path_plan.rx_capacity), path_plan=path_plan)
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
    def __init__(self, host, loaded, bits, *, total, transmit, receive, path_plan=None):
        super().__init__(host, loaded, bits)
        self.total_bits = total
        self.expected_tx = len(path_plan.tx_bits) if path_plan is not None else total if transmit else 0
        self.expected_rx = path_plan.rx_capacity if path_plan is not None else total if receive else 0
        self.path_plan = path_plan
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
        can_end_early = self.path_plan is not None and self.path_plan.can_end_tx_early
        if not (offered and old is not None and old.busy and reply.code is Code.REJECTED and
                reply.tag == self.tag and reply.valid and reply.retained and (reply.fault or can_end_early) and
                reply.tx_accepted == self.tx_accepted and
                (reply.rx_start, reply.rx_valid, reply.data) in (
                    (old.rx_start, old.rx_valid, old.data), (len(self.rx_bits), 0, 0)) and
                reply.tx_free <= self.host.depth and reply.rx_queued <= self.host.depth):
            raise error
        before_tx, before_rx = self.tx_accepted, len(self.rx_bits)
        receipt = super().pump(max_bits=0)
        self.terminal_retries.append(dict(rejected_sequence=reply.sequence, empty_sequence=receipt.sequence,
            owner_tag=self.tag, unchanged_tx_accepted=before_tx, acknowledged_rx_end=before_rx))
        if receipt.tx_accepted != before_tx:
            raise StreamProtocolError('Empty terminal retry unexpectedly accepted TX')
        return receipt

    def pump(self, *, max_bits=64, scheduled_bits=None):
        """Send a credit-driven exchange or offer whole beats at a scheduled time.

        A timed caller may schedule a refill based on device progress since
        the last receipt. The frontend checks live room and the exact accepted
        prefix is established only by the validated exchange receipt.
        """
        self._local()
        if self._operation is not None or self.host.transport.inflight is not None:
            raise StreamProtocolError('Recover the uncertain Ready operation first')
        if scheduled_bits is None:
            return super().pump(max_bits=max_bits)
        if (type(scheduled_bits) is not int or scheduled_bits not in (32, 64) or
                type(max_bits) is not int or max_bits not in (32, 64) or scheduled_bits > max_bits):
            raise ValueError('Scheduled TX offer must be 32 or 64 bits within the exchange budget')
        if self.last is None or not self.last.busy or self.expected_tx - self.tx_accepted < scheduled_bits:
            raise StreamProtocolError('Scheduled TX offer requires a busy owner with that many unsent bits')
        return self._exchange_offer(self.tx_bits[self.tx_accepted:self.tx_accepted + scheduled_bits])

    def _exchange_offer(self, bits):
        self._offered = len(bits)
        try:
            return super()._exchange_offer(bits)
        except StreamRejected as error:
            return self._terminal_retry(error, len(bits))

    def _outcome(self, receipt):
        image = self.loaded.image
        if self.path_plan is not None:
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
