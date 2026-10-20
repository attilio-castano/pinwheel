"""Versioned quad sampled-pin transport for the streaming continuation.

The v1 buffered serial interface is unchanged. This link sends 176-bit requests
and reads held 208-bit responses, four bits per sampled SCK rising edge. MISO
is observed before the engine edge; READY is observed afterward. CRC detects
specified corruption patterns, not arbitrary faults or malicious messages.
"""
from dataclasses import dataclass
from enum import IntEnum, IntFlag


FORMAT = 'streaming-quad-v1'
REQUEST_BITS, RESPONSE_BITS = 176, 208
REQUEST_HEADER, RESPONSE_HEADER = 0xA720, 0x5A20
MAX_BITS = 65535


class Opcode(IntEnum):
    WRITE = 1
    COMMIT = 2
    START = 3
    RELEASE = 4
    WARM_RESET = 7
    EXCHANGE0 = 8
    EXCHANGE32 = 9
    EXCHANGE64 = 10


class Code(IntEnum):
    ACCEPTED = 0
    BAD_LENGTH = 1
    BAD_HEADER = 2
    BAD_CRC = 3
    BAD_PAYLOAD = 4
    REJECTED = 5


class Flags(IntFlag):
    VALID = 1
    BUSY = 2
    RETAINED = 4
    FAULT = 8
    REJECTED = 16
    WAIT_TX = 32
    WAIT_RX = 64


RESPONSE_FIELDS = (('data', 64), ('tag', 32), ('tx_accepted', 16),
    ('rx_start', 16), ('rx_valid', 7), ('tx_free', 4), ('rx_queued', 4),
    ('flags', 8), ('reserved', 9))


class StreamProtocolError(RuntimeError):
    pass


class StreamTransportError(RuntimeError):
    """An operation has uncertain delivery; its exact request remains in flight."""
    def __init__(self, cause, pending=None):
        super().__init__(str(cause))
        self.cause, self.pending = cause, pending


class StreamRejected(RuntimeError):
    def __init__(self, receipt):
        super().__init__('Streaming command rejected: ' + receipt.code.name)
        self.receipt = receipt


def uint(value, width, name):
    if type(value) is not int or not 0 <= value < (1 << width):
        raise ValueError(name + ' must be an unsigned ' + str(width) + '-bit integer')
    return value


def crc16(data):
    """CRC-16/CCITT-FALSE: 1021, FFFF, nonreflected, xorout zero."""
    if type(data) is not bytes:
        raise TypeError('CRC input must be captured bytes')
    crc = 0xffff
    for byte in data:
        crc ^= byte << 8
        for _ in range(8):
            crc = ((crc << 1) ^ (0x1021 if crc & 0x8000 else 0)) & 0xffff
    return crc


def pack(fields):
    result = 0
    for name, width, value in fields:
        result = (result << width) | uint(value, width, name)
    return result


def checked_frame(logical, width):
    uint(logical, width, 'Logical frame')
    if width % 8:
        raise ValueError('Logical frame must contain whole bytes')
    return (logical << 16) | crc16(logical.to_bytes(width // 8, 'big'))


def frame_body(packet, width):
    uint(packet, width + 16, 'Wire frame')
    logical = packet >> 16
    if crc16(logical.to_bytes(width // 8, 'big')) != packet & 0xffff:
        raise StreamProtocolError('Streaming frame CRC mismatch')
    return logical


@dataclass(frozen=True)
class Request:
    sequence: int
    opcode: Opcode
    payload: int

    def __post_init__(self):
        uint(self.sequence, 16, 'Request sequence')
        if type(self.opcode) is not Opcode:
            raise ValueError('Request opcode must be an Opcode')
        uint(self.payload, 128, 'Request payload')

    @property
    def logical(self):
        return ((REQUEST_HEADER | self.opcode) << 144) | (self.sequence << 128) | self.payload

    @property
    def packet(self):
        return checked_frame(self.logical, 160)

    @property
    def bytes(self):
        return self.packet.to_bytes(22, 'big')


def command(sequence, opcode, **fields):
    if type(opcode) is not Opcode:
        raise ValueError('Command requires an Opcode')
    layouts = {
        Opcode.WRITE: (('address', 6), ('word', 64), ('reserved', 58)),
        Opcode.COMMIT: (('count', 7), ('idle_levels', 3), ('idle_enabled', 3), ('reserved', 115)),
        Opcode.START: (('expected_generation', 16), ('bit_count', 16), ('reserved', 96)),
        Opcode.RELEASE: (('tag', 32), ('reserved', 96)),
        Opcode.WARM_RESET: (('reserved', 128),),
        Opcode.EXCHANGE0: (('tag', 32), ('tx_offset', 16), ('rx_ack', 16), ('data', 64)),
        Opcode.EXCHANGE32: (('tag', 32), ('tx_offset', 16), ('rx_ack', 16), ('data', 64)),
        Opcode.EXCHANGE64: (('tag', 32), ('tx_offset', 16), ('rx_ack', 16), ('data', 64)),
    }
    layout = layouts[opcode]
    allowed = {name for name, _ in layout} - {'reserved'}
    if set(fields) - allowed:
        raise ValueError('Unexpected streaming command fields')
    values = {name: uint(fields.get(name, 0), width, name) for name, width in layout}
    if opcode is Opcode.COMMIT and not 1 <= values['count'] <= 64:
        raise ValueError('Program count must be in 1..64')
    if opcode is Opcode.EXCHANGE0 and values['data']:
        raise ValueError('EXCHANGE0 cannot supply TX data')
    if opcode is Opcode.EXCHANGE32 and values['data'] & 0xffffffff:
        raise ValueError('EXCHANGE32 uses the high word and requires zero low tail')
    return Request(sequence, opcode, pack((name, width, values[name]) for name, width in layout))


def decode_request(packet):
    logical = frame_body(packet, 160)
    if logical >> 148 != REQUEST_HEADER >> 4:
        raise StreamProtocolError('Wrong streaming request header/version')
    try:
        opcode = Opcode((logical >> 144) & 15)
    except ValueError as error:
        raise StreamProtocolError('Unsupported streaming opcode') from error
    request = Request((logical >> 128) & 0xffff, opcode, logical & ((1 << 128) - 1))
    layouts = {
        Opcode.WRITE: (('address', 6), ('word', 64), ('reserved', 58)),
        Opcode.COMMIT: (('count', 7), ('idle_levels', 3), ('idle_enabled', 3), ('reserved', 115)),
        Opcode.START: (('expected_generation', 16), ('bit_count', 16), ('reserved', 96)),
        Opcode.RELEASE: (('tag', 32), ('reserved', 96)),
        Opcode.WARM_RESET: (('reserved', 128),),
    }
    layout = layouts.get(opcode, (('tag', 32), ('tx_offset', 16), ('rx_ack', 16), ('data', 64)))
    remaining, values = 128, {}
    for name, width in layout:
        remaining -= width
        value = (request.payload >> remaining) & ((1 << width) - 1)
        if name == 'reserved':
            if value:
                raise StreamProtocolError('Reserved streaming request bits are nonzero')
        else:
            values[name] = value
    try:
        canonical = command(request.sequence, opcode, **values)
    except ValueError as error:
        raise StreamProtocolError('Noncanonical streaming request payload') from error
    if canonical != request:
        raise StreamProtocolError('Noncanonical streaming request')
    return request


@dataclass(frozen=True)
class Receipt:
    sequence: int
    code: Code
    data: int = 0
    tag: int = 0
    tx_accepted: int = 0
    rx_start: int = 0
    rx_valid: int = 0
    tx_free: int = 0
    rx_queued: int = 0
    flags: int = 0
    reserved: int = 0

    def __post_init__(self):
        uint(self.sequence, 16, 'Response sequence')
        if type(self.code) is not Code:
            raise ValueError('Response requires a Code')
        for name, width in RESPONSE_FIELDS:
            uint(getattr(self, name), width, name)
        if self.reserved or self.flags & 0x80:
            raise StreamProtocolError('Reserved streaming response bits are nonzero')
        if self.rx_valid > 64 or self.data >> self.rx_valid:
            raise StreamProtocolError('RX data is not canonical right-aligned valid bits')
        if self.rx_start + self.rx_valid > MAX_BITS:
            raise StreamProtocolError('RX prefix exceeds the wire bit-count bound')
        if self.busy and self.retained:
            raise StreamProtocolError('Streaming slot cannot be busy and retained')
        if self.fault and not self.retained:
            raise StreamProtocolError('Fault must identify a retained terminal outcome')
        if self.flags & (Flags.WAIT_TX | Flags.WAIT_RX) and not self.busy:
            raise StreamProtocolError('Only an executing stream can wait for queue credit')
        if self.code in (Code.ACCEPTED, Code.REJECTED) and bool(self.flags & Flags.REJECTED) != (self.code is Code.REJECTED):
            raise StreamProtocolError('Response code and latched rejection disagree')

    @property
    def busy(self): return bool(self.flags & Flags.BUSY)
    @property
    def retained(self): return bool(self.flags & Flags.RETAINED)
    @property
    def fault(self): return bool(self.flags & Flags.FAULT)
    @property
    def valid(self): return bool(self.flags & Flags.VALID)
    @property
    def generation(self): return self.tag >> 16
    @property
    def transfer(self): return self.tag & 0xffff
    @property
    def rx_end(self): return self.rx_start + self.rx_valid
    @property
    def rx_bits(self):
        return tuple(bool((self.data >> bit) & 1) for bit in range(self.rx_valid - 1, -1, -1))
    @property
    def packet(self):
        payload = pack((name, width, getattr(self, name)) for name, width in RESPONSE_FIELDS)
        logical = ((RESPONSE_HEADER | self.code) << 176) | (self.sequence << 160) | payload
        return checked_frame(logical, 192)


def decode_response(packet, expected_sequence=None):
    logical = frame_body(packet, 192)
    if logical >> 180 != RESPONSE_HEADER >> 4:
        raise StreamProtocolError('Wrong streaming response header/version')
    sequence = (logical >> 160) & 0xffff
    if expected_sequence is not None and sequence != uint(expected_sequence, 16, 'Expected sequence'):
        raise StreamProtocolError('Streaming response sequence mismatch')
    try:
        code = Code((logical >> 176) & 15)
    except ValueError as error:
        raise StreamProtocolError('Unsupported streaming response code') from error
    payload, values = logical & ((1 << 160) - 1), {}
    remaining = 160
    for name, width in RESPONSE_FIELDS:
        remaining -= width
        values[name] = (payload >> remaining) & ((1 << width) - 1)
    return Receipt(sequence, code, **values)


def bits_left(bits, width=64):
    if type(bits) is not tuple or len(bits) > width or any(type(bit) is not bool for bit in bits):
        raise ValueError('TX bits must be an immutable Boolean tuple within the field width')
    result = 0
    for bit in bits:
        result = (result << 1) | bit
    return result << (width - len(bits))


def byte_bits(data, bit_count=None, *, msb_first=True):
    if type(data) is not bytes or type(msb_first) is not bool:
        raise ValueError('Payload must be bytes with an explicit Boolean bit order')
    bit_count = 8 * len(data) if bit_count is None else uint(bit_count, 16, 'Bit count')
    if len(data) != (bit_count + 7) // 8:
        raise ValueError('Payload byte length differs from its declared bit count')
    order = range(7, -1, -1) if msb_first else range(8)
    padded = tuple(bool((byte >> bit) & 1) for byte in data for bit in order)
    if any(padded[bit_count:]):
        raise ValueError('Unused final payload bits must be zero')
    return padded[:bit_count]


def jtag_bits(data, bit_count):
    """Construct one positive LSB-first scan, including a canonical last byte.

    Generic START0 remains valid. A zero-bit JTAG scan has no last data bit on
    which to leave Shift-DR, so the protocol helper refuses it before wire I/O.
    """
    uint(bit_count, 16, 'JTAG bit count')
    if bit_count == 0:
        raise ValueError('JTAG scan must contain at least one data bit')
    return byte_bits(data, bit_count, msb_first=False)


class QuadTransport:
    """One outstanding captured request; recovery never invents a new command.

    A backend implements tick(csn, sck, mosi), where mosi/miso are nibbles,
    and returns pre-edge miso plus post-edge ready. On uncertain delivery the
    immutable request remains available through inflight and recover().
    """
    def __init__(self, backend, *, phase_cycles=1, ready_timeout_edges=128):
        if not callable(getattr(backend, 'tick', None)):
            raise ValueError('Quad backend must supply tick')
        if type(phase_cycles) is not int or phase_cycles < 1:
            raise ValueError('Phase duration must be a positive integer')
        if type(ready_timeout_edges) is not int or ready_timeout_edges < 1:
            raise ValueError('Readiness timeout must be a positive integer')
        self.backend, self.phase_cycles = backend, phase_cycles
        self.ready_timeout_edges = ready_timeout_edges
        self.physical_edges = self.transactions = self.request_frames = self.response_frames = self.recoveries = 0
        self.opcode_counts = {opcode: 0 for opcode in Opcode}
        self.edge_count_uncertain = False
        self._sequence, self._inflight, self._validator = 0, None, None
        self._pins = dict(csn=1, sck=0, mosi=0)

    @property
    def inflight(self): return self._inflight

    def _tick(self, **pins):
        self._pins.update(pins)
        for name, width in (('csn', 1), ('sck', 1), ('mosi', 4)):
            uint(self._pins[name], width, name)
        before = getattr(self.backend, 'cycle', None)
        completed = False
        try:
            result = self.backend.tick(**self._pins)
            completed = True
        finally:
            after = getattr(self.backend, 'cycle', None)
            if type(before) is int and type(after) is int and after >= before:
                self.physical_edges += after - before
                if not completed and after == before:
                    self.edge_count_uncertain = True
            elif completed:
                self.physical_edges += 1
            else:
                self.edge_count_uncertain = True
        if type(result) is not dict:
            raise StreamProtocolError('Quad backend must return pin observations')
        uint(result.get('miso'), 4, 'Pre-edge MISO')
        uint(result.get('ready'), 1, 'Post-edge READY')
        return result

    def _phase(self, **pins):
        first = self._tick(**pins)
        for _ in range(self.phase_cycles - 1):
            self._tick()
        return first

    def idle(self, edges):
        """Sample deselected host edges while the protocol engine keeps running."""
        if type(edges) is not int or edges < 0:
            raise ValueError('Idle edge count must be a nonnegative integer')
        observed = None
        for _ in range(edges):
            observed = self._tick(csn=1, sck=0, mosi=0)
        return observed

    def cold_reset(self):
        reset = getattr(self.backend, 'cold_reset', None)
        if not callable(reset):
            raise ValueError('Backend must supply physical cold_reset')
        before = getattr(self.backend, 'cycle', None)
        try:
            reset()
        finally:
            after = getattr(self.backend, 'cycle', None)
            if type(before) is int and type(after) is int and after >= before:
                self.physical_edges += after - before
            else:
                self.edge_count_uncertain = True
            self._inflight = None
            self._validator = None
            self._sequence = 0
            self._pins = dict(csn=1, sck=0, mosi=0)

    def _send(self, request):
        observed = self._tick(csn=1, sck=0, mosi=0)
        if observed['ready']:
            raise StreamProtocolError('An unread response prevents a new request frame')
        self.request_frames += 1
        packet = request.packet
        for shift in range(REQUEST_BITS - 4, -1, -4):
            self._phase(csn=0, sck=0, mosi=(packet >> shift) & 15)
            self._phase(sck=1)
        self._tick(csn=1, sck=0, mosi=0)

    def _read(self, sequence):
        observed = self._tick(csn=1, sck=0, mosi=0)
        for _ in range(self.ready_timeout_edges):
            if observed['ready']:
                break
            observed = self._tick()
        else:
            raise TimeoutError('Streaming response readiness budget expired')
        packet = 0
        for _ in range(RESPONSE_BITS // 4):
            self._phase(csn=0, sck=0, mosi=0)
            observed = self._phase(sck=1)
            packet = (packet << 4) | observed['miso']
        self.response_frames += 1
        # Close even a corrupt complete response. Recovery can then replay the
        # exact original request against the endpoint's persistent last cache.
        closed = self._tick(csn=1, sck=0, mosi=0)
        if closed['ready']:
            raise StreamProtocolError('Exact response read did not clear READY')
        return decode_response(packet, sequence)

    def request(self, opcode, *, validate=None, **fields):
        if self._inflight is not None:
            raise StreamProtocolError('Recover the outstanding request before another command')
        if validate is not None and not callable(validate):
            raise ValueError('Receipt validator must be callable')
        if self._sequence > 65535:
            raise StreamProtocolError('Quad sequence exhausted; physical initialization is required')
        request = command(self._sequence, opcode, **fields)
        self._sequence += 1
        self._inflight = request
        self._validator = validate
        self.transactions += 1
        self.opcode_counts[opcode] += 1
        try:
            self._send(request)
            receipt = self._read(request.sequence)
            if receipt.code in (Code.BAD_LENGTH, Code.BAD_HEADER, Code.BAD_CRC):
                raise StreamProtocolError('Endpoint framing rejection did not consume the sequence; recover exact request')
            if validate is not None and receipt.code is Code.ACCEPTED:
                validate(receipt)
            self._inflight = None
            self._validator = None
            return receipt
        except Exception as error:
            raise StreamTransportError(error) from error

    def recover(self):
        if self._inflight is None:
            raise StreamProtocolError('There is no in-flight streaming request to recover')
        request = self._inflight
        self.recoveries += 1
        try:
            observed = self._tick(csn=1, sck=0, mosi=0)
            # Delivery can have occurred just before acknowledgement loss.
            # Give the bounded dispatch/CRC pipeline time to publish its held
            # receipt before deciding that an exact request replay is needed.
            for _ in range(self.ready_timeout_edges):
                if observed['ready']:
                    break
                observed = self._tick()
            if not observed['ready']:
                self._send(request)
            receipt = self._read(request.sequence)
            if receipt.code in (Code.BAD_LENGTH, Code.BAD_HEADER, Code.BAD_CRC):
                raise StreamProtocolError('Endpoint framing rejection did not consume the sequence; recover exact request')
            if self._validator is not None and receipt.code is Code.ACCEPTED:
                self._validator(receipt)
            self._inflight = None
            self._validator = None
            return receipt
        except Exception as error:
            raise StreamTransportError(error) from error

    def exchange(self, tag, tx_offset, rx_ack, bits=(), *, validate=None):
        data = bits_left(bits)
        requested = 0 if not bits else 32 if len(bits) <= 32 else 64
        opcode = {0: Opcode.EXCHANGE0, 32: Opcode.EXCHANGE32, 64: Opcode.EXCHANGE64}[requested]
        return self.request(opcode, tag=tag, tx_offset=tx_offset, rx_ack=rx_ack, data=data, validate=validate)


def require_accepted(receipt):
    if receipt.code is not Code.ACCEPTED:
        raise StreamRejected(receipt)
    return receipt


@dataclass(frozen=True)
class LoadedStream:
    host: object
    image: object
    epoch: int
    generation: int

    def submit(self, tx_bits):
        return self.host._submit(self, tx_bits)


class StreamHost:
    def __init__(self, transport, *, depth):
        if type(transport) is not QuadTransport or depth not in (2, 4):
            raise ValueError('Streaming host requires its quad transport and depth 2 or 4')
        self.transport, self.depth = transport, depth
        self._epoch, self._pending, self._last = 0, None, None

    def initialize(self):
        self._epoch += 1
        self._pending = self._last = None
        self.transport.cold_reset()

    def load(self, image):
        # The compiler owns the immutable source/word binding. Validate before
        # even querying the link, including when a local owner already exists.
        from streaming_compile import validate_image
        certificate = validate_image(image)
        stream = image.source.instructions[certificate.stream_row].cell
        if not stream.transmit or not stream.receive:
            raise ValueError('StreamHost requires one duplex TX/RX stream; use QuadTransport for simplex images')
        if self._pending is not None:
            raise StreamProtocolError('Release or explicitly reset the current stream before loading')
        self._epoch += 1
        for address, word in enumerate(image.words):
            self._last = require_accepted(self.transport.request(Opcode.WRITE, address=address, word=word))
        self._last = require_accepted(self.transport.request(Opcode.COMMIT, count=len(image.words),
            idle_levels=image.idle_levels, idle_enabled=image.idle_enabled))
        if not self._last.valid:
            raise StreamProtocolError('COMMIT receipt did not establish a valid image')
        return LoadedStream(self, image, self._epoch, self._last.generation)

    def warm_reset(self):
        if self.transport.inflight is not None:
            raise StreamProtocolError('Recover the outstanding operation before warm reset')
        self._epoch += 1
        self._pending = self._last = None
        self._last = require_accepted(self.transport.request(Opcode.WARM_RESET))
        return self._last

    def _submit(self, loaded, bits):
        if loaded.host is not self or loaded.epoch != self._epoch or self._pending is not None:
            raise StreamProtocolError('Stale image or unreleased stream owner')
        if type(bits) is not tuple or len(bits) > MAX_BITS or any(type(bit) is not bool for bit in bits):
            raise ValueError('TX stream must be an immutable Boolean tuple of at most 65535 bits')
        pending = PendingStream(self, loaded, bits)
        self._pending = pending
        try:
            receipt = self.transport.request(Opcode.START,
                expected_generation=loaded.generation, bit_count=len(bits), validate=pending._validate_started)
            pending._started(require_accepted(receipt))
        except StreamTransportError as error:
            raise StreamTransportError(error.cause, pending) from error
        except Exception:
            self._pending = None
            raise
        return pending


class PendingStream:
    def __init__(self, host, loaded, bits):
        self.host, self.loaded, self.tx_bits = host, loaded, bits
        self.tag, self.tx_accepted = None, 0
        self.rx_bits = ()
        self.last = None
        self._operation = 'start'

    def _local(self):
        if self.host._pending is not self or self.loaded.epoch != self.host._epoch:
            raise StreamProtocolError('Stream handle no longer owns this host session')

    def _validate_started(self, receipt):
        if (receipt.generation != self.loaded.generation or receipt.transfer == 0 or
                not receipt.valid or receipt.tx_accepted or receipt.rx_valid):
            raise StreamProtocolError('START receipt has inconsistent owner or initial offsets')

    def _started(self, receipt):
        self._validate_started(receipt)
        self.tag, self.last, self._operation = receipt.tag, receipt, None
        self.host._last = receipt

    def _validate_received(self, receipt):
        if receipt.tag != self.tag or not self.tx_accepted <= receipt.tx_accepted <= len(self.tx_bits):
            raise StreamProtocolError('Receipt has a stale owner or invalid TX accepted offset')
        if receipt.tx_free > self.host.depth or receipt.rx_queued > self.host.depth:
            raise StreamProtocolError('Receipt queue counts exceed the configured hardware depth')
        if receipt.rx_start != len(self.rx_bits) or receipt.rx_end > len(self.tx_bits):
            raise StreamProtocolError('Receipt RX interval duplicates, skips or exceeds the owned stream')

    def _received(self, receipt):
        self._validate_received(receipt)
        self.tx_accepted = receipt.tx_accepted
        self.rx_bits += receipt.rx_bits
        self.last, self.host._last, self._operation = receipt, receipt, None

    def pump(self, *, max_bits=64):
        if type(max_bits) is not int or max_bits not in (0, 32, 64):
            raise ValueError('Exchange TX budget must be 0, 32 or 64 bits')
        self._local()
        if self.tag is None or self._operation is not None:
            raise StreamProtocolError('Recover the uncertain stream operation first')
        remaining = len(self.tx_bits) - self.tx_accepted
        offered = (min(remaining, max_bits, 64 if self.last.tx_free >= 2 else 32 if self.last.tx_free >= 1 else 0)
                   if self.last.busy else 0)
        bits = self.tx_bits[self.tx_accepted:self.tx_accepted + offered]
        self._operation = 'exchange'
        try:
            receipt = self.host.transport.exchange(self.tag, self.tx_accepted, len(self.rx_bits), bits,
                validate=self._validate_received)
            require_accepted(receipt)
            self._received(receipt)
            return receipt
        except StreamTransportError as error:
            raise StreamTransportError(error.cause, self) from error
        except StreamRejected:
            self._operation = None
            raise

    def wait(self, *, max_exchanges=100000):
        if type(max_exchanges) is not int or max_exchanges < 0:
            raise ValueError('Exchange budget must be a nonnegative integer')
        self._local()
        for _ in range(max_exchanges):
            if (self.last is not None and self.last.retained and not self.last.rx_queued and
                    (self.last.fault or len(self.rx_bits) == len(self.tx_bits))):
                return self.last
            self.pump()
        raise TimeoutError('Streaming exchange budget expired; owner remains live')

    def release(self):
        self._local()
        if self.last is None or not self.last.retained or self.last.rx_queued:
            raise StreamProtocolError('RELEASE requires a drained retained stream')
        # An empty exchange acknowledges the last exported RX interval before
        # RELEASE. It must not hide unread RX data or mutate the TX prefix.
        self.pump()
        if not self.last.retained or self.last.rx_queued:
            raise StreamProtocolError('RX data remains after the final acknowledgement')
        self._operation = 'release'
        try:
            receipt = require_accepted(self.host.transport.request(Opcode.RELEASE, tag=self.tag,
                validate=self._validate_released))
            self.host._pending, self.host._last, self._operation = None, receipt, None
            return receipt
        except StreamTransportError as error:
            raise StreamTransportError(error.cause, self) from error

    def _validate_released(self, receipt):
        if receipt.busy or receipt.retained or receipt.tag != self.tag:
            raise StreamProtocolError('RELEASE did not establish the matching free slot')

    def recover(self):
        self._local()
        operation = self._operation
        receipt = require_accepted(self.host.transport.recover())
        if operation == 'start':
            self._started(receipt)
        elif operation == 'exchange':
            self._received(receipt)
        elif operation == 'release':
            self._validate_released(receipt)
            self.host._pending, self.host._last, self._operation = None, receipt, None
        else:
            raise StreamProtocolError('No uncertain owned operation requires recovery')
        return receipt
