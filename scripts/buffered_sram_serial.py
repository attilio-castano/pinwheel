"""Version-1 atomic serial requests for the buffered SRAM owner interface.

The backend supplies clock ticks and physical MISO/READY only. Requests are
160 bits, responses 192 bits, both MSB first in separate CS transactions.
The endpoint must receive physical initialization before parsing frames. Poll
budgets count complete serial polls; ``physical_edges`` records their cost.
"""
from dataclasses import dataclass

from buffered_hardware import (BufferedHardwareTransportError,
    BufferedHardwareWaitTimeout, LoadedBufferedHardware, PendingBufferedHardware,
    _integer, _status)
from buffered_sram_hardware import BufferedSramHardwareHost
from pinwheel_buffers import TransferError


FORMAT = 'pinwheel-buffered-sram-serial-v1'
REQUEST_BITS, RESPONSE_BITS = 160, 192
REQUEST_HEADER, RESPONSE_HEADER = 0xA710, 0x5A10
STATUS_FIELDS = (('valid', 1), ('busy', 1), ('retained', 1), ('pending', 1),
    ('rejected', 1), ('mode', 2), ('pc', 8), ('remaining', 8), ('levels', 3),
    ('enabled', 3), ('tx_consumed', 6), ('rx_length', 6), ('rx_data', 32),
    ('read_valid', 1), ('read_bit', 1), ('generation', 16), ('transfer', 16),
    ('exhausted', 1), ('stage1', 2), ('stage2', 2), ('virtual_pc', 10),
    ('env0', 3), ('env1', 3), ('phase', 3), ('wait_left', 8), ('scratch', 16))
STATUS_BITS = sum(width for _, width in STATUS_FIELDS)
LAYOUTS = {
    0: (('read_index', 5, 0, 31),),
    1: (('word', 64, 0, (1 << 64) - 1), ('control', 24, 64, (1 << 24) - 1),
        ('branch', 4, 88, 15), ('address', 6, 92, 63)),
    2: (('count', 7, 0, 64), ('virtual_span', 11, 7, 1024),
        ('idle_levels', 3, 18, 7), ('idle_enabled', 3, 21, 7)),
    3: (('tx_data', 32, 0, (1 << 32) - 1), ('tx_length', 6, 32, 32),
        ('rx_capacity', 6, 38, 32), ('expected_generation', 16, 44, 65535)),
    4: (('expected_generation', 16, 0, 65535), ('expected_transfer', 16, 16, 65535)),
    6: (('branch', 56, 0, (1 << 56) - 1), ('address', 4, 56, 15)),
    7: (), 8: ()}


class SerialProtocolError(RuntimeError):
    """A received response fails the exact serial ABI or rejects its frame."""
    def __init__(self, message, *, code=None):
        super().__init__(message)
        self.code = code


def encode_request(sequence, *, command=0, initialize=0, **fields):
    """Validate command-specific fields completely before any transport I/O."""
    _integer(sequence, 0, 65535, 'Serial sequence')
    _integer(command, 0, 7, 'Buffered command')
    _integer(initialize, 0, 1, 'Buffered initialization')
    if initialize and command:
        raise ValueError('Initialization cannot accompany a command')
    op = 8 if initialize else command
    if op not in LAYOUTS:
        raise ValueError('Unsupported serial buffered operation')
    layout = LAYOUTS[op]
    if set(fields) - {name for name, _, _, _ in layout}:
        raise ValueError('Unexpected fields for serial buffered operation')
    payload = 0
    for name, _, offset, maximum in layout:
        value = _integer(fields.get(name, 0), 0, maximum, name)
        if name in ('count', 'virtual_span') and value == 0:
            raise ValueError(name + ' must be nonzero')
        payload |= value << offset
    return ((REQUEST_HEADER | op) << 144) | (sequence << 128) | payload


def decode_request(packet):
    """Strict request decoder for tooling; the hardware decoder is independent."""
    _integer(packet, 0, (1 << REQUEST_BITS) - 1, 'Serial request')
    header = packet >> 144
    if header & 0xFFF0 != REQUEST_HEADER:
        raise ValueError('Wrong serial request header/version')
    op = header & 15
    if op not in LAYOUTS:
        raise ValueError('Unsupported serial buffered operation')
    payload = packet & ((1 << 128) - 1)
    fields, used = {}, 0
    for name, width, offset, _ in LAYOUTS[op]:
        fields[name] = (payload >> offset) & ((1 << width) - 1)
        used |= ((1 << width) - 1) << offset
    if payload & ~used:
        raise ValueError('Reserved serial request payload bits are nonzero')
    sequence = (packet >> 128) & 65535
    result = dict(command=0 if op == 8 else op, initialize=int(op == 8), **fields)
    if encode_request(sequence, **result) != packet:
        raise ValueError('Noncanonical serial request')
    return sequence, result


def _checked_status(status):
    values = _status(status)
    for name, width in STATUS_FIELDS:
        value = status[name]
        _integer(value, 0, (1 << width) - 1, 'Serial status ' + name)
        values[name] = value
    phase = values['phase']
    mode = 0 if phase == 0 else 1 if phase < 5 else 2 if phase == 5 else 3
    if values['mode'] != mode:
        raise SerialProtocolError('Inconsistent serial phase and mode')
    return values


def encode_response(sequence, code, status):
    """Encode an exact held response for fixtures and diagnostics."""
    _integer(sequence, 0, 65535, 'Serial sequence')
    _integer(code, 0, 4, 'Serial response code')
    values = _checked_status(status)
    if code in (0, 4) and values['rejected'] != int(code == 4):
        raise ValueError('Serial rejection code differs from core receipt')
    packed, offset = 0, 0
    for name, width in STATUS_FIELDS:
        packed |= values[name] << offset
        offset += width
    return ((RESPONSE_HEADER | code) << 176) | (sequence << 160) | packed


def decode_response(packet, *, expected_sequence=None):
    _integer(packet, 0, (1 << RESPONSE_BITS) - 1, 'Serial response')
    if expected_sequence is not None:
        _integer(expected_sequence, 0, 65535, 'Expected serial sequence')
    header, sequence = packet >> 176, (packet >> 160) & 65535
    if header & 0xFFF0 != RESPONSE_HEADER or header & 15 > 4:
        raise SerialProtocolError('Wrong serial response header/version/code')
    if expected_sequence is not None and sequence != expected_sequence:
        raise SerialProtocolError('Serial receipt sequence differs from request')
    if (packet >> STATUS_BITS) & ((1 << (160 - STATUS_BITS)) - 1):
        raise SerialProtocolError('Reserved serial response status bits are nonzero')
    status, offset = {}, 0
    for name, width in STATUS_FIELDS:
        status[name] = (packet >> offset) & ((1 << width) - 1)
        offset += width
    status = _checked_status(status)
    code = header & 15
    if code in (0, 4) and status['rejected'] != int(code == 4):
        raise SerialProtocolError('Serial rejection code differs from core receipt')
    return sequence, code, status


class BufferedSramSerialTransport:
    """Public pin transport with one outstanding request and explicit recovery.

    ``tick`` returns integer pre-edge ``miso`` and post-edge ``ready``. A failed
    transaction remains outstanding. ``recover_response`` drains its held
    receipt or uses a fresh STATUS after a corrupt complete receipt was consumed
    and idle CS/READY were established. It never retries an owned command.
    Backend initialization and protocol input sampling are its responsibility.
    """
    def __init__(self, backend, *, phase_cycles=1, ready_timeout_edges=8):
        if not callable(getattr(backend, 'tick', None)):
            raise ValueError('Serial backend must supply tick(**pins)')
        _integer(phase_cycles, 1, (1 << 31) - 1, 'Serial phase cycles')
        _integer(ready_timeout_edges, 1, (1 << 31) - 1, 'Serial readiness budget')
        self.backend, self.phase_cycles = backend, phase_cycles
        self.ready_timeout_edges = ready_timeout_edges
        self.physical_edges = self.requests = self.responses = 0
        self.edge_count_uncertain = False
        self._sequence, self._inflight = 0, None
        self._receipt, self._response_complete = None, False
        self._pins = dict(csn=1, sck=0, mosi=0)

    def _tick(self, **pins):
        self._pins.update(pins)
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
            raise SerialProtocolError('Serial backend must return pin observations')
        for name in ('miso', 'ready'):
            _integer(result.get(name), 0, 1, 'Serial pin ' + name)
        return result

    def _phase(self, **pins):
        first = self._tick(**pins)
        for _ in range(self.phase_cycles - 1):
            self._tick()
        return first

    def cold_reset(self):
        reset = getattr(self.backend, 'cold_reset', None)
        if not callable(reset):
            raise ValueError('Backend does not supply physical endpoint initialization')
        before = getattr(self.backend, 'cycle', None)
        try:
            reset()
        finally:
            after = getattr(self.backend, 'cycle', None)
            if type(before) is int and type(after) is int and after >= before:
                self.physical_edges += after - before
            else:
                self.edge_count_uncertain = True
        self._pins = dict(csn=1, sck=0, mosi=0)
        self._sequence, self._inflight = 0, None
        self._receipt, self._response_complete = None, False

    def _accept_receipt(self, receipt):
        _, code, status = receipt
        self._inflight, self._receipt, self._response_complete = None, None, False
        self.responses += 1
        if code not in (0, 4):
            raise SerialProtocolError('Endpoint rejected serial request framing', code=code)
        return status

    def _read_response(self, sequence):
        observed = self._tick(csn=1, sck=0, mosi=0)
        for _ in range(self.ready_timeout_edges):
            if observed['ready']:
                break
            observed = self._tick()
        else:
            if not observed['ready']:
                raise TimeoutError('Serial response readiness budget expired')
        packet = 0
        self._response_complete = False
        for _ in range(RESPONSE_BITS):
            self._phase(csn=0, sck=0, mosi=0)
            observed = self._phase(sck=1)
            packet = (packet << 1) | observed['miso']
        self._response_complete = True
        # Preserve a validated receipt before the closing tick, whose transport
        # acknowledgement can fail even when the endpoint consumed the snapshot.
        self._receipt = decode_response(packet, expected_sequence=sequence)
        closed = self._tick(csn=1, sck=0, mosi=0)
        if closed['ready']:
            raise SerialProtocolError('Exact serial response read did not release its snapshot')
        return self._accept_receipt(self._receipt)

    def edge(self, **fields):
        sequence = self._sequence
        packet = encode_request(sequence, **fields)
        if self._inflight is not None:
            raise SerialProtocolError('Recover the outstanding serial receipt or initialize the endpoint')
        observed = self._tick(csn=1, sck=0, mosi=0)
        if observed['ready']:
            raise SerialProtocolError('Endpoint has an unowned unread serial receipt')
        self._inflight = sequence
        self._receipt, self._response_complete = None, False
        self._sequence = (sequence + 1) & 65535
        self.requests += 1
        for shift in range(REQUEST_BITS - 1, -1, -1):
            self._phase(csn=0, sck=0, mosi=(packet >> shift) & 1)
            self._phase(sck=1)
        self._tick(csn=1, sck=0, mosi=0)
        return self._read_response(sequence)

    def recover_response(self):
        if self._inflight is None:
            raise SerialProtocolError('There is no outstanding serial receipt to recover')
        if self._response_complete:
            observed = self._tick(csn=1, sck=0, mosi=0)
            if not observed['ready']:
                if self._receipt is not None:
                    return self._accept_receipt(self._receipt)
                # An invalid full response has now been consumed, with idle CS
                # and no unread receipt. Explicit recovery can safely request a
                # fresh STATUS; it does not retry the original owned command.
                self._inflight, self._response_complete = None, False
                return self.edge(command=0)
        return self._read_response(self._inflight)


@dataclass(frozen=True)
class LoadedBufferedSramSerial(LoadedBufferedHardware):
    def run(self, *, tx, rx_limit=None, timeout_polls=100_000):
        """Run and release; release transport errors also carry immutable ``result``.

        That completion was already read successfully. The existing ``pending``
        and ``cause`` still describe the uncertain RELEASE and its recovery.
        """
        _integer(timeout_polls, 0, (1 << 63) - 1, 'Host serial poll budget')
        pending = self.submit(tx=tx, rx_limit=rx_limit)
        pending.wait(timeout_polls=timeout_polls)
        result = pending.read()
        try:
            pending.release()
        except BufferedHardwareTransportError as error:
            error.result = result
            raise
        return result


@dataclass(frozen=True)
class PendingBufferedSramSerial(PendingBufferedHardware):
    def _edge(self, **fields):
        releasing = fields == dict(command=4,
            expected_generation=self.identity.generation,
            expected_transfer=self.identity.transfer)
        if releasing:
            self._require_local()
            self.host._release_attempt = self
        status = super()._edge(**fields)
        if releasing:
            # A returned command receipt is handled by release() normally. An
            # exception keeps this exact local operation available for recovery.
            self.host._release_attempt = None
        return status

    def wait(self, *, timeout_polls=100_000):
        _integer(timeout_polls, 0, (1 << 63) - 1, 'Host serial poll budget')
        self._require_local()
        status = self._owned(self.host._last) if self.host._last is not None else self._edge(command=0)
        for _ in range(timeout_polls):
            if not status['busy']:
                break
            status = self._edge(command=0)
        if status['busy']:
            raise BufferedHardwareWaitTimeout(self)
        if not status['retained']:
            raise TransferError('Hardware no longer retains this transfer')
        return dict(status)

    def read(self):
        """Read the retained prefix atomically from one complete frozen receipt.

        The serial response already snapshots the whole RX word, bounds,
        outcome, scratch and identity on one edge. Indexed polls are unnecessary
        for this ABI; the index-zero window still witnesses the public read port.
        """
        status = self._edge(command=0, read_index=0)
        if not status['retained'] or status['busy']:
            raise TransferError('Result read requires a retained hardware completion')
        length, data = status['rx_length'], status['rx_data']
        if status['read_valid'] != int(length > 0):
            raise RuntimeError('Serial retained result has an invalid read window')
        if length and status['read_bit'] != (data & 1):
            raise RuntimeError('Serial indexed first bit differs from its frozen RX word')
        raw = tuple(bool(data & (1 << index)) for index in range(length))
        outcome = self.host._result_outcome(status)
        if outcome == 'complete' and status['tx_consumed'] != self.image.tx_bits:
            raise ValueError('Completed hardware transfer did not consume the declared TX demand')
        payload = self.image.decode_rx(raw) if outcome == 'complete' else None
        return self.host._make_result(self, status, outcome, raw, payload)

    def recover(self):
        """Recover a receipt without retrying the command; finalize known RELEASE.

        A matching accepted RELEASE can already have freed the hardware slot
        when its acknowledgement was lost. Its recovered free-state receipt
        also releases this host's local handle. Other commands retain ownership.
        """
        self._require_local()
        try:
            status = self.host.transport.recover_response()
            self.host._last = _checked_status(status)
            status = self._owned(self.host._last)
            if self.host._release_attempt is self:
                if status['retained']:
                    # The result is still owned, so an explicit release attempt
                    # remains possible after a rejected or undelivered command.
                    self.host._release_attempt = None
                elif (status['valid'] and not status['pending'] and
                      not status['busy'] and not status['rejected'] and
                      status['mode'] == 0 and status['phase'] == 0):
                    self.host._pending = self.host._release_attempt = None
                else:
                    raise SerialProtocolError('Recovered RELEASE did not establish the matching free slot')
            return dict(status)
        except TransferError:
            raise
        except Exception as error:
            raise BufferedHardwareTransportError(self, error) from error


class BufferedSramSerialHost(BufferedSramHardwareHost):
    """Canonical SRAM images and retained ownership over the versioned pins."""
    def __init__(self, transport):
        if type(transport) is not BufferedSramSerialTransport:
            raise ValueError('Serial SRAM host requires its versioned transport')
        super().__init__(transport)
        self._release_attempt = None

    def _invalidate(self):
        super()._invalidate()
        self._release_attempt = None

    def _edge(self, **fields):
        status = self.transport.edge(**fields)
        self.edges += 1
        # The parallel base host deliberately drops bulk RX data from its
        # observation. This ABI validates and retains the complete frozen word.
        self._last = _checked_status(status)
        return self._last

    def initialize(self):
        # A partially delivered physical reset must invalidate software handles
        # even when the backend fails before returning its acknowledgement.
        self._epoch += 1
        self._invalidate()
        if callable(getattr(self.transport.backend, 'cold_reset', None)):
            self.transport.cold_reset()
        status = self._edge(initialize=1)
        if any(status[name] for name in ('valid', 'busy', 'retained', 'pending',
                                         'generation', 'transfer', 'exhausted')):
            raise RuntimeError('Cold initialization did not clear the hardware session')
        return dict(status)

    def load(self, source):
        loaded = super().load(source)
        return LoadedBufferedSramSerial(self, loaded.image, loaded.epoch, loaded.generation)

    def _serial_pending(self, pending):
        serial = PendingBufferedSramSerial(self, pending.image, pending.identity,
                                          pending.tx_count, pending.rx_limit)
        self._pending = serial
        return serial

    def _submit(self, loaded, tx, rx_limit):
        try:
            return self._serial_pending(super()._submit(loaded, tx, rx_limit))
        except BufferedHardwareTransportError as error:
            pending = self._serial_pending(error.pending)
            raise BufferedHardwareTransportError(pending, error.cause) from error
