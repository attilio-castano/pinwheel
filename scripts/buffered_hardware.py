"""Versioned image and public parallel host for the buffered linear RTL slice.

This target is separate from the retained paired chip and its serial transport.
Only an explicitly supported linear subset lowers; reactive/counting programs
are rejected before transport I/O. Cold initialization must go through the host
to create a fresh software epoch. Raw identities across an external cold reset
or power loss are outside this session contract.
"""
from dataclasses import dataclass, field
import hashlib
import json
from uuid import uuid4

from buffered_engine import BufferedInstruction, BufferedProgram
from pinwheel_buffers import TransferError


FORMAT = 'pinwheel-buffered-linear32-v1'
INSTRUCTION_CAPACITY = 128
TX_CAPACITY = RX_CAPACITY = 32
MAX_ID = (1 << 16) - 1
KINDS = {'drive': 0, 'shift': 1, 'keep': 2, 'halt': 3, 'fault': 4}


def _integer(value, low, high, name):
    if type(value) is not int or not low <= value <= high:
        raise ValueError(f'{name} must be an integer in {low}..{high}')
    return value


def encode_instruction(instruction):
    """Encode a supported instruction without silently dropping model fields."""
    if type(instruction) is not BufferedInstruction or instruction.kind not in KINDS:
        raise ValueError('Hardware target accepts only linear drive/shift/keep/halt/fault')
    if (instruction.shift_enabled or instruction.shift_invert or instruction.preserve_enabled or
            instruction.entry_capture is not None or instruction.terminal_capture is not None or
            instruction.check_mask or instruction.check_value or instruction.finish is not None or
            instruction.wait_input != 0 or not instruction.wait_level or instruction.budget != 1 or
            instruction.outcome != 'fault'):
        raise ValueError('Instruction contains fields unsupported by buffered linear hardware')
    _integer(instruction.duration, 1, 256, 'Hardware instruction duration')
    kind = KINDS[instruction.kind]
    if instruction.kind in ('halt', 'fault'):
        return kind
    rx = 0 if instruction.append_input is None else instruction.append_input + 1
    shift = instruction.shift_pin if instruction.kind == 'shift' else 0
    return (kind | instruction.levels << 3 | instruction.enabled << 6 |
            (instruction.duration - 1) << 9 | instruction.preserve << 17 |
            shift << 20 | rx << 22)


def decode_instruction(word):
    """Reject reserved bits and noncanonical fields before constructing a model leaf."""
    _integer(word, 0, (1 << 32) - 1, 'Instruction word')
    kind = word & 7
    if word >> 24 or kind > 4:
        raise ValueError('Reserved instruction bits or unknown hardware operation')
    if kind in (3, 4):
        if word != kind:
            raise ValueError('Terminal hardware words must be exactly HALT or FAULT')
        return BufferedInstruction('halt' if kind == 3 else 'fault')
    levels, enabled = (word >> 3) & 7, (word >> 6) & 7
    duration, preserve = ((word >> 9) & 255) + 1, (word >> 17) & 7
    shift, rx = (word >> 20) & 3, (word >> 22) & 3
    if rx == 3 or (kind != 2 and preserve) or (kind != 1 and shift) or (kind == 1 and shift == 3):
        raise ValueError('Noncanonical hardware instruction fields')
    return BufferedInstruction(('drive', 'shift', 'keep')[kind], duration,
        levels=levels, enabled=enabled, preserve=preserve,
        shift_pin=shift if kind == 1 else None, append_input=None if rx == 0 else rx - 1)


@dataclass(frozen=True)
class BufferedHardwareImage:
    words: tuple[int, ...]
    program_key: str
    idle_levels: int = 0
    idle_enabled: int = 7
    wire_order: str = 'lsb-per-byte'
    protocol: str = 'generic'
    image_format: str = FORMAT
    _program: BufferedProgram = field(init=False, repr=False)
    _key: str = field(init=False, repr=False)

    def __post_init__(self):
        if self.image_format != FORMAT:
            raise ValueError('Wrong buffered hardware image version')
        if type(self.words) is not tuple or not 1 <= len(self.words) <= INSTRUCTION_CAPACITY:
            raise ValueError('Hardware image requires an immutable 1..128 instruction tuple')
        instructions = tuple(decode_instruction(word) for word in self.words)
        program = BufferedProgram(instructions, self.idle_levels, self.idle_enabled,
                                  self.wire_order, self.protocol)
        if type(self.program_key) is not str or self.program_key != program.key:
            raise ValueError('Hardware image differs from its canonical source program identity')
        if program.tx_bits > TX_CAPACITY or program.rx_bits > RX_CAPACITY:
            raise ValueError('Program demand exceeds the dedicated 32-bit hardware buffers')
        object.__setattr__(self, '_program', program)
        canonical = dict(format=self.image_format, program_key=self.program_key,
            words=list(self.words), idle_levels=self.idle_levels, idle_enabled=self.idle_enabled,
            wire_order=self.wire_order, protocol=self.protocol,
            tx_bits=program.tx_bits, rx_bits=program.rx_bits)
        object.__setattr__(self, '_key', hashlib.sha256(json.dumps(canonical,
            sort_keys=True, separators=(',', ':')).encode()).hexdigest())

    @property
    def key(self): return self._key
    @property
    def tx_bits(self): return self._program.tx_bits
    @property
    def rx_bits(self): return self._program.rx_bits
    @property
    def execution_edges(self): return self._program.execution_edges

    def encode_tx(self, payload):
        return self._program.encode_tx(payload)

    def decode_rx(self, bits):
        return self._program.decode_rx(bits)

    def to_bytes(self):
        return (json.dumps(dict(format=self.image_format, program_key=self.program_key,
            image_key=self.key, words=list(self.words), idle_levels=self.idle_levels,
            idle_enabled=self.idle_enabled, wire_order=self.wire_order, protocol=self.protocol,
            tx_bits=self.tx_bits, rx_bits=self.rx_bits), sort_keys=True, indent=2) + '\n').encode()

    @classmethod
    def from_bytes(cls, data):
        if type(data) is not bytes:
            raise ValueError('Captured hardware image must be bytes')
        obj = json.loads(data)
        fields = {'format', 'program_key', 'image_key', 'words', 'idle_levels',
                  'idle_enabled', 'wire_order', 'protocol', 'tx_bits', 'rx_bits'}
        if type(obj) is not dict or set(obj) != fields or type(obj['words']) is not list:
            raise ValueError('Unsupported buffered hardware image schema')
        image = cls(tuple(obj['words']), obj['program_key'], obj['idle_levels'],
                    obj['idle_enabled'], obj['wire_order'], obj['protocol'], obj['format'])
        if (type(obj['tx_bits']) is not int or type(obj['rx_bits']) is not int or
                obj['tx_bits'] != image.tx_bits or obj['rx_bits'] != image.rx_bits or
                obj['image_key'] != image.key):
            raise ValueError('Hardware image demand or identity metadata differs')
        return image


def lower_buffered(program):
    if type(program) is not BufferedProgram or program.schedule is not None:
        raise ValueError('Hardware lowering requires a linear buffered reference program')
    if any(value is not None for value in (program.declared_tx_bits,
            program.declared_rx_bits, program.max_rx_bits)):
        raise ValueError('Reactive demand declarations cannot target the linear hardware image')
    if len(program.instructions) > INSTRUCTION_CAPACITY:
        raise ValueError('Program exceeds 128 hardware instruction rows')
    words = tuple(encode_instruction(item) for item in program.instructions)
    return BufferedHardwareImage(words, program.key, program.idle_levels,
                                 program.idle_enabled, program.wire_order, program.protocol)


def pack_wire_bits(bits):
    if type(bits) is not tuple or len(bits) > TX_CAPACITY or any(type(bit) is not bool for bit in bits):
        raise ValueError('Hardware TX must be an immutable at-most-32 Boolean tuple')
    return sum(int(bit) << index for index, bit in enumerate(bits))


def _field(snapshot, name):
    try:
        value = snapshot[name] if type(snapshot) is dict else getattr(snapshot, name)
    except (KeyError, AttributeError) as error:
        raise RuntimeError('Hardware observation is missing ' + name) from error
    if type(value) is not int:
        raise RuntimeError('Hardware observation ' + name + ' must be an integer')
    return value


def _status(snapshot):
    widths = dict(valid=1, busy=1, retained=1, rejected=1, mode=2, pc=8, remaining=8,
        levels=3, enabled=3, tx_consumed=6, rx_length=6, read_valid=1, read_bit=1,
        generation=16, transfer=16, exhausted=1, pending=1)
    values = {name: _field(snapshot, name) for name in widths}
    for name, width in widths.items():
        if not 0 <= values[name] < 1 << width:
            raise RuntimeError('Hardware observation ' + name + ' exceeds its port width')
    if (values['busy'] != (values['mode'] == 1) or
            values['retained'] != (values['mode'] in (2, 3)) or
            values['tx_consumed'] > TX_CAPACITY or values['rx_length'] > RX_CAPACITY):
        raise RuntimeError('Inconsistent buffered hardware status')
    return values


@dataclass(frozen=True)
class HardwareTransferId:
    epoch: int
    generation: int
    transfer: int
    owner: str

    def __post_init__(self):
        if type(self.epoch) is not int or self.epoch < 0:
            raise ValueError('Hardware session epoch must be a nonnegative model integer')
        _integer(self.generation, 1, MAX_ID, 'Hardware identity generation')
        _integer(self.transfer, 1, MAX_ID, 'Hardware transfer identity')
        if type(self.owner) is not str or not self.owner:
            raise ValueError('Hardware identity needs its software host namespace')


@dataclass(frozen=True)
class BufferedHardwareResult:
    identity: HardwareTransferId
    image_key: str
    program_key: str
    protocol: str
    outcome: str
    tx_consumed_bits: int
    rx_valid_bits: int
    payload: bytes | None
    raw_rx_bits: tuple[bool, ...]


class BufferedHardwareWaitTimeout(TimeoutError):
    def __init__(self, pending):
        super().__init__('Host wait expired; hardware transfer remains owned')
        self.pending = pending


class BufferedHardwareTransportError(RuntimeError):
    """A START or owned command has uncertain transport delivery; retain its handle."""
    def __init__(self, pending, cause):
        super().__init__('Buffered hardware transport failed; inspect the pending transfer')
        self.pending, self.cause = pending, cause


class BufferedHardwareHost:
    """Operate public hardware ports; no engine state or memory is inspected.

    The host owns image changes and cold initialization for this session. START
    snapshots TX and reservation; completed indexed reads do not release them.
    Counters saturate within a hardware initialization epoch. A fresh software
    epoch prevents aliasing handles after a host-issued cold initialization.
    """
    def __init__(self, transport):
        if not callable(getattr(transport, 'edge', None)):
            raise ValueError('Hardware transport must supply public edge(**fields)')
        self.transport = transport
        self._epoch, self._owner = 0, uuid4().hex
        self._image = self._generation = self._pending = self._last = None
        self.edges = 0

    def _edge(self, **fields):
        snapshot = self.transport.edge(**fields)
        self.edges += 1
        self._last = _status(snapshot)
        return self._last

    def status(self):
        return dict(self._edge(command=0))

    def _invalidate(self):
        self._image = self._generation = self._pending = None

    def initialize(self):
        self._epoch += 1
        self._invalidate()
        status = self._edge(initialize=1)
        if any(status[name] for name in ('valid', 'busy', 'retained', 'pending',
                                         'generation', 'transfer', 'exhausted')):
            raise RuntimeError('Cold initialization did not clear the hardware session')
        return dict(status)

    def reset(self):
        self._invalidate()
        status = self._edge(command=7)
        if any(status[name] for name in ('valid', 'busy', 'retained', 'pending')):
            raise RuntimeError('Warm reset did not cancel the owned image and transfer')
        return dict(status)

    def load(self, source):
        # Reconstructing an image validates its full canonical bytes and source
        # identity before even a status observation advances the transport.
        image = lower_buffered(source) if type(source) is BufferedProgram else source
        if type(image) is not BufferedHardwareImage:
            raise ValueError('Hardware load requires a versioned buffered image')
        image = BufferedHardwareImage.from_bytes(image.to_bytes())
        if self._pending is not None:
            raise TransferError('Release or reset the owned transfer before loading an image')
        before = self._edge(command=0)
        if before['busy'] or before['retained']:
            raise TransferError('Hardware transfer remains owned')
        if before['generation'] == MAX_ID:
            raise TransferError('Hardware generation is exhausted; cold initialize a new epoch')
        self._image = self._generation = None
        for address, word in enumerate(image.words):
            written = self._edge(command=1, address=address, word=word)
            if written['rejected'] or written['busy'] or written['retained'] or not written['pending']:
                raise TransferError('Hardware rejected buffered instruction upload')
        committed = self._edge(command=2, count=len(image.words),
            idle_levels=image.idle_levels, idle_enabled=image.idle_enabled)
        if (committed['rejected'] or not committed['valid'] or committed['pending'] or
                committed['busy'] or committed['retained'] or
                committed['generation'] != before['generation'] + 1 or
                committed['transfer'] != before['transfer']):
            raise TransferError('Hardware did not accept the exact buffered image commit')
        self._image, self._generation = image, committed['generation']
        return LoadedBufferedHardware(self, image, self._epoch, self._generation)

    def _submit(self, loaded, tx, rx_limit):
        loaded._require_current()
        if self._pending is not None:
            raise TransferError('Release or reset the owned transfer before submitting another')
        if type(tx) not in (bytes, bytearray, memoryview):
            raise ValueError('Hardware TX must be bytes or a byte buffer')
        bits = loaded.image.encode_tx(bytes(tx))
        rx_limit = loaded.image.rx_bits if rx_limit is None else rx_limit
        _integer(rx_limit, loaded.image.rx_bits, RX_CAPACITY, 'Hardware RX reservation')
        data = pack_wire_bits(bits)
        before = self._edge(command=0)
        if (before['busy'] or before['retained'] or before['pending'] or
                not before['valid'] or before['generation'] != loaded.generation):
            raise TransferError('Hardware lost the loaded buffered image or owns another transfer')
        if before['transfer'] == MAX_ID:
            raise TransferError('Hardware transfer identities are exhausted; cold initialize')
        identity = HardwareTransferId(self._epoch, loaded.generation,
                                      before['transfer'] + 1, self._owner)
        pending = PendingBufferedHardware(self, loaded.image, identity, len(bits), rx_limit)
        self._pending = pending
        try:
            accepted = self._edge(command=3, tx_data=data, tx_length=len(bits),
                rx_capacity=rx_limit, expected_generation=loaded.generation)
        except Exception as error:
            raise BufferedHardwareTransportError(pending, error) from error
        if (accepted['rejected'] or accepted['generation'] != identity.generation or
                accepted['transfer'] != identity.transfer or
                not (accepted['busy'] or accepted['retained'])):
            if (accepted['rejected'] and not accepted['busy'] and not accepted['retained'] and
                    accepted['generation'] == before['generation'] and
                    accepted['transfer'] == before['transfer']):
                self._pending = None
                raise TransferError('Hardware rejected the owned START')
            raise BufferedHardwareTransportError(pending,
                RuntimeError('Hardware START receipt is inconsistent with its owned identity'))
        return pending


@dataclass(frozen=True)
class LoadedBufferedHardware:
    host: BufferedHardwareHost
    image: BufferedHardwareImage
    epoch: int
    generation: int

    def _require_current(self):
        if (self.epoch != self.host._epoch or self.image != self.host._image or
                self.generation != self.host._generation):
            raise TransferError('Loaded buffered image belongs to a stale hardware session')

    def submit(self, *, tx, rx_limit=None):
        return self.host._submit(self, tx, rx_limit)

    def run(self, *, tx, rx_limit=None, timeout_cycles=100_000):
        _integer(timeout_cycles, 0, (1 << 63) - 1, 'Host wait budget')
        pending = self.submit(tx=tx, rx_limit=rx_limit)
        pending.wait(timeout_cycles=timeout_cycles)
        result = pending.read()
        pending.release()
        return result


@dataclass(frozen=True)
class PendingBufferedHardware:
    host: BufferedHardwareHost
    image: BufferedHardwareImage
    identity: HardwareTransferId
    tx_count: int
    rx_limit: int

    def _require_local(self):
        if (self.identity.owner != self.host._owner or self.identity.epoch != self.host._epoch or
                self.host._pending is not self):
            raise TransferError('Stale or unowned hardware transfer handle')

    def _owned(self, status):
        if (status['generation'] != self.identity.generation or
                status['transfer'] != self.identity.transfer):
            raise TransferError('Hardware observation belongs to a different transfer identity')
        if status['tx_consumed'] > self.tx_count or status['rx_length'] > self.rx_limit:
            raise RuntimeError('Hardware result exceeds its accepted data bounds')
        return status

    def _edge(self, **fields):
        self._require_local()
        try:
            return self._owned(self.host._edge(**fields))
        except TransferError:
            raise
        except Exception as error:
            raise BufferedHardwareTransportError(self, error) from error

    def wait(self, *, timeout_cycles=100_000):
        _integer(timeout_cycles, 0, (1 << 63) - 1, 'Host wait budget')
        self._require_local()
        status = self._owned(self.host._last) if self.host._last is not None else self._edge(command=0)
        remaining = timeout_cycles
        while status['busy']:
            if remaining == 0:
                raise BufferedHardwareWaitTimeout(self)
            status = self._edge(command=0)
            remaining -= 1
        if not status['retained']:
            raise TransferError('Hardware no longer retains this transfer')
        return dict(status)

    def read(self):
        first = self._edge(command=0, read_index=0)
        if not first['retained'] or first['busy']:
            raise TransferError('Result read requires a retained hardware completion')
        bits = []
        frozen = tuple(first[name] for name in ('generation', 'transfer', 'mode',
                         'tx_consumed', 'rx_length', 'levels', 'enabled'))
        for index in range(first['rx_length']):
            status = first if index == 0 else self._edge(command=0, read_index=index)
            if (not status['retained'] or status['busy'] or not status['read_valid'] or
                    tuple(status[name] for name in ('generation', 'transfer', 'mode',
                          'tx_consumed', 'rx_length', 'levels', 'enabled')) != frozen):
                raise RuntimeError('Indexed hardware result changed or its bit window is invalid')
            bits.append(bool(status['read_bit']))
        if not bits and first['read_valid']:
            raise RuntimeError('Empty hardware result exposed a valid read bit')
        outcome = 'complete' if first['mode'] == 2 else 'fault'
        raw = tuple(bits)
        if outcome == 'complete' and first['tx_consumed'] != self.image.tx_bits:
            raise ValueError('Completed hardware transfer did not consume the declared TX demand')
        payload = self.image.decode_rx(raw) if outcome == 'complete' else None
        return BufferedHardwareResult(self.identity, self.image.key, self.image.program_key,
            self.image.protocol, outcome, first['tx_consumed'], len(raw), payload, raw)

    def release(self):
        before = self._edge(command=0)
        if not before['retained'] or before['busy']:
            raise TransferError('Matching release requires a retained hardware completion')
        released = self._edge(command=4, expected_generation=self.identity.generation,
                              expected_transfer=self.identity.transfer)
        if released['rejected'] or released['busy'] or released['retained']:
            raise TransferError('Hardware rejected matching release')
        self.host._pending = None
