"""Static compiler for the separately named sampled-ready streaming target.

No link is opened here. ReadyHost must revalidate the exact source/word binding
before its first link action. Transfer data and START counts are not image rows.
"""
from dataclasses import asdict, dataclass
import hashlib
import json
import re

from streaming_compile import Cell, FIELDS, BOOLS, integer, word_bytes

FORMAT = 'pinwheel-streaming-ready-cell64-v1'
OPCODES = {'pulse': 0, 'stream': 1, 'halt': 2, 'fault': 3, 'drive_wait': 4}
GUARD_FIELDS = (('mask', 50, 2), ('expected', 52, 2), ('budget', 54, 8))
I2C64_BITS = 9 * 65


@dataclass(frozen=True)
class WaitLimit:
    """None explicitly names an unbounded wait; bounded values count polls.

    A budget B permits B predicate tests. Readiness wins on the final test;
    otherwise test B faults. The device initializes its countdown to B-1.
    """
    budget: int | None

    def __post_init__(self):
        if self.budget is not None:
            integer(self.budget, 1, 255, 'Bounded ready poll budget')

    @classmethod
    def unbounded(cls):
        return cls(None)

    @classmethod
    def misses(cls, count):
        integer(count, 1, 255, 'Bounded ready poll budget')
        return cls(count)

    @property
    def encoded(self):
        return 0 if self.budget is None else self.budget


@dataclass(frozen=True)
class Guard:
    mask: int = 0
    expected: int = 0
    limit: WaitLimit = WaitLimit.unbounded()

    def __post_init__(self):
        integer(self.mask, 0, 3, 'Ready input mask')
        integer(self.expected, 0, 3, 'Ready expected value')
        if self.expected & ~self.mask:
            raise ValueError('Ready expected value has bits outside its mask')
        if type(self.limit) is not WaitLimit:
            raise ValueError('Guard requires an explicitly named WaitLimit')
        self.limit.__post_init__()


@dataclass(frozen=True)
class Pins:
    levels: int = 0
    enabled: int = 0

    def __post_init__(self):
        integer(self.levels, 0, 7, 'Ready pin levels')
        integer(self.enabled, 0, 7, 'Ready pin enables')


@dataclass(frozen=True)
class Instruction:
    operation: str
    cell: Cell | None = None
    guard: Guard | None = None
    pins: Pins | None = None

    def __post_init__(self):
        if type(self.operation) is not str or self.operation not in OPCODES:
            raise ValueError('Unsupported ready operation')
        if self.operation in ('pulse', 'stream'):
            if type(self.cell) is not Cell or self.pins is not None:
                raise ValueError('Ready pulse/stream requires only a Cell and optional stream guard')
            self.cell.__post_init__()
            if self.operation == 'pulse' and (self.guard is not None or not self.cell.pulse_canonical()):
                raise ValueError('Pulse has noncanonical stream/guard operands')
        elif self.operation == 'drive_wait':
            if self.cell is not None or type(self.pins) is not Pins or type(self.guard) is not Guard:
                raise ValueError('Drive-wait requires only Pins and a Guard')
            self.pins.__post_init__()
        elif any(value is not None for value in (self.cell, self.guard, self.pins)):
            raise ValueError('Terminal instructions have no operands')
        if self.guard is not None:
            if type(self.guard) is not Guard:
                raise ValueError('Ready instruction requires a typed Guard')
            self.guard.__post_init__()


def encode(instruction):
    if type(instruction) is not Instruction:
        raise ValueError('Expected a typed ready instruction')
    instruction.__post_init__()
    word = OPCODES[instruction.operation]
    if instruction.cell is not None:
        for name, shift, _ in FIELDS:
            value = getattr(instruction.cell, name)
            word |= int(value - 1 if name.endswith('_cycles') else value) << shift
    if instruction.pins is not None:
        word |= instruction.pins.levels << 19 | instruction.pins.enabled << 22
    if instruction.guard is not None:
        guard = instruction.guard
        word |= guard.mask << 50 | guard.expected << 52 | guard.limit.encoded << 54
        if instruction.operation == 'stream':
            word |= 1 << 62
    return word


def decode(word):
    integer(word, 0, (1 << 64) - 1, 'Ready word')
    opcode = word & 7
    if word >> 63 or opcode > 4:
        raise ValueError('Reserved ready opcode or bits')
    operation = next(name for name, code in OPCODES.items() if code == opcode)
    if operation in ('halt', 'fault'):
        if word != opcode:
            raise ValueError('Noncanonical terminal operands')
        return Instruction(operation)
    mask, expected, budget = ((word >> shift) & ((1 << width) - 1)
                              for _, shift, width in GUARD_FIELDS)
    guard = Guard(mask, expected, WaitLimit.unbounded() if budget == 0 else WaitLimit.misses(budget))
    if operation == 'drive_wait':
        allowed = 7 | 7 << 19 | 7 << 22 | ((1 << 12) - 1) << 50
        if word & ~allowed:
            raise ValueError('Noncanonical drive-wait operands')
        result = Instruction(operation, guard=guard, pins=Pins((word >> 19) & 7, (word >> 22) & 7))
    else:
        if operation == 'pulse' and word >> 31:
            raise ValueError('Pulse has noncanonical stream/guard operands')
        enabled = bool(word & (1 << 62))
        if not enabled and word >> 50:
            raise ValueError('Inactive ready guard fields must be zero')
        values = {}
        for name, shift, width in FIELDS:
            value = (word >> shift) & ((1 << width) - 1)
            values[name] = bool(value) if name in BOOLS else value + 1 if name.endswith('_cycles') else value
        result = Instruction(operation, Cell(**values), guard if enabled else None)
    if encode(result) != word:
        raise ValueError('Ready word does not round trip')
    return result


@dataclass(frozen=True)
class Source:
    instructions: tuple[Instruction, ...]
    idle_levels: int = 0
    idle_enabled: int = 0

    def validate(self):
        integer(self.idle_levels, 0, 7, 'Ready idle levels')
        integer(self.idle_enabled, 0, 7, 'Ready idle enables')
        if type(self.instructions) is not tuple or not 2 <= len(self.instructions) <= 64:
            raise ValueError('Ready program requires 2..64 stored instructions')
        operations = []
        for instruction in self.instructions:
            encode(instruction)
            operations.append(instruction.operation)
        if operations[-1] not in ('halt', 'fault') or operations.count('stream') != 1:
            raise ValueError('Ready program requires one stream and a final halt/fault')
        if any(operation not in ('pulse', 'stream', 'drive_wait') for operation in operations[:-1]):
            raise ValueError('Only pulse/drive-wait prefixes and suffixes are supported')


def source_bytes(source):
    return json.dumps(asdict(source), sort_keys=True, separators=(',', ':')).encode()


@dataclass(frozen=True)
class Certificate:
    format: str
    source_sha256: str
    words_sha256: str
    rows: int
    stream_row: int

    def __post_init__(self):
        if type(self.format) is not str or self.format != FORMAT:
            raise ValueError('Unsupported ready certificate format')
        for value in (self.source_sha256, self.words_sha256):
            if type(value) is not str or not re.fullmatch(r'[0-9a-f]{64}', value):
                raise ValueError('Malformed ready certificate hash')
        integer(self.rows, 2, 64, 'Ready certificate rows')
        integer(self.stream_row, 0, self.rows - 2, 'Ready certificate stream row')


@dataclass(frozen=True)
class CompiledImage:
    source: Source
    words: tuple[int, ...]
    certificate: Certificate

    def __post_init__(self):
        validate_image(self)

    @property
    def idle_levels(self): return self.source.idle_levels

    @property
    def idle_enabled(self): return self.source.idle_enabled


def validate_image(image):
    if type(image) is not CompiledImage or type(image.source) is not Source:
        raise ValueError('Ready upload requires a CompiledImage with a typed source')
    image.source.validate()
    expected = tuple(map(encode, image.source.instructions))
    if type(image.words) is not tuple or image.words != expected:
        raise ValueError('Ready compiled words differ from their source')
    if any(decode(word) != instruction for word, instruction in zip(image.words, image.source.instructions)):
        raise ValueError('Ready decoding differs from source')
    certificate = Certificate(FORMAT, hashlib.sha256(source_bytes(image.source)).hexdigest(),
        hashlib.sha256(word_bytes(expected)).hexdigest(), len(expected),
        next(k for k, instruction in enumerate(image.source.instructions) if instruction.operation == 'stream'))
    if type(image.certificate) is not Certificate:
        raise ValueError('Ready certificate does not match source/words')
    image.certificate.__post_init__()
    if image.certificate != certificate:
        raise ValueError('Ready certificate does not match source/words')
    return certificate


def lower(instructions, *, idle_levels=0, idle_enabled=0):
    source = Source(tuple(instructions), idle_levels, idle_enabled)
    source.validate()
    words = tuple(map(encode, source.instructions))
    certificate = Certificate(FORMAT, hashlib.sha256(source_bytes(source)).hexdigest(),
        hashlib.sha256(word_bytes(words)).hexdigest(), len(words),
        next(k for k, instruction in enumerate(source.instructions) if instruction.operation == 'stream'))
    return CompiledImage(source, words, certificate)


def i2c_image(low_cycles=4, high_cycles=4, wait_budget=31, *, peer_tco=1, stretch_bound=28):
    """One 585-slot address+64-byte read OR write; data/ACK roles are host bits.

    SCL is output0/raw0, SDA output1/raw1. Peers must satisfy the named sampled
    timing contract; these static inequalities do not establish electrical timing.
    NACKs are observed afterward. No repeated START or NACK branch is encoded.
    """
    integer(low_cycles, 3, 256, 'I2C LOW cycles')
    integer(high_cycles, 3, 256, 'I2C HIGH cycles')
    integer(wait_budget, 1, 255, 'I2C bounded poll budget')
    integer(peer_tco, 0, 253, 'I2C peer tco')
    integer(stretch_bound, 0, 252, 'I2C stretch bound')
    if low_cycles < peer_tco + 3:
        raise ValueError('I2C LOW requires peer_tco + 3 sample clocks')
    if wait_budget < stretch_bound + 3:
        raise ValueError('I2C poll budget requires stretch_bound + 3 clocks')
    limit = WaitLimit.misses(wait_budget)
    def stationary(enabled):
        return Instruction('pulse', Cell(high_cycles, high_cycles,
            low_enabled=enabled, high_enabled=enabled))
    def wait(enabled, mask, expected):
        return Instruction('drive_wait', guard=Guard(mask, expected, limit), pins=Pins(0, enabled))
    stream = Instruction('stream', Cell(low_cycles, high_cycles,
        low_enabled=1, high_enabled=0, tx_output=1, rx_input=1,
        transmit=True, receive=True, tx_enable_mode=True), Guard(1, 1, limit))
    # SCL stays LOW through both halves, but must retain the declared LOW
    # duration even when LOW is much longer than the HIGH setup interval.
    stop_low = Instruction('pulse', Cell(low_cycles, high_cycles,
        low_enabled=3, high_enabled=3))
    return lower((wait(0, 3, 3), stationary(2), stream, stop_low,
                  wait(2, 1, 1), stationary(2), Instruction('halt')))


def lean_guard(guard):
    limit = '.unbounded' if guard.limit.budget is None else f'.misses {guard.limit.budget - 1}'
    return '{ mask := ' + str(guard.mask) + ', expected := ' + str(guard.expected) + ', limit := ' + limit + ' }'


def lean_instruction(instruction):
    from streaming_compile import lean_instruction as old_instruction, Instruction as OldInstruction
    if instruction.operation == 'drive_wait':
        return '.driveWait ⟨' + str(instruction.pins.levels) + ', ' + str(instruction.pins.enabled) + '⟩ (' + lean_guard(instruction.guard) + ')'
    if instruction.cell is None:
        return '.' + instruction.operation
    text = old_instruction(OldInstruction(instruction.operation, instruction.cell))
    if instruction.operation == 'stream':
        text += ' ' + ('none' if instruction.guard is None else '(some (' + lean_guard(instruction.guard) + '))')
    return text


def lean_certificate(image):
    """Emit an automatic closed kernel check of exact source, words and idle."""
    validate_image(image)
    instructions = ',\n  '.join(map(lean_instruction, image.source.instructions))
    words = ', '.join(str(word) for word in image.words)
    return ('import Pinwheel.Program.StreamingReadyCompile\nopen Pinwheel.Program.StreamingReady\n'
        'set_option maxRecDepth 10000\ndef source : List Instruction := [\n  ' + instructions + ']\n'
        'example : (match compile source ⟨' + str(image.idle_levels) + ', ' + str(image.idle_enabled) +
        '⟩ with | .ok image => some image.words | .error _ => none) = some [' + words +
        '] := by decide +kernel\n')
