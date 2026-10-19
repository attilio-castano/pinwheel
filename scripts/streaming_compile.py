"""Static source compiler for the versioned programmable streaming ISA.

Lengths are START operands, never unrolled into instruction rows. No transport
is opened here. A host must call validate_image before its first link action.
"""
from dataclasses import asdict, dataclass
import hashlib
import json
import re

FORMAT = 'pinwheel-streaming-cell64-v1'
FIELDS = (
    ('low_cycles', 3, 8), ('high_cycles', 11, 8),
    ('low_levels', 19, 3), ('low_enabled', 22, 3),
    ('high_levels', 25, 3), ('high_enabled', 28, 3),
    ('tx_output', 31, 2), ('rx_input', 33, 1),
    ('transmit', 34, 1), ('receive', 35, 1),
    ('last_low_levels', 36, 3), ('last_high_levels', 39, 3),
    ('tx_invert', 42, 1), ('tx_enable_mode', 43, 1),
    ('last_low_enabled', 44, 3), ('last_high_enabled', 47, 3),
)
OPCODES = {'pulse': 0, 'stream': 1, 'halt': 2, 'fault': 3}
BOOLS = {'transmit', 'receive', 'tx_invert', 'tx_enable_mode'}


def integer(value, low, high, name):
    if type(value) is not int or not low <= value <= high:
        raise ValueError(f'{name} must be an integer in {low}..{high}')


@dataclass(frozen=True)
class Cell:
    low_cycles: int = 1
    high_cycles: int = 1
    low_levels: int = 0
    low_enabled: int = 0
    high_levels: int = 0
    high_enabled: int = 0
    tx_output: int = 0
    rx_input: int = 0
    transmit: bool = False
    receive: bool = False
    last_low_levels: int = 0
    last_high_levels: int = 0
    tx_invert: bool = False
    tx_enable_mode: bool = False
    last_low_enabled: int = 0
    last_high_enabled: int = 0

    def __post_init__(self):
        for name, _, width in FIELDS:
            value = getattr(self, name)
            if name in BOOLS:
                if type(value) is not bool:
                    raise ValueError(name + ' must be Boolean')
            elif name.endswith('_cycles'):
                integer(value, 1, 256, name)
            else:
                integer(value, 0, 2 if name == 'tx_output' else (1 << width) - 1, name)

    def pulse_canonical(self):
        return not any(getattr(self, name) for name in (
            'tx_output', 'rx_input', 'transmit', 'receive', 'tx_invert', 'tx_enable_mode',
            'last_low_levels', 'last_high_levels', 'last_low_enabled', 'last_high_enabled'))


@dataclass(frozen=True)
class Instruction:
    operation: str
    cell: Cell | None = None

    def __post_init__(self):
        if type(self.operation) is not str or self.operation not in OPCODES:
            raise ValueError('Unsupported streaming operation')
        if self.operation in ('pulse', 'stream'):
            if type(self.cell) is not Cell:
                raise ValueError('A pulse/stream requires a Cell')
            if self.operation == 'pulse' and not self.cell.pulse_canonical():
                raise ValueError('Pulse has noncanonical stream fields')
        elif self.cell is not None:
            raise ValueError('Terminal instructions have no cell operands')


def encode(instruction):
    if type(instruction) is not Instruction:
        raise ValueError('Expected a typed streaming instruction')
    instruction.__post_init__()
    word = OPCODES[instruction.operation]
    if instruction.cell is not None:
        instruction.cell.__post_init__()
        for name, shift, _ in FIELDS:
            value = getattr(instruction.cell, name)
            if name.endswith('_cycles'):
                value -= 1
            word |= int(value) << shift
    return word


def decode(word):
    integer(word, 0, (1 << 64) - 1, 'Streaming word')
    opcode = word & 7
    if word >> 50 or opcode > 3:
        raise ValueError('Reserved streaming opcode or bits')
    operation = tuple(OPCODES)[opcode]
    if operation in ('halt', 'fault'):
        if word != opcode:
            raise ValueError('Noncanonical terminal operands')
        return Instruction(operation)
    values = {}
    for name, shift, width in FIELDS:
        value = (word >> shift) & ((1 << width) - 1)
        values[name] = bool(value) if name in BOOLS else value + 1 if name.endswith('_cycles') else value
    result = Instruction(operation, Cell(**values))
    if encode(result) != word:
        raise ValueError('Streaming word does not round trip')
    return result


@dataclass(frozen=True)
class Source:
    instructions: tuple[Instruction, ...]
    idle_levels: int = 0
    idle_enabled: int = 0

    def validate(self):
        integer(self.idle_levels, 0, 7, 'Idle levels')
        integer(self.idle_enabled, 0, 7, 'Idle enables')
        if type(self.instructions) is not tuple or not 2 <= len(self.instructions) <= 64:
            raise ValueError('Streaming program requires 2..64 stored instructions')
        operations = []
        for instruction in self.instructions:
            encode(instruction)
            operations.append(instruction.operation)
        if operations[-1] not in ('halt', 'fault') or operations.count('stream') != 1:
            raise ValueError('Program requires exactly one stream and a final halt/fault')
        if any(operation not in ('pulse', 'stream') for operation in operations[:-1]):
            raise ValueError('Only pulse prefix/suffix around one stream are supported')


def source_bytes(source):
    return json.dumps(asdict(source), sort_keys=True, separators=(',', ':')).encode()


def word_bytes(words):
    return b''.join(word.to_bytes(8, 'little') for word in words)


@dataclass(frozen=True)
class Certificate:
    format: str
    source_sha256: str
    words_sha256: str
    rows: int
    stream_row: int

    def __post_init__(self):
        if self.format != FORMAT or type(self.format) is not str:
            raise ValueError('Unsupported streaming certificate format')
        for value in (self.source_sha256, self.words_sha256):
            if type(value) is not str or not re.fullmatch(r'[0-9a-f]{64}', value):
                raise ValueError('Malformed streaming certificate hash')
        integer(self.rows, 2, 64, 'Certificate rows')
        integer(self.stream_row, 0, self.rows - 2, 'Certificate stream row')


@dataclass(frozen=True)
class CompiledImage:
    source: Source
    words: tuple[int, ...]
    certificate: Certificate

    def __post_init__(self):
        validate_image(self)

    @property
    def idle_levels(self):
        return self.source.idle_levels

    @property
    def idle_enabled(self):
        return self.source.idle_enabled


def validate_image(image):
    """Recheck the whole source/word binding; call before every upload begins."""
    if type(image) is not CompiledImage or type(image.source) is not Source:
        raise ValueError('Upload requires a CompiledImage with a typed source')
    image.source.validate()
    expected = tuple(map(encode, image.source.instructions))
    if type(image.words) is not tuple or image.words != expected:
        raise ValueError('Compiled words differ from their source')
    if any(decode(word) != instruction for word, instruction in zip(image.words, image.source.instructions)):
        raise ValueError('Compiled instruction decoding differs from source')
    certificate = Certificate(FORMAT, hashlib.sha256(source_bytes(image.source)).hexdigest(),
        hashlib.sha256(word_bytes(expected)).hexdigest(), len(expected),
        next(index for index, instruction in enumerate(image.source.instructions)
             if instruction.operation == 'stream'))
    if type(image.certificate) is not Certificate:
        raise ValueError('Compiled certificate does not match source/words')
    image.certificate.__post_init__()
    if image.certificate != certificate:
        raise ValueError('Compiled certificate does not match source/words')
    return certificate


def lower(instructions, *, idle_levels=0, idle_enabled=0):
    source = Source(tuple(instructions), idle_levels, idle_enabled)
    source.validate()
    words = tuple(map(encode, source.instructions))
    certificate = Certificate(FORMAT, hashlib.sha256(source_bytes(source)).hexdigest(),
        hashlib.sha256(word_bytes(words)).hexdigest(), len(words),
        next(index for index, instruction in enumerate(source.instructions) if instruction.operation == 'stream'))
    return CompiledImage(source, words, certificate)


def spi_image(half_cycles=4):
    """One generic duplex stream, START count is the number of wire bits."""
    integer(half_cycles, 3, 256, 'SPI half cycles')
    hold = Cell(half_cycles, half_cycles, low_enabled=7, high_enabled=7)
    stream = Cell(half_cycles, half_cycles, low_enabled=7, high_levels=2, high_enabled=7,
                  transmit=True, receive=True)
    # A pulse returns to its LOW pins before HALT. Keep CS asserted through
    # that return; only HALT releases CS, so there is no reselection glitch.
    release = Cell(half_cycles, half_cycles, low_enabled=7, high_enabled=7)
    return lower((Instruction('pulse', hold), Instruction('stream', stream),
                  Instruction('pulse', release), Instruction('halt')), idle_levels=4, idle_enabled=7)


def jtag_image(half_cycles=4):
    """Reset→Shift-DR, last-bit TMS mask, Update-DR→Run-Test/Idle."""
    integer(half_cycles, 3, 256, 'JTAG half cycles')
    def pulse(tms):
        return Instruction('pulse', Cell(half_cycles, half_cycles,
            low_levels=tms << 2, high_levels=(tms << 2) | 2, low_enabled=7, high_enabled=7))
    prefix = tuple(pulse(tms) for tms in (1, 1, 1, 1, 1, 0, 1, 0, 0))
    stream = Instruction('stream', Cell(half_cycles, half_cycles, low_enabled=7,
        high_levels=2, high_enabled=7, transmit=True, receive=True,
        last_low_levels=4, last_high_levels=4))
    return lower((*prefix, stream, pulse(1), pulse(0), Instruction('halt')),
                 idle_levels=0, idle_enabled=7)


def lean_instruction(instruction):
    if instruction.cell is None:
        return '.' + instruction.operation
    c = instruction.cell
    boolean = lambda value: 'true' if value else 'false'
    return '.' + instruction.operation + ' {' + ', '.join((
        f'lowDuration := {c.low_cycles - 1}', f'highDuration := {c.high_cycles - 1}',
        f'lowPins := ⟨{c.low_levels}, {c.low_enabled}⟩',
        f'highPins := ⟨{c.high_levels}, {c.high_enabled}⟩',
        f'txOutput := {c.tx_output}', f'rxInput := {c.rx_input}',
        f'transmit := {boolean(c.transmit)}', f'receive := {boolean(c.receive)}',
        f'lastLowLevels := {c.last_low_levels}', f'lastHighLevels := {c.last_high_levels}',
        f'txInvert := {boolean(c.tx_invert)}', f'txEnableMode := {boolean(c.tx_enable_mode)}',
        f'lastLowEnabled := {c.last_low_enabled}', f'lastHighEnabled := {c.last_high_enabled}')) + '}'


def lean_certificate(image):
    """Generate a closed automatic kernel check; no user agreement proof needed."""
    validate_image(image)
    instructions = ',\n  '.join(map(lean_instruction, image.source.instructions))
    words = ', '.join(str(word) for word in image.words)
    return ('import Pinwheel.Program.StreamingCompile\nopen Pinwheel.Program.Streaming\n'
        'set_option maxRecDepth 10000\n'
        'def source : List Instruction := [\n  ' + instructions + ']\n'
        'example : (match compile source ⟨' + str(image.idle_levels) + ', ' + str(image.idle_enabled) +
        '⟩ with | .ok image => some image.words | .error _ => none) = some [' + words +
        '] := by decide +kernel\n')
