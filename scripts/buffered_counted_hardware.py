"""Canonical compact timed images for the separate counted buffered circuit.

Each physical row stores one existing 32-bit timed instruction and 24 bits of
enclosing-loop metadata. Schedule syntax and virtual positions are not rows.
The original immutable source tree is retained and re-lowered when importing an
image; sequence grouping cannot be reconstructed from row metadata alone.
Ownership, indexed result reads and reset epochs reuse the linear host.
"""
from dataclasses import asdict, dataclass, field, fields
import hashlib
import json

from buffered_engine import (BufferedBlock, BufferedInstruction, BufferedProgram,
                             BufferedRepeat, BufferedSequence)
from buffered_hardware import (BufferedHardwareHost, RX_CAPACITY, TX_CAPACITY,
    _field, _integer, _status, decode_instruction, encode_instruction)


FORMAT = 'pinwheel-buffered-counted32-v1'
INSTRUCTION_CAPACITY = 64
CONTROL_WIDTH = 24
ROW_WIDTH = 32 + CONTROL_WIDTH
VIRTUAL_CAPACITY = 1024


@dataclass(frozen=True)
class CountedControl:
    depth: int = 0
    outer_start: int = 0
    outer_count: int = 1
    inner_start: int = 0
    inner_count: int = 1
    outer_end: bool = False
    inner_end: bool = False

    def __post_init__(self):
        _integer(self.depth, 0, 2, 'Loop depth')
        for name in ('outer_start', 'inner_start'):
            _integer(getattr(self, name), 0, 63, name)
        for name in ('outer_count', 'inner_count'):
            _integer(getattr(self, name), 1, 8, name)
        if type(self.outer_end) is not bool or type(self.inner_end) is not bool:
            raise ValueError('Loop endings must be Boolean')
        if self.depth == 0 and (self.outer_start or self.outer_count != 1 or self.outer_end):
            raise ValueError('Inactive outer-loop fields must be zero')
        if self.depth < 2 and (self.inner_start or self.inner_count != 1 or self.inner_end):
            raise ValueError('Inactive inner-loop fields must be zero')
        if self.depth == 2 and (self.inner_start < self.outer_start or
                               self.outer_end and not self.inner_end):
            raise ValueError('Inner loop must nest inside its enclosing outer loop')


def encode_control(control):
    if type(control) is not CountedControl:
        raise ValueError('Counted metadata requires a canonical loop descriptor')
    return (control.depth | control.outer_start << 2 |
            (control.outer_count - 1) << 8 | control.inner_start << 11 |
            (control.inner_count - 1) << 17 | int(control.outer_end) << 20 |
            int(control.inner_end) << 21)


def decode_control(word):
    _integer(word, 0, (1 << CONTROL_WIDTH) - 1, 'Counted control word')
    if word >> 22 or word & 3 == 3:
        raise ValueError('Reserved counted metadata bits or invalid loop depth')
    return CountedControl(word & 3, (word >> 2) & 63, ((word >> 8) & 7) + 1,
        (word >> 11) & 63, ((word >> 17) & 7) + 1,
        bool(word & (1 << 20)), bool(word & (1 << 21)))


def _totals(code):
    """Derive full timed-path demands without expanding a repeat body."""
    if type(code) is BufferedBlock:
        return (len(code.instructions), sum(i.kind == 'shift' for i in code.instructions),
            sum(i.append_input is not None for i in code.instructions),
            sum(i.duration for i in code.instructions if i.kind not in ('halt', 'fault')))
    if type(code) is BufferedSequence:
        children = [_totals(part) for part in code.parts]
        return tuple(sum(child[index] for child in children) for index in range(4))
    if type(code) is BufferedRepeat:
        return tuple(code.count * value for value in _totals(code.body))
    raise ValueError('Unsupported compact timed schedule')


def _lower(program):
    if type(program) is not BufferedProgram:
        raise ValueError('Counted lowering requires a buffered reference program')
    code = program.schedule or BufferedBlock(program.instructions)
    if code.words > INSTRUCTION_CAPACITY or code.nodes > 256 or code.nesting > 2:
        raise ValueError('Counted image exceeds 64 leaves, 256 syntax nodes or two loop levels')
    span, tx_bits, rx_bits, edges = _totals(code)
    if not 1 <= span <= VIRTUAL_CAPACITY:
        raise ValueError('Counted virtual span must be in 1..1024')
    if tx_bits > TX_CAPACITY or rx_bits > RX_CAPACITY:
        raise ValueError('Counted demand exceeds the dedicated 32-bit hardware buffers')
    if program.schedule is not None and (program.declared_tx_bits != tx_bits or
            program.declared_rx_bits != rx_bits or program.max_rx_bits != rx_bits):
        raise ValueError('Counted timed declarations must equal the derived TX/RX demands')

    rows = []
    endings = []

    def walk(node, enclosing=()):
        if type(node) is BufferedBlock:
            for instruction in node.instructions:
                rows.append((instruction, enclosing))
                endings.append([False, False])
        elif type(node) is BufferedSequence:
            for part in node.parts:
                walk(part, enclosing)
        elif type(node) is BufferedRepeat:
            loop = (len(rows), node.count)
            walk(node.body, (*enclosing, loop))
            endings[-1][len(enclosing)] = True
        else:
            raise ValueError('Unsupported compact timed schedule')

    walk(code)
    terminals = [index for index, (instruction, _) in enumerate(rows)
                 if instruction.kind in ('halt', 'fault')]
    if terminals != [len(rows) - 1] or rows[-1][1]:
        raise ValueError('Counted timed schedules require one final terminal outside repeats')
    words, controls = [], []
    for index, (instruction, enclosing) in enumerate(rows):
        words.append(encode_instruction(instruction))
        outer = enclosing[0] if enclosing else (0, 1)
        inner = enclosing[1] if len(enclosing) == 2 else (0, 1)
        controls.append(encode_control(CountedControl(len(enclosing), *outer, *inner,
                                                    *endings[index])))
    return tuple(words), tuple(controls), (span, tx_bits, rx_bits, edges)


def _definition(program):
    return dict(target=program.target, protocol=program.protocol,
        idle_levels=program.idle_levels, idle_enabled=program.idle_enabled,
        wire_order=program.wire_order,
        instructions=[asdict(item) for item in program.instructions],
        schedule=None if program.schedule is None else program.schedule.definition(),
        declared_tx_bits=program.declared_tx_bits, declared_rx_bits=program.declared_rx_bits,
        max_rx_bits=program.max_rx_bits)


def _read_instruction(obj):
    if type(obj) is not dict or set(obj) != {f.name for f in fields(BufferedInstruction)}:
        raise ValueError('Unsupported source instruction schema')
    values = dict(obj)
    for name in ('entry_capture', 'terminal_capture', 'finish'):
        if type(values[name]) is list:
            values[name] = tuple(values[name])
    return BufferedInstruction(**values)


def _read_code(obj, depth=0):
    if type(obj) is not dict or depth > 256:
        raise ValueError('Unsupported or excessively nested source schedule')
    kind = obj.get('kind')
    if kind == 'block' and set(obj) == {'kind', 'instructions'}:
        if type(obj['instructions']) is not list:
            raise ValueError('Source instruction block must be a list')
        return BufferedBlock(tuple(_read_instruction(i) for i in obj['instructions']))
    if kind == 'seq' and set(obj) == {'kind', 'parts'}:
        if type(obj['parts']) is not list:
            raise ValueError('Source sequence parts must be a list')
        return BufferedSequence(tuple(_read_code(p, depth + 1) for p in obj['parts']))
    if kind == 'repeat' and set(obj) == {'kind', 'count', 'body'}:
        return BufferedRepeat(obj['count'], _read_code(obj['body'], depth + 1))
    raise ValueError('Unsupported source schedule schema')


def _read_program(obj):
    required = {'target', 'protocol', 'idle_levels', 'idle_enabled', 'wire_order',
                'instructions', 'schedule', 'declared_tx_bits', 'declared_rx_bits', 'max_rx_bits'}
    if type(obj) is not dict or set(obj) != required or type(obj['instructions']) is not list:
        raise ValueError('Unsupported counted source-program schema')
    values = dict(obj)
    values['instructions'] = tuple(_read_instruction(i) for i in values['instructions'])
    values['schedule'] = None if values['schedule'] is None else _read_code(values['schedule'])
    return BufferedProgram(**values)


@dataclass(frozen=True)
class BufferedCountedHardwareImage:
    words: tuple[int, ...]
    controls: tuple[int, ...]
    program_key: str
    source: BufferedProgram = field(repr=False)
    image_format: str = FORMAT
    _key: str = field(init=False, repr=False)
    _totals: tuple = field(init=False, repr=False)

    def __post_init__(self):
        if self.image_format != FORMAT:
            raise ValueError('Wrong counted hardware image version')
        if (type(self.words) is not tuple or type(self.controls) is not tuple or
                not 1 <= len(self.words) <= INSTRUCTION_CAPACITY or
                len(self.words) != len(self.controls)):
            raise ValueError('Counted image requires matching immutable 1..64 row tuples')
        for word, control in zip(self.words, self.controls):
            decode_instruction(word)
            decode_control(control)
        expected_words, expected_controls, totals = _lower(self.source)
        source_key = hashlib.sha256(json.dumps(_definition(self.source),
            sort_keys=True, separators=(',', ':')).encode()).hexdigest()
        if (type(self.program_key) is not str or self.program_key != source_key or
                self.source.key != source_key):
            raise ValueError('Counted image differs from its original source identity')
        if self.words != expected_words or self.controls != expected_controls:
            raise ValueError('Counted rows or metadata differ from canonical source lowering')
        object.__setattr__(self, '_totals', totals)
        canonical = dict(format=self.image_format, program_key=self.program_key,
            words=list(self.words), controls=list(self.controls), source=_definition(self.source),
            physical_count=len(self.words), virtual_span=self.virtual_span,
            tx_bits=self.tx_bits, rx_bits=self.rx_bits)
        object.__setattr__(self, '_key', hashlib.sha256(json.dumps(canonical,
            sort_keys=True, separators=(',', ':')).encode()).hexdigest())

    @property
    def key(self): return self._key
    @property
    def virtual_span(self): return self._totals[0]
    @property
    def tx_bits(self): return self._totals[1]
    @property
    def rx_bits(self): return self._totals[2]
    @property
    def execution_edges(self): return self._totals[3]
    @property
    def idle_levels(self): return self.source.idle_levels
    @property
    def idle_enabled(self): return self.source.idle_enabled
    @property
    def wire_order(self): return self.source.wire_order
    @property
    def protocol(self): return self.source.protocol

    def storage(self):
        return dict(self.source.storage(), physical_rows=len(self.words),
                    instruction_bits=32 * len(self.words),
                    control_bits=CONTROL_WIDTH * len(self.controls),
                    uploaded_bits=ROW_WIDTH * len(self.words), image_format=FORMAT)

    def encode_tx(self, payload): return self.source.encode_tx(payload)
    def decode_rx(self, bits): return self.source.decode_rx(bits)

    def to_bytes(self):
        return (json.dumps(dict(format=self.image_format, program_key=self.program_key,
            image_key=self.key, words=list(self.words), controls=list(self.controls),
            source=_definition(self.source), physical_count=len(self.words),
            virtual_span=self.virtual_span, tx_bits=self.tx_bits, rx_bits=self.rx_bits),
            sort_keys=True, indent=2) + '\n').encode()

    @classmethod
    def from_bytes(cls, data):
        if type(data) is not bytes:
            raise ValueError('Captured counted image must be bytes')
        obj = json.loads(data)
        required = {'format', 'program_key', 'image_key', 'words', 'controls', 'source',
                    'physical_count', 'virtual_span', 'tx_bits', 'rx_bits'}
        if (type(obj) is not dict or set(obj) != required or
                type(obj['words']) is not list or type(obj['controls']) is not list):
            raise ValueError('Unsupported counted hardware image schema')
        image = cls(tuple(obj['words']), tuple(obj['controls']), obj['program_key'],
                    _read_program(obj['source']), obj['format'])
        expected = dict(physical_count=len(image.words), virtual_span=image.virtual_span,
                        tx_bits=image.tx_bits, rx_bits=image.rx_bits)
        if any(type(obj[k]) is not int or obj[k] != v for k, v in expected.items()) or obj['image_key'] != image.key:
            raise ValueError('Counted image demand, span or identity metadata differs')
        return image


def lower_counted(program):
    words, controls, _ = _lower(program)
    return BufferedCountedHardwareImage(words, controls, program.key, program)


class BufferedCountedHardwareHost(BufferedHardwareHost):
    """Same single-owner host lifecycle, with counted image/port admission."""
    def _prepare_image(self, source):
        image = lower_counted(source) if type(source) is BufferedProgram else source
        if type(image) is not BufferedCountedHardwareImage:
            raise ValueError('Counted load requires its versioned compact image')
        return BufferedCountedHardwareImage.from_bytes(image.to_bytes())

    def _write_fields(self, image, address):
        return dict(command=1, address=address, word=image.words[address],
                    control=image.controls[address])

    def _commit_fields(self, image):
        return dict(command=2, count=len(image.words), virtual_span=image.virtual_span,
                    idle_levels=image.idle_levels, idle_enabled=image.idle_enabled)

    def _edge(self, **command):
        snapshot = self.transport.edge(**command)
        self.edges += 1
        values = _status(snapshot)
        for name, width in (('virtual_pc', 10), ('env0', 3), ('env1', 3)):
            value = _field(snapshot, name)
            if not 0 <= value < 1 << width:
                raise RuntimeError('Counted hardware observation ' + name + ' exceeds its port width')
            values[name] = value
        self._last = values
        return values


def compact_spi(byte_count=4, half_cycles=4):
    """Mode-0 SPI: four stored leaves, two counted loops, continuous CS."""
    _integer(byte_count, 1, 4, 'SPI byte count')
    _integer(half_cycles, 3, 256, 'SPI half period')
    body = BufferedBlock((BufferedInstruction('shift', half_cycles, shift_pin=0),
        BufferedInstruction('keep', half_cycles, levels=2, preserve=1, append_input=0)))
    schedule = BufferedSequence((BufferedRepeat(byte_count, BufferedRepeat(8, body)),
        BufferedBlock((BufferedInstruction('drive', half_cycles), BufferedInstruction('halt')))))
    return BufferedProgram((), idle_levels=4, wire_order='msb-per-byte',
        protocol='spi-mode0', schedule=schedule, declared_tx_bits=8 * byte_count,
        declared_rx_bits=8 * byte_count, max_rx_bits=8 * byte_count)


def compact_jtag(bit_count=17, half_cycles=4):
    """Reset-selected DR scan, preserving the final TMS bit and byte padding."""
    _integer(bit_count, 1, 32, 'JTAG scan bit count')
    _integer(half_cycles, 3, 256, 'JTAG half period')

    def clocks(tms_values):
        return BufferedBlock(tuple(BufferedInstruction('drive', half_cycles, levels=(tms << 2) | high)
            for tms in tms_values for high in (0, 2)))

    body = BufferedBlock((BufferedInstruction('shift', half_cycles, shift_pin=0),
        BufferedInstruction('keep', half_cycles, levels=2, preserve=1, append_input=0)))
    parts = [BufferedRepeat(5, clocks((1,))), clocks((0, 1, 0, 0))]
    whole, remainder = divmod(bit_count - 1, 8)
    if whole:
        parts.append(BufferedRepeat(whole, BufferedRepeat(8, body)))
    if remainder:
        parts.append(BufferedRepeat(remainder, body))
    parts.extend((BufferedBlock((BufferedInstruction('shift', half_cycles, levels=4, shift_pin=0),
        BufferedInstruction('keep', half_cycles, levels=6, preserve=1, append_input=0))),
        clocks((1, 0)), BufferedBlock((BufferedInstruction('drive', half_cycles), BufferedInstruction('halt')))))
    return BufferedProgram((), wire_order='lsb-per-byte', protocol='jtag-reset-dr',
        schedule=BufferedSequence(tuple(parts)), declared_tx_bits=bit_count,
        declared_rx_bits=bit_count, max_rx_bits=bit_count)
