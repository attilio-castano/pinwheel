"""Source-bound 144-bit rows for the separate counted reactive circuit.

Timed/reactive effects, counted succession and explicit successor coordinates
are programmable data. A stored body is uploaded once. Original syntax and
declared successful demands remain part of identity: branching can terminate
with a shorter TX/RX prefix, and maximum RX reservation can exceed success RX.
The parallel host reuses the existing ownership and indexed-read lifecycle.
"""
from dataclasses import asdict, dataclass, field
import hashlib
import json

from buffered_engine import (BufferedBlock, BufferedInstruction, BufferedProgram,
                             BufferedRepeat, BufferedSequence)
from buffered_counted_hardware import (CountedControl, _definition, _read_program,
    compact_jtag, compact_spi, decode_control, encode_control)
from buffered_hardware import (BufferedHardwareHost, BufferedHardwareResult,
    RX_CAPACITY, TX_CAPACITY, _field, _integer, _status)
from buffered_i2c import buffered_i2c_read, register_read_tx


FORMAT = 'pinwheel-buffered-reactive32-v1'
INSTRUCTION_CAPACITY = 64
INSTRUCTION_WIDTH, CONTROL_WIDTH, BRANCH_WIDTH = 64, 24, 56
ROW_WIDTH = INSTRUCTION_WIDTH + CONTROL_WIDTH + BRANCH_WIDTH
VIRTUAL_CAPACITY = 1024
KINDS = dict(drive=0, shift=1, keep=2, halt=3, fault=4, wait=5, checked=6, qualify=7)


def _capture_bits(capture):
    return 0 if capture is None else 1 | capture[0] << 1 | capture[1] << 2


def _capture_value(bits):
    if not bits & 1:
        if bits:
            raise ValueError('Inactive scratch capture fields must be zero')
        return None
    return ((bits >> 1) & 1, bits >> 2)


def encode_reactive_instruction(instruction):
    """Canonical word; CHECKED successors are stored in the branch descriptor."""
    if type(instruction) is not BufferedInstruction:
        raise ValueError('Reactive hardware requires a buffered instruction')
    # Validate even if a frozen object was altered through low-level reflection.
    BufferedInstruction(**asdict(instruction))
    _integer(instruction.duration, 1, 256, 'Reactive instruction duration')
    kind = instruction.kind
    if (kind != 'fault' and instruction.outcome != 'fault' or
            kind != 'wait' and (instruction.wait_input != 0 or not instruction.wait_level) or
            kind not in ('wait', 'qualify') and instruction.budget != 1 or
            kind == 'wait' and instruction.duration != 1):
        raise ValueError('Noncanonical inactive reactive instruction fields')
    if kind in ('halt', 'fault'):
        return KINDS[kind] | (int(instruction.outcome == 'timeout') << 55)
    rx = 0 if instruction.append_input is None else instruction.append_input + 1
    shift = instruction.shift_pin if kind == 'shift' else 0
    word = (KINDS[kind] | instruction.levels << 3 | instruction.enabled << 6 |
        (instruction.duration - 1) << 9 | instruction.preserve << 17 |
        shift << 20 | rx << 22 | int(instruction.shift_enabled) << 24 |
        int(instruction.shift_invert) << 25 | instruction.preserve_enabled << 26 |
        _capture_bits(instruction.entry_capture) << 29 |
        _capture_bits(instruction.terminal_capture) << 35 |
        instruction.check_mask << 41 | instruction.check_value << 43)
    if kind == 'wait':
        word |= instruction.wait_input << 45 | int(instruction.wait_level) << 46
    if kind in ('wait', 'qualify'):
        word |= (instruction.budget - 1) << 47
    return word


def decode_reactive_instruction(word):
    """Strictly decode meaningful fields, then check exact canonical encoding."""
    _integer(word, 0, (1 << INSTRUCTION_WIDTH) - 1, 'Reactive instruction word')
    if word >> 56:
        raise ValueError('Reserved reactive instruction bits')
    kind = tuple(KINDS)[word & 7]
    if kind in ('halt', 'fault'):
        instruction = BufferedInstruction(kind,
            outcome='timeout' if word & (1 << 55) else 'fault')
    else:
        rx = (word >> 22) & 3
        if rx == 3:
            raise ValueError('Invalid reactive RX selector')
        instruction = BufferedInstruction(kind, ((word >> 9) & 255) + 1,
            levels=(word >> 3) & 7, enabled=(word >> 6) & 7,
            preserve=(word >> 17) & 7,
            shift_pin=(word >> 20) & 3 if kind == 'shift' else None,
            append_input=None if rx == 0 else rx - 1,
            shift_enabled=bool(word & (1 << 24)), shift_invert=bool(word & (1 << 25)),
            preserve_enabled=(word >> 26) & 7,
            entry_capture=_capture_value((word >> 29) & 63),
            terminal_capture=_capture_value((word >> 35) & 63),
            check_mask=(word >> 41) & 3, check_value=(word >> 43) & 3,
            wait_input=(word >> 45) & 1 if kind == 'wait' else 0,
            wait_level=bool(word & (1 << 46)) if kind == 'wait' else True,
            budget=((word >> 47) & 255) + 1 if kind in ('wait', 'qualify') else 1)
    if encode_reactive_instruction(instruction) != word:
        raise ValueError('Noncanonical reactive instruction fields')
    return instruction


@dataclass(frozen=True)
class ReactiveEndpoint:
    next: bool = False
    virtual_pc: int = 0
    physical_pc: int = 0
    outer: int = 0
    inner: int = 0

    def __post_init__(self):
        if type(self.next) is not bool:
            raise ValueError('Endpoint NEXT must be Boolean')
        _integer(self.virtual_pc, 0, 1023, 'Endpoint virtual PC')
        _integer(self.physical_pc, 0, 64, 'Endpoint physical PC')
        _integer(self.outer, 0, 7, 'Endpoint outer index')
        _integer(self.inner, 0, 7, 'Endpoint inner index')
        if self.next and (self.virtual_pc or self.physical_pc or self.outer or self.inner):
            raise ValueError('NEXT endpoints contain no absolute coordinates')
        if self.physical_pc == 64 and (self.outer or self.inner):
            raise ValueError('Invalid absolute endpoints contain no loop indices')


def encode_endpoint(endpoint):
    if type(endpoint) is not ReactiveEndpoint:
        raise ValueError('Reactive endpoint requires canonical coordinates')
    return (int(endpoint.next) | endpoint.virtual_pc << 1 | endpoint.physical_pc << 11 |
            endpoint.outer << 18 | endpoint.inner << 21)


def decode_endpoint(word):
    _integer(word, 0, (1 << 24) - 1, 'Reactive endpoint word')
    return ReactiveEndpoint(bool(word & 1), (word >> 1) & 1023,
        (word >> 11) & 127, (word >> 18) & 7, (word >> 21) & 7)


@dataclass(frozen=True)
class ReactiveBranch:
    finish: int = 0  # 0 counted NEXT, 1 absolute jump, 2 scratch branch
    slot: int = 0
    yes: ReactiveEndpoint = ReactiveEndpoint()
    no: ReactiveEndpoint = ReactiveEndpoint()

    def __post_init__(self):
        _integer(self.finish, 0, 2, 'Reactive finish kind')
        _integer(self.slot, 0, 15, 'Reactive branch scratch slot')
        if type(self.yes) is not ReactiveEndpoint or type(self.no) is not ReactiveEndpoint:
            raise ValueError('Reactive branch endpoints must be canonical')
        if self.finish == 0 and (self.slot or self.yes != ReactiveEndpoint() or
                                self.no != ReactiveEndpoint()):
            raise ValueError('Counted NEXT contains no branch fields')
        if self.finish == 1 and (self.slot or self.yes.next or self.no != ReactiveEndpoint()):
            raise ValueError('Absolute jump contains one absolute endpoint')


def encode_branch(branch):
    if type(branch) is not ReactiveBranch:
        raise ValueError('Reactive branch requires a canonical descriptor')
    return branch.finish | branch.slot << 2 | encode_endpoint(branch.yes) << 6 | encode_endpoint(branch.no) << 30


def decode_branch(word):
    _integer(word, 0, (1 << BRANCH_WIDTH) - 1, 'Reactive branch word')
    if word >> 54:
        raise ValueError('Reserved reactive branch bits')
    return ReactiveBranch(word & 3, (word >> 2) & 15,
                          decode_endpoint((word >> 6) & ((1 << 24) - 1)),
                          decode_endpoint((word >> 30) & ((1 << 24) - 1)))


def _coordinates(code, pc, physical=0, enclosing=()):
    """Normalize one absolute target by walking syntax, without expanding bodies."""
    if not 0 <= pc < code.span:
        return None
    if type(code) is BufferedBlock:
        return (physical + pc, *(enclosing + (0,) * (2 - len(enclosing))))
    if type(code) is BufferedSequence:
        for part in code.parts:
            if pc < part.span:
                return _coordinates(part, pc, physical, enclosing)
            pc -= part.span
            physical += part.words
    elif type(code) is BufferedRepeat:
        index, pc = divmod(pc, code.body.span)
        return _coordinates(code.body, pc, physical, (*enclosing, index))
    raise ValueError('Unsupported reactive source schedule')


def _endpoint(code, pc):
    if pc is None:
        return ReactiveEndpoint(next=True)
    coordinates = _coordinates(code, pc)
    return ReactiveEndpoint(False, pc, *(coordinates or (64, 0, 0)))


def _lower(program):
    if type(program) is not BufferedProgram:
        raise ValueError('Reactive lowering requires a buffered reference program')
    _read_program(_definition(program))
    code = program.schedule or BufferedBlock(program.instructions)
    if code.words > INSTRUCTION_CAPACITY or code.nodes > 256 or code.nesting > 2:
        raise ValueError('Reactive image exceeds 64 leaves, 256 syntax nodes or two loop levels')
    if not 1 <= code.span <= VIRTUAL_CAPACITY:
        raise ValueError('Reactive virtual span must be in 1..1024')
    for name, value, capacity in (('TX demand', program.tx_bits, TX_CAPACITY),
            ('RX demand', program.rx_bits, RX_CAPACITY),
            ('RX reservation', program.rx_reservation_bits, RX_CAPACITY)):
        _integer(value, 0, capacity, 'Reactive hardware ' + name)
    rows, endings = [], []

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
            raise ValueError('Unsupported reactive source schedule')

    walk(code)
    words, controls, branches = [], [], []
    for index, (instruction, enclosing) in enumerate(rows):
        words.append(encode_reactive_instruction(instruction))
        outer = enclosing[0] if enclosing else (0, 1)
        inner = enclosing[1] if len(enclosing) == 2 else (0, 1)
        controls.append(encode_control(CountedControl(len(enclosing), *outer, *inner,
                                                    *endings[index])))
        finish = instruction.finish
        if finish is None:
            branch = ReactiveBranch()
        elif type(finish) is int:
            branch = ReactiveBranch(1, yes=_endpoint(code, finish))
        else:
            branch = ReactiveBranch(2, finish[0], _endpoint(code, finish[1]), _endpoint(code, finish[2]))
        branches.append(encode_branch(branch))
    return tuple(words), tuple(controls), tuple(branches)


@dataclass(frozen=True)
class BufferedReactiveHardwareImage:
    words: tuple[int, ...]
    controls: tuple[int, ...]
    branches: tuple[int, ...]
    program_key: str
    source: BufferedProgram = field(repr=False)
    image_format: str = FORMAT
    _key: str = field(init=False, repr=False)

    def __post_init__(self):
        if self.image_format != FORMAT:
            raise ValueError('Wrong reactive hardware image version')
        if (any(type(rows) is not tuple for rows in (self.words, self.controls, self.branches)) or
                not 1 <= len(self.words) <= INSTRUCTION_CAPACITY or
                not len(self.words) == len(self.controls) == len(self.branches)):
            raise ValueError('Reactive image requires matching immutable 1..64 row tuples')
        for word, control, branch in zip(self.words, self.controls, self.branches):
            instruction = decode_reactive_instruction(word)
            decode_control(control)
            decode_branch(branch)
            if instruction.kind != 'checked' and branch:
                raise ValueError('Only CHECKED instructions have branch descriptors')
        expected = _lower(self.source)
        source_key = hashlib.sha256(json.dumps(_definition(self.source),
            sort_keys=True, separators=(',', ':')).encode()).hexdigest()
        if (type(self.program_key) is not str or self.program_key != source_key or
                self.source.key != source_key):
            raise ValueError('Reactive image differs from its original source identity')
        if (self.words, self.controls, self.branches) != expected:
            raise ValueError('Reactive rows or coordinates differ from canonical source lowering')
        object.__setattr__(self, '_key', hashlib.sha256(json.dumps(self._canonical(),
            sort_keys=True, separators=(',', ':')).encode()).hexdigest())

    def _canonical(self):
        return dict(format=self.image_format, program_key=self.program_key,
            words=list(self.words), controls=list(self.controls), branches=list(self.branches),
            source=_definition(self.source), physical_count=len(self.words),
            virtual_span=self.virtual_span, tx_bits=self.tx_bits, rx_bits=self.rx_bits,
            rx_reservation_bits=self.rx_reservation_bits)

    @property
    def key(self): return self._key
    @property
    def virtual_span(self): return self.source.span
    @property
    def tx_bits(self): return self.source.tx_bits
    @property
    def rx_bits(self): return self.source.rx_bits
    @property
    def rx_reservation_bits(self): return self.source.rx_reservation_bits
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
            instruction_bits=INSTRUCTION_WIDTH * len(self.words),
            control_bits=CONTROL_WIDTH * len(self.words), branch_bits=BRANCH_WIDTH * len(self.words),
            uploaded_bits=ROW_WIDTH * len(self.words), image_format=FORMAT)

    def encode_tx(self, payload): return self.source.encode_tx(payload)
    def decode_rx(self, bits): return self.source.decode_rx(bits)

    def to_bytes(self):
        return (json.dumps(dict(self._canonical(), image_key=self.key),
                           sort_keys=True, indent=2) + '\n').encode()

    @classmethod
    def from_bytes(cls, data):
        if type(data) is not bytes:
            raise ValueError('Captured reactive image must be bytes')
        obj = json.loads(data)
        required = {'format', 'program_key', 'image_key', 'words', 'controls', 'branches',
                    'source', 'physical_count', 'virtual_span', 'tx_bits', 'rx_bits', 'rx_reservation_bits'}
        if (type(obj) is not dict or set(obj) != required or
                any(type(obj[k]) is not list for k in ('words', 'controls', 'branches'))):
            raise ValueError('Unsupported reactive hardware image schema')
        image = cls(tuple(obj['words']), tuple(obj['controls']), tuple(obj['branches']),
                    obj['program_key'], _read_program(obj['source']), obj['format'])
        expected = dict(physical_count=len(image.words), virtual_span=image.virtual_span,
            tx_bits=image.tx_bits, rx_bits=image.rx_bits, rx_reservation_bits=image.rx_reservation_bits)
        if (any(type(obj[k]) is not int or obj[k] != v for k, v in expected.items()) or
                obj['image_key'] != image.key):
            raise ValueError('Reactive image demand, span or identity metadata differs')
        return image


def lower_reactive(program):
    words, controls, branches = _lower(program)
    return BufferedReactiveHardwareImage(words, controls, branches, program.key, program)


@dataclass(frozen=True)
class BufferedReactiveHardwareResult(BufferedHardwareResult):
    scratch_bits: tuple[bool, ...]

    @property
    def scratch(self):
        return sum(int(bit) << index for index, bit in enumerate(self.scratch_bits))


class BufferedReactiveHardwareHost(BufferedHardwareHost):
    """Shared lifecycle, maximum RX admission and scratch-bearing completions."""
    def _prepare_image(self, source):
        image = lower_reactive(source) if type(source) is BufferedProgram else source
        if type(image) is not BufferedReactiveHardwareImage:
            raise ValueError('Reactive load requires its versioned compact image')
        return BufferedReactiveHardwareImage.from_bytes(image.to_bytes())

    def _write_fields(self, image, address):
        return dict(command=1, address=address, word=image.words[address],
                    control=image.controls[address], branch=image.branches[address])

    def _commit_fields(self, image):
        return dict(command=2, count=len(image.words), virtual_span=image.virtual_span,
                    idle_levels=image.idle_levels, idle_enabled=image.idle_enabled)

    def _edge(self, **command):
        snapshot = self.transport.edge(**command)
        self.edges += 1
        values = _status(snapshot)
        for name, width in (('virtual_pc', 10), ('env0', 3), ('env1', 3),
                            ('phase', 3), ('wait_left', 8), ('scratch', 16)):
            value = _field(snapshot, name)
            if not 0 <= value < 1 << width:
                raise RuntimeError('Reactive hardware observation ' + name + ' exceeds its port width')
            values[name] = value
        phase = values['phase']
        mode = 0 if phase == 0 else 1 if phase < 5 else 2 if phase == 5 else 3
        if values['mode'] != mode:
            raise RuntimeError('Inconsistent reactive hardware phase and mode')
        self._last = values
        return values

    def _result_fingerprint(self, status):
        return super()._result_fingerprint(status) + (status['phase'], status['scratch'])

    def _result_outcome(self, status):
        try:
            return {5: 'complete', 6: 'timeout', 7: 'fault'}[status['phase']]
        except KeyError as error:
            raise RuntimeError('Retained reactive result has no terminal phase') from error

    def _make_result(self, pending, status, outcome, raw, payload):
        image = pending.image
        scratch = tuple(bool(status['scratch'] & (1 << index)) for index in range(16))
        return BufferedReactiveHardwareResult(pending.identity, image.key, image.program_key,
            image.protocol, outcome, status['tx_consumed'], len(raw), payload, raw, scratch)


def compact_i2c_read(byte_count=4, phase_cycles=4, wait_cycles=32):
    """Register-read source admitted by the 32-bit reactive target."""
    _integer(byte_count, 1, 4, 'Hardware I2C reply byte count')
    return buffered_i2c_read(byte_count, phase_cycles, wait_cycles)
