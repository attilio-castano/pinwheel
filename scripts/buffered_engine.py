"""Executable buffered-transfer model; this is not a paired hardware image.

The engine has no protocol cases. Immutable instructions use timed and reactive
control, take a TX wire bit, append sampled RX, capture scratch, or terminate.
Counted schedules locate reusable stored bodies at virtual execution addresses.
Protocol frontends below supply only programs and byte/wire-order conversion.
The package fixture resolves physical pads and applies a peer callback's drive
on the next edge, followed by the engine's two-register input sampler.
"""
from dataclasses import asdict, dataclass, field
import hashlib
import json

from pad_io import OUTPUT_MASK, PadDrive, PadObservation


TARGET = 'buffered-reference-v1'


def _integer(value, low, high, name):
    if type(value) is not int or value < low or (high is not None and value > high):
        raise ValueError(f'{name} must be an integer in {low}..{high or "unbounded"}')
    return value


@dataclass(frozen=True)
class BufferedInstruction:
    """Capture and TX consumption happen once, on instruction entry.

    KEEP and reactive commands can preserve selected levels and enables. SHIFT
    can set a level or an enable, with inversion for open drain. A TX bit taken
    here is not a count of peripheral clock transitions. RX append is separate
    from control scratch; a CHECKED terminal capture feeds its successor.
    """
    kind: str
    duration: int = 1
    levels: int = 0
    enabled: int = 7
    preserve: int = 0
    shift_pin: int | None = None
    append_input: int | None = None
    outcome: str = 'fault'
    shift_enabled: bool = False
    shift_invert: bool = False
    preserve_enabled: int = 0
    entry_capture: tuple[int, int] | None = None
    terminal_capture: tuple[int, int] | None = None
    check_mask: int = 0
    check_value: int = 0
    wait_input: int = 0
    wait_level: bool = True
    budget: int = 1
    finish: int | tuple[int, int | None, int | None] | None = None

    def __post_init__(self):
        if self.kind not in ('drive', 'shift', 'keep', 'wait', 'checked',
                             'qualify', 'halt', 'fault'):
            raise ValueError('Unknown buffered instruction')
        _integer(self.duration, 1, None, 'Duration')
        for name in ('levels', 'enabled', 'preserve', 'preserve_enabled'):
            _integer(getattr(self, name), 0, 7, name)
        if self.kind == 'shift':
            _integer(self.shift_pin, 0, 2, 'TX output')
        elif self.shift_pin is not None:
            raise ValueError('Only SHIFT may consume a TX bit')
        for name in ('shift_enabled', 'shift_invert', 'wait_level'):
            if type(getattr(self, name)) is not bool:
                raise ValueError(f'{name} must be Boolean')
        if (self.shift_enabled or self.shift_invert) and self.kind != 'shift':
            raise ValueError('Only SHIFT may select or invert its TX destination')
        if (self.preserve or self.preserve_enabled) and self.kind not in (
                'keep', 'wait', 'checked', 'qualify'):
            raise ValueError('Only KEEP or reactive instructions may preserve outputs')
        if self.append_input is not None:
            _integer(self.append_input, 0, 1, 'RX input')
            if self.kind in ('halt', 'fault'):
                raise ValueError('Terminal instructions cannot append RX')
        if self.kind in ('halt', 'fault') and (self.duration != 1 or self.levels or
                self.preserve or self.preserve_enabled or self.enabled != 7):
            raise ValueError('Terminal instructions restore program idle outputs')
        if self.outcome not in ('fault', 'timeout'):
            raise ValueError('Fault outcome must be fault or timeout')
        for name in ('entry_capture', 'terminal_capture'):
            capture = getattr(self, name)
            if capture is not None:
                if type(capture) is not tuple or len(capture) != 2:
                    raise ValueError('Scratch capture must be an immutable input/slot pair')
                _integer(capture[0], 0, 1, 'Scratch input')
                _integer(capture[1], 0, 15, 'Scratch slot')
                if self.kind in ('halt', 'fault'):
                    raise ValueError('Terminal instructions cannot capture scratch inputs')
                if name == 'entry_capture' and self.kind in ('wait', 'qualify'):
                    raise ValueError('WAIT and QUALIFY do not capture scratch on entry')
        if self.terminal_capture is not None and self.kind != 'checked':
            raise ValueError('Terminal scratch capture requires CHECKED')
        for name in ('check_mask', 'check_value'):
            _integer(getattr(self, name), 0, 3, name)
        if (self.check_mask or self.check_value) and self.kind not in ('checked', 'qualify'):
            raise ValueError('Input checks require CHECKED or QUALIFY')
        _integer(self.wait_input, 0, 1, 'Wait input')
        _integer(self.budget, 1, 256, 'Wait budget')
        if self.finish is not None:
            if self.kind != 'checked':
                raise ValueError('Explicit successors require CHECKED')
            if type(self.finish) is int:
                _integer(self.finish, 0, 1023, 'Jump target')
            elif type(self.finish) is tuple and len(self.finish) == 3:
                _integer(self.finish[0], 0, 15, 'Branch scratch slot')
                for target in self.finish[1:]:
                    if target is not None:
                        _integer(target, 0, 1023, 'Branch target')
            else:
                raise ValueError('Successor must be a jump or scratch/true/false branch')


@dataclass(frozen=True)
class BufferedBlock:
    """Stored leaves; n leaves account for n−1 binary sequence descriptors."""
    instructions: tuple[BufferedInstruction, ...]

    def __post_init__(self):
        if type(self.instructions) is not tuple or not self.instructions or any(
                type(item) is not BufferedInstruction for item in self.instructions):
            raise ValueError('Block requires an immutable nonempty instruction tuple')

    @property
    def span(self): return len(self.instructions)
    @property
    def words(self): return len(self.instructions)
    @property
    def nodes(self): return 2 * len(self.instructions) - 1
    @property
    def loops(self): return 0
    @property
    def nesting(self): return 0

    def locate(self, pc, environment=(0, 0)):
        return (self.instructions[pc], environment) if 0 <= pc < self.span else None

    def definition(self):
        return dict(kind='block', instructions=[asdict(i) for i in self.instructions])


@dataclass(frozen=True)
class BufferedSequence:
    parts: tuple

    def __post_init__(self):
        if type(self.parts) is not tuple or not self.parts or any(
                type(part) not in (BufferedBlock, BufferedSequence, BufferedRepeat)
                for part in self.parts):
            raise ValueError('Sequence requires immutable compact schedule parts')

    @property
    def span(self): return sum(p.span for p in self.parts)
    @property
    def words(self): return sum(p.words for p in self.parts)
    @property
    def nodes(self): return len(self.parts) - 1 + sum(p.nodes for p in self.parts)
    @property
    def loops(self): return sum(p.loops for p in self.parts)
    @property
    def nesting(self): return max(p.nesting for p in self.parts)

    def locate(self, pc, environment=(0, 0)):
        if pc < 0: return None
        for part in self.parts:
            if pc < part.span: return part.locate(pc, environment)
            pc -= part.span
        return None

    def definition(self):
        return dict(kind='seq', parts=[p.definition() for p in self.parts])


@dataclass(frozen=True)
class BufferedRepeat:
    count: int
    body: object

    def __post_init__(self):
        _integer(self.count, 1, 8, 'Repeat count')
        if type(self.body) not in (BufferedBlock, BufferedSequence, BufferedRepeat):
            raise ValueError('Repeat requires a compact schedule body')

    @property
    def span(self): return self.count * self.body.span
    @property
    def words(self): return self.body.words
    @property
    def nodes(self): return 1 + self.body.nodes
    @property
    def loops(self): return 1 + self.body.loops
    @property
    def nesting(self): return 1 + self.body.nesting

    def locate(self, pc, environment=(0, 0)):
        if not 0 <= pc < self.span: return None
        return self.body.locate(pc % self.body.span,
                                (pc // self.body.span, environment[0]))

    def definition(self):
        return dict(kind='repeat', count=self.count, body=self.body.definition())


def _stored_instructions(code):
    """Validate stored leaves without constructing repeated virtual addresses."""
    if type(code) is BufferedBlock:
        yield from code.instructions
    elif type(code) is BufferedSequence:
        for part in code.parts:
            yield from _stored_instructions(part)
    else:
        yield from _stored_instructions(code.body)


@dataclass(frozen=True)
class BufferedProgram:
    """Data-independent model program, bound by a hash of its full definition.

    Linear ``tx_bits`` and ``rx_bits`` derive from the full instruction sequence.
    Reactive programs explicitly declare successful TX/RX lengths and maximum
    RX reservation; early fault/timeout preserves actual prefixes. Those lengths
    are validated at admission/read, not a proof of every branch's behavior.
    Terminal entry takes no extra wire edge. Encoding cannot target Host.
    """
    instructions: tuple[BufferedInstruction, ...]
    idle_levels: int = 0
    idle_enabled: int = 7
    wire_order: str = 'lsb-per-byte'
    protocol: str = 'generic'
    target: str = TARGET
    schedule: BufferedBlock | BufferedSequence | BufferedRepeat | None = None
    declared_tx_bits: int | None = None
    declared_rx_bits: int | None = None
    max_rx_bits: int | None = None
    _key: str = field(init=False, repr=False)

    def __post_init__(self):
        if self.target != TARGET:
            raise ValueError('Buffered programs require the reference-model target')
        if type(self.instructions) is not tuple or any(
                type(item) is not BufferedInstruction for item in self.instructions):
            raise ValueError('Instructions must be an immutable instruction tuple')
        if self.schedule is not None:
            if self.instructions or type(self.schedule) not in (
                    BufferedBlock, BufferedSequence, BufferedRepeat):
                raise ValueError('Compact schedules replace the linear instruction bank')
            if self.schedule.span > 1024 or self.schedule.nodes > 256 or self.schedule.nesting > 2:
                raise ValueError('Compact schedule exceeds 1024 addresses, 256 nodes, or two loops')
        elif not self.instructions:
            raise ValueError('Buffered program requires a nonempty instruction bank')
        reactive = self.schedule is not None or any(item.kind in (
            'wait', 'checked', 'qualify') for item in self.instructions)
        if not reactive:
            if self.instructions[-1].kind not in ('halt', 'fault') or any(
                    item.kind in ('halt', 'fault') for item in self.instructions[:-1]):
                raise ValueError('Buffered program needs exactly one final terminal instruction')
            if any(value is not None for value in (
                    self.declared_tx_bits, self.declared_rx_bits, self.max_rx_bits)):
                raise ValueError('Linear programs derive their exact demands from instructions')
        else:
            if self.schedule is None and (len(self.instructions) > 1024 or
                                           2 * len(self.instructions) - 1 > 256):
                raise ValueError('Reactive instruction syntax exceeds its model geometry')
            for item in _stored_instructions(self.schedule or BufferedBlock(self.instructions)):
                _integer(item.duration, 1, 256, 'Reactive duration')
                if item.kind == 'wait' and item.duration != 1:
                    raise ValueError('WAIT uses its budget, not an action duration')
            for name in ('declared_tx_bits', 'declared_rx_bits', 'max_rx_bits'):
                _integer(getattr(self, name), 0, None, name)
            if self.max_rx_bits < self.declared_rx_bits:
                raise ValueError('RX reservation must cover the successful result length')
        _integer(self.idle_levels, 0, 7, 'Idle levels')
        _integer(self.idle_enabled, 0, 7, 'Idle enables')
        if self.wire_order not in ('lsb-per-byte', 'msb-per-byte'):
            raise ValueError('Unknown buffered byte wire order')
        if type(self.protocol) is not str or not self.protocol:
            raise ValueError('Protocol metadata must be a nonempty string')
        canonical = json.dumps(dict(target=self.target, protocol=self.protocol,
            idle_levels=self.idle_levels, idle_enabled=self.idle_enabled,
            wire_order=self.wire_order,
            instructions=[asdict(item) for item in self.instructions],
            schedule=None if self.schedule is None else self.schedule.definition(),
            declared_tx_bits=self.declared_tx_bits,
            declared_rx_bits=self.declared_rx_bits, max_rx_bits=self.max_rx_bits),
            sort_keys=True, separators=(',', ':')).encode()
        object.__setattr__(self, '_key', hashlib.sha256(canonical).hexdigest())

    @property
    def key(self):
        return self._key

    @property
    def image_format(self):
        """Make existing hardware Host reject this target before transport I/O."""
        return self.target

    @property
    def tx_bits(self):
        return (self.declared_tx_bits if self.declared_tx_bits is not None else
                sum(item.kind == 'shift' for item in self.instructions))

    @property
    def rx_bits(self):
        return (self.declared_rx_bits if self.declared_rx_bits is not None else
                sum(item.append_input is not None for item in self.instructions))

    @property
    def rx_reservation_bits(self):
        return self.rx_bits if self.max_rx_bits is None else self.max_rx_bits

    @property
    def span(self):
        return len(self.instructions) if self.schedule is None else self.schedule.span

    def locate(self, pc):
        if self.schedule is None:
            return (self.instructions[pc], (0, 0)) if 0 <= pc < self.span else None
        return self.schedule.locate(pc)

    def fetch(self, pc):
        located = self.locate(pc)
        return None if located is None else located[0]

    def storage(self):
        """Syntax counts include sequence/repeat descriptors, never expanded slots.

        These counts have no mapped area or physical register-width meaning.
        """
        code = self.schedule or BufferedBlock(self.instructions)
        return dict(virtual_slots=code.span, instruction_words=code.words,
                    control_nodes=code.nodes - code.words, stored_nodes=code.nodes,
                    repeat_nodes=code.loops, nesting=code.nesting,
                    expanded_at_runtime=False, target=self.target)

    @property
    def execution_edges(self):
        # This exact horizon belongs only to the original linear model. Reactive
        # waits/branches can take a variable number of edges, including no end.
        if self.schedule is not None or any(item.kind in ('wait', 'checked', 'qualify')
                                            for item in self.instructions):
            raise ValueError('Reactive execution requires an explicit host wait horizon')
        return sum(item.duration for item in self.instructions[:-1])

    def validate_transfer(self, tx_bits, rx_limit):
        if type(tx_bits) is not tuple or any(type(bit) is not bool for bit in tx_bits):
            raise ValueError('TX wire bits must be an immutable Boolean tuple')
        if len(tx_bits) != self.tx_bits:
            raise ValueError('TX length differs from program demand')
        _integer(rx_limit, self.rx_reservation_bits, None, 'RX reservation')

    def encode_tx(self, payload):
        """Encode bytes into wire order, rejecting nonzero unused bit padding."""
        if type(payload) is not bytes or len(payload) != (self.tx_bits + 7) // 8:
            raise ValueError('Payload must be bytes matching the declared TX bit length')
        order = range(8) if self.wire_order == 'lsb-per-byte' else range(7, -1, -1)
        padded = tuple(bool((byte >> bit) & 1) for byte in payload for bit in order)
        if any(padded[self.tx_bits:]):
            raise ValueError('Non-byte payload has nonzero unused padding bits')
        return padded[:self.tx_bits]

    def decode_rx(self, bits):
        if type(bits) is not tuple or any(type(bit) is not bool for bit in bits):
            raise ValueError('RX wire bits must be an immutable Boolean tuple')
        if len(bits) != self.rx_bits:
            raise ValueError('RX length differs from complete program result')
        result = bytearray((len(bits) + 7) // 8)
        for index, bit in enumerate(bits):
            position = index % 8 if self.wire_order == 'lsb-per-byte' else 7 - index % 8
            result[index // 8] |= int(bit) << position
        return bytes(result)


class BufferedEngine:
    """One finite transaction executing against an exclusively owned slot.

    step() advances one chip edge. Input captures use the pre-edge second
    sampler register. Stale identities propagate an ownership error; only TX
    underflow/RX overflow becomes a retained engine fault.
    """
    def __init__(self, slot, identity, program, *, initial_first_sample=3,
                 initial_second_sample=3):
        if type(program) is not BufferedProgram:
            raise ValueError('Engine requires a buffered reference program')
        descriptor = slot.descriptor
        if slot.state != 'running' or descriptor is None or descriptor.identity != identity:
            raise ValueError('Engine requires the matching running buffer owner')
        if descriptor.program_key != program.key:
            raise ValueError('Program key differs from accepted transfer')
        if (descriptor.tx_bit_count != program.tx_bits or
                descriptor.rx_limit < program.rx_reservation_bits):
            raise ValueError('Accepted buffers cannot satisfy the program demands')
        _integer(initial_first_sample, 0, 3, 'Initial first input sample')
        _integer(initial_second_sample, 0, 3, 'Initial second input sample')
        self.slot, self.identity, self.program = slot, identity, program
        self.cycle = self.pc = 0
        self.levels, self.enabled = program.idle_levels, program.idle_enabled
        # START entry observes the sampler history before that edge. Hardware
        # fixtures can supply it without rewriting already-applied effects.
        self._first, self._second = initial_first_sample, initial_second_sample
        self._remaining = 0
        self._wait_left = 0
        self.samples = (False,) * 16
        self.mode = 'active'
        self.done = False
        self._enter(self._second)

    def _finish(self, outcome):
        self.slot.complete(self.identity, outcome=outcome)
        self.levels, self.enabled = self.program.idle_levels, self.program.idle_enabled
        self.mode = 'completed' if outcome == 'complete' else outcome
        self.pc = self._remaining = self._wait_left = 0
        self.done = True

    def fail(self, outcome='fault'):
        """Retain a terminal result after a model/peer execution failure."""
        if type(outcome) is not str or outcome not in ('fault', 'timeout'):
            raise ValueError('Engine failure outcome must be fault or timeout')
        if not self.done:
            self._finish(outcome)

    def _enter(self, sampled):
        from pinwheel_buffers import BufferFault
        instruction = self.program.fetch(self.pc)
        if instruction is None:
            self._finish('fault')
            return
        # Reactive's typed branch normalizes both endpoints on fetch. At the
        # final model address, a relative next endpoint cannot fit, including
        # an unselected endpoint. Reject before scratch or data entry effects.
        if (instruction.kind == 'checked' and type(instruction.finish) is tuple
                and self.pc == 1023 and None in instruction.finish[1:]):
            self._finish('fault')
            return
        if instruction.kind in ('halt', 'fault'):
            self._finish('complete' if instruction.kind == 'halt' else instruction.outcome)
            return
        self._capture(instruction.entry_capture, sampled)
        try:
            levels, enabled = instruction.levels, instruction.enabled
            if instruction.kind == 'shift':
                bit = self.slot.take_tx(self.identity) != instruction.shift_invert
                mask = 1 << instruction.shift_pin
                if instruction.shift_enabled:
                    enabled = (enabled & ~mask) | (int(bit) << instruction.shift_pin)
                else:
                    levels = (levels & ~mask) | (int(bit) << instruction.shift_pin)
            if instruction.preserve:
                levels = ((levels & ~instruction.preserve) |
                          (self.levels & instruction.preserve))
            if instruction.preserve_enabled:
                enabled = ((enabled & ~instruction.preserve_enabled) |
                           (self.enabled & instruction.preserve_enabled))
            if instruction.append_input is not None:
                self.slot.append_rx(self.identity,
                                    bool((sampled >> instruction.append_input) & 1))
        except BufferFault:
            self._finish('fault')
            return
        self.levels, self.enabled = levels, enabled
        self.mode = {'wait': 'waiting', 'checked': 'checked',
                     'qualify': 'qualifying'}.get(instruction.kind, 'active')
        self._remaining = instruction.budget if instruction.kind == 'wait' else instruction.duration
        self._wait_left = instruction.budget if instruction.kind == 'qualify' else 0

    def _capture(self, capture, sampled):
        if capture is not None:
            source, destination = capture
            values = list(self.samples)
            values[destination] = bool((sampled >> source) & 1)
            self.samples = tuple(values)

    def _dispatch(self, sampled, finish=None):
        target = self.pc + 1
        if type(finish) is int:
            target = finish
        elif type(finish) is tuple:
            target = finish[1] if self.samples[finish[0]] else finish[2]
            if target is None:
                target = self.pc + 1
        self.pc = target
        self._enter(sampled)

    @property
    def remaining(self):
        """Reactive's duration/budget minus one convention for state witnesses."""
        return max(0, self._remaining - 1)

    @property
    def wait_left(self):
        return max(0, self._wait_left - 1)

    def step(self, incoming=3):
        _integer(incoming, 0, 3, 'Sampled input pads')
        if self.done:
            return
        from pinwheel_buffers import TransferError
        descriptor = self.slot.descriptor
        if (self.slot.state != 'running' or descriptor is None or
                descriptor.identity != self.identity):
            raise TransferError('Stale or unowned engine transfer identity')
        sampled = self._second
        self._second, self._first = self._first, incoming
        self.cycle += 1
        instruction = self.program.fetch(self.pc)
        if instruction is None:
            self._finish('fault')
            return
        ready = (sampled & instruction.check_mask) == (
                 instruction.check_value & instruction.check_mask)
        if self.mode == 'waiting':
            if bool((sampled >> instruction.wait_input) & 1) == instruction.wait_level:
                self._dispatch(sampled)
            elif self._remaining > 1:
                self._remaining -= 1
            else:
                self._finish('timeout')
        elif self.mode == 'checked':
            if not ready:
                self._finish('fault')
            elif self._remaining > 1:
                self._remaining -= 1
            else:
                self._capture(instruction.terminal_capture, sampled)
                self._dispatch(sampled, instruction.finish)
        elif self.mode == 'qualifying':
            if ready:
                if self._remaining > 1:
                    self._remaining -= 1
                    self._wait_left = instruction.budget
                else:
                    self._dispatch(sampled)
            elif self._wait_left > 1:
                self._remaining = instruction.duration
                self._wait_left -= 1
            else:
                self._finish('timeout')
        else:
            if self._remaining > 1:
                self._remaining -= 1
            else:
                self._dispatch(sampled)


def resolve_pads(engine, drive):
    """Digital package fixture with push-pull contention and declared links."""
    levels, enabled = engine.levels << 2, engine.enabled << 2
    groups = [{index} for index in range(8)]
    for selected, pair in ((drive.links & 1, (0, 2)), (drive.links & 2, (1, 3))):
        if selected:
            first = next(group for group in groups if pair[0] in group)
            second = next(group for group in groups if pair[1] in group)
            if first is not second:
                first.update(second)
                groups.remove(second)
    wires = known = 0
    for group in groups:
        mask = sum(1 << pad for pad in group)
        strong = set()
        for source_levels, source_enabled in ((levels, enabled), (drive.levels, drive.enabled)):
            strong.update((source_levels >> pad) & 1 for pad in group
                          if source_enabled & (1 << pad))
        if len(strong) < 2:
            known |= mask
            level = next(iter(strong)) if strong else bool(drive.pullups & mask)
            if level:
                wires |= mask
    return PadObservation(int(not engine.done), levels, enabled, wires, known)


class BufferedWireSimulation:
    """Observe every edge without exposing engine instructions to the peer."""
    def __init__(self, engine, peer):
        self.engine, self.peer = engine, peer
        self.cycle = 0
        self._drive = PadDrive()
        self.trace = []
        self._observe()

    def _observe(self):
        self.observation = resolve_pads(self.engine, self._drive)
        self.trace.append(self.observation)
        drive = self.peer.drive(self.cycle, self.observation, 0)
        if type(drive) is not PadDrive:
            raise ValueError('Wire peer must return a PadDrive')
        self.observation.validate_drive(drive)
        self._drive = drive

    def step(self):
        if self.engine.done:
            return
        incoming = resolve_pads(self.engine, self._drive)
        self.engine.step(incoming.bit(0) | (incoming.bit(1) << 1))
        self.cycle += 1
        self._observe()

    def run(self, max_edges):
        _integer(max_edges, 0, None, 'Host wait horizon')
        stop = self.cycle + max_edges
        while not self.engine.done:
            if self.cycle >= stop:
                raise TimeoutError('Host wait expired; engine and buffers remain owned')
            self.step()
        return self.engine.slot.peek(self.engine.identity)


def buffered_spi(byte_count=4, half_cycles=4):
    """One continuous-CS, mode-0 SPI model program, independent of TX bytes."""
    _integer(byte_count, 1, None, 'SPI byte count')
    _integer(half_cycles, 3, None, 'SPI half period')
    instructions = []
    for _ in range(8 * byte_count):
        instructions.append(BufferedInstruction('shift', half_cycles, shift_pin=0))
        instructions.append(BufferedInstruction('keep', half_cycles, levels=2,
                                                 preserve=1, append_input=0))
    instructions.extend((BufferedInstruction('drive', half_cycles),
                         BufferedInstruction('halt')))
    return BufferedProgram(tuple(instructions), idle_levels=4,
                           wire_order='msb-per-byte', protocol='spi-mode0')


def buffered_jtag(bit_count=32, half_cycles=4):
    """Reset-selected DR scan; no instruction register or chain selection.

    The last data bit asserts TMS on its scan clock. Five reset clocks recover
    any initial TAP state. Arbitrary positive bit counts need no byte padding
    on the wire; the byte encoding checks unused high bits in the last byte.
    """
    _integer(bit_count, 1, None, 'JTAG scan bit count')
    _integer(half_cycles, 3, None, 'JTAG half period')
    instructions = []
    for tms in (1, 1, 1, 1, 1, 0, 1, 0, 0):
        instructions.extend((BufferedInstruction('drive', half_cycles, levels=tms << 2),
                             BufferedInstruction('drive', half_cycles, levels=(tms << 2) | 2)))
    for bit in range(bit_count):
        tms = int(bit == bit_count - 1) << 2
        instructions.extend((BufferedInstruction('shift', half_cycles, levels=tms, shift_pin=0),
                             BufferedInstruction('keep', half_cycles, levels=tms | 2,
                                                 preserve=1, append_input=0)))
    for tms in (1, 0):
        instructions.extend((BufferedInstruction('drive', half_cycles, levels=tms << 2),
                             BufferedInstruction('drive', half_cycles, levels=(tms << 2) | 2)))
    instructions.extend((BufferedInstruction('drive', half_cycles),
                         BufferedInstruction('halt')))
    return BufferedProgram(tuple(instructions), protocol='jtag-reset-dr')
