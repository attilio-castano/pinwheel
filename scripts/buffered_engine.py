"""Executable buffered-transfer model; this is not a paired hardware image.

The engine has no protocol cases. Immutable timed instructions drive the three
logical outputs, take a TX wire bit, append a sampled input bit, or terminate.
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

    KEEP preserves selected output bits while setting the other outputs. A TX
    bit consumed by SHIFT is not a count of peripheral clock transitions.
    """
    kind: str
    duration: int = 1
    levels: int = 0
    enabled: int = 7
    preserve: int = 0
    shift_pin: int | None = None
    append_input: int | None = None
    outcome: str = 'fault'

    def __post_init__(self):
        if self.kind not in ('drive', 'shift', 'keep', 'halt', 'fault'):
            raise ValueError('Unknown buffered instruction')
        _integer(self.duration, 1, None, 'Duration')
        for name in ('levels', 'enabled', 'preserve'):
            _integer(getattr(self, name), 0, 7, name)
        if self.kind == 'shift':
            _integer(self.shift_pin, 0, 2, 'TX output')
        elif self.shift_pin is not None:
            raise ValueError('Only SHIFT may consume a TX bit')
        if self.preserve and self.kind != 'keep':
            raise ValueError('Only KEEP may preserve outputs')
        if self.append_input is not None:
            _integer(self.append_input, 0, 1, 'RX input')
            if self.kind in ('halt', 'fault'):
                raise ValueError('Terminal instructions cannot append RX')
        if self.kind in ('halt', 'fault') and (self.duration != 1 or self.levels or
                                                self.preserve or self.enabled != 7):
            raise ValueError('Terminal instructions restore program idle outputs')
        if self.outcome not in ('fault', 'timeout'):
            raise ValueError('Fault outcome must be fault or timeout')


@dataclass(frozen=True)
class BufferedProgram:
    """Data-independent model program, bound by a hash of its full definition.

    ``tx_bits`` and ``rx_bits`` are demands of the complete instruction sequence,
    not inferred hardware capacity. The terminal instruction takes no extra
    wire edge. Encoding has no upload_words method and cannot target Host.
    """
    instructions: tuple[BufferedInstruction, ...]
    idle_levels: int = 0
    idle_enabled: int = 7
    wire_order: str = 'lsb-per-byte'
    protocol: str = 'generic'
    target: str = TARGET
    _key: str = field(init=False, repr=False)

    def __post_init__(self):
        if self.target != TARGET:
            raise ValueError('Buffered programs require the reference-model target')
        if type(self.instructions) is not tuple or not self.instructions or any(
                type(item) is not BufferedInstruction for item in self.instructions):
            raise ValueError('Instructions must be an immutable nonempty tuple')
        if self.instructions[-1].kind not in ('halt', 'fault') or any(
                item.kind in ('halt', 'fault') for item in self.instructions[:-1]):
            raise ValueError('Buffered program needs exactly one final terminal instruction')
        _integer(self.idle_levels, 0, 7, 'Idle levels')
        _integer(self.idle_enabled, 0, 7, 'Idle enables')
        if self.wire_order not in ('lsb-per-byte', 'msb-per-byte'):
            raise ValueError('Unknown buffered byte wire order')
        if type(self.protocol) is not str or not self.protocol:
            raise ValueError('Protocol metadata must be a nonempty string')
        canonical = json.dumps(dict(target=self.target, protocol=self.protocol,
            idle_levels=self.idle_levels, idle_enabled=self.idle_enabled,
            wire_order=self.wire_order,
            instructions=[asdict(item) for item in self.instructions]),
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
        return sum(item.kind == 'shift' for item in self.instructions)

    @property
    def rx_bits(self):
        return sum(item.append_input is not None for item in self.instructions)

    @property
    def execution_edges(self):
        return sum(item.duration for item in self.instructions[:-1])

    def validate_transfer(self, tx_bits, rx_limit):
        if type(tx_bits) is not tuple or any(type(bit) is not bool for bit in tx_bits):
            raise ValueError('TX wire bits must be an immutable Boolean tuple')
        if len(tx_bits) != self.tx_bits:
            raise ValueError('TX length differs from program demand')
        _integer(rx_limit, self.rx_bits, None, 'RX reservation')

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
    def __init__(self, slot, identity, program):
        if type(program) is not BufferedProgram:
            raise ValueError('Engine requires a buffered reference program')
        descriptor = slot.descriptor
        if slot.state != 'running' or descriptor is None or descriptor.identity != identity:
            raise ValueError('Engine requires the matching running buffer owner')
        if descriptor.program_key != program.key:
            raise ValueError('Program key differs from accepted transfer')
        if descriptor.tx_bit_count != program.tx_bits or descriptor.rx_limit < program.rx_bits:
            raise ValueError('Accepted buffers cannot satisfy the program demands')
        self.slot, self.identity, self.program = slot, identity, program
        self.cycle = self.pc = 0
        self.levels, self.enabled = program.idle_levels, program.idle_enabled
        self._first = self._second = 3
        self._remaining = 0
        self.done = False
        self._enter(self._second)

    def _finish(self, outcome):
        self.slot.complete(self.identity, outcome=outcome)
        self.levels, self.enabled = self.program.idle_levels, self.program.idle_enabled
        self.done = True

    def fail(self, outcome='fault'):
        """Retain a terminal result after a model/peer execution failure."""
        if type(outcome) is not str or outcome not in ('fault', 'timeout'):
            raise ValueError('Engine failure outcome must be fault or timeout')
        if not self.done:
            self._finish(outcome)

    def _enter(self, sampled):
        from pinwheel_buffers import BufferFault
        instruction = self.program.instructions[self.pc]
        if instruction.kind in ('halt', 'fault'):
            self._finish('complete' if instruction.kind == 'halt' else instruction.outcome)
            return
        try:
            levels = instruction.levels
            if instruction.kind == 'shift':
                bit = self.slot.take_tx(self.identity)
                mask = 1 << instruction.shift_pin
                levels = (levels & ~mask) | (int(bit) << instruction.shift_pin)
            elif instruction.kind == 'keep':
                levels = ((levels & ~instruction.preserve) |
                          (self.levels & instruction.preserve))
            if instruction.append_input is not None:
                self.slot.append_rx(self.identity,
                                    bool((sampled >> instruction.append_input) & 1))
        except BufferFault:
            self._finish('fault')
            return
        self.levels, self.enabled = levels, instruction.enabled
        self._remaining = instruction.duration

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
        self._remaining -= 1
        if self._remaining == 0:
            self.pc += 1
            self._enter(sampled)


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
