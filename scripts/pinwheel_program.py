"""Named, explicitly timed programs for the existing paired protocol engine.

Durations and wait budgets are chip edges, not rates measured on a board. The
builder resolves labels and checks the complete upload before returning a
Program; it performs no I/O and does not add protocol-specific circuitry.
"""
from collections.abc import Mapping

from paired_execution import GRAMMAR, fields
from pinwheel_host import LEGACY_FORMAT, PAIRED_FORMAT, RESIDENT_FORMAT, Program


def _integer(value, minimum, maximum, name):
    if type(value) is not int or not minimum <= value <= maximum:
        raise ValueError(f'{name} must be an integer in {minimum}..{maximum}')
    return value


def _boolean(value, name):
    if type(value) is not bool:
        raise ValueError(f'{name} must be a Boolean')
    return int(value)


def _encode(values):
    word = offset = 0
    for name, width in GRAMMAR['FIELDS']:
        value = _integer(values.get(name, 0), 0, (1 << width) - 1, name)
        word |= value << offset
        offset += width
    return word


class ProgramBuilder:
    """Build a source image using names for pins, capture slots and labels.

    ``high`` names output value bits. ``enabled`` names actively driven output
    pins; other pins are released. Pin indices name the three logical outputs
    and two sampled inputs, not package pad numbers.
    """
    def __init__(self, *, outputs=None, inputs=None, captures=None,
                 idle_high=(), idle_enabled=(), image_format=RESIDENT_FORMAT):
        self.outputs = self._names(outputs if outputs is not None else
                                   {'out0': 0, 'out1': 1, 'out2': 2}, 2, 'output')
        self.inputs = self._names(inputs if inputs is not None else
                                  {'in0': 0, 'in1': 1}, 1, 'input')
        self.captures = self._names(captures if captures is not None else {}, 15, 'capture')
        if image_format not in (LEGACY_FORMAT, PAIRED_FORMAT, RESIDENT_FORMAT):
            raise ValueError('Unsupported program image format')
        self.image_format = image_format
        self.idle_levels = self._mask(idle_high)
        self.idle_enabled = self._mask(idle_enabled)
        self.instructions = []
        self.labels = {}

    @staticmethod
    def _names(values, maximum, name):
        if not isinstance(values, Mapping):
            raise ValueError(f'{name} names must be a mapping')
        result = dict(values)
        for key, value in result.items():
            if not isinstance(key, str) or not key:
                raise ValueError(f'{name} names must be nonempty strings')
            _integer(value, 0, maximum, f'{name} index')
        return result

    @staticmethod
    def _resolve_name(value, names, maximum, name):
        if isinstance(value, str):
            if value not in names:
                raise ValueError(f'Unknown {name}: {value}')
            return names[value]
        return _integer(value, 0, maximum, name)

    def _mask(self, pins):
        if isinstance(pins, str):
            pins = (pins,)
        result = 0
        for pin in pins:
            result |= 1 << self._resolve_name(pin, self.outputs, 2, 'output')
        return result

    def _capture(self, capture):
        if capture is None:
            return 0
        if not isinstance(capture, (tuple, list)) or len(capture) != 2:
            raise ValueError('Capture must name an input and a destination')
        pin = self._resolve_name(capture[0], self.inputs, 1, 'input')
        slot = self._resolve_name(capture[1], self.captures, 15, 'capture')
        return 1 | pin << 1 | slot << 2

    def _guard(self, guard):
        if guard is None:
            return 0
        if not isinstance(guard, Mapping):
            raise ValueError('Guard must map input names to Boolean levels')
        mask = value = 0
        for pin, level in guard.items():
            index = self._resolve_name(pin, self.inputs, 1, 'input')
            level = _boolean(level, 'Guard level')
            if mask & (1 << index) and ((value >> index) & 1) != level:
                raise ValueError('Guard has conflicting aliases for one input')
            mask |= 1 << index
            value |= level << index
        return mask | value << 2

    def _append(self, kind, duration=1, *, high=(), enabled=(), **values):
        if len(self.instructions) >= 256:
            raise ValueError('Program exceeds 256 positions')
        self.instructions.append(dict(kind=kind, levels=self._mask(high),
            enabled=self._mask(enabled), duration=_integer(duration, 1, 256, 'Duration') - 1,
            **values))
        return self

    def label(self, name):
        if not isinstance(name, str) or not name or name in self.labels:
            raise ValueError('Labels must be unique nonempty strings')
        self.labels[name] = len(self.instructions)
        return self

    def action(self, duration, *, high=(), enabled=(), capture=None):
        return self._append(0, duration, high=high, enabled=enabled, entry=self._capture(capture))

    def wait(self, input, level, budget, *, high=(), enabled=()):
        pin = self._resolve_name(input, self.inputs, 1, 'input')
        return self._append(1, budget, high=high, enabled=enabled,
                            check=pin | _boolean(level, 'Wait level') << 1)

    def checked(self, duration, *, high=(), enabled=(), guard=None,
                capture=None, terminal_capture=None, jump=None, branch=None):
        if jump is not None and branch is not None:
            raise ValueError('Checked action cannot have both jump and branch')
        values = dict(check=self._guard(guard), entry=self._capture(capture),
                      terminal=self._capture(terminal_capture))
        if jump is not None:
            values.update(finish=1, yes=jump)
        if branch is not None:
            if not isinstance(branch, (tuple, list)) or len(branch) != 3:
                raise ValueError('Branch must name a capture and two targets')
            values.update(finish=2,
                sample=self._resolve_name(branch[0], self.captures, 15, 'capture'),
                yes=branch[1], no=branch[2])
        return self._append(2, duration, high=high, enabled=enabled, **values)

    def qualify(self, duration, budget, *, condition, high=(), enabled=()):
        return self._append(3, duration, high=high, enabled=enabled,
            check=self._guard(condition), budget=_integer(budget, 1, 256, 'Wait budget') - 1)

    def shift(self, pin, duration, *, msb_first=False, high=(), enabled=()):
        if self.image_format != RESIDENT_FORMAT:
            raise ValueError('SHIFT requires the resident source format')
        selected = self._resolve_name(pin, self.outputs, 2, 'output')
        return self._append(5, duration, high=high, enabled=enabled,
                            entry=selected | _boolean(msb_first, 'Bit order') << 2)

    def keep(self, duration, *, preserve=(), high=(), enabled=(), capture=None):
        if self.image_format != RESIDENT_FORMAT:
            raise ValueError('KEEP requires the resident source format')
        return self._append(6, duration, high=high, enabled=enabled,
                            entry=self._capture(capture), terminal=self._mask(preserve))

    def halt(self):
        return self._append(4)

    def _target(self, target):
        if isinstance(target, str):
            if target not in self.labels:
                raise ValueError(f'Unknown label: {target}')
            target = self.labels[target]
        return _integer(target, 0, len(self.instructions) - 1, 'Branch target')

    def build(self):
        if not self.instructions:
            raise ValueError('Program must contain at least one instruction')
        words = []
        for pending in self.instructions:
            values = dict(pending)
            for target in ('yes', 'no'):
                if target in values:
                    values[target] = self._target(values[target])
            words.append(_encode(values))
        program = Program(tuple(words), len(words) - 1, self.idle_levels,
                          self.idle_enabled, self.image_format)
        program.upload_words()
        return program


def resource_report(program):
    """Return actual source and upload capacities, checking admission first."""
    upload = program.upload_words()
    slots = set()
    for word in program.words[:program.last + 1]:
        decoded = fields(word)
        descriptors = []
        if decoded['kind'] in (0, 2, 6):
            descriptors.append(decoded['entry'])
        if decoded['kind'] == 2:
            descriptors.append(decoded['terminal'])
            if decoded['finish'] == 2:
                slots.add(decoded['sample'])
        for descriptor in descriptors:
            if descriptor & 1:
                slots.add(descriptor >> 2)
    used_parameters = None
    if program.image_format in (PAIRED_FORMAT, RESIDENT_FORMAT):
        from paired_execution import compile_e64, compile_resident
        compiler = compile_resident if program.image_format == RESIDENT_FORMAT else compile_e64
        used_parameters = compiler(program.words, (program.idle_levels, program.idle_enabled),
                                   program.last).used_parameters
    return dict(positions=program.last + 1, source_words=len(program.words),
        distinct_records=len(set((*program.words, *((4,) * (256 - len(program.words)))))),
        capture_slots=sorted(slots), used_parameters=used_parameters, upload_words=len(upload))


def resident_uart(bit_cycles=4):
    """One unchanged 8N1 UART TX program; accepted START supplies the byte."""
    builder = ProgramBuilder(outputs={'tx': 0, 'aux': 1, 'cs_n': 2},
        idle_high=('tx', 'cs_n'), idle_enabled=('tx', 'aux', 'cs_n'))
    driven = ('tx', 'aux', 'cs_n')
    builder.action(bit_cycles, high=('cs_n',), enabled=driven)
    for _ in range(8):
        builder.shift('tx', bit_cycles, high=('cs_n',), enabled=driven)
    builder.action(bit_cycles, high=('tx', 'cs_n'), enabled=driven).halt()
    return builder.build()


def resident_spi(half_cycles=4):
    """One-byte SPI controller, mode 0/MSB first and continuous chip select.

    Receive bit 7 is captured in slot 0, so raw low-byte captures are in wire
    order. No host payload can change an in-progress transfer.
    """
    builder = ProgramBuilder(outputs={'mosi': 0, 'sclk': 1, 'cs_n': 2},
        inputs={'miso': 0}, idle_high=('cs_n',),
        idle_enabled=('mosi', 'sclk', 'cs_n'))
    driven = ('mosi', 'sclk', 'cs_n')
    for slot in range(8):
        builder.shift('mosi', half_cycles, msb_first=True, enabled=driven)
        builder.keep(half_cycles, preserve=('mosi',), high=('sclk',),
                     enabled=driven, capture=('miso', slot))
    builder.action(half_cycles, enabled=driven).halt()
    return builder.build()
