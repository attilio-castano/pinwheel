"""Independent PWL v0 reader and instruction-lookup oracle for generated fixtures.

This Python implementation reads the documented byte grammar; it does not call Lean.
It is a validation oracle, not a hardware implementation or a public loader API.
"""
import csv
from pathlib import Path


class InvalidImage(ValueError):
    pass


class Reader:
    def __init__(self, data):
        self.data = data
        self.offset = 0

    def byte(self, bound=256):
        if self.offset >= len(self.data):
            raise InvalidImage('truncated record')
        value = self.data[self.offset]
        self.offset += 1
        if value >= bound:
            raise InvalidImage(f'field {value} outside 0..{bound - 1}')
        return value

    def index(self):
        tag = self.byte(2)
        return tag, self.byte(8 if tag == 0 else 2)

    def pins(self):
        tag = self.byte(2)
        base = self.byte(8), self.byte(8)
        if tag == 0:
            return (tag, *base)
        return (tag, *base, self.byte(3), self.byte(2), self.index(), self.index(),
                self.byte(2), self.byte(2))

    def sample(self):
        return (self.byte(2), self.index()) if self.byte(2) else None

    def target(self):
        tag = self.byte(2)
        return (tag, self.byte(128)) if tag == 0 else (tag,)

    def transfer(self, conditional=False):
        tag = self.byte(4 if conditional else 3)
        if tag == 0:
            return tag,
        if tag == 1:
            return tag, self.target()
        if tag == 2:
            return tag, self.index(), self.target(), self.target()
        return tag, self.index(), self.byte(8), self.transfer(), self.transfer()

    def template(self):
        tag = self.byte(5)
        if tag == 4:
            return tag,
        pins = self.pins()
        if tag == 0:
            return tag, pins, self.byte(), self.sample()
        if tag == 1:
            return tag, pins, (self.byte(2), self.byte(2)), self.byte()
        if tag == 2:
            return (tag, pins, self.byte(), (self.byte(4), self.byte(4)), self.sample(),
                    self.sample(), self.transfer(True))
        return tag, pins, (self.byte(4), self.byte(4)), self.byte(), self.byte()

    def code(self, fuel=64):
        if fuel == 0:
            raise InvalidImage('layout depth exceeds parser fuel')
        tag = self.byte(3)
        if tag == 0:
            return tag, self.template()
        if tag == 1:
            return tag, self.code(fuel - 1), self.code(fuel - 1)
        return tag, self.byte(8) + 1, self.code(fuel - 1)


def dimensions(code):
    if code[0] == 0:
        return 1, 1, 0
    if code[0] == 1:
        a, b = dimensions(code[1]), dimensions(code[2])
        return a[0] + b[0], 1 + a[1] + b[1], max(a[2], b[2])
    body = dimensions(code[2])
    return code[1] * body[0], 1 + body[1], 1 + body[2]


def locate(code, pc, env=(0, 0)):
    if code[0] == 0:
        return (code[1], env) if pc == 0 else None
    if code[0] == 1:
        size = dimensions(code[1])[0]
        return locate(code[1], pc, env) if pc < size else locate(code[2], pc - size, env)
    size = dimensions(code[2])[0]
    if pc >= code[1] * size:
        return None
    return locate(code[2], pc % size, (pc // size, env[0]))


def index_value(index, env):
    return index[1] if index[0] == 0 else env[index[1]]


def resolve(template, data, env, pc):
    if template[0] == 4:
        return template
    pins = template[1]
    levels, enables = pins[1:3]
    if pins[0] == 1:
        pin, enable, byte_index, bit_index, msb, invert = pins[3:]
        byte = index_value(byte_index, env)
        if byte >= len(data):
            return None
        bit = index_value(bit_index, env)
        value = ((data[byte] >> (7 - bit if msb else bit)) & 1) ^ invert
        current = enables if enable else levels
        current = (current | (1 << pin)) if value else (current & ~(1 << pin))
        if enable:
            enables = current
        else:
            levels = current

    def sample(capture):
        return None if capture is None else (capture[0], (0, index_value(capture[1], env)))

    def target(value):
        result = value[1] if value[0] == 0 else pc + 1
        if result >= 128:
            raise InvalidImage('next target overflow')
        return 0, result

    def transfer(value):
        if value[0] == 3:
            return transfer(value[3] if index_value(value[1], env) == value[2] else value[4])
        if value[0] == 0:
            return value
        if value[0] == 1:
            return 1, target(value[1])
        return 2, (0, index_value(value[1], env)), target(value[2]), target(value[3])

    base = (template[0], (0, levels, enables))
    if template[0] == 0:
        return (*base, template[2], sample(template[3]))
    if template[0] == 2:
        try:
            return (*base, template[2], template[3], sample(template[4]), sample(template[5]),
                    transfer(template[6]))
        except InvalidImage:
            return None
    return (*base, *template[2:])


def template_bytes(template):
    def flatten(value):
        if isinstance(value, tuple):
            return [item for part in value for item in flatten(part)]
        return [value]

    def sample(value):
        return [0] if value is None else [1, *flatten(value)]

    if template[0] == 4:
        return [4]
    result = [template[0], *flatten(template[1])]
    if template[0] == 0:
        return [*result, template[2], *sample(template[3])]
    if template[0] == 2:
        return [*result, template[2], *template[3], *sample(template[4]), *sample(template[5]),
                *flatten(template[6])]
    return [*result, *flatten(template[2:])]


def read(data):
    reader = Reader(data)
    if [reader.byte() for _ in range(4)] != [0x50, 0x57, 0x4c, 0]:
        raise InvalidImage('magic or version')
    kind = reader.byte(2)
    image = {'kind': kind, 'idle': (reader.byte(8), reader.byte(8))}
    if kind == 0:
        image['last'] = reader.byte(128)
        image['memory'] = [reader.template() for _ in range(128)]
        for template in image['memory']:
            # A literal instruction is a fixed point of operand substitution.
            if resolve(template, (0, 0), (0, 0), 0) != template:
                raise InvalidImage('dynamic operand in explicit image')
    else:
        image['data'] = reader.byte(), reader.byte()
        image['code'] = reader.code()
        span, nodes, depth = dimensions(image['code'])
        if span > 128 or nodes > 64 or depth > 2:
            raise InvalidImage('program bounds')
        image['last'] = span - 1
    if reader.offset != len(data):
        raise InvalidImage('trailing bytes')
    return image


def fetch(image, pc):
    if image['kind'] == 0:
        return image['memory'][pc]
    found = locate(image['code'], pc)
    return (4,) if found is None else resolve(found[0], image['data'], found[1], pc)


def verify(directory: Path):
    checks = 0
    images = sorted(directory.glob('*.pwl'))
    if len(images) != 4:
        raise AssertionError('expected four generated program images')
    for path in images:
        image = read(path.read_bytes())
        with path.with_suffix('.fetch.csv').open() as stream:
            rows = list(csv.DictReader(stream))
        if [int(row['pc']) for row in rows] != list(range(128)):
            raise AssertionError(f'incomplete fetch oracle: {path.name}')
        for row in rows:
            decoded = fetch(image, int(row['pc']))
            expected = [int(value) for value in row['record_bytes'].split(':')]
            if decoded is None or template_bytes(decoded) != expected:
                raise AssertionError(f'lookup differs: {path.name} pc={row["pc"]}')
            checks += 1
    return {'images': len(images), 'fetched_instructions': checks}


if __name__ == '__main__':
    print(verify(Path(__file__).resolve().parents[1] / 'build/binary'))
