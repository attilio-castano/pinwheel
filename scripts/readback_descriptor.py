"""Configure the shared RTL importer from a Lean-emitted read-back descriptor.

`backend_readback.py` is configured through module-level tables: the top
module, the Lean types and circuit, and for every input, register and output
its RTL name, width and Lean constructor term. Adapters have typed these tables
by hand. A descriptor (emitted by the files in EMITTERS) carries the
same facts, generated from the enumerations the emitter uses.

Checked-in copies live in scripts/readback_descriptors, so importing does not
need a Lean run; test/test_readback_descriptor.py fails if they differ from a
fresh emission.

`apply` writes a descriptor's facts into an importer module. Artifact naming
(namespace, Lean header) stays with the adapter. `configuration` snapshots
every table in order, so two ways of configuring the importer can be compared
exactly: the generated proof files depend only on this configuration and the
RTL.
"""
from __future__ import annotations

import functools
import json
from pathlib import Path
import re

SCHEMA = 'pinwheel.readback-descriptor.v1'
# Tables the descriptor owns. NAMESPACE, HEADER, KIND and ADDR_BITS stay with the adapter.
OWNED = ('TOP', 'INPUTS', 'REGISTERS', 'OUTPUTS', 'FAMILIES', 'INPUT_TYPE', 'REGISTER_TYPE', 'OUTPUT_TYPE',
         'CIRCUIT')
COMPARED = OWNED + ('NAMESPACE', 'HEADER', 'KIND', 'ADDR_BITS')
DIRECTORY = Path(__file__).resolve().parent / 'readback_descriptors'
# Each emitter writes these descriptors; together they write every name in NAMES.
EMITTERS = {'test/StreamingReadyReadbackDescriptor.lean': ('streaming-core-d2', 'streaming-core-d4',
                                                           'ready-core-d2', 'ready-core-d4', 'frontend'),
            'test/BufferedReadbackDescriptor.lean': ('buffered-sram', 'buffered-serial')}
NAMES = tuple(name for names in EMITTERS.values() for name in names)
LOCAL_IMPORT = re.compile(r'^import\s+(Pinwheel\.\S+)', re.M)


def emitter_imports(emitter, root=DIRECTORY.parent.parent):
    """The local modules an emitter imports. `lake env lean --run` loads them
    from the build without building them, so build these first."""
    return LOCAL_IMPORT.findall((Path(root) / emitter).read_text())


def emitter_for(name):
    return next(emitter for emitter, names in EMITTERS.items() if name in names)


def load(path):
    descriptor = json.loads(Path(path).read_text())
    if descriptor.get('schema') != SCHEMA:
        raise ValueError(f'{path}: expected {SCHEMA}')
    for key in ('inputs', 'registers', 'outputs'):
        names = [port['name'] for port in descriptor[key]]
        if len(names) != len(set(names)):
            raise ValueError(f'{path}: duplicate {key} name')
    return descriptor


@functools.cache
def checked_in(name):
    """A checked-in descriptor by name. Shared between callers: do not mutate."""
    if name not in NAMES:
        raise ValueError(f'Unknown read-back descriptor {name!r}')
    return load(DIRECTORY / f'{name}.json')


def table(ports):
    return {port['name']: (port['width'], port['term']) for port in ports}


def families(registers):
    """Indexed register families, in first-appearance order.

    A register whose term carries an index (`.word 3#6`) belongs to the family
    named by its RTL name without the trailing number."""
    found = {}
    for port in registers:
        match = INDEXED.fullmatch(port['term'])
        if match is None:
            continue
        prefix = re.sub(r'\d+$', '', port['name'].removeprefix('r_'))
        key = (prefix, match.group(1), int(match.group(2)))
        found[key] = found.get(key, 0) + 1
    return [(prefix, ctor, count, width) for (prefix, ctor, width), count in found.items()]


INDEXED = re.compile(r'\.(\w+) \d+#(\d+)')


def plain(descriptor, key):
    """(RTL name, constructor) of every field without an index, in order. Field
    lists stay whole when an adapter edits the importer's tables afterwards."""
    return [(port['name'], port['term'][1:]) for port in descriptor[key] if INDEXED.fullmatch(port['term']) is None]


def fields(descriptor, key, wrapper=None, *, strip=''):
    """(name, width, constructor) tables in descriptor order, for adapters that
    work with constructor names. Without `wrapper`: fields that are a single
    constructor (`.sck`). With it: fields wrapped once (`.status .valid`), giving
    the inner constructor. `strip` is removed from the front of each RTL name."""
    found = []
    for port in descriptor[key]:
        parts = port['term'].split(' ')
        if wrapper is None and len(parts) == 1:
            ctor = parts[0][1:]
        elif wrapper is not None and len(parts) == 2 and parts[0] == '.' + wrapper and parts[1].startswith('.'):
            ctor = parts[1][1:]
        else:
            continue
        if not port['name'].startswith(strip):
            raise ValueError(f"{port['name']}: expected the prefix {strip!r}")
        found.append((port['name'][len(strip):], port['width'], ctor))
    return found


def apply_ports(rb, descriptor):
    """Set only the module and port tables, for adapters that name their Lean
    types and circuit themselves."""
    rb.TOP = descriptor['module']
    rb.INPUTS = table(descriptor['inputs'])
    rb.REGISTERS = table(descriptor['registers'])
    rb.OUTPUTS = table(descriptor['outputs'])
    rb.DESCRIPTOR = descriptor
    return rb


def apply(rb, descriptor):
    rb.TOP = descriptor['module']
    rb.INPUTS = table(descriptor['inputs'])
    rb.REGISTERS = table(descriptor['registers'])
    rb.OUTPUTS = table(descriptor['outputs'])
    rb.FAMILIES = families(descriptor['registers'])
    rb.INPUT_TYPE = descriptor['input_type']
    rb.REGISTER_TYPE = descriptor['register_type']
    rb.OUTPUT_TYPE = descriptor['output_type']
    rb.CIRCUIT = descriptor['circuit']
    rb.DESCRIPTOR = descriptor
    return rb


def configuration(rb):
    """Every compared table, with dict order preserved."""
    def ordered(value):
        return list(value.items()) if isinstance(value, dict) else value
    return {name: ordered(getattr(rb, name, None)) for name in COMPARED}


def differences(left, right):
    """Names of compared tables that differ, including order."""
    return [name for name in COMPARED if left[name] != right[name]]
