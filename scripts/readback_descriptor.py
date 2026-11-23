"""Configure the shared RTL importer from a Lean-emitted read-back descriptor.

`backend_readback.py` is configured through module-level tables: the top
module, the Lean types and circuit, and for every input, register and output
its RTL name, width and Lean constructor term. Adapters have typed these tables
by hand. A descriptor (test/StreamingReadyReadbackDescriptor.lean) carries the
same facts, generated from the enumerations the emitter uses.

`apply` writes a descriptor's facts into an importer module. Artifact naming
(namespace, Lean header) stays with the adapter. `configuration` snapshots
every table in order, so two ways of configuring the importer can be compared
exactly: the generated proof files depend only on this configuration and the
RTL.
"""
from __future__ import annotations

import json
from pathlib import Path
import re

SCHEMA = 'pinwheel.readback-descriptor.v1'
# Tables the descriptor owns. NAMESPACE, HEADER, KIND and ADDR_BITS stay with the adapter.
OWNED = ('TOP', 'INPUTS', 'REGISTERS', 'OUTPUTS', 'FAMILIES', 'INPUT_TYPE', 'REGISTER_TYPE', 'OUTPUT_TYPE',
         'CIRCUIT')
COMPARED = OWNED + ('NAMESPACE', 'HEADER', 'KIND', 'ADDR_BITS')


def load(path):
    descriptor = json.loads(Path(path).read_text())
    if descriptor.get('schema') != SCHEMA:
        raise ValueError(f'{path}: expected {SCHEMA}')
    for key in ('inputs', 'registers', 'outputs'):
        names = [port['name'] for port in descriptor[key]]
        if len(names) != len(set(names)):
            raise ValueError(f'{path}: duplicate {key} name')
    return descriptor


def table(ports):
    return {port['name']: (port['width'], port['term']) for port in ports}


def families(registers):
    """Indexed register families, in first-appearance order.

    A register whose term carries an index (`.word 3#6`) belongs to the family
    named by its RTL name without the trailing number."""
    found = {}
    for port in registers:
        match = re.fullmatch(r'\.(\w+) \d+#(\d+)', port['term'])
        if match is None:
            continue
        prefix = re.sub(r'\d+$', '', port['name'].removeprefix('r_'))
        key = (prefix, match.group(1), int(match.group(2)))
        found[key] = found.get(key, 0) + 1
    return [(prefix, ctor, count, width) for (prefix, ctor, width), count in found.items()]


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
    return rb


def configuration(rb):
    """Every compared table, with dict order preserved."""
    def ordered(value):
        return list(value.items()) if isinstance(value, dict) else value
    return {name: ordered(getattr(rb, name, None)) for name in COMPARED}


def differences(left, right):
    """Names of compared tables that differ, including order."""
    return [name for name in COMPARED if left[name] != right[name]]
