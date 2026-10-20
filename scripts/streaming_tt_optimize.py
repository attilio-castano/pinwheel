"""State-preserving, explicitly conditional word specialization candidate.

The producer is deliberately not an equivalence authority. Original top-level
word instances, ports and connections remain intact. Only a word's internal
constant-connected input is specialized. Its later kernel certificate must
state that input premise, and the component link must discharge it from actual
wiring. No FF optimization, state quotient or old optimized netlist is used.
"""
from copy import deepcopy
from hashlib import sha256
import argparse
import json
from pathlib import Path
import subprocess
import time

from streaming_mapped_flow import quoted, state_inventory
from streaming_mapped_hierarchy import binary, hierarchical_source
from streaming_mapped_liberty import load_library, require
from streaming_mapped_cost import measure

SCHEMA = 'pinwheel.streaming-tt-constant-specialization.v1'
SMALL_COMPARE = frozenset(('$lt', '$gt', '$ge', '$eq', '$ne'))


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'), allow_nan=False)


def fixed_operands(cell):
    """Return only supported *whole* constant operands, not guessed values."""
    kind, wires = cell['type'], cell['connections']
    if kind != '$mux' and not (kind in SMALL_COMPARE and len(wires['A']) <= 8):
        return {}
    result = {}
    for pin in ('A', 'B'):
        values = wires[pin]
        if values and all(type(bit) is str and bit in ('0', '1') for bit in values):
            result[pin] = ''.join(reversed(values))
    return result


def specialized_source(data, top):
    """Create an untrusted hierarchy with full original operand interfaces.

    Constants in descriptors are hints only. Proof generation rechecks the
    actual mapped leaf, and static top wiring is independently checked.
    """
    result, descriptions = hierarchical_source(data, top)
    original = data['modules'][top]
    specialized, instances = {}, {}
    for name, source_cell in sorted(original['cells'].items()):
        if source_cell['type'] == '$dff': continue
        fixed = fixed_operands(source_cell)
        if not fixed: continue
        top_cell = result['modules'][top]['cells'][name]
        original_type = top_cell['type']
        descriptor = dict(kind=source_cell['type'], parameters=deepcopy(source_cell['parameters']),
            ports={pin: len(bits) for pin, bits in source_cell['connections'].items()},
            fixed_operands=fixed)
        key = canonical(descriptor)
        module_name = 'pinwheel_tt_opt_word_' + sha256(key.encode()).hexdigest()[:16]
        if module_name not in specialized:
            require(module_name not in result['modules'], 'Specialization module collision')
            module = deepcopy(result['modules'][original_type])
            # A direct original word operator is used, rather than preserving a
            # generic ripple whose cross-FA constants ABC cannot see.
            operator = dict(type=source_cell['type'], parameters=deepcopy(source_cell['parameters']),
                attributes={}, port_directions=deepcopy(source_cell['port_directions']),
                connections={pin: deepcopy(port['bits']) for pin, port in module['ports'].items()})
            for pin, bits in fixed.items(): operator['connections'][pin] = list(reversed(bits))
            module['cells'] = {'operator': operator}
            module['netnames'] = {pin: dict(hide_name=0, bits=deepcopy(port['bits']), attributes={})
                for pin, port in module['ports'].items()}
            result['modules'][module_name] = module
            specialized[module_name] = descriptor
            descriptions[module_name] = descriptor
        else:
            require(specialized[module_name] == descriptor, 'Specialization digest collision')
        top_cell['type'] = module_name
        instances[name] = dict(module=module_name, original_module=original_type, fixed_operands=fixed)
        require(top_cell['connections'] == source_cell['connections'] and
            top_cell['port_directions'] == source_cell['port_directions'], 'Changed original word boundary')
    return result, dict(schema=SCHEMA, top=top, words=descriptions,
        specializations=specialized, instances=instances,
        specialized_instances=len(instances), specialized_modules=len(specialized),
        equivalence_proved=False,
        boundary='Untrusted combinational candidate; all-state kernel linkage is required separately.')


def mapping_script(source, top, out, library, abc):
    require(type(top) is str and top.replace('_', '').isalnum(), 'Unsafe top name')
    out = Path(out).resolve()
    return '\n'.join((
        'read_json ' + quoted(source), 'hierarchy -check -top ' + top,
        'setattr -set keep 1 t:$dff', 'setattr -set keep 1 w:r_*',
        'techmap', 'opt_expr',
        'write_json ' + quoted(out / 'pre-map.json'),
        'dfflibmap -liberty ' + quoted(library),
        'abc -exe ' + quoted(abc) + ' -liberty ' + quoted(library),
        'read_liberty -lib ' + quoted(library), 'check -assert',
        'write_json ' + quoted(out / 'mapped.json'),
        'write_verilog -noattr -noexpr ' + quoted(out / 'mapped.v'),
    )) + '\n'


def produce(raw_json, top, library, yosys, abc, out, *, timeout=180, native_executor=None):
    """A retained, explicitly unqualified development mapping and exact bill."""
    raw_json, library, yosys, abc = [Path(p).resolve() for p in (raw_json, library, yosys, abc)]
    out = Path(out).resolve()
    require(not out.exists(), 'Refusing to overwrite a candidate directory')
    inputs = {str(p): sha256(p.read_bytes()).hexdigest() for p in (raw_json, library, yosys, abc)}
    lib = load_library(library)
    source = json.loads(raw_json.read_bytes())
    hierarchy, descriptor = specialized_source(source, top)
    out.mkdir(parents=True)
    (out / 'source.json').write_text(canonical(hierarchy) + '\n')
    (out / 'words.json').write_text(canonical(descriptor) + '\n')
    script = mapping_script(out / 'source.json', top, out, library, abc)
    (out / 'map.ys').write_text(script)
    report = dict(schema=SCHEMA, passed=False, qualified=False, input_sha256=inputs,
        top=top, argv=[str(yosys), '-s', str(out / 'map.ys')], **{
            key: descriptor[key] for key in ('specialized_instances', 'specialized_modules')})
    start = time.monotonic()
    if native_executor is None:
        with (out / 'yosys.log').open('w') as log:
            completed = subprocess.run(report['argv'], stdout=log, stderr=subprocess.STDOUT, timeout=timeout)
    else:
        completed = native_executor.run(report['argv'], out / 'yosys.log', timeout=timeout)
        report.update(argv=completed.native_argv, native_journal_index=completed.native_journal_index)
    report.update(elapsed_seconds=time.monotonic()-start, exit_code=completed.returncode)
    require(completed.returncode == 0, 'Candidate mapping failed; retained log identifies the attempt')
    mapped = json.loads((out / 'mapped.json').read_bytes())
    inventory = state_inventory(source, mapped, top, lib)
    (out / 'state-inventory.json').write_text(canonical(inventory) + '\n')
    cost = measure(out / 'mapped.json', top, library, inventory['register_bits'])
    (out / 'cost.json').write_text(canonical(cost) + '\n')
    require(inputs == {str(p): sha256(p.read_bytes()).hexdigest() for p in (raw_json, library, yosys, abc)},
        'Mapping inputs changed during the native operation')
    report.update(mapping_completed=True, full_ff_q_bijection=True, register_bits=inventory['register_bits'],
        cell_area_um2=cost['cell_area_um2'], combinational_cells=cost['combinational_cells'],
        longest_combinational_gate_path=cost['longest_combinational_gate_path'],
        output_sha256={p.name: sha256(p.read_bytes()).hexdigest() for p in out.iterdir() if p.is_file()})
    (out / 'report.json').write_text(canonical(report) + '\n')
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ('raw-json', 'top', 'library', 'yosys', 'abc', 'out'): parser.add_argument('--' + name, required=True)
    args = parser.parse_args()
    print(canonical(produce(args.raw_json, args.top, args.library, args.yosys, args.abc, args.out)))


if __name__ == '__main__': main()
