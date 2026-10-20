"""State-preserving mapping candidate and explicit source/mapped boundary.

This flow deliberately avoids synth/opt/FSM/FF optimization. Its inventory is
not an equivalence proof: every D and public output still needs a certificate.
"""
from pathlib import Path
import re

from streaming_mapped_liberty import FF, require
from streaming_mapped_netlist import parse_mapped


def quoted(path):
    text = str(Path(path).resolve())
    require('"' not in text and '\n' not in text and '\r' not in text, 'Unsafe Yosys path')
    return '"' + text + '"'


def mapping_script(source, top, out, library, abc):
    require(type(top) is str and re.fullmatch(r'[A-Za-z_][A-Za-z0-9_]*', top), 'Invalid mapped top')
    out = Path(out).resolve()
    return '\n'.join((
        'read_json ' + quoted(source),
        'hierarchy -check -top ' + top,
        'setattr -set keep 1 t:$dff',
        'setattr -set keep 1 w:r_*',
        'techmap',
        'write_json ' + quoted(out / 'pre-map.json'),
        'dfflibmap -liberty ' + quoted(library),
        'abc -exe ' + quoted(abc) + ' -liberty ' + quoted(library),
        'read_liberty -lib ' + quoted(library),
        'check -assert',
        'write_json ' + quoted(out / 'mapped.json'),
        'write_verilog -noattr -noexpr ' + quoted(out / 'mapped.v'),
    )) + '\n'


def source_state(data, top):
    require(type(data) is dict and top in data.get('modules', {}), 'Missing source top')
    module = data['modules'][top]
    require(not module.get('processes') and not module.get('memories'), 'Unlowered source state')
    require(not any('init' in net.get('attributes', {}) for net in module.get('netnames', {}).values()),
        'Implicit source state initialization needs a separate contract')
    ports = module.get('ports', {})
    require('clk' in ports and ports['clk']['direction'] == 'input' and len(ports['clk']['bits']) == 1,
        'Source needs one direct clock')
    clock = ports['clk']['bits'][0]
    require(type(clock) is int, 'Source clock is constant')
    fields = {name: tuple(net['bits']) for name, net in module.get('netnames', {}).items()
        if name.startswith('r_')}
    require(fields and all(values for values in fields.values()), 'Missing declared source state')
    bits = [value for values in fields.values() for value in values]
    require(all(type(value) is int for value in bits) and len(bits) == len(set(bits)),
        'Source state is constant or aliased')
    flops = {}
    for name, cell in module.get('cells', {}).items():
        kind = cell['type']
        if kind != '$dff':
            require('dff' not in kind.lower() and 'latch' not in kind.lower(), 'Unsupported source storage')
            continue
        connections, params = cell['connections'], cell['parameters']
        require(set(params) == {'CLK_POLARITY', 'WIDTH'} and cell.get('port_directions') ==
            {'CLK': 'input', 'D': 'input', 'Q': 'output'} and set(connections) == {'CLK', 'D', 'Q'} and connections['CLK'] == [clock] and
            int(params['CLK_POLARITY'], 2) == 1 and len(connections['D']) == len(connections['Q']) and
            int(params['WIDTH'], 2) == len(connections['Q']), 'Unsupported source FF shape')
        for d, q in zip(connections['D'], connections['Q']):
            require(type(q) is int and q not in flops, 'Aliased or constant source Q')
            flops[q] = dict(cell=name, d=d)
    require(set(bits) == set(flops), 'Declared source state does not exactly cover all FF Qs')
    return fields, flops


def state_inventory(source, mapped, top, library):
    """Require full FF Q bijection and matching public port names/widths.

    Named state positions supply only the proposed bijection. They supply no
    functional logic; proof generators must independently check every D root.
    """
    fields, source_flops = source_state(source, top)
    graph = parse_mapped(mapped, top, library)
    module = mapped['modules'][top]
    mapped_fields = {name: tuple(net['bits']) for name, net in module.get('netnames', {}).items()
        if name.startswith('r_')}
    require(fields.keys() == mapped_fields.keys() and
        all(len(bits) == len(mapped_fields[name]) for name, bits in fields.items()),
        'Mapped declared register inventory changed')
    named = [bit for values in mapped_fields.values() for bit in values]
    require(all(type(value) is int for value in named) and len(named) == len(set(named)) and
        set(named) == graph.state_bits, 'Mapped FF Q/register bijection lost state, aliases or constants')
    source_ports = source['modules'][top]['ports']
    mapped_ports = module['ports']
    require(source_ports.keys() == mapped_ports.keys() and all(
        source_ports[name]['direction'] == mapped_ports[name]['direction'] and
        len(source_ports[name]['bits']) == len(mapped_ports[name]['bits']) for name in source_ports),
        'Mapped public port inventory changed')
    by_q = {ff.q: ff for ff in graph.flipflops}
    registers = [dict(register=name, index=index, source_q=q, mapped_q=mapped_fields[name][index],
        source_d=source_flops[q]['d'], mapped_d=by_q[mapped_fields[name][index]].d,
        mapped_cell=by_q[mapped_fields[name][index]].name)
        for name, bits in sorted(fields.items()) for index, q in enumerate(bits)]
    inputs = [dict(port=name, index=index, source=bit, mapped=mapped_ports[name]['bits'][index])
        for name, port in sorted(source_ports.items()) if port['direction'] == 'input'
        for index, bit in enumerate(port['bits'])]
    outputs = [dict(port=name, index=index, source=bit, mapped=mapped_ports[name]['bits'][index])
        for name, port in sorted(source_ports.items()) if port['direction'] == 'output'
        for index, bit in enumerate(port['bits'])]
    return dict(schema='pinwheel.streaming-mapped-state-inventory.v1', top=top,
        boundary='Proposed full-state bijection only; D and public outputs still require kernel equivalence certificates.',
        complete_ff_q_bijection=True, register_fields=len(fields), register_bits=len(registers),
        mapped_comb_cells=len(graph.gates), mapped_ff_cells=len(graph.flipflops),
        cell_counts=graph.cell_counts, registers=registers, inputs=inputs, outputs=outputs)
