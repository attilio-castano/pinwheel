"""Saved Yosys binding checks for the public buffered SRAM serial package.

The checker establishes direct pin/port connectivity and ownership of retained
cells. Controller/frontend circuit meaning, response framing and memory
availability require the gate's separate equivalence and replay checks.
"""
import json
from pathlib import Path
import re

from buffered_hardware_synthesis import CAD
from buffered_reactive_hardware_rtl import COMMAND_FIELDS, STATE_WIDTHS
from validation_run import sha


ROOT = Path(__file__).resolve().parents[1]
TOP = 'pinwheel_buffered_shared_branches_sram_serial'
FRONTEND = 'pinwheel_buffered_sram_serial_frontend'
CONTROLLER = 'pinwheel_buffered_shared_branches_sram_controller'
MACRO = 'RM_IHPSG13_1P_64x64_c2_bm_bist'
VIEWS = ROOT / 'build/storage/macros'
WRAPPER = ROOT / 'physical/buffered_sram_serial_wrapper.sv'
MEMORY = ROOT / 'physical/buffered_sram_memory.sv'
PUBLIC_INPUTS = dict(clk=1, initialize=1, csn=1, sck=1, mosi=1, raw_inputs=2)
PUBLIC_OUTPUTS = dict(miso=1, ready=1, busy=1, levels=3, enabled=3)
MEMORY_WIDTHS = dict(mem_addr0=6, mem_addr1=6, mem_data=64,
    mem_write=1, mem_read=1, mem_q0=64, mem_q1=64)
OWNED_PREFIXES = ('frontend.', 'controller.',
    '$flatten\\frontend.', '$flatten\\controller.')


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def _attribute_enabled(value):
    if type(value) is str:
        try:
            return int(value, 2) != 0
        except ValueError as error:
            raise RuntimeError('Malformed serial binding module attribute') from error
    require(type(value) in (int, bool), 'Malformed serial binding module attribute')
    return bool(value)


def binding_readback(data):
    """Verify the complete flattened package, including all inter-module aliases."""
    require(type(data) is dict and type(data.get('modules')) is dict and
        TOP in data['modules'], 'Missing complete serial package module')
    module = data['modules'][TOP]
    require(type(module) is dict, 'Malformed complete serial package module')
    ports, nets, cells = (module.get(key) for key in ('ports', 'netnames', 'cells'))
    require(all(type(value) is dict for value in (ports, nets, cells)),
            'Missing complete serial package ports, wires or cells')
    public = {name: ('input', width) for name, width in PUBLIC_INPUTS.items()}
    public.update({name: ('output', width) for name, width in PUBLIC_OUTPUTS.items()})
    require(set(ports) == set(public) and all(type(ports[name]) is dict and
        ports[name].get('direction') == direction and
        type(ports[name].get('bits')) is list and len(ports[name]['bits']) == width
        for name, (direction, width) in public.items()),
        'Changed complete serial public wrapper boundary')

    def net(name, width):
        entry = nets.get(name, {})
        bits = entry.get('bits') if type(entry) is dict else None
        require(type(bits) is list and len(bits) == width and all(
            (type(bit) is int and bit >= 2) or
            (type(bit) is str and bit in ('0', '1', 'x', 'z')) for bit in bits),
                'Missing complete serial wire: ' + name)
        return bits

    def alias(left, right, width, kind):
        require(net(left, width) == net(right, width),
                'Changed transparent serial ' + kind + ': ' + left + ' / ' + right)

    for name, (_, width) in public.items():
        require(ports[name]['bits'] == net(name, width),
                'Changed transparent serial public port wire: ' + name)
    for name, width in PUBLIC_INPUTS.items():
        alias(name, 'frontend.' + name, width, 'frontend physical wire')
    for name in ('miso', 'ready'):
        alias(name, 'frontend.' + name, 1, 'frontend physical wire')
    alias('clk', 'controller.clk', 1, 'controller clock')
    alias('clk', 'memory.clk', 1, 'memory clock')

    core_inputs = dict(COMMAND_FIELDS, raw_inputs=2)
    for name, width in core_inputs.items():
        alias('core_' + name, 'frontend.core_' + name, width, 'core wire')
        alias('core_' + name, 'controller.' + name, width, 'core wire')
    alias('raw_inputs', 'core_raw_inputs', 2, 'raw input passthrough')
    for name, width in STATE_WIDTHS.items():
        alias('status_' + name, 'frontend.status_' + name, width, 'status wire')
        alias('status_' + name, 'controller.' + name, width, 'status wire')
    for name in ('busy', 'levels', 'enabled'):
        alias(name, 'status_' + name, PUBLIC_OUTPUTS[name], 'protocol output wire')
    for name, width in MEMORY_WIDTHS.items():
        alias(name, 'controller.' + name, width, 'controller memory wire')
        alias(name, 'memory.' + name, width, 'memory wire')

    for name, expected in (('frontend', FRONTEND), ('controller', CONTROLLER),
                           ('memory', 'pinwheel_buffered_sram_memory')):
        cell = cells.get(name, {})
        require(type(cell) is dict and cell.get('type') == '$scopeinfo' and
            cell.get('parameters', {}).get('TYPE') == 'module' and
            cell.get('attributes', {}).get('module') == expected,
            'Changed complete serial module identity: ' + name)

    def foreign_blackbox(cell):
        definition = data['modules'].get(cell['type'], {})
        attributes = definition.get('attributes', {})
        require(type(attributes) is dict, 'Malformed serial binding module attributes')
        opaque = any(_attribute_enabled(attributes.get(name, 0))
                     for name in ('blackbox', 'whitebox'))
        # Pinned standard cells are legitimate in mapped frontend/controller
        # scopes. Other opaque modules participate in the exact macro census.
        return opaque and not cell['type'].startswith('sg13cmos5l_')

    require(all(type(cell) is dict and type(cell.get('type')) is str
                for cell in cells.values()), 'Malformed complete serial cell')
    macros = {name: cell for name, cell in cells.items()
        if cell['type'].startswith('RM_IHPSG13_') or foreign_blackbox(cell)}
    require(set(macros) == {'memory.storage0', 'memory.storage1'},
            'Wrong serial SRAM macro instances')
    require(all(cell['type'] == MACRO for cell in macros.values()),
            'Wrong serial SRAM macro type')
    require(all(cell['type'] == '$scopeinfo' or name in macros or
        name.startswith(OWNED_PREFIXES) for name, cell in cells.items()),
        'Circuitry outside serial frontend, controller and SRAM macros')

    common = dict(A_CLK=net('clk', 1), A_MEN=['1'], A_DLY=['1'],
        A_WEN=net('mem_write', 1), A_REN=net('mem_read', 1),
        A_DIN=net('mem_data', 64), A_BM=['1'] * 64,
        A_BIST_CLK=['0'], A_BIST_EN=['0'], A_BIST_MEN=['0'],
        A_BIST_WEN=['0'], A_BIST_REN=['0'], A_BIST_ADDR=['0'] * 6,
        A_BIST_DIN=['0'] * 64, A_BIST_BM=['0'] * 64)
    for k in range(2):
        expected = dict(common, A_ADDR=net(f'mem_addr{k}', 6),
                        A_DOUT=net(f'mem_q{k}', 64))
        cell = macros[f'memory.storage{k}']
        require(cell.get('connections') == expected,
                'Changed complete serial SRAM macro port binding: ' + str(k))
        require(cell.get('port_directions') ==
            {name: 'output' if name == 'A_DOUT' else 'input' for name in expected},
            'Changed complete serial SRAM macro port directions: ' + str(k))

    clocked_cells = 0
    for name, cell in cells.items():
        kind = cell['type']
        connections = cell.get('connections', {})
        require(type(connections) is dict, 'Malformed serial cell connections: ' + name)
        require(not kind.startswith(('$dlatch', '$adlatch', '$_DLATCH')),
                'Unexpected serial package latch: ' + name)
        clock_port = ('CLK' if kind.startswith(('$dff', '$adff', '$sdff')) else
            'C' if kind.startswith('$_DFF') else
            'CLK' if kind.startswith('sg13cmos5l_') and 'CLK' in connections else None)
        if clock_port is not None:
            require(connections.get(clock_port) == net('clk', 1),
                    'Changed serial package register clock: ' + name)
            if 'CLK_POLARITY' in cell.get('parameters', {}):
                require(_attribute_enabled(cell['parameters']['CLK_POLARITY']),
                        'Changed serial package register clock polarity: ' + name)
            require(not re.match(r'\$_DFF(?:E|SR|SRE)?_N', kind),
                    'Changed serial package register clock polarity: ' + name)
            clocked_cells += 1

    return dict(macros=2, macro=MACRO, ports_per_macro=len(common)+2,
        frontend_module=FRONTEND, controller_module=CONTROLLER,
        public_input_ports=len(PUBLIC_INPUTS), public_output_ports=len(PUBLIC_OUTPUTS),
        core_input_aliases=len(core_inputs), status_aliases=len(STATE_WIDTHS),
        raw_input_passthrough=True, common_clock=True, checked_clocked_cells=clocked_cells,
        full_word_broadcast=True, independent_addresses=True, bist_disabled=True,
        response_edge='Macro Q connects directly to controller input; no wrapper response register.',
        boundary='Saved direct aliases, macro pins and scoped circuitry; circuit/serial meaning and availability are separate checks.')


def _yosys_path(path):
    """Quote one path for a Yosys script without treating it as shell text."""
    text = str(Path(path))
    require('\n' not in text and '\r' not in text and '\x00' not in text,
            'Invalid serial binding path')
    return '"' + text.replace('\\', '\\\\').replace('"', '\\"') + '"'


def read_complete_binding(run, out, frontsv, controllersv, label, library=None):
    """Flatten actual emitted/mapped modules with the unchanged public wrapper."""
    require(type(label) is str and re.fullmatch(r'[A-Za-z0-9_.-]+', label),
            'Invalid serial binding label')
    path = Path(out) / (label + '-binding.json')
    lines = ['read_liberty -lib ' + _yosys_path(VIEWS / (MACRO + '_typ_1p20V_25C.lib'))]
    if library is not None:
        lines.append('read_liberty -lib ' + _yosys_path(library))
    lines += ['read_verilog -sv ' + ' '.join(map(_yosys_path,
        (frontsv, controllersv, WRAPPER, MEMORY))),
        'hierarchy -check -top ' + TOP, 'proc', 'flatten', 'opt_clean',
        'check -assert', 'write_json ' + _yosys_path(path)]
    script = Path(out) / (label + '-binding.ys')
    script.write_text('\n'.join(lines) + '\n')
    run([CAD / 'yosys', '-Q', '-T', '-s', script], label + '-binding-readback')
    return dict(binding_readback(json.loads(path.read_text())), readback_sha256=sha(path))
