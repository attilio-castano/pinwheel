"""Matched two-bank, two-read, one-write FF-array screen; not a chip emitter.

Both sizes use the same explicit word/decode/mux RTL. Every mapped saved
netlist is checked with an arbitrary-state next-state/output SAT miter.
Standalone cell-delay STA excludes macro arcs, execution logic and all wires.
"""
from collections import Counter
from copy import deepcopy
import hashlib
import json
from pathlib import Path
import re
import runpy
import shutil

from validation_run import sha

ROOT = Path(__file__).resolve().parents[1]
CAD = ROOT / 'build/tools/oss-cad-suite/bin'
FF = 'sg13cmos5l_dfrbpq_1'


def rtl(address_bits, width):
    depth = 1 << address_bits
    lines = [f'''module lookup(input clk, input write_enable, input write_bank,
      input [{address_bits-1}:0] write_address, input [{width-1}:0] write_data,
      input read_bank, input [{address_bits-1}:0] read_address0, read_address1,
      output reg [{width-1}:0] value0, value1);''']
    for b in range(2):
        for k in range(depth):
            lines += [f'reg [{width-1}:0] word_{b}_{k};',
                f'always @(posedge clk) if (write_enable && write_bank == 1\'d{b} && '
                f'write_address == {address_bits}\'d{k}) word_{b}_{k} <= write_data;']
    for port in range(2):
        lines.append(f'always @* case ({{read_bank, read_address{port}}})')
        for b in range(2):
            for k in range(depth):
                lines.append(f"{address_bits+1}'d{b*depth+k}: value{port} = word_{b}_{k};")
        lines += [f"default: value{port} = {width}'b0;", 'endcase']
    return '\n'.join(lines + ['endmodule', ''])


def oracle(address_bits, width):
    """Independent packed-array semantics, including read-before-write state.

    No DUT decoders or mux topology are used to construct expected values.
    """
    size = 2*(1 << address_bits)*width
    return f'''module oracle(input write_enable, write_bank,
      input [{address_bits-1}:0] write_address, input [{width-1}:0] write_data,
      input read_bank, input [{address_bits-1}:0] read_address0, read_address1,
      input [{size-1}:0] state, output reg [{size-1}:0] next_state,
      output [{width-1}:0] value0, value1);
      assign value0 = state[{{read_bank,read_address0}}*{width} +: {width}];
      assign value1 = state[{{read_bank,read_address1}}*{width} +: {width}];
      always @* begin
        next_state = state;
        if (write_enable) next_state[{{write_bank,write_address}}*{width} +: {width}] = write_data;
      end
    endmodule
    '''


def cut_state(module, address_bits, width):
    cut = deepcopy(module)
    cut['attributes'] = {}
    ports = dict(clk=1, write_enable=1, write_bank=1, write_address=address_bits,
                 write_data=width, read_bank=1, read_address0=address_bits,
                 read_address1=address_bits, value0=width, value1=width)
    if set(cut['ports']) != set(ports):
        raise ValueError('lookup interface mismatch')
    for p, n in ports.items():
        if len(cut['ports'][p]['bits']) != n or cut['ports'][p]['direction'] != (
                'output' if p.startswith('value') else 'input'):
            raise ValueError('lookup port width/direction mismatch')
    flops = {}
    for name, c in list(cut['cells'].items()):
        if c['type'] == '$scopeinfo':
            del cut['cells'][name]
        elif c['type'] == FF:
            pins = c['connections']
            if (set(pins) != {'D','Q','CLK','RESET_B'} or
                    any(len(v) != 1 for v in pins.values()) or
                    pins['CLK'] != cut['ports']['clk']['bits'] or pins['RESET_B'] != ['1']):
                raise ValueError('unexpected lookup FF control')
            q = pins['Q'][0]
            if not isinstance(q, int) or q in flops:
                raise ValueError('duplicate/constant lookup FF')
            flops[q] = pins['D'][0]
            del cut['cells'][name]
        elif c['type'].startswith(('$', 'sg13cmos5l_df')):
            raise ValueError('unsupported state or unmapped cell')
    bits = []
    for b in range(2):
        for k in range(1 << address_bits):
            word = cut['netnames'].get(f'word_{b}_{k}', {}).get('bits', [])
            if len(word) != width:
                raise ValueError('lost lookup word')
            bits += word
    if len(set(bits)) != len(bits) or set(bits) != set(flops):
        raise ValueError('lookup state is not an exact FF bijection')
    del cut['ports']['clk']
    cut['ports']['state'] = dict(direction='input', bits=bits)
    cut['ports']['next_state'] = dict(direction='output', bits=[flops[b] for b in bits])
    return cut


def screen(run, out):
    helpers = runpy.run_path(str(ROOT/'scripts/check-map-tile.py'))
    sta = runpy.run_path(str(ROOT/'scripts/check-sram-timing.py'))
    libraries = helpers['pinned_libraries']()
    lock = json.loads((ROOT/'tools/physical-toolchain.json').read_text())
    info = json.loads(run(['docker','image','inspect',lock['container_tag']], 'lookup-image'))[0]
    runtime = {k:v for k,v in info['Config'].items() if v is not None}
    runtime_hash = hashlib.sha256(json.dumps(runtime, sort_keys=True).encode()).hexdigest()
    if (info['Architecture'] != 'arm64' or info['Os'] != 'linux' or
            info['RootFS']['Layers'] != lock['container_rootfs_diff_ids'] or
            runtime_hash != lock['container_runtime_config_sha256']):
        raise ValueError('unmatched installed STA image')
    result = dict(scope='standalone matched FF tables; not the current emitted map or complete candidate',
                  tool_image=info['Id'], runtime_config_sha256=runtime_hash,
                  variants={}, containers={}, wire_parasitics=False,
                  assumptions=dict(period_ns=20, input_max_ns=4, input_min_ns=.2,
                                   output_max_ns=4, output_min_ns=.2, output_load_pf=.01,
                                   input_driver='sg13cmos5l_buf_2', clock_uncertainty_ns=.2,
                                   clock_transition_ns=.15))
    (out/'abc.constr').write_text('set_driving_cell sg13cmos5l_buf_2\nset_load 10\n')

    def yosys(label, lines, reject=None):
        script = out/(label+'.ys')
        script.write_text('\n'.join(map(str,lines))+'\n')
        return run([CAD/'yosys','-Q','-T','-s',script],label,reject=reject)

    for variant, address_bits, width in [('index',8,5),('parameter',5,20)]:
        design, spec = out/(variant+'.sv'), out/(variant+'-oracle.sv')
        design.write_text(rtl(address_bits,width))
        spec.write_text(oracle(address_bits,width))
        result['variants'][variant] = {}
        for corner, lib in libraries.items():
            prefix = variant+'-'+corner
            folder = out/prefix
            folder.mkdir()
            mapped, readback = folder/'mapped.json', folder/'readback.json'
            netlist = folder/'design.v'
            log = yosys(prefix+'-map', [f'read_liberty -lib {lib}',
                f'read_verilog -sv {design}', 'synth -top lookup -noabc',
                f'dfflibmap -liberty {lib}',
                f'abc -liberty {lib} -constr {out}/abc.constr -D 10000',
                'clean','check -assert',f'stat -liberty {lib}',
                f'write_json {mapped}',f'write_verilog -noattr -noexpr {netlist}'])
            yosys(prefix+'-readback',[f'read_liberty -lib {lib}',
                f'read_verilog {netlist}','hierarchy -check -top lookup',
                'check -assert',f'write_json {readback}'])
            data = json.loads(readback.read_text())
            module = data['modules']['lookup']
            cut = cut_state(module,address_bits,width)
            counts = Counter(c['type'] for c in module['cells'].values() if c['type']!='$scopeinfo')
            original = json.loads(mapped.read_text())['modules']['lookup']
            if counts != Counter(c['type'] for c in original['cells'].values() if c['type']!='$scopeinfo'):
                raise ValueError('mapped readback cell counts differ')
            metrics = dict(flip_flops=counts[FF], cells=sum(counts.values()), cell_types=dict(counts),
                area_um2=round(sum(float(data['modules'][k]['attributes']['area'])*n for k,n in counts.items()),4),
                abc_module_delays_ps=list(map(float,re.findall(r'ABC(?: RESULTS)?:.*?Delay\s*=\s*([\d.]+)',log))))

            def prove(negative=False):
                check = deepcopy(cut)
                if negative:
                    check['ports']['value1']['bits'] = check['ports']['value0']['bits']
                    # JSON intake reconstructs named port wires. Mutate the
                    # matching netname too, as in the established map checker.
                    check['netnames']['value1']['bits'] = check['ports']['value0']['bits']
                path = folder/('negative-cut.json' if negative else 'cut.json')
                path.write_text(json.dumps(dict(modules=dict(dut=check)))+'\n')
                proof = yosys(prefix+('-negative' if negative else '-proof'),
                    [f'read_liberty -ignore_miss_func {lib}',f'read_json {path}',
                     f'read_verilog -sv {spec}','proc',
                     'miter -equiv -flatten -make_outputs oracle dut miter',
                     'hierarchy -check -top miter','flatten','opt_clean',
                     'sat -verify -prove trigger 0 -set-def-inputs miter'],
                     reject='proof did fail' if negative else None)
                if not negative and 'SAT proof finished - no model found: SUCCESS!' not in proof:
                    raise ValueError('incomplete lookup SAT proof')
            prove()
            if variant=='parameter' and corner=='typical':
                prove(True)
            shutil.copyfile(lib,folder/'cells.lib')
            tcl = '''read_liberty cells.lib
read_verilog design.v
link_design lookup
create_clock -name clk -period 20 [get_ports clk]
set inputs [get_ports {write_enable write_bank write_address[*] write_data[*] read_bank read_address0[*] read_address1[*]}]
set_input_delay -clock clk -max 4 $inputs
set_input_delay -clock clk -min .2 $inputs
set_output_delay -clock clk -max 4 [all_outputs]
set_output_delay -clock clk -min .2 [all_outputs]
set_driving_cell -lib_cell sg13cmos5l_buf_2 -pin X $inputs
set_load .010 [all_outputs]
set_clock_uncertainty .2 [get_clocks clk]
set_clock_transition .15 [get_clocks clk]
puts "PINWHEEL_SETUP_CHECK"
check_setup -verbose
puts "PINWHEEL_MAX_SLACK"
report_worst_slack -max
puts "PINWHEEL_MIN_SLACK"
report_worst_slack -min
puts "PINWHEEL_READ_PATH"
report_checks -to [all_outputs] -path_delay max -group_path_count 2 -fields {slew cap fanout}
puts "PINWHEEL_WRITE_PATH"
report_checks -path_delay max -group_path_count 2 -fields {slew cap fanout}
puts "PINWHEEL_ELECTRICAL"
report_check_types -max_slew -max_capacitance -max_fanout -min_pulse_width -min_period -violators
'''
            (folder/'timing.tcl').write_text('if {[catch {\n'+tcl+'''} message]} {
puts stderr $message
exit 1
}
puts "PINWHEEL_STA_COMPLETE"
exit 0
''')
            timing = sta['run_sta'](run,folder,info['Id'], 'pinwheel-'+out.name+'-'+prefix,
                                     result['containers'],prefix+'-sta')
            metrics['cell_timing'] = sta['parse_timing'](timing)
            section = timing.split('PINWHEEL_READ_PATH',1)[1].split('PINWHEEL_',1)[0]
            arrivals = re.findall(r'([0-9.]+)\s+data arrival time',section)
            if not arrivals:
                raise ValueError('missing lookup read timing path')
            metrics['worst_read_arrival_ns'] = max(map(float,arrivals))
            result['variants'][variant][corner] = metrics
    return result
