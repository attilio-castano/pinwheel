"""Complete named-port package and Tiny Tapeout wiring for streaming-ready-quad-v1.

Only exact emitter inventories are accepted. The generated sources contain
wiring and public output masking; all protocol behavior remains in the generic
core and quad frontend. No preexisting wrapper or ABI is changed.
"""
import re


PUBLIC_INPUTS = dict(initialize=1, csn=1, sck=1, mosi=4, raw_inputs=2)
PUBLIC_OUTPUTS = dict(miso=4, ready=1, busy=1, levels=3, enabled=3)


def ports(description, key):
    result = {}
    for item in description[key]:
        if (type(item) is not dict or set(item) != {'name', 'width'} or
                type(item['name']) is not str or not re.fullmatch(r'[a-zA-Z_][a-zA-Z0-9_]*', item['name']) or
                item['name'] in result or type(item['width']) is not int or item['width'] <= 0):
            raise ValueError('Malformed or duplicate emitter port inventory')
        result[item['name']] = item['width']
    return result


def width(value):
    return '' if value == 1 else f'[{value - 1}:0] '


def validate(core, frontend):
    if not re.fullmatch(r'pinwheel_streaming_ready_core_d[24]', core.get('module', '')):
        raise ValueError('Expected the depth-2 or depth-4 streaming core')
    if frontend.get('module') != 'pinwheel_streaming_quad_frontend':
        raise ValueError('Unexpected streaming quad frontend module')
    ci, co = ports(core, 'inputs'), ports(core, 'outputs')
    fi, fo = ports(frontend, 'inputs'), ports(frontend, 'outputs')
    if fi != {**PUBLIC_INPUTS, **{'status_' + name: bits for name, bits in co.items()}}:
        raise ValueError('Frontend inputs do not cover every public pin and core status exactly')
    if fo != {**{'core_' + name: bits for name, bits in ci.items()}, 'miso': 4, 'ready': 1}:
        raise ValueError('Frontend outputs do not cover every core input and host output exactly')
    for name in ('busy', 'levels', 'enabled'):
        if co.get(name) != PUBLIC_OUTPUTS[name]:
            raise ValueError('Changed public streaming protocol output')
    return ci, co, fi, fo


def package_source(core, frontend):
    ci, co, fi, fo = validate(core, frontend)
    depth = int(core['module'][-1])
    declarations = ['input wire clk']
    declarations += [f'input wire {width(bits)}{name}' for name, bits in PUBLIC_INPUTS.items()]
    declarations += [f'output wire {width(bits)}{name}' for name, bits in PUBLIC_OUTPUTS.items()]
    wires = [f'  wire {width(bits)}core_{name};' for name, bits in ci.items()]
    wires += [f'  wire {width(bits)}status_{name};' for name, bits in co.items()]
    front_bindings = ['.clk(clk)'] + [f'.{name}({name})' for name in PUBLIC_INPUTS]
    front_bindings += [f'.status_{name}(status_{name})' for name in co]
    front_bindings += [f'.core_{name}(core_{name})' for name in ci]
    front_bindings += ['.miso(miso)', '.ready(ready)']
    core_bindings = ['.clk(clk)'] + [f'.{name}(core_{name})' for name in ci]
    core_bindings += [f'.{name}(status_{name})' for name in co]
    return ('`default_nettype none\n' +
        f'module pinwheel_streaming_ready_quad_d{depth}(\n  ' + ',\n  '.join(declarations) + '\n);\n' +
        '\n'.join(wires) + '\n' +
        f'  {frontend["module"]} frontend(\n    ' + ',\n    '.join(front_bindings) + '\n  );\n' +
        f'  {core["module"]} core(\n    ' + ',\n    '.join(core_bindings) + '\n  );\n' +
        '  assign busy = status_busy;\n  assign levels = status_levels;\n' +
        '  assign enabled = status_enabled;\nendmodule\n`default_nettype wire\n')


def tt_source(depth):
    if type(depth) is not int or depth not in (2, 4):
        raise ValueError('Qualified streaming depth must be 2 or 4')
    return f'''`default_nettype none
// streaming-ready-quad-v1. All host and protocol inputs are sampled by clk.
// CSn ui0, SCK ui1, MOSI lanes0..3 ui2/5/6/7, raw inputs ui3/4.
// MISO lanes0..3 uo0..3, READY uo4, BUSY uo5; protocol outputs uio0..2.
// This introduces no asynchronous clock domain or electrical timing claim.
module tt_um_pinwheel_streaming_ready_d{depth}(
  input wire [7:0] ui_in, output wire [7:0] uo_out,
  input wire [7:0] uio_in, output wire [7:0] uio_out, output wire [7:0] uio_oe,
  input wire ena, input wire clk, input wire rst_n
);
  wire active = ena && rst_n;
  wire [3:0] miso;
  wire ready, busy;
  wire [2:0] levels, enabled;
  pinwheel_streaming_ready_quad_d{depth} engine(
    .clk(clk), .initialize(!active), .csn(ui_in[0]), .sck(ui_in[1]),
    .mosi({{ui_in[7:5], ui_in[2]}}), .raw_inputs(ui_in[4:3]),
    .miso(miso), .ready(ready), .busy(busy), .levels(levels), .enabled(enabled)
  );
  assign uo_out = active ? {{2'b0, busy, ready, miso}} : 8'b0;
  assign uio_out = active ? {{5'b0, levels}} : 8'b0;
  assign uio_oe = active ? {{5'b0, enabled}} : 8'b0;
  wire _unused = &{{uio_in, 1'b0}};
endmodule
`default_nettype wire
'''


def bridge_source(depth):
    if type(depth) is not int or depth not in (2, 4):
        raise ValueError('Qualified streaming depth must be 2 or 4')
    return f'''`timescale 1ns/1ps
// Public TT ports only. MISO/raw inputs are sampled before the core edge;
// READY, BUSY and protocol pads are observed afterward. No private DUT state.
module streaming_quad_host_bridge;
  reg clk=0;
  reg initialize=0, csn=1, sck=0;
  reg [3:0] mosi=0;
  reg [7:0] peer_levels=0, peer_enabled=0, pullups=255;
  reg [1:0] links=0;
  tri [7:0] pads;
  wire [7:0] ui_in={{mosi[3:1],pads[1:0],mosi[0],sck,csn}};
  wire [7:0] uo_out,uio_out,uio_oe;
  wire [7:0] output_levels={{3'b0,uio_out[2:0],2'b0}};
  wire [7:0] output_enabled={{3'b0,uio_oe[2:0],2'b0}};
  tt_um_pinwheel_streaming_ready_d{depth} dut(.ui_in(ui_in),.uo_out(uo_out),.uio_in(8'b0),
    .uio_out(uio_out),.uio_oe(uio_oe),.ena(1'b1),.clk(clk),.rst_n(!initialize));
  genvar k;
  generate for(k=0;k<8;k=k+1) begin: pad
    assign pads[k]=output_enabled[k] ? output_levels[k] : 1'bz;
    assign pads[k]=peer_enabled[k] ? peer_levels[k] : 1'bz;
    assign (weak1,weak0) pads[k]=pullups[k] ? 1'b1 : 1'bz;
  end endgenerate
  tranif1 scl_link(pads[0],pads[2],links[0]);
  tranif1 sda_link(pads[1],pads[3],links[1]);
  reg [3:0] edge_miso;
  reg [1:0] edge_inputs;
  reg [7:0] wire_values,known,required,connected;
  integer fd,code,j;
  integer in_initialize,in_csn,in_sck,in_mosi,in_peer_levels,in_peer_enabled,in_links,in_pullups;
  reg [8191:0] line,extra;
  initial begin
    fd=$fopen("/dev/stdin","r");
    if(!fd) $fatal(1,"Missing streaming quad pin pipe");
    while(1) begin
      code=$fgets(line,fd);
      if(!code) $finish;
      if(code>23) $fatal(1,"Malformed streaming quad pin input");
      code=$sscanf(line,"%d %d %d %d %d %d %d %d %s",in_initialize,in_csn,in_sck,in_mosi,
        in_peer_levels,in_peer_enabled,in_links,in_pullups,extra);
      if(code!=8 || ( ^{{in_initialize,in_csn,in_sck,in_mosi,in_peer_levels,in_peer_enabled,in_links,in_pullups}})===1'bx ||
        in_initialize<0 || in_initialize>1 || in_csn<0 || in_csn>1 || in_sck<0 || in_sck>1 ||
        in_mosi<0 || in_mosi>15 || in_peer_levels<0 || in_peer_levels>255 ||
        in_peer_enabled<0 || in_peer_enabled>255 || in_links<0 || in_links>3 || in_pullups<0 || in_pullups>255)
        $fatal(1,"Malformed streaming quad pin input");
      initialize=in_initialize;csn=in_csn;sck=in_sck;mosi=in_mosi;
      peer_levels=in_peer_levels;peer_enabled=in_peer_enabled;links=in_links;pullups=in_pullups;
      clk=0;#10;
      if((^uo_out[3:0])===1'bx || (^pads[1:0])===1'bx) $fatal(1,"Unknown streaming pre-edge pins");
      if((output_enabled & peer_enabled)!==8'b0) $fatal(1,"External peer drives a DUT output");
      connected=0;
      if(links[0]) connected=connected|8'h05;
      if(links[1]) connected=connected|8'h0a;
      if((connected & ((output_levels & output_enabled)|(peer_levels & peer_enabled)))!==8'b0)
        $fatal(1,"Board links require open-drain low/release drivers");
      edge_miso=uo_out[3:0];edge_inputs=pads[1:0];
      clk=1;#10;clk=0;
      if((^{{uo_out,uio_out,uio_oe}})===1'bx) $fatal(1,"Unknown streaming post-edge outputs");
      if(uo_out[7:6]!==0 || uio_out[7:3]!==0 || uio_oe[7:3]!==0) $fatal(1,"Unused TT outputs are not zero");
      wire_values=0;known=0;
      for(j=0;j<8;j=j+1) if(pads[j]===1'b0 || pads[j]===1'b1) begin
        known[j]=1;wire_values[j]=pads[j];
      end
      required=8'h03|output_enabled|peer_enabled|connected;
      if((known & required)!==required) $fatal(1,"Unknown/contention on streaming pads");
      if((output_enabled & peer_enabled)!==0) $fatal(1,"External peer drives a post-edge DUT output");
      $display("STREAM_QUAD %0d %0d %0d %0d %0d %0d %0d %0d",edge_miso,uo_out[4],uo_out[5],
        uio_out[2:0],uio_oe[2:0],wire_values,known,edge_inputs);
      $fflush();
    end
  end
endmodule
'''
