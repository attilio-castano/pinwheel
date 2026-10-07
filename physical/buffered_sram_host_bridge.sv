`timescale 1ns/1ps
// One public command per edge; the external peer sees resolved package pads.
// The SRAM target uses the identical public command and observation ABI.
// This bridge contains neither expected values nor internal DUT references.
module buffered_reactive_host_bridge;
  reg clk = 0;
  reg initialize = 0;
  reg [2:0] command = 0;
  reg [5:0] address = 0;
  reg [63:0] word = 0;
  reg [55:0] branch = 0;
  reg [31:0] tx_data = 0;
  reg [6:0] count = 0;
  reg [23:0] control = 0;
  reg [10:0] virtual_span = 0;
  reg [2:0] idle_levels = 0, idle_enabled = 0;
  reg [5:0] tx_length = 0, rx_capacity = 0;
  reg [15:0] expected_generation = 0, expected_transfer = 0;
  reg [4:0] read_index = 0;
  reg [7:0] peer_levels = 0, peer_enabled = 0, pullups = 255;
  reg [1:0] links = 0;
  wire valid, busy, retained, rejected, read_valid, read_bit, exhausted, pending;
  wire [1:0] mode, stage1, stage2;
  wire [7:0] pc;
  wire [7:0] remaining;
  wire [9:0] virtual_pc;
  wire [2:0] env0, env1, phase;
  wire [7:0] wait_left;
  wire [15:0] scratch;
  wire [2:0] levels, enabled;
  wire [5:0] tx_consumed, rx_length;
  wire [31:0] rx_data;
  wire [15:0] generation, transfer;
  tri [7:0] pads;
  wire [1:0] raw_inputs = pads[1:0];
  wire [7:0] output_levels = {3'b0, levels, 2'b0};
  wire [7:0] output_enabled = {3'b0, enabled, 2'b0};
  pinwheel_buffered_shared_branches_sram dut(.*);

  genvar k;
  generate for (k = 0; k < 8; k = k + 1) begin: pad
    assign pads[k] = output_enabled[k] ? output_levels[k] : 1'bz;
    assign pads[k] = peer_enabled[k] ? peer_levels[k] : 1'bz;
    assign (weak1, weak0) pads[k] = pullups[k] ? 1'b1 : 1'bz;
  end endgenerate
  tranif1 scl_link(pads[0], pads[2], links[0]);
  tranif1 sda_link(pads[1], pads[3], links[1]);

  reg [7:0] wire_values, known, required, connected;
  reg command_rejected;
  reg [1:0] edge_inputs;
  integer fd, code, j;
  reg [8191:0] line;
  initial begin
    fd = $fopen("/dev/stdin", "r");
    if (!fd) $fatal(1, "Missing reactive hardware command pipe");
    while (1) begin
      code = $fgets(line, fd);
      if (!code) $finish;
      code = $sscanf(line,
        "%d %d %d %h %d %h %d %d %d %d %d %d %d %d %d %d %d %d %d %d",
        initialize, command, address, word, control, branch, count, virtual_span, idle_levels, idle_enabled, tx_data,
        tx_length, rx_capacity, expected_generation, expected_transfer, read_index,
        peer_levels, peer_enabled, links, pullups);
      if (code != 20) $fatal(1, "Malformed reactive hardware command");
      clk = 0; #10;
      // This observation belongs to the bridge, not to the circuit state cut.
      // Capture resolved raw inputs before the edge that samples them.
      if ((raw_inputs[0] !== 1'b0 && raw_inputs[0] !== 1'b1) ||
          (raw_inputs[1] !== 1'b0 && raw_inputs[1] !== 1'b1))
        $fatal(1, "Unknown pre-edge reactive input pads");
      if ((output_enabled & peer_enabled) !== 8'h00)
        $fatal(1, "External peer drives a pre-edge buffered DUT-owned output pad");
      connected = 0;
      if (links[0]) connected = connected | 8'h05;
      if (links[1]) connected = connected | 8'h0a;
      if ((connected & ((output_levels & output_enabled) |
                        (peer_levels & peer_enabled))) !== 8'h00)
        $fatal(1, "Pre-edge buffered board links require open-drain low/release drivers");
      edge_inputs = raw_inputs;
      command_rejected = rejected;
      clk = 1; #10; clk = 0;
      wire_values = 0; known = 0;
      for (j = 0; j < 8; j = j + 1) begin
        if (pads[j] === 1'b0 || pads[j] === 1'b1) begin
          known[j] = 1; wire_values[j] = pads[j];
        end
      end
      required = 8'h03 | output_enabled | peer_enabled;
      if (links[0]) required = required | 8'h05;
      if (links[1]) required = required | 8'h0a;
      if ((known & required) !== required)
        $fatal(1, "Unknown/contention on reactive resolved pads values=%h known=%h required=%h",
          wire_values, known, required);
      if ((output_enabled & peer_enabled) !== 8'h00)
        $fatal(1, "External peer drives a buffered DUT-owned output pad");
      connected = 0;
      if (links[0]) connected = connected | 8'h05;
      if (links[1]) connected = connected | 8'h0a;
      if ((connected & ((output_levels & output_enabled) |
                        (peer_levels & peer_enabled))) !== 8'h00)
        $fatal(1, "Buffered board links require open-drain low/release drivers");
      $display("REACTIVE %0d %0d %0d %0d %0d %0d %0d %0d %0d %0d %0d %0d %0d %0d %0d %0d %0d %0d %0d %0d %0d %0d %0d %0d %0d %0d %0d %0d %0d",
        valid, busy, retained, command_rejected, mode, pc, remaining, levels, enabled,
        tx_consumed, rx_length, rx_data, read_valid, read_bit,
        generation, transfer, exhausted, pending, stage1, stage2, virtual_pc, env0, env1, phase, wait_left, scratch, wire_values, known, edge_inputs);
      $fflush();
    end
  end
endmodule
