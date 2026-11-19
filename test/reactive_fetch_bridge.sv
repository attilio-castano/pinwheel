`timescale 1ns/1ps
// Same resolved-pad wire protocol as pinwheel_sim.Simulation, with raw Reactive
// setup commands and public cut diagnostics packed into the command/status.
module reactive_fetch_bridge;
  reg clk = 0, rst_n;
  reg [76:0] command;
  reg [7:0] peer_levels, peer_enabled, pullups;
  reg [1:0] links, sampled_raw;
  wire reset = !rst_n, start = command[75], write = command[74];
  wire [1:0] bank = command[73:72], incoming;
  wire [7:0] address = command[71:64];
  wire [63:0] data = command[63:0];
  wire busy;
  wire [2:0] mode, levels, enabled;
  wire [7:0] pc, remaining;
  wire [15:0] samples;
`ifdef REGISTERED_FETCH
  wire fetch_wait;
`else
  wire fetch_wait = 1'b0;
`endif
  `REACTIVE_MODULE dut(.clk(clk), .reset(reset), .start(start), .incoming(incoming),
    .write(write), .bank(bank), .address(address), .data(data),
    .busy(busy), .mode(mode), .pc(pc), .remaining(remaining),
    .levels(levels), .enabled(enabled),
`ifdef REGISTERED_FETCH
    .fetch_wait(fetch_wait),
`endif
    .sample0(samples[0]), .sample1(samples[1]), .sample2(samples[2]), .sample3(samples[3]),
    .sample4(samples[4]), .sample5(samples[5]), .sample6(samples[6]), .sample7(samples[7]),
    .sample8(samples[8]), .sample9(samples[9]), .sample10(samples[10]), .sample11(samples[11]),
    .sample12(samples[12]), .sample13(samples[13]), .sample14(samples[14]), .sample15(samples[15]));

  tri [7:0] pads;
  wire [7:0] physical_levels = {3'b0, levels, 2'b0};
  wire [7:0] physical_enabled = {3'b0, enabled, 2'b0};
  assign incoming = pads[1:0];
  genvar k;
  generate for (k = 0; k < 8; k = k + 1) begin : pad
    assign pads[k] = physical_enabled[k] ? physical_levels[k] : 1'bz;
    assign pads[k] = peer_enabled[k] ? peer_levels[k] : 1'bz;
    assign (weak1, weak0) pads[k] = pullups[k] ? 1'b1 : 1'bz;
  end endgenerate
  tranif1 scl_link(pads[0], pads[2], links[0]);
  tranif1 sda_link(pads[1], pads[3], links[1]);

  integer fd, status, cycles, j;
  reg [4095:0] line;
  reg [7:0] values, known;
  initial begin
    fd = $fopen("/dev/stdin", "r");
    if (!fd) $fatal(1, "Missing reactive fetch host pipe");
    while ($fgets(line, fd)) begin
      status = $sscanf(line, "%d %d %d %d %d %d %d", rst_n, command,
                       peer_levels, peer_enabled, links, pullups, cycles);
      if (status != 7 || cycles != 1) $fatal(1, "Expected one reactive fetch edge");
      clk = 0; #10;
      sampled_raw = incoming;
      clk = 1; #10;
      clk = 0;
      if (command[76]) begin
        values = 0;
        known = 0;
        for (j = 0; j < 8; j = j + 1) begin
          if (pads[j] === 1'b0 || pads[j] === 1'b1) begin
            known[j] = 1;
            values[j] = pads[j];
          end
        end
        $display("PINWHEEL %0d %0d %0d %0d %0d", {sampled_raw, fetch_wait, samples, remaining, pc, mode, busy},
                 physical_levels, physical_enabled, values, known);
      end else begin
        // Before loading idle metadata, raw output pins can be undefined.
        $display("PINWHEEL 0 0 0 255 255");
      end
      $fflush();
    end
    $finish;
  end
endmodule
