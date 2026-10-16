`timescale 1ns/1ps
// One physical core edge per numeric input line, through the exact TT ports. The external protocol peer observes
// only public output pins and resolved pads. MISO is sampled before that edge;
// ready and protocol pads are observed afterwards. There are no DUT references
// below its public serial/pad ports and no parallel command or status transport.
module tt_buffered_sram_serial_host_bridge;
  reg clk = 0;
  reg initialize = 0, csn = 1, sck = 0, mosi = 0;
  reg ena = 1;
  reg [7:0] peer_levels = 0, peer_enabled = 0, pullups = 255;
  reg [1:0] links = 0;
  tri [7:0] pads;
  wire [7:0] ui_in = {3'b0, pads[1:0], mosi, sck, csn};
  wire [7:0] uo_out, uio_out, uio_oe;
  wire [7:0] uio_in = {5'b0, pads[4:2]};
  wire rst_n = !initialize;
  wire miso = uo_out[0], ready = uo_out[1], busy = uo_out[2];
  wire [2:0] levels = uio_out[2:0], enabled = uio_oe[2:0];
  wire [1:0] raw_inputs = pads[1:0];
  wire [7:0] output_levels = {3'b0, levels, 2'b0};
  wire [7:0] output_enabled = {3'b0, enabled, 2'b0};
  tt_um_pinwheel_buffered dut (.*);

  genvar k;
  generate for (k = 0; k < 8; k = k + 1) begin: pad
    assign pads[k] = output_enabled[k] ? output_levels[k] : 1'bz;
    assign pads[k] = peer_enabled[k] ? peer_levels[k] : 1'bz;
    assign (weak1, weak0) pads[k] = pullups[k] ? 1'b1 : 1'bz;
  end endgenerate
  tranif1 scl_link(pads[0], pads[2], links[0]);
  tranif1 sda_link(pads[1], pads[3], links[1]);

  reg [7:0] wire_values, known, required, connected;
  reg edge_miso;
  reg [1:0] edge_inputs;
  integer fd, code, line_length, j;
  integer in_initialize, in_csn, in_sck, in_mosi;
  integer in_ena, in_rst_n;
  integer in_peer_levels, in_peer_enabled, in_links, in_pullups;
  reg [8191:0] line;
  reg [8191:0] extra;
  initial begin
    fd = $fopen("/dev/stdin", "r");
    if (!fd) $fatal(1, "Missing Tiny Tapeout buffered SRAM serial pin pipe");
    while (1) begin
      line_length = $fgets(line, fd);
      if (!line_length) $finish;
      // Control transitions occur without a rising clk, demonstrating the
      // wrapper's immediate mask independently of synchronous invalidation.
      code = $sscanf(line, "TT_CONTROL %d %d %s", in_ena, in_rst_n, extra);
      if (code == 2) begin
        if (line_length > 15)
          $fatal(1, "Malformed Tiny Tapeout control input");
        if (in_ena < 0 || in_ena > 1 || in_rst_n < 0 || in_rst_n > 1)
          $fatal(1, "Malformed Tiny Tapeout control input");
        ena = in_ena; initialize = !in_rst_n; #10;
        if (!ena || !rst_n) begin
          if ({uo_out, uio_out, uio_oe} !== 24'b0)
            $fatal(1, "Tiny Tapeout reset/deselect did not immediately mask outputs");
        end
        $display("TT_CONTROL %0d %0d %0d %0d %0d", ena, rst_n, uo_out, uio_out, uio_oe);
        $fflush();
      end else begin
      // Eight canonical decimal fields occupy at most 22 bytes including LF.
      // Bound the line before integer parsing can overflow or truncate it.
      if (line_length > 22) $fatal(1, "Malformed buffered SRAM serial pin input");
      code = $sscanf(line, "%d %d %d %d %d %d %d %d %s",
        in_initialize, in_csn, in_sck, in_mosi,
        in_peer_levels, in_peer_enabled, in_links, in_pullups, extra);
      if (code != 8 ||
          (^{in_initialize, in_csn, in_sck, in_mosi,
             in_peer_levels, in_peer_enabled, in_links, in_pullups}) === 1'bx ||
          in_initialize < 0 || in_initialize > 1 ||
          in_csn < 0 || in_csn > 1 || in_sck < 0 || in_sck > 1 ||
          in_mosi < 0 || in_mosi > 1 ||
          in_peer_levels < 0 || in_peer_levels > 255 ||
          in_peer_enabled < 0 || in_peer_enabled > 255 ||
          in_links < 0 || in_links > 3 || in_pullups < 0 || in_pullups > 255)
        $fatal(1, "Malformed buffered SRAM serial pin input");
      initialize = in_initialize; csn = in_csn; sck = in_sck; mosi = in_mosi;
      peer_levels = in_peer_levels; peer_enabled = in_peer_enabled;
      links = in_links; pullups = in_pullups;
      clk = 0; #10;
      if (!ena || !rst_n) begin
        if ({uo_out, uio_out, uio_oe} !== 24'b0)
          $fatal(1, "Tiny Tapeout pre-edge reset/deselect output mask");
      end
      if ({uo_out[7:3], uio_out[7:3], uio_oe[7:3]} !== 15'b0)
        $fatal(1, "Tiny Tapeout unused outputs are not tied low");
      if (miso !== 1'b0 && miso !== 1'b1)
        $fatal(1, "Unknown pre-edge buffered SRAM serial MISO");
      if ((raw_inputs[0] !== 1'b0 && raw_inputs[0] !== 1'b1) ||
          (raw_inputs[1] !== 1'b0 && raw_inputs[1] !== 1'b1))
        $fatal(1, "Unknown pre-edge buffered SRAM serial input pads");
      if ((output_enabled & peer_enabled) !== 8'h00)
        $fatal(1, "External peer drives a pre-edge buffered serial DUT-owned output pad");
      connected = 0;
      if (links[0]) connected = connected | 8'h05;
      if (links[1]) connected = connected | 8'h0a;
      if ((connected & ((output_levels & output_enabled) |
                        (peer_levels & peer_enabled))) !== 8'h00)
        $fatal(1, "Pre-edge buffered serial board links require open-drain low/release drivers");
      edge_miso = miso; edge_inputs = raw_inputs;
      clk = 1; #10; clk = 0;
      if ((^{ready, busy, levels, enabled}) === 1'bx)
        $fatal(1, "Unknown post-edge buffered SRAM serial public output");
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
        $fatal(1, "Unknown/contention on buffered SRAM serial resolved pads values=%h known=%h required=%h",
          wire_values, known, required);
      if ((output_enabled & peer_enabled) !== 8'h00)
        $fatal(1, "External peer drives a buffered serial DUT-owned output pad");
      connected = 0;
      if (links[0]) connected = connected | 8'h05;
      if (links[1]) connected = connected | 8'h0a;
      if ((connected & ((output_levels & output_enabled) |
                        (peer_levels & peer_enabled))) !== 8'h00)
        $fatal(1, "Buffered serial board links require open-drain low/release drivers");
      $display("SRAM_SERIAL %0d %0d %0d %0d %0d %0d %0d %0d",
        edge_miso, ready, busy, levels, enabled, wire_values, known, edge_inputs);
      $fflush();
      end
    end
  end
endmodule
