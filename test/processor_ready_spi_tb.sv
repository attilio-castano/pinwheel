`default_nettype none
module tb;
  reg clk = 0, reset = 1, loading = 1, valid = 0;
  reg [1:0] address = 0;
  reg [31:0] reply;
  wire [31:0] gpio, pc, instruction, write_data, trap_pc, trap_instruction;
  wire retire, writing, trapping;
  wire [4:0] rd;
  wire [7:0] uo, levels, enables;
  integer cycle = 0, edges = 0, transfers = 0, index = 0, mode = 0;
  wire idle_sck = mode == 2;
  reg selected = 0, previous_sck = 0;
  reg [31:0] transmitted = 0;
  wire raw = reply[31-index] ^ $test$plusargs("invert-peer");

  processor_loadable_system cpu(.clk(clk), .in_state_0(reset), .in_state_1({24'b0,uo}),
    .in_state_2(1'b0), .in_state_3(1'b0), .in_state_4(8'b0), .in_state_5(1'b0),
    .in_state_6(loading), .in_state_7(valid), .in_state_8(address), .in_state_9(32'b0),
    .state_11(retire), .state_12(pc), .state_13(instruction), .state_15(writing),
    .state_16(rd), .state_17(write_data), .state_18(trapping), .state_19(trap_pc),
    .state_21(trap_instruction), .state_34(gpio));

  tt_um_pinwheel_streaming_ready_d2 device(
    .clk(clk), .rst_n(!reset && !loading), .ena(1'b1), .uio_in(8'b0),
    .ui_in({gpio[5:3],1'b0,raw,gpio[2],gpio[1],!gpio[0]}),
    .uo_out(uo), .uio_out(levels), .uio_oe(enables));

  always #5 clk = !clk;
  initial begin
    if (!$value$plusargs("reply=%h", reply)) $fatal(1, "missing peer reply");
    if ($value$plusargs("mode=%d", mode) && mode != 0 && mode != 2) $fatal(1, "unsupported mode");
    repeat (2) @(negedge clk);
    reset = 0;
    valid = 1;
    for (integer j = 0; j < 4; j = j + 1) begin
      address = j[1:0];
      @(negedge clk);
    end
    valid = 0;
    loading = 0;
  end

  // Observe the public SPI drive after it has settled for the next sample.
  always @(negedge clk) if (!loading && enables[2:0] === 3'b111) begin
    if (!levels[2]) begin
      if (!selected) begin
        if (levels[1] !== idle_sck || transfers != 0) $fatal(1, "bad select");
        selected = 1;
        previous_sck = idle_sck;
        transfers = transfers + 1;
      end
      if (levels[1] != idle_sck && previous_sck == idle_sck) begin
        if (edges >= 32) $fatal(1, "extra clock");
        transmitted = {transmitted[30:0],levels[0]};
        edges = edges + 1;
      end
      if (levels[1] == idle_sck && previous_sck != idle_sck && index < 31) index = index + 1;
      previous_sck = levels[1];
    end else if (selected) begin
      if (levels[1] !== idle_sck || edges != 32) $fatal(1, "incomplete transfer");
      selected = 0;
    end
  end

  // Retirement ports are sampled before the active edge, like the core model.
  always @(posedge clk) begin
    cycle = cycle + 1;
    if (!loading && !reset) begin
      if ((^uo) === 1'bx || (^gpio) === 1'bx) $fatal(1, "unknown GPIO");
      $display("EDGE %08x %02x",gpio,uo);
    end
    if (retire && writing && pc == 100 && rd == 12)
      $display("NIBBLE %x",write_data[3:0]);
    if (retire && writing && rd == 25) $display("RESULT %08x",write_data);
    if (trapping) begin
      if (trap_pc !== 152 || trap_instruction !== 32'h00100073)
        $fatal(1, "unexpected trap at %x instruction %x",trap_pc,trap_instruction);
      if (transfers != 1 || selected || edges != 32 || levels[2:1] !== {1'b1,idle_sck})
        $fatal(1, "bad terminal pins");
      $display("DONE %0d %08x",cycle,transmitted);
      $finish;
    end
    if (cycle > 120000) $fatal(1, "firmware timeout at pc %x, gpio %x",pc,gpio);
  end
endmodule
`default_nettype wire
