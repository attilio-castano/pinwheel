// Independent replay of the public memory request/response pins against the
// pinned IHP functional model. This fixture has no controller or DUT internals.
`timescale 1ns/10ps
module buffered_sram_memory_tb;
  reg clk = 0;
  reg [5:0] mem_addr0 = 0, mem_addr1 = 0;
  reg [63:0] mem_data = 0;
  reg mem_write = 0, mem_read = 0;
  wire [63:0] mem_q0, mem_q1;
  reg [63:0] expected [0:63];
  reg [63:0] held0, held1;
  integer k, edges = 0;
  pinwheel_buffered_sram_memory dut (.*);

  function [63:0] pattern(input [5:0] address);
    pattern = {8'h81, address, 1'b1, 17'h15555, address, 26'h2aaaaaa};
  endfunction

  task tick;
    begin
      #4; clk = 1; #1;
      edges = edges + 1;
      clk = 0; #1;
    end
  endtask

  task check_read;
    begin
      if (mem_q0 !== expected[mem_addr0] || mem_q1 !== expected[mem_addr1])
        $fatal(1, "Buffered SRAM independent read mismatch at edge %0d", edges);
    end
  endtask

  task check_hold;
    begin
      if (mem_q0 !== held0 || mem_q1 !== held1)
        $fatal(1, "Buffered SRAM response hold mismatch at edge %0d", edges);
    end
  endtask

  initial begin
    #1;
    if (!$isunknown(mem_q0) || !$isunknown(mem_q1))
      $fatal(1, "Buffered SRAM fixture assumed initialized power-up Q");
    // Reading an unwritten cell supplies no promised value.
    mem_read = 1; mem_addr0 = 17; mem_addr1 = 43; tick;
    if (!$isunknown(mem_q0) || !$isunknown(mem_q1))
      $fatal(1, "Buffered SRAM fixture assumed initialized power-up contents");
    mem_read = 0; mem_write = 1;
    for (k = 0; k < 64; k = k + 1) begin
      mem_addr0 = k; mem_addr1 = k;
      mem_data = pattern(k); expected[k] = mem_data;
      held0 = mem_q0; held1 = mem_q1;
      tick; check_hold;
    end
    mem_write = 0; mem_read = 1;
    for (k = 0; k < 128; k = k + 1) begin
      held0 = mem_q0; held1 = mem_q1;
      mem_addr0 = k; mem_addr1 = k * 7 + 13;
      // Address changes cannot affect the response already present before edge.
      #1; check_hold;
      tick; check_read;
    end
    // Both copies receive a replacement write; writing holds their distinct Q.
    mem_read = 0; mem_write = 1;
    held0 = mem_q0; held1 = mem_q1;
    mem_addr0 = 7; mem_addr1 = 7; mem_data = 64'hdca5f03e9768b214;
    expected[7] = mem_data; tick; check_hold;
    mem_write = 0; mem_read = 1;
    tick; check_read;
    // Idle requests hold Q regardless of new addresses and data.
    mem_read = 0;
    held0 = mem_q0; held1 = mem_q1;
    mem_addr0 = 31; mem_addr1 = 59; mem_data = 0;
    tick; check_hold;
    mem_read = 1; tick; check_read;
    $display("Buffered SRAM memory passed: %0d edges, 128 independent read pairs", edges);
    $finish;
  end
endmodule
