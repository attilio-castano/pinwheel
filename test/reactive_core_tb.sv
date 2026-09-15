module reactive_core_tb;
  reg clk = 0;
  reg reset, start, write;
  reg [1:0] incoming, bank;
  reg [7:0] address;
  reg [63:0] data;
  wire [2:0] mode, levels, enabled;
  wire [7:0] pc, remaining, wait_left, read_a, read_b;
  wire busy;
  wire sample0, sample1, sample2, sample3, sample4, sample5, sample6, sample7, sample8, sample9, sample10, sample11, sample12, sample13, sample14, sample15;
  wire [15:0] samples = {sample15, sample14, sample13, sample12, sample11, sample10, sample9, sample8, sample7, sample6, sample5, sample4, sample3, sample2, sample1, sample0};
`ifdef INDEXED
  pinwheel_reactive_indexed dut(.*);
`else
  pinwheel_reactive_direct dut(.*);
`endif
  integer file, status, count = 0, checked = 0;
  reg check_outputs;
  reg [2:0] e_mode, e_levels, e_enabled;
  reg [7:0] e_pc, e_remaining, e_wait;
  reg [15:0] e_samples;
  initial begin
`ifdef INDEXED
    file = $fopen("build/reactive-core/indexed-vectors.txt", "r");
`else
    file = $fopen("build/reactive-core/direct-vectors.txt", "r");
`endif
    if (!file) $fatal(1, "missing vectors");
    while (!$feof(file)) begin
      clk = 0;
      status = $fscanf(file, "%d %d %d %d %d %d %d %d %d %d %d %d %d %d %d\n",
        reset, start, incoming, write, bank, address, data, check_outputs,
        e_mode, e_pc, e_remaining, e_wait, e_levels, e_enabled, e_samples);
      if (status != 15) $fatal(1, "malformed vector");
      #1; clk = 1; #1;
      if (check_outputs) begin
        if (mode !== e_mode || pc !== e_pc || remaining !== e_remaining || wait_left !== e_wait ||
            levels !== e_levels || enabled !== e_enabled || samples !== e_samples ||
            busy !== (e_mode >= 1 && e_mode <= 4) || read_a !== e_pc)
          $fatal(1, "CORE edge %0d actual=%0d,%0d,%0d,%0d,%0d,%0d,%0d expected=%0d,%0d,%0d,%0d,%0d,%0d,%0d",
            count, mode, pc, remaining, wait_left, levels, enabled, samples,
            e_mode, e_pc, e_remaining, e_wait, e_levels, e_enabled, e_samples);
        checked = checked+1;
      end
      count = count+1;
    end
    $display("Passed %0d integrated core edges, %0d checked states", count, checked);
    $finish;
  end
endmodule
