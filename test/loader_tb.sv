module loader_tb;
  reg clk = 0;
  reg init, reset;
  reg [2:0] command;
  reg [63:0] data;
  reg [1:0] incoming;
  wire loader_active, loader_valid, loader_pending, loader_push, loader_commit, loader_start, loader_rejected;
  wire [8:0] loader_cursor;
  wire [2:0] mode, levels, enabled;
  wire [7:0] pc, remaining, wait_left, read_a, read_b;
  wire busy;
  wire sample0, sample1, sample2, sample3, sample4, sample5, sample6, sample7, sample8, sample9, sample10, sample11, sample12, sample13, sample14, sample15;
  wire [15:0] samples = {sample15, sample14, sample13, sample12, sample11, sample10, sample9, sample8, sample7, sample6, sample5, sample4, sample3, sample2, sample1, sample0};
  pinwheel_atomic_indexed dut(.*);
  wire [63:0] observed [0:643];
`include "build/loader/memory-observe.svh"
  reg [63:0] expected [0:643];
  reg known [0:643];
  integer file, status, count = 0, storage_checks = 0, k, destination;
  reg e_push, e_commit, e_start, e_rejected, e_active, e_valid, e_pending;
  reg [8:0] e_cursor;
  reg [2:0] e_mode, e_levels, e_enabled;
  reg [7:0] e_pc, e_remaining, e_wait;
  reg [15:0] e_samples;
  initial begin
    for (k = 0; k < 644; k = k+1) known[k] = 0;
    file = $fopen("build/loader/vectors.txt", "r");
    if (!file) $fatal(1, "missing vectors");
    while (!$feof(file)) begin
      clk = 0;
      status = $fscanf(file, "%d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d\n",
        init, reset, command, data, incoming, e_push, e_commit, e_start, e_rejected,
        e_active, e_valid, e_pending, e_cursor,
        e_mode, e_pc, e_remaining, e_wait, e_levels, e_enabled, e_samples);
      if (status != 20) $fatal(1, "malformed vector");
      #1;
      if ({loader_push, loader_commit, loader_start, loader_rejected} !== {e_push, e_commit, e_start, e_rejected})
        $fatal(1, "LOADER edge %0d handshake actual=%b expected=%b", count,
          {loader_push, loader_commit, loader_start, loader_rejected}, {e_push, e_commit, e_start, e_rejected});
      if (e_push) begin
        destination = (loader_active ? 0 : 322) + loader_cursor;
        expected[destination] = data;
        known[destination] = 1;
      end
      clk = 1; #1;
      if (mode !== e_mode || pc !== e_pc || remaining !== e_remaining || wait_left !== e_wait ||
          levels !== e_levels || enabled !== e_enabled || samples !== e_samples ||
          busy !== (e_mode >= 1 && e_mode <= 4) || read_a !== e_pc ||
          loader_active !== e_active || loader_valid !== e_valid || loader_pending !== e_pending || loader_cursor !== e_cursor)
        $fatal(1, "LOADER edge %0d state actual control=%d,%d,%d,%d core=%0d,%0d,%0d,%0d,%0d,%0d,%0d expected control=%d,%d,%d,%d core=%0d,%0d,%0d,%0d,%0d,%0d,%0d",
          count, loader_active, loader_valid, loader_pending, loader_cursor, mode, pc, remaining, wait_left, levels, enabled, samples,
          e_active, e_valid, e_pending, e_cursor, e_mode, e_pc, e_remaining, e_wait, e_levels, e_enabled, e_samples);
      for (k = 0; k < 644; k = k+1) if (known[k]) begin
        if (observed[k] !== expected[k])
          $fatal(1, "LOADER edge %0d storage[%0d] actual=%h expected=%h", count, k, observed[k], expected[k]);
        storage_checks = storage_checks+1;
      end
      count = count+1;
    end
    $display("Passed %0d atomic loader edges and %0d physical storage observations", count, storage_checks);
    $finish;
  end
endmodule
