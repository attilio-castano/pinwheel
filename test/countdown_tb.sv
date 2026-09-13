`timescale 1ns/1ps
module countdown_tb;
  reg clk = 0;
  reg reset = 1;
  reg load = 0;
  reg [7:0] duration = 0;
  wire [7:0] remaining;
  wire active, boundary;
  pinwheel_countdown dut(.*);

  integer cycle = 0, deadline = -1, fd, d, j, n;
  integer mixed [0:3];
  reg expected_boundary, expected_active;
  integer expected_remaining;
  string trace_path;

  // Independent integer deadline model. Check boundary before the edge, registers after it.
  task edge_check(input bit rst, input bit ld, input integer duration_minus_one);
    begin
      reset = rst;
      load = ld;
      duration = duration_minus_one;
      #5;
      expected_boundary = !rst && deadline == cycle;
      if (boundary !== expected_boundary)
        $fatal(1, "BOUNDARY edge %0d: got %b expected %b", cycle, boundary, expected_boundary);
      if (rst) deadline = -1;
      else if (ld) deadline = cycle + duration + 1;
      else if (expected_boundary) deadline = -1;
      expected_active = deadline >= 0;
      expected_remaining = expected_active ? deadline - cycle - 1 : 0;
      clk = 1;
      #1;
      if (active !== expected_active || remaining !== expected_remaining[7:0])
        $fatal(1, "STATE edge %0d: got %b/%0d expected %b/%0d",
          cycle, active, remaining, expected_active, expected_remaining);
      $fwrite(fd, "%0d,%0d,%0d,%0d,%0d,%0d,%0d\n", cycle, rst, ld, duration,
        expected_boundary, remaining, active);
      clk = 0;
      #4;
      cycle = cycle + 1;
    end
  endtask

  initial begin
    if (!$value$plusargs("trace=%s", trace_path)) trace_path = "build/hardware/countdown-rtl.csv";
    fd = $fopen(trace_path, "w");
    if (!fd) $fatal(1, "Cannot open trace output");
    $fwrite(fd, "cycle,reset,load,duration_minus_one,boundary_at_edge,remaining,active\n");
    edge_check(1, 1, 255);
    edge_check(0, 0, 0);
    edge_check(0, 0, 0);
    for (d = 1; d <= 256; d = d + 1) begin
      edge_check(0, 1, d - 1);
      for (j = 0; j < d + 2; j = j + 1) edge_check(0, 0, 0);
    end
    mixed[0] = 1; mixed[1] = 4; mixed[2] = 256; mixed[3] = 1;
    for (n = 0; n < 4; n = n + 1) begin
      edge_check(0, 1, mixed[n] - 1);
      for (j = 0; j < mixed[n] - 1; j = j + 1) edge_check(0, 0, 0);
    end
    edge_check(0, 0, 0);
    for (n = 0; n < 4096; n = n + 1)
      edge_check(n % 37 == 0, n % 11 == 0 || n % 13 == 0, (73 * n + 19) % 256);
    $fclose(fd);
    $display("PASS: %0d RTL edges checked against independent deadlines", cycle);
    $finish;
  end
endmodule
