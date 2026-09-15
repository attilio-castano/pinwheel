module execution_store_tb;
  reg clk = 0;
  reg write, busy, index_bank;
  reg [7:0] address, read_a, read_b;
  reg [63:0] data;
  wire a_valid, b_valid;
  wire [2:0] a_kind, a_levels, a_enabled, b_kind, b_levels, b_enabled;
  wire [7:0] a_duration, a_budget, a_yes, a_no, b_duration, b_budget, b_yes, b_no;
  wire [3:0] a_check, a_sample, b_check, b_sample;
  wire [5:0] a_entry, a_terminal, b_entry, b_terminal;
  wire [1:0] a_finish, b_finish;
  wire [63:0] a_fields = {1'b0, a_no, a_yes, a_sample, a_finish, a_terminal, a_entry,
                          a_check, a_budget, a_duration, a_enabled, a_levels, a_kind};
  wire [63:0] b_fields = {1'b0, b_no, b_yes, b_sample, b_finish, b_terminal, b_entry,
                          b_check, b_budget, b_duration, b_enabled, b_levels, b_kind};
`ifdef INDEXED
  pinwheel_e64_indexed dut(.*);
`else
  pinwheel_e64_direct dut(.*);
`endif
  integer file, trace, status, edge_count = 0, checked = 0;
  reg check_outputs, expected_a_valid, expected_b_valid;
  reg [63:0] expected_a_fields, expected_b_fields;
  string trace_path;
  initial begin
`ifdef INDEXED
    file = $fopen("build/execution/indexed-vectors.txt", "r");
`else
    file = $fopen("build/execution/direct-vectors.txt", "r");
`endif
    if (!file) $fatal(1, "missing store vectors");
    if (!$value$plusargs("trace=%s", trace_path)) $fatal(1, "missing trace path");
    trace = $fopen(trace_path, "w");
    if (!trace) $fatal(1, "cannot open trace");
    $fdisplay(trace, "edge,a_valid,a_word,b_valid,b_word");
    while (!$feof(file)) begin
      clk = 0;
      status = $fscanf(file, "%d %d %d %d %d %d %d %d %d %d %d %d\n",
        write, busy, index_bank, address, data, read_a, read_b, check_outputs,
        expected_a_valid, expected_a_fields, expected_b_valid, expected_b_fields);
      if (status != 12) $fatal(1, "malformed store vector");
      #1; clk = 1; #1;
      if (check_outputs) begin
        if (a_valid !== expected_a_valid || a_fields !== expected_a_fields ||
            b_valid !== expected_b_valid || b_fields !== expected_b_fields)
          $fatal(1, "STORE edge %0d write=%0d busy=%0d bank=%0d addr=%0d", edge_count, write, busy, index_bank, address);
        $fdisplay(trace, "%0d,%0d,%0d,%0d,%0d", edge_count, a_valid, a_fields, b_valid, b_fields);
        checked = checked + 1;
      end
      edge_count = edge_count + 1;
    end
    $display("Passed %0d store edges, %0d checked read pairs", edge_count, checked);
    $fclose(trace);
    $finish;
  end
endmodule
