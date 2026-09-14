module execution_decoder_tb;
  reg [63:0] word;
  wire valid;
  wire [2:0] kind, levels, enabled;
  wire [7:0] duration, budget, yes, no;
  wire [3:0] check, sample;
  wire [5:0] entry, terminal;
  wire [1:0] finish;
  wire [63:0] fields = {1'b0, no, yes, sample, finish, terminal, entry,
                        check, budget, duration, enabled, levels, kind};
  pinwheel_e64_decoder dut(.*);
  integer file, status, count = 0;
  reg expected_valid;
  reg [63:0] expected_fields;
  initial begin
    file = $fopen("build/execution/decoder-vectors.txt", "r");
    if (!file) $fatal(1, "missing decoder vectors");
    while (!$feof(file)) begin
      status = $fscanf(file, "%d %d %d\n", word, expected_valid, expected_fields);
      if (status != 3) $fatal(1, "malformed decoder vector");
      #1;
      if (valid !== expected_valid || fields !== expected_fields)
        $fatal(1, "DECODE vector %0d word %h", count, word);
      count = count + 1;
    end
    $display("Passed %0d raw E64 decoder vectors", count);
    $finish;
  end
endmodule
