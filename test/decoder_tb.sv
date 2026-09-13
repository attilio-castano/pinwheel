`timescale 1ns/1ps
module decoder_tb;
  reg [15:0] word;
  wire [1:0] kind;
  wire [2:0] levels, slot;
  wire [7:0] duration;
  wire capture;
  integer n, expected_kind, valid_words = 0;
  pinwheel_decoder dut(.*);
  initial begin
    for (n = 0; n < 65536; n = n + 1) begin
      word = n;
      expected_kind = n == 32768 ? 2 : n >= 32768 || (n % 16 > 0 && n % 16 < 8) ? 3 : 1;
      #1;
      if (kind !== expected_kind[1:0] || levels !== ((n / 4096) % 8) ||
          duration !== ((n / 16) % 256) || capture !== ((n / 8) % 2) || slot !== (n % 8))
        $fatal(1, "DECODE word %0d", n);
      if (kind != 3) valid_words = valid_words + 1;
    end
    if (valid_words != 18433) $fatal(1, "Valid word count");
    $display("PASS decoder 65536 words, %0d valid", valid_words);
    $finish;
  end
endmodule
