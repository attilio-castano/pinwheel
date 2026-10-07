// Latency-one instruction storage for the shared-branch buffered target.
// The single program image occupies all 64 rows in each copy. Accepted writes
// reach both copies; their read addresses are independent. Neither SRAM has a
// reset. Electrical qualification of these exact macros remains separate.
module pinwheel_buffered_sram_memory (
  input clk,
  input [5:0] mem_addr0, mem_addr1,
  input [63:0] mem_data,
  input mem_write, mem_read,
  output [63:0] mem_q0, mem_q1
);
  RM_IHPSG13_1P_64x64_c2_bm_bist storage0 (
    .A_CLK(clk), .A_MEN(1'b1), .A_DLY(1'b1),
    .A_WEN(mem_write), .A_REN(mem_read), .A_ADDR(mem_addr0),
    .A_DIN(mem_data), .A_DOUT(mem_q0), .A_BM(64'hffffffffffffffff),
    .A_BIST_CLK(1'b0), .A_BIST_EN(1'b0), .A_BIST_MEN(1'b0),
    .A_BIST_WEN(1'b0), .A_BIST_REN(1'b0), .A_BIST_ADDR(6'd0),
    .A_BIST_DIN(64'd0), .A_BIST_BM(64'd0)
  );
  RM_IHPSG13_1P_64x64_c2_bm_bist storage1 (
    .A_CLK(clk), .A_MEN(1'b1), .A_DLY(1'b1),
    .A_WEN(mem_write), .A_REN(mem_read), .A_ADDR(mem_addr1),
    .A_DIN(mem_data), .A_DOUT(mem_q1), .A_BM(64'hffffffffffffffff),
    .A_BIST_CLK(1'b0), .A_BIST_EN(1'b0), .A_BIST_MEN(1'b0),
    .A_BIST_WEN(1'b0), .A_BIST_REN(1'b0), .A_BIST_ADDR(6'd0),
    .A_BIST_DIN(64'd0), .A_BIST_BM(64'd0)
  );
endmodule
