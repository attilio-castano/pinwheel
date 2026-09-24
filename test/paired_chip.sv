// One physical array; each 256-row half is an atomic program image.
module pinwheel_paired_memory (
  input clk, input [8:0] mem_addr0,
  input [63:0] mem_data, input mem_write, mem_read, output [63:0] mem_q0
);
  RM_IHPSG13_1P_512x64_c2_bm_bist storage (
    .A_CLK(clk), .A_MEN(1'b1), .A_DLY(1'b1),
    .A_WEN(mem_write), .A_REN(mem_read), .A_ADDR(mem_addr0),
    .A_DIN(mem_data), .A_DOUT(mem_q0), .A_BM(64'hffffffffffffffff),
    .A_BIST_CLK(1'b0), .A_BIST_EN(1'b0), .A_BIST_MEN(1'b0),
    .A_BIST_WEN(1'b0), .A_BIST_REN(1'b0), .A_BIST_ADDR(9'd0),
    .A_BIST_DIN(64'd0), .A_BIST_BM(64'd0)
  );
endmodule

module tt_um_pinwheel (
  input clk, input [7:0] ui_in, uio_in, input ena, rst_n,
  output [7:0] uo_out, uio_out, uio_oe
);
  wire [8:0] mem_addr0;
  wire [63:0] mem_data, mem_q0;
  wire mem_write, mem_read;
  pinwheel_paired_controller controller (.*);
  pinwheel_paired_memory memory (.*);
endmodule

module pinwheel_paired_core (
  input clk, init, reset, input [2:0] command,
  input [63:0] data, input [1:0] incoming,
  output loader_active, loader_valid, loader_pending, output [8:0] loader_cursor,
  output loader_push, loader_commit, loader_start, loader_rejected,
  output [2:0] mode, levels, enabled,
  output [7:0] pc, remaining, wait_left, read_a, read_b,
  output busy,
  output sample0, sample1, sample2, sample3, sample4, sample5, sample6, sample7,
    sample8, sample9, sample10, sample11, sample12, sample13, sample14, sample15
);
  wire [8:0] mem_addr0;
  wire [63:0] mem_data, mem_q0;
  wire mem_write, mem_read;
  pinwheel_paired_core_controller controller (.*);
  pinwheel_paired_memory memory (.*);
endmodule
