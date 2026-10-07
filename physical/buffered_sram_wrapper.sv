// Public parallel command/observation ABI shared with the flip-flop target.
// Q is already registered inside each macro; the wrapper adds no sampling edge.
module pinwheel_buffered_shared_branches_sram (
  input clk, initialize,
  input [2:0] command,
  input [5:0] address,
  input [63:0] word,
  input [55:0] branch,
  input [23:0] control,
  input [10:0] virtual_span,
  input [6:0] count,
  input [2:0] idle_levels, idle_enabled,
  input [31:0] tx_data,
  input [5:0] tx_length, rx_capacity,
  input [15:0] expected_generation, expected_transfer,
  input [4:0] read_index,
  input [1:0] raw_inputs,
  output valid, busy, retained, pending, rejected,
  output [1:0] mode,
  output [7:0] pc, remaining,
  output [2:0] levels, enabled,
  output [5:0] tx_consumed, rx_length,
  output [31:0] rx_data,
  output read_valid, read_bit,
  output [15:0] generation, transfer,
  output exhausted,
  output [1:0] stage1, stage2,
  output [9:0] virtual_pc,
  output [2:0] env0, env1, phase,
  output [7:0] wait_left,
  output [15:0] scratch
);
  wire [5:0] mem_addr0, mem_addr1;
  wire [63:0] mem_data, mem_q0, mem_q1;
  wire mem_write, mem_read;
  pinwheel_buffered_shared_branches_sram_controller controller (.*);
  pinwheel_buffered_sram_memory memory (.*);
endmodule
