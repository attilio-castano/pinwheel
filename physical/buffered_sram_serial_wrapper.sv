// The serial frontend owns command framing. The execution controller and both
// latency-one instruction macros retain their existing sampling clock.
module pinwheel_buffered_shared_branches_sram_serial (
  input clk, initialize, csn, sck, mosi,
  input [1:0] raw_inputs,
  output miso, ready, busy,
  output [2:0] levels, enabled
);
  wire core_initialize;
  wire [2:0] core_command;
  wire [5:0] core_address;
  wire [63:0] core_word;
  wire [55:0] core_branch;
  wire [23:0] core_control;
  wire [10:0] core_virtual_span;
  wire [6:0] core_count;
  wire [2:0] core_idle_levels, core_idle_enabled;
  wire [31:0] core_tx_data;
  wire [5:0] core_tx_length, core_rx_capacity;
  wire [15:0] core_expected_generation, core_expected_transfer;
  wire [4:0] core_read_index;
  wire [1:0] core_raw_inputs;
  wire status_valid, status_busy, status_retained, status_pending;
  wire status_rejected, status_read_valid, status_read_bit, status_exhausted;
  wire [1:0] status_mode, status_stage1, status_stage2;
  wire [7:0] status_pc, status_remaining, status_wait_left;
  wire [2:0] status_levels, status_enabled, status_env0, status_env1, status_phase;
  wire [5:0] status_tx_consumed, status_rx_length;
  wire [31:0] status_rx_data;
  wire [15:0] status_generation, status_transfer, status_scratch;
  wire [9:0] status_virtual_pc;
  wire [5:0] mem_addr0, mem_addr1;
  wire [63:0] mem_data, mem_q0, mem_q1;
  wire mem_write, mem_read;

  pinwheel_buffered_sram_serial_frontend frontend (.*);
  pinwheel_buffered_shared_branches_sram_controller controller (
    .clk(clk), .initialize(core_initialize), .command(core_command),
    .address(core_address), .word(core_word), .branch(core_branch),
    .control(core_control), .virtual_span(core_virtual_span), .count(core_count),
    .idle_levels(core_idle_levels), .idle_enabled(core_idle_enabled),
    .tx_data(core_tx_data), .tx_length(core_tx_length),
    .rx_capacity(core_rx_capacity),
    .expected_generation(core_expected_generation),
    .expected_transfer(core_expected_transfer), .read_index(core_read_index),
    .raw_inputs(core_raw_inputs), .mem_q0(mem_q0), .mem_q1(mem_q1),
    .valid(status_valid), .busy(status_busy), .retained(status_retained),
    .pending(status_pending), .rejected(status_rejected), .mode(status_mode),
    .pc(status_pc), .remaining(status_remaining), .levels(status_levels),
    .enabled(status_enabled), .tx_consumed(status_tx_consumed),
    .rx_length(status_rx_length), .rx_data(status_rx_data),
    .read_valid(status_read_valid), .read_bit(status_read_bit),
    .generation(status_generation), .transfer(status_transfer),
    .exhausted(status_exhausted), .stage1(status_stage1), .stage2(status_stage2),
    .virtual_pc(status_virtual_pc), .env0(status_env0), .env1(status_env1),
    .phase(status_phase), .wait_left(status_wait_left), .scratch(status_scratch),
    .mem_addr0(mem_addr0), .mem_addr1(mem_addr1), .mem_data(mem_data),
    .mem_write(mem_write), .mem_read(mem_read)
  );
  pinwheel_buffered_sram_memory memory (.*);
  assign busy = status_busy;
  assign levels = status_levels;
  assign enabled = status_enabled;
endmodule
