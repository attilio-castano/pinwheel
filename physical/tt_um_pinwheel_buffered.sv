// Tiny Tapeout boundary for the accepted buffered SRAM serial engine.
//
// ui_in[0:2] : host CSn, SCK, MOSI (sampled by the free-running clk)
// ui_in[3:4] : raw protocol input 0, 1
// uo_out[0:2]: host MISO, READY, BUSY
// uio[0:2]  : protocol output 0, 1, 2 with independently controlled enables
// Remaining outputs and output enables are zero; remaining inputs are unused.
//
// rst_n and ena immediately mask the public outputs. The engine's initialize
// is synchronous: hold rst_n low for at least one rising clk after selecting,
// then upload a fresh image. A clock edge while deselected also invalidates
// the engine. SRAM arrays have no reset and their contents are never presumed
// valid across deselection/power loss. A stopped clock does not invalidate
// state by itself, so selection must always be followed by physical reset.
// The wrapper adds no clock domain: host CSn/SCK/MOSI must meet the existing
// sampled serial contract relative to clk. It does not qualify asynchronous
// host timing or physical pad behavior.
`default_nettype none
module tt_um_pinwheel_buffered (
  input  wire [7:0] ui_in,
  output wire [7:0] uo_out,
  input  wire [7:0] uio_in,
  output wire [7:0] uio_out,
  output wire [7:0] uio_oe,
  input  wire ena,
  input  wire clk,
  input  wire rst_n
);
  wire active = ena && rst_n;
  wire initialize = !active;
  wire miso, ready, busy;
  wire [2:0] levels, enabled;

  pinwheel_buffered_shared_branches_sram_serial engine (
    .clk(clk), .initialize(initialize),
    .csn(ui_in[0]), .sck(ui_in[1]), .mosi(ui_in[2]),
    .raw_inputs(ui_in[4:3]),
    .miso(miso), .ready(ready), .busy(busy),
    .levels(levels), .enabled(enabled)
  );

  assign uo_out = active ? {5'b0, busy, ready, miso} : 8'b0;
  assign uio_out = active ? {5'b0, levels} : 8'b0;
  assign uio_oe = active ? {5'b0, enabled} : 8'b0;

  // Preserve the standard Tiny Tapeout input boundary without adding logic.
  wire _unused = &{uio_in, ui_in[7:5], 1'b0};
endmodule
`default_nettype wire
