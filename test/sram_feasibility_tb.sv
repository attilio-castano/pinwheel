// Feasibility harness, not an emitted or proved Pinwheel implementation.
// Both 256-word atomic images occupy each 512x64 macro. Writes are broadcast.
`timescale 1ns/10ps
module direct_store (
    input clk, write_dictionary, write_index, bank,
    input [7:0] cursor, index,
    input [63:0] data,
    input read_enable,
    input [7:0] address0, address1,
    output [63:0] q0, q1
);
  // A single staging dictionary suffices: active records are already expanded.
  reg [63:0] scratch [0:31];
  always @(posedge clk)
    if (write_dictionary && cursor < 32) scratch[cursor[4:0]] <= data;
  wire [63:0] expanded = scratch[index[4:0]];
  wire [8:0] a0 = {bank, write_index ? cursor : address0};
  wire [8:0] a1 = {bank, write_index ? cursor : address1};
  RM_IHPSG13_1P_512x64_c2_bm_bist m0 (
    .A_CLK(clk), .A_MEN(write_index | read_enable), .A_WEN(write_index),
    .A_REN(read_enable & ~write_index), .A_ADDR(a0), .A_DIN(expanded),
    .A_BM(64'hffffffffffffffff), .A_DLY(1'b1), .A_DOUT(q0),
    .A_BIST_CLK(1'b0), .A_BIST_EN(1'b0), .A_BIST_MEN(1'b0),
    .A_BIST_WEN(1'b0), .A_BIST_REN(1'b0), .A_BIST_ADDR(9'b0),
    .A_BIST_DIN(64'b0), .A_BIST_BM(64'b0));
  RM_IHPSG13_1P_512x64_c2_bm_bist m1 (
    .A_CLK(clk), .A_MEN(write_index | read_enable), .A_WEN(write_index),
    .A_REN(read_enable & ~write_index), .A_ADDR(a1), .A_DIN(expanded),
    .A_BM(64'hffffffffffffffff), .A_DLY(1'b1), .A_DOUT(q1),
    .A_BIST_CLK(1'b0), .A_BIST_EN(1'b0), .A_BIST_MEN(1'b0),
    .A_BIST_WEN(1'b0), .A_BIST_REN(1'b0), .A_BIST_ADDR(9'b0),
    .A_BIST_DIN(64'b0), .A_BIST_BM(64'b0));
endmodule

module tb;
  reg clk=0, wd=0, wi=0, bank=0, ren=0;
  reg [7:0] cursor=0, index=0, a0=0, a1=0;
  reg [63:0] data=0;
  wire [63:0] q0,q1;
  direct_store dut(clk,wd,wi,bank,cursor,index,data,ren,a0,a1,q0,q1);
  reg commit=0, last_commit=0;
  reg [63:0] saved_start;
  wire [63:0] start_word=last_commit ? q0 : saved_start;
  // A macro's new Q cannot be captured by a second register on the same edge.
  // Bypass it for an immediate start, then retain it on the following edge.
  always @(posedge clk) begin
    last_commit <= commit;
    if(last_commit) saved_start <= q0;
  end
  reg [63:0] expected [0:511];
  reg [63:0] words [0:31];
  reg [63:0] held0,held1,current,successor;
  integer n,k,pc,target,version,edges=0,branches=0;

  task tick;
    begin #4; clk=1; #1; edges=edges+1; clk=0; #1; end
  endtask
  task check_read;
    begin
      if(q0 !== expected[{bank,a0}] || q1 !== expected[{bank,a1}])
        $fatal(1,"SRAM lookup mismatch at edge %0d",edges);
    end
  endtask
  // Valid E64 checked records, duration zero, terminal capture of pin 0 into
  // sample 0, branching to two different addresses. Every execution edge can
  // therefore need either successor, including the first edge after entry.
  task upload(input integer v);
    begin
      ren=0; wd=1;
      for(n=0;n<64;n=n+1) begin
        cursor=n;
        data=64'd2 | (64'(v & 7)<<3) | (64'd1<<35) | (64'd2<<41)
             | (64'((n+1)%32)<<47) | (64'((n+7)%32)<<55);
        if(n>=32) data=64'd4; // Valid padding required by the small-image loader.
        if(n<32) words[n]=data;
        tick;
      end
      wd=0; wi=1;
      for(n=0;n<256;n=n+1) begin
        cursor=n; index=n%32; expected[{bank,cursor}]=words[index]; tick;
      end
      wi=0;
      // Idle and last metadata remain ordinary control registers.
      tick; tick;
    end
  endtask
  task execute(input integer count, input integer fresh_commit);
    begin
      // Commit edge reads word 0 of the newly selected bank. Its registered
      // response is the immediate start source, not an extra DFF sampled here.
      ren=1;
      if(fresh_commit) begin
        a0=0; a1=0; commit=1; tick; check_read; commit=0;
      end
      if(start_word !== expected[{bank,8'b0}]) $fatal(1,"SRAM start ownership mismatch");
      current=start_word; pc=0;
      // Start enters word 0 and fetches its two successors on that same edge.
      a0=current[62:55]; a1=current[54:47]; tick; check_read;
      for(k=0;k<count;k=k+1) begin
        target=(k%3==0) ? current[54:47] : current[62:55];
        successor=(k%3==0) ? q1 : q0;
        if(successor !== expected[{bank,8'(target)}])
          $fatal(1,"SRAM branch unavailable at edge %0d",edges);
        // Addresses depend on the response already present before this edge.
        a0=successor[62:55]; a1=successor[54:47];
        tick; check_read;
        current=successor; pc=target; branches=branches+1;
      end
      // Disabled reads retain both responses; no initialized SRAM is assumed.
      held0=q0; held1=q1; ren=0; tick;
      if(q0 !== held0 || q1 !== held1) $fatal(1,"SRAM disabled-read hold mismatch");
      if(start_word !== expected[{bank,8'b0}]) $fatal(1,"SRAM retained start mismatch");
    end
  endtask
  initial begin
    bank=1; upload(1); execute(300,1);
    // A partial inactive replacement (including a write) does not affect the
    // active image. Abort/reset invalidate controller state, not SRAM bits.
    bank=0; wd=1; cursor=0; data=64'h1234; tick; wd=0;
    wi=1; cursor=0; index=0; tick; wi=0;
    // Restart directly from the retained start word: no extra commit/read edge.
    bank=1; execute(100,0);
    // Full back-to-back uploads replace both banks, with no hidden expansion
    // cycle between the last index, metadata, commit and immediate start.
    bank=0; upload(2); execute(300,1);
    bank=1; upload(3); execute(300,1);
    $display("SRAM feasibility passed: %0d edges, %0d consecutive branch dispatches",edges,branches);
    $finish;
  end
endmodule
