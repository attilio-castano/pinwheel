`timescale 1ns/1ps
// All loader handshakes before the edge and core/control state after it.
// Expected values come from the independent atomic machine, not SRAM RTL.
module sram_core_tb;
  reg clk=0, init, reset;
  reg [2:0] command;
  reg [63:0] data;
  reg [1:0] incoming;
  wire loader_active, loader_valid, loader_pending, loader_push, loader_commit, loader_start, loader_rejected;
  wire [8:0] loader_cursor;
  wire [2:0] mode, levels, enabled;
  wire [7:0] pc, remaining, wait_left, read_a, read_b;
  wire busy;
  wire sample0, sample1, sample2, sample3, sample4, sample5, sample6, sample7, sample8, sample9, sample10, sample11, sample12, sample13, sample14, sample15;
  wire [15:0] samples={sample15,sample14,sample13,sample12,sample11,sample10,sample9,sample8,sample7,sample6,sample5,sample4,sample3,sample2,sample1,sample0};
  pinwheel_sram_core dut(.*);
  reg e_push, e_commit, e_start, e_rejected, e_active, e_valid, e_pending;
  reg [8:0] e_cursor;
  reg [2:0] e_mode, e_levels, e_enabled;
  reg [7:0] e_pc, e_remaining, e_wait;
  reg [15:0] e_samples;
  integer fd, code, count=0;
  reg [4095:0] path;
  initial begin
    if(!$value$plusargs("vectors=%s",path)) $fatal(1,"Missing SRAM core vectors argument");
    fd=$fopen(path,"r");
    if(!fd) $fatal(1,"Missing SRAM core vectors");
    while(!$feof(fd)) begin
      clk=0;
      code=$fscanf(fd,"%d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d\n",
        init,reset,command,data,incoming,e_push,e_commit,e_start,e_rejected,
        e_active,e_valid,e_pending,e_cursor,e_mode,e_pc,e_remaining,e_wait,e_levels,e_enabled,e_samples);
      if(code!=20) $fatal(1,"Malformed SRAM core vector");
      #1;
      if({loader_push,loader_commit,loader_start,loader_rejected} !== {e_push,e_commit,e_start,e_rejected})
        $fatal(1,"SRAM core handshake edge %0d",count);
      clk=1; #1;
      if({loader_active,loader_valid,loader_pending,loader_cursor,mode,pc,remaining,wait_left,levels,enabled,samples} !==
         {e_active,e_valid,e_pending,e_cursor,e_mode,e_pc,e_remaining,e_wait,e_levels,e_enabled,e_samples} ||
         busy !== (e_mode>=1 && e_mode<=4) || read_a !== e_pc)
        $fatal(1,"SRAM core state edge %0d actual=%d,%d,%d,%d,%d,%d,%d expected=%d,%d,%d,%d,%d,%d,%d",
          count,mode,pc,remaining,wait_left,levels,enabled,samples,e_mode,e_pc,e_remaining,e_wait,e_levels,e_enabled,e_samples);
      count=count+1;
    end
    $display("Passed %0d independent SRAM core edges",count);
    $finish;
  end
endmodule
