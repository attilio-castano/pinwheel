`timescale 1ns/1ps
// Same independent before/after pin checks as chip_tb, now at the 20 ns SDC
// clock. Dump only one settled workload window per invocation.
module power_tb;
  reg clk=0, rst_n, ena=1;
  reg [7:0] ui_in,uio_in;
  wire [7:0] uo_out,uio_out,uio_oe;
  tt_um_pinwheel dut(.*);
  reg [7:0] before_uo,before_out,before_oe,after_uo,after_out,after_oe;
  integer fd,code,check,count=0,first_edge,last_edge;
  reg [4095:0] path,wave;
  initial begin
    if(!$value$plusargs("vectors=%s",path) || !$value$plusargs("vcd=%s",wave)
       || !$value$plusargs("first=%d",first_edge) || !$value$plusargs("last=%d",last_edge))
      $fatal(1,"Missing power trace arguments");
    fd=$fopen(path,"r");
    if(!fd || first_edge<1 || last_edge<=first_edge) $fatal(1,"Invalid trace window");
    while(count<last_edge) begin
      // Begin one picosecond before the first falling edge. The converter
      // rebases this known start and removes that one-picosecond preamble.
      if(count==first_edge) begin
        $dumpfile(wave); $dumpvars(1,dut);
      end
      #0.001; clk=0;
      code=$fscanf(fd,"%d %d %d %d %d %d %d %d %d %d\n",rst_n,ui_in,uio_in,check,
        before_uo,before_out,before_oe,after_uo,after_out,after_oe);
      if(code!=10) $fatal(1,"Malformed chip vector");
      #9.999;
      if(check && {uo_out,uio_out,uio_oe} !== {before_uo,before_out,before_oe})
        $fatal(1,"CHIP before edge %0d actual=%h expected=%h",count,{uo_out,uio_out,uio_oe},{before_uo,before_out,before_oe});
      clk=1; #10;
      if(check && {uo_out,uio_out,uio_oe} !== {after_uo,after_out,after_oe})
        $fatal(1,"CHIP after edge %0d actual=%h expected=%h",count,{uo_out,uio_out,uio_oe},{after_uo,after_out,after_oe});
      count=count+1;
    end
    $display("Passed %0d independent whole-chip edges; trace [%0d,%0d) at 20 ns",count,first_edge,last_edge);
    $finish;
  end
endmodule
