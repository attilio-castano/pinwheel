`timescale 1ns/1ps
module chip_tb;
  reg clk=0, rst_n, ena=1;
  reg [7:0] ui_in,uio_in;
  wire [7:0] uo_out,uio_out,uio_oe;
  tt_um_pinwheel dut(.*);
  reg [7:0] before_uo,before_out,before_oe,after_uo,after_out,after_oe;
  integer fd,code,check,count=0;
  reg [4095:0] path;
  initial begin
    if(!$value$plusargs("vectors=%s",path)) $fatal(1,"Missing chip vectors argument");
    fd=$fopen(path,"r");
    if(!fd) $fatal(1,"Missing chip vectors");
    while(!$feof(fd)) begin
      clk=0;
      code=$fscanf(fd,"%d %d %d %d %d %d %d %d %d %d\n",rst_n,ui_in,uio_in,check,
        before_uo,before_out,before_oe,after_uo,after_out,after_oe);
      if(code!=10) $fatal(1,"Malformed chip vector");
      #1;
      if(check && {uo_out,uio_out,uio_oe} !== {before_uo,before_out,before_oe})
        $fatal(1,"CHIP before edge %0d actual=%h expected=%h",count,{uo_out,uio_out,uio_oe},{before_uo,before_out,before_oe});
      clk=1; #1;
      if(check && {uo_out,uio_out,uio_oe} !== {after_uo,after_out,after_oe})
        $fatal(1,"CHIP after edge %0d actual=%h expected=%h",count,{uo_out,uio_out,uio_oe},{after_uo,after_out,after_oe});
      count=count+1;
    end
    $display("Passed %0d independent whole-chip edges",count);
    $finish;
  end
endmodule
