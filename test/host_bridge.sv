`timescale 1ns/1ps
// Interactive transport: no expected values and no internal DUT references.
module host_bridge;
  reg clk=0, rst_n=1, ena=1;
  reg [7:0] ui_in=4, uio_in=3;
  wire [7:0] uo_out,uio_out,uio_oe;
  tt_um_pinwheel dut(.*);
  integer fd,code,cycles,n;
  reg [4095:0] line;
  initial begin
    fd=$fopen("/dev/stdin","r");
    if (!fd) $fatal(1,"Missing host pipe");
    while (1) begin
      code=$fgets(line,fd);
      if (!code) $finish;
      code=$sscanf(line,"%d %d %d %d",rst_n,ui_in,uio_in,cycles);
      if (code != 4) $finish;
      if (cycles < 1 || cycles > 1000000) $fatal(1,"Invalid edge count");
      for(n=0;n<cycles;n=n+1) begin
        clk=0; #10; clk=1; #10;
      end
      clk=0;
      $display("PINWHEEL %0d %0d %0d",uo_out,uio_out,uio_oe);
      $fflush();
    end
  end
endmodule
