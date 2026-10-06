`timescale 1ns/1ps
// Resolved package pads: no expected values and no internal DUT references.
module host_bridge;
  reg clk=0, rst_n=1, ena=1;
  reg [7:0] ui_in=4, peer_levels=0, peer_enabled=0, pullups=255;
  reg [1:0] links=0;
  tri [7:0] pads;
  wire [7:0] uio_in=pads;
  wire [7:0] uo_out,uio_out,uio_oe;
  tt_um_pinwheel dut(.*);
  genvar k;
  generate for(k=0;k<8;k=k+1) begin: pad
    assign pads[k]=uio_oe[k] ? uio_out[k] : 1'bz;
    assign pads[k]=peer_enabled[k] ? peer_levels[k] : 1'bz;
    assign (weak1,weak0) pads[k]=pullups[k] ? 1'b1 : 1'bz;
  end endgenerate
  // Board fixture: SCL drive2/sense0, SDA drive3/sense1.
  tranif1 scl_link(pads[0],pads[2],links[0]);
  tranif1 sda_link(pads[1],pads[3],links[1]);
  reg [7:0] wire_values,known,required,connected;
  integer fd,code,cycles,n,j;
  reg [4095:0] line;
  initial begin
    fd=$fopen("/dev/stdin","r");
    if (!fd) $fatal(1,"Missing host pipe");
    while (1) begin
      code=$fgets(line,fd);
      if (!code) $finish;
      code=$sscanf(line,"%d %d %d %d %d %d %d",rst_n,ui_in,
                   peer_levels,peer_enabled,links,pullups,cycles);
      if (code != 7) $fatal(1,"Malformed resolved-pad host command");
      if (cycles < 1 || cycles > 1000000) $fatal(1,"Invalid edge count");
      for(n=0;n<cycles;n=n+1) begin
        clk=0; #10; clk=1; #10;
        wire_values=0; known=0;
        for(j=0;j<8;j=j+1) begin
          if(pads[j] === 1'b0 || pads[j] === 1'b1) begin
            known[j]=1; wire_values[j]=pads[j];
          end
        end
        required=8'h03 | uio_oe | peer_enabled;
        if(links[0]) required=required | 8'h05;
        if(links[1]) required=required | 8'h0a;
        if(rst_n && (known & required) !== required)
          $fatal(1,"Unknown/contention on resolved pads values=%h known=%h required=%h",wire_values,known,required);
        if(rst_n && (uio_oe & peer_enabled) !== 8'h00)
          $fatal(1,"External peer drives a DUT-owned package pad");
        connected=0;
        if(links[0]) connected=connected | 8'h05;
        if(links[1]) connected=connected | 8'h0a;
        if(rst_n && (connected & ((uio_out & uio_oe) | (peer_levels & peer_enabled))) !== 8'h00)
          $fatal(1,"I2C board links require open-drain low/release drivers");
      end
      clk=0;
      $display("PINWHEEL %0d %0d %0d %0d %0d",uo_out,uio_out,uio_oe,wire_values,known);
      $fflush();
    end
  end
endmodule
