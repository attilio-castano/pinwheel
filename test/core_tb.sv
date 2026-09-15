`timescale 1ns/1ps
module core_tb;
  reg clk = 0;
  reg initialize, reset, start, commit, sample;
  reg [514:0] image;
  wire valid, timer_active, busy, completed, fault;
  wire [1:0] status;
  wire [4:0] pc;
  wire [7:0] remaining, rx;
  wire [2:0] levels;
  reg [514:0] images [0:`IMAGE_COUNT-1];
  integer input_file, trace_file, fields, cycle = 0;
  integer flags, image_index, ev, es, ep, er, ea, el, ex, known, expected_program, ei, eb, ec;
  reg [1023:0] trace_path;
  pinwheel_core dut(.clk(clk), .initialize(initialize), .reset(reset), .start(start),
    .commit(commit), .sample(sample), .idle(image[514:512]), .valid(valid), .status(status),
    .pc(pc), .remaining(remaining), .timer_active(timer_active), .levels(levels),
    .busy(busy), .completed(completed), .fault(fault),
    .word0(image[0 +: 16]),
    .word1(image[16 +: 16]),
    .word2(image[32 +: 16]),
    .word3(image[48 +: 16]),
    .word4(image[64 +: 16]),
    .word5(image[80 +: 16]),
    .word6(image[96 +: 16]),
    .word7(image[112 +: 16]),
    .word8(image[128 +: 16]),
    .word9(image[144 +: 16]),
    .word10(image[160 +: 16]),
    .word11(image[176 +: 16]),
    .word12(image[192 +: 16]),
    .word13(image[208 +: 16]),
    .word14(image[224 +: 16]),
    .word15(image[240 +: 16]),
    .word16(image[256 +: 16]),
    .word17(image[272 +: 16]),
    .word18(image[288 +: 16]),
    .word19(image[304 +: 16]),
    .word20(image[320 +: 16]),
    .word21(image[336 +: 16]),
    .word22(image[352 +: 16]),
    .word23(image[368 +: 16]),
    .word24(image[384 +: 16]),
    .word25(image[400 +: 16]),
    .word26(image[416 +: 16]),
    .word27(image[432 +: 16]),
    .word28(image[448 +: 16]),
    .word29(image[464 +: 16]),
    .word30(image[480 +: 16]),
    .word31(image[496 +: 16]),
    .sample0(rx[7]),
    .sample1(rx[6]),
    .sample2(rx[5]),
    .sample3(rx[4]),
    .sample4(rx[3]),
    .sample5(rx[2]),
    .sample6(rx[1]),
    .sample7(rx[0]));
  initial begin
    $readmemh("build/core/images.hex", images);
    input_file = $fopen("build/core/stimuli.txt", "r");
    if (!input_file) $fatal(1, "Missing stimuli");
    if (!$value$plusargs("trace=%s", trace_path)) trace_path = "build/core/rtl.csv";
    trace_file = $fopen(trace_path, "w");
    if (!trace_file) $fatal(1, "Missing trace file");
    $fwrite(trace_file, "edge,valid,status,pc,remaining,active,levels,rx\n");
    while (!$feof(input_file)) begin
      fields = $fscanf(input_file, "%d %d %d %d %d %d %d %d %d %d %d %d %d %d\n",
        flags, image_index, ev, es, ep, er, ea, el, ex, known, expected_program, ei, eb, ec);
      if (fields != 14) $fatal(1, "Malformed stimulus");
      initialize = flags[0]; reset = flags[1]; start = flags[2]; commit = flags[3]; sample = flags[4];
      image = images[image_index];
      #4; clk = 1; #1;
      if (pc !== ep[4:0]) $fatal(1, "ADDRESS cycle %0d got %0d expected %0d", cycle, pc, ep);
      if (rx !== ex[7:0]) $fatal(1, "CAPTURE cycle %0d got %0d expected %0d", cycle, rx, ex);
      if (valid !== ev[0] || status !== es[1:0] || remaining !== er[7:0] ||
          timer_active !== ea[0] || levels !== el[2:0] || busy !== eb[0] || completed !== ec[0] || fault !== (es == 3))
        $fatal(1, "STATE cycle %0d status=%0d expected=%0d remaining=%0d expected=%0d levels=%0d expected=%0d",
          cycle, status, es, remaining, er, levels, el);
      if (dut.r_idle !== ei[2:0]) $fatal(1, "IDLE cycle %0d", cycle);
      if (known) begin
        if (dut.r_word0 !== images[expected_program][0 +: 16]) $fatal(1, "MEMORY cycle %0d slot 0", cycle);
        if (dut.r_word1 !== images[expected_program][16 +: 16]) $fatal(1, "MEMORY cycle %0d slot 1", cycle);
        if (dut.r_word2 !== images[expected_program][32 +: 16]) $fatal(1, "MEMORY cycle %0d slot 2", cycle);
        if (dut.r_word3 !== images[expected_program][48 +: 16]) $fatal(1, "MEMORY cycle %0d slot 3", cycle);
        if (dut.r_word4 !== images[expected_program][64 +: 16]) $fatal(1, "MEMORY cycle %0d slot 4", cycle);
        if (dut.r_word5 !== images[expected_program][80 +: 16]) $fatal(1, "MEMORY cycle %0d slot 5", cycle);
        if (dut.r_word6 !== images[expected_program][96 +: 16]) $fatal(1, "MEMORY cycle %0d slot 6", cycle);
        if (dut.r_word7 !== images[expected_program][112 +: 16]) $fatal(1, "MEMORY cycle %0d slot 7", cycle);
        if (dut.r_word8 !== images[expected_program][128 +: 16]) $fatal(1, "MEMORY cycle %0d slot 8", cycle);
        if (dut.r_word9 !== images[expected_program][144 +: 16]) $fatal(1, "MEMORY cycle %0d slot 9", cycle);
        if (dut.r_word10 !== images[expected_program][160 +: 16]) $fatal(1, "MEMORY cycle %0d slot 10", cycle);
        if (dut.r_word11 !== images[expected_program][176 +: 16]) $fatal(1, "MEMORY cycle %0d slot 11", cycle);
        if (dut.r_word12 !== images[expected_program][192 +: 16]) $fatal(1, "MEMORY cycle %0d slot 12", cycle);
        if (dut.r_word13 !== images[expected_program][208 +: 16]) $fatal(1, "MEMORY cycle %0d slot 13", cycle);
        if (dut.r_word14 !== images[expected_program][224 +: 16]) $fatal(1, "MEMORY cycle %0d slot 14", cycle);
        if (dut.r_word15 !== images[expected_program][240 +: 16]) $fatal(1, "MEMORY cycle %0d slot 15", cycle);
        if (dut.r_word16 !== images[expected_program][256 +: 16]) $fatal(1, "MEMORY cycle %0d slot 16", cycle);
        if (dut.r_word17 !== images[expected_program][272 +: 16]) $fatal(1, "MEMORY cycle %0d slot 17", cycle);
        if (dut.r_word18 !== images[expected_program][288 +: 16]) $fatal(1, "MEMORY cycle %0d slot 18", cycle);
        if (dut.r_word19 !== images[expected_program][304 +: 16]) $fatal(1, "MEMORY cycle %0d slot 19", cycle);
        if (dut.r_word20 !== images[expected_program][320 +: 16]) $fatal(1, "MEMORY cycle %0d slot 20", cycle);
        if (dut.r_word21 !== images[expected_program][336 +: 16]) $fatal(1, "MEMORY cycle %0d slot 21", cycle);
        if (dut.r_word22 !== images[expected_program][352 +: 16]) $fatal(1, "MEMORY cycle %0d slot 22", cycle);
        if (dut.r_word23 !== images[expected_program][368 +: 16]) $fatal(1, "MEMORY cycle %0d slot 23", cycle);
        if (dut.r_word24 !== images[expected_program][384 +: 16]) $fatal(1, "MEMORY cycle %0d slot 24", cycle);
        if (dut.r_word25 !== images[expected_program][400 +: 16]) $fatal(1, "MEMORY cycle %0d slot 25", cycle);
        if (dut.r_word26 !== images[expected_program][416 +: 16]) $fatal(1, "MEMORY cycle %0d slot 26", cycle);
        if (dut.r_word27 !== images[expected_program][432 +: 16]) $fatal(1, "MEMORY cycle %0d slot 27", cycle);
        if (dut.r_word28 !== images[expected_program][448 +: 16]) $fatal(1, "MEMORY cycle %0d slot 28", cycle);
        if (dut.r_word29 !== images[expected_program][464 +: 16]) $fatal(1, "MEMORY cycle %0d slot 29", cycle);
        if (dut.r_word30 !== images[expected_program][480 +: 16]) $fatal(1, "MEMORY cycle %0d slot 30", cycle);
        if (dut.r_word31 !== images[expected_program][496 +: 16]) $fatal(1, "MEMORY cycle %0d slot 31", cycle);
      end
      $fwrite(trace_file, "%0d,%0d,%0d,%0d,%0d,%0d,%0d,%0d\n", cycle, valid, status, pc, remaining, timer_active, levels, rx);
      #4; clk = 0; #1;
      cycle = cycle + 1;
    end
    $fclose(input_file); $fclose(trace_file);
    $display("PASS core %0d edges", cycle);
    $finish;
  end
endmodule
