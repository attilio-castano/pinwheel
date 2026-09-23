// Independent behavioral specification for arbitrary stored contents.
// No initialization sequence, shared generated decode, or sampled test vectors.
module tile_oracle(
  input write_enable,
  input [3:0] write_hi, read_hi0, read_hi1,
  input [4:0] write_data,
  input [79:0] state,
  output [4:0] index0, index1,
  output reg [79:0] next_state
);
  assign index0 = state[read_hi0 * 5 +: 5];
  assign index1 = state[read_hi1 * 5 +: 5];
  integer word_index;
  always @* begin
    next_state = state;
    for (word_index = 0; word_index < 16; word_index = word_index + 1)
      if (write_enable && write_hi == word_index)
        next_state[word_index * 5 +: 5] = write_data;
  end
endmodule

module map_oracle(
  input write_enable, write_bank, read_bank,
  input [8:0] cursor,
  input [4:0] write_data,
  input [7:0] pc0, pc1,
  input [2559:0] state,
  output [4:0] index0, index1,
  output reg [2559:0] next_state
);
  assign index0 = state[(read_bank * 256 + pc0) * 5 +: 5];
  assign index1 = state[(read_bank * 256 + pc1) * 5 +: 5];
  integer bank_index, word_index;
  always @* begin
    next_state = state;
    for (bank_index = 0; bank_index < 2; bank_index = bank_index + 1)
      for (word_index = 0; word_index < 256; word_index = word_index + 1)
        if (write_enable && write_bank == bank_index && cursor == 64 + word_index)
          next_state[(bank_index * 256 + word_index) * 5 +: 5] = write_data;
  end
endmodule
