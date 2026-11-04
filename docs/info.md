## How it works

Pinwheel runs small programs that drive and sample pins at precise cycle
boundaries. The host loads up to 64 instructions through a four-bit link.
The engine uses separate two-word transmit and receive queues so the host can
service a transfer while Pinwheel controls the protocol pins. Programs cover
SPI, JTAG, UART, and I²C, including a sampled wait that lets an I²C target
stretch the clock.

`clk` clocks the entire design. Host SCK is sampled by `clk`. When `ena` is low
or `rst_n` is low, the wrapper holds its dedicated outputs low and releases
the protocol outputs. Raw protocol inputs use `ui[3]` and `ui[4]`. The `uio` pins are
driven only when the program enables them, and their input paths are unused.

## How to test

1. Start with a slow external `clk`. Hold host CSn high, host SCK low, and MOSI
   at zero. With the project selected, hold `rst_n` low across a clock edge,
   then release it. READY and BUSY should be low before a request.
2. Send the 22-byte request shown below, most significant nibble first. Set
   MOSI with SCK low so the engine can sample it on the following SCK rise. Hold
   each phase across at least one `clk` edge. Keep CSn low for the request,
   then raise it with SCK low. This sends sequence zero with the warm-reset
   opcode, empty payload, and CRC-16.
3. Wait for READY to assert, then lower CSn and read 52 MISO nibbles on SCK
   rises. Sample MISO before the engine `clk` edge that observes the SCK rise.
   Raise CSn after the last nibble. Decode the 26-byte response and check that
   its header is `0x5A20`, sequence is zero, its CRC is valid, and READY falls
   after the completed read.
4. For the I²C demo, connect protocol output 0 to raw input 0 for SCL and
   output 1 to raw input 1 for SDA. Use a compatible external target and
   pull-ups on both lines. With the documented sample program, read and
   write 64 bytes at address `0x52` and compare the captured payload with the
   target. A clock stretch should delay capture until SCL is observed high.

```text
A7 27 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 98 59
```

See the [quad host wire format](https://github.com/attilio-castano/pinwheel/blob/main/docs/protocols/streaming-continuation.md#quad-host-wire-format)
and the [sampled-ready I²C profile](https://github.com/attilio-castano/pinwheel/blob/main/docs/protocols/streaming-ready.md).

This is the CMOS5L 8×4 rehearsal candidate. The implementation targets a
20 ns clock period. The release clock rate and shuttle allocation remain open.
