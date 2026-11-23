# Pinwheel Streaming

I set out to design a chip whose protocol behavior I could change after it was fabricated, and to see how much of the path from a mathematical model to the implemented circuit I could check. Pinwheel is a programmable pin engine. I can load a UART receiver, test an SPI device, or talk to an I²C target by uploading a different program to the same engine.

## The architecture

The core executes up to 64 instructions of 64 bits each. Instructions drive pins, hold levels for a programmed number of cycles, sample inputs, and control when the engine advances. Two raw inputs are sampled by the project clock, and three output pins have independent level and enable control. A four-bit host link loads programs and services two-word transmit and receive queues. The queues let the engine handle a long transfer without storing its full payload on the chip. The host can separately inspect a retained result and release it when it is done.

In the I²C example, a seven-instruction image handles both a 64-byte read and a 64-byte write. The host streams the address and payload plan. The engine advances the high phase only when it samples SCL high, which lets the target stretch the clock. If the target exceeds the programmed wait budget, the engine retains the captured prefix and reports a fault. The same pin, timing and branch operations can be used to construct other protocols within the pin count, instruction store, sampling and host-service limits.

[Architecture, instruction set and host wire format](protocols/streaming-continuation.md) · [Wait guards and I²C examples](protocols/streaming-ready.md) · [Pinout and host test procedure](info.md)

## Try the examples

The fixture command prints the upload words, pin roles and expected data for UART receive, SPI duplex, and I²C reads and writes. The I²C example includes a target that stretches the clock and uses external pull-ups in the board wiring. The Python host API separates the command protocol from the actual GPIO adapter so the same fixture can be used with a digital simulation and adapted to a board.

```sh
python3 -B scripts/streaming_8x4_bringup.py fixture
```

The programs count time in core clocks, so the board clock sets the wire timing. At a 4 MHz core clock the default I²C program meets Fast-mode Plus timing. For a standard-mode or Fast-mode target, `--i2c-mode standard` or `--i2c-mode fast` emits a program with longer SCL phases. The [board clock guide](https://github.com/attilio-castano/pinwheel/blob/main/docs/board-clock-guide.md) lists the settings for each example at 4 MHz and at the 20 ns design target.

[Example programs and fixture generator](../scripts/streaming_8x4_bringup.py) · [Instruction encoder with I²C example](../scripts/streaming_ready_compile.py) · [Host transport](../scripts/streaming_ready_transport.py)

## Verification

I used executable Lean models to specify timing in clock cycles, instruction behavior, and how the host and engine share the queues and retained results. The Lean kernel checks proofs about the represented two-state execution, including queue bounds, capture order and timeout prefixes. The emitter produces typed MLIR, which CIRCT lowers to SystemVerilog. The hardware checks connect the generated register and output equations back to the model. Separate public-pin simulation uses independent peers to exercise the actual host interface and protocol traces. AI tools helped write and review implementation and proof attempts, build the test harnesses, and investigate physical-design failures. I used kernel checking, independent simulation and tool reports to decide what held up.

Because the proofs count clock cycles, I also stated in Lean what each example needs from the board clock. Starting from a real-time description of the bus, each clock contract derives the cycle-level peer assumption that the protocol proofs use. CAN and PS/2 receive need a 4 MHz core. The I²C proofs fix SCL LOW and HIGH durations, the SDA setup time and the clock-stretch deadline in core clocks. Those numbers are compared with the standard, Fast and Fast-mode Plus minimums. UART receive tolerates roughly −5 % to +5.5 % baud mismatch. SPI and JTAG sample data in three core clocks before each leading clock edge, which bounds how quickly a peer must respond. The contracts also exposed limits: the Ethernet demo needs a 60 MHz core locked to the PHY clock, above the layout target, and the I²C controller releases SDA on the same clock edge that drives SCL low. A Lean-generated [board clock guide](https://github.com/attilio-castano/pinwheel/blob/main/docs/board-clock-guide.md) turns these contracts into settings for each example. Pad delays and board wiring remain outside these models.

On the exact 8×4 CMOS5L layout, digital correspondence covers 6,039 state bits and 24 output bits. The implemented gate netlist passed 35 public-pin cases across UART, SPI, I²C and JTAG. A deliberate sampler-pin mutation was detected. The local physical evidence records clean main DRC, supplemental enclosure and foundry antenna checks, and matched transistor LVS. The frozen layout passed all ten current Tiny Tapeout checks locally, including the full CMOS5L main DRC and Verilog syntax check. The 20 ns clock period is a design target, and these digital results are from simulation. The release operating clock and board behavior remain open.

[Lean definitions and proof scope](protocols/streaming-ready.md#verification-boundaries) · [Implemented-netlist tests](research/streaming-8x4-hold-cap-digital-precheck-20261107.md) · [Physical checks](research/streaming-8x4-hold-cap-physical-20261107.md) · [Current release rehearsal](research/streaming-8x4-jane-street-release-20261114.md)

## Entry checklist

The organizer's November 9 update confirms 8×4 on the planned March 2027 CMOS5L shuttle. The public entry deadline is January 18, 2027. The organizer asks for a public repository with RTL, tests, a passing GDS and precheck from the Tiny Tapeout flow, architecture and instruction documentation, example programs and a verification write-up. The announcement describes the custom-GDS action for a local Tiny Tapeout build that would exceed the hosted run limit. The final form link was still pending when checked on November 14. [Jane Street announcement and FAQ](https://blog.janestreet.com/protocol-emulator-asic-competition/)

| Entry item | Review before submission |
| --- | --- |
| Public source | Select a public release revision containing the four generated RTL files under `src/`, tests, and Apache-2.0 license and applicable notices. Preserve the source and GDS identities below. |
| Programmability and testing | Include the architecture links, assembler and host examples above. The public-pin tests and four-case bring-up can be run with Icarus. A demo video is optional. |
| Tiny Tapeout flow | Use the official TTIHP27a custom-GDS action for the frozen handoff if accepted for the entry. Check that the action's `tt_submission` artifact and passing precheck are downloadable from the release revision and contain the reviewed GDS. Confirm checker versions and account for any differences from the pinned rehearsal. |
| Entry form | Check the live form fields once the organizers publish it. Prepare the public revision, artifact/run link and write-up for review before filing. Retain the form receipt after submission. |

The project top is `tt_um_pinwheel_streaming_ready_d2`. The reviewed GDS SHA-256 is `d4cd48f0919ac47ec4b2ceb061bc5dc6a217ce730b02b819a6b7e09d9e73c832`, and the frozen rehearsal source revision is `a305a4b339767e80719c9720a12ced7345b0e814`. Preserving the local rehearsal and obtaining the hosted Tiny Tapeout artifact are separate steps. Qualified timing, power and exact-candidate shuttle acceptance are tracked independently for the project's fabrication decision. [Fabrication gates](research/status.md)

### Reproduce the release RTL

In the local rehearsal worktree, use the installed Lean 4.33.1 toolchain, CIRCT `firtool-1.159.0` and the pinned OSS CAD Suite. The source exporter takes the frozen rehearsal manifest and reads the exact committed source into a separate directory. It checks the four regenerated files against the hashes consumed by the physical parent, compiles the standalone Tiny Tapeout top, and compares the public-pin bring-up outcomes against the frozen placed-cell simulation. [Toolchain pins](../tools/hardware-toolchain.json)

```sh
python3 -B scripts/streaming_8x4_jane_street_source.py \
  --out build/8x4-jane-street-entry-20261114/source-replay \
  --lean-bin "$PINWHEEL_LEAN_BIN" --circt "$PINWHEEL_CIRCT" \
  --iverilog "$PINWHEEL_IVERILOG" --vvp "$PINWHEEL_VVP"
```

The first successful local export is `build/8x4-jane-street-entry-20261114/source-02/`. The 3,600-file Git snapshot checked all 2,050 source entries selected by the rehearsal manifest. All four RTL files regenerated byte for byte and both the standalone top and public-pin bridge compiled. UART receive, SPI duplex, and I²C read and write matched the placed-cell fixture results. The export receipt has SHA-256 `a84c12db47394f89e9060c3b6616ffe0b41d7a147335e877137dc2f5eadaf89f`. This exercise regenerates the release RTL; a fresh physical build has its own source-to-GDS evidence.
