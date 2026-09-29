# Four SPI modes and bounded transactions

This extends the [original mode-0 byte milestone](spi-model.md) to a bounded
controller transaction with one or two bytes, all four modes and a continuous
chip-select interval. It uses the existing timed-action and capture instructions.
The [continuation](../research/established-protocol-continuation.md) owns the
selected scope and the independent package-wiring repair.

## Wire contract

`Pinwheel/SPI/Transaction.lean` defines mode bits CPOL and CPHA, a half-period
`H` from 1 to 256, and a byte count of one or two. A 16-bit payload supplies the
low eight bits for a byte transaction or all sixteen for a two-byte transaction.
Bits are transmitted MSB-first; in the two-byte form the high byte comes first.

| Mode | Idle SCLK | Sample edge | Setup edge |
| --- | --- | --- | --- |
| 0 | Low | Rising | Falling |
| 1 | Low | Falling | Rising |
| 2 | High | Falling | Rising |
| 3 | High | Rising | Falling |

The mode definitions follow the
[Microchip SPI transfer-mode table](https://onlinedocs.microchip.com/oxy/GUID-F5813793-E016-46F5-A9E2-718D8BCED496-en-US-15/GUID-0E901CC4-8D8D-458D-8FF5-8898F0C41259.html).
Pinwheel chooses the following transaction timing; these durations are not
universal requirements of SPI devices.

Acceptance presents the first outgoing bit, asserts CS_N and holds the configured
idle SCLK for `H` engine edges. For `N=8` or `16` bits, the `2N` clock transitions
occur at `H, 2H, …, 2NH`. Leading edges move away from CPOL; trailing edges return
to CPOL. CPHA=0 samples at `H, 3H, …, (2N−1)H`. CPHA=1 samples at
`2H, 4H, …, 2NH`; its first setup edge may leave the already presented first bit
unchanged. MOSI retains the last bit during the final idle-clock hold interval.
At `(2N+1)H`, CS_N deasserts and MOSI returns low. SCLK retains CPOL.

Chip select remains low between the first and second byte. Raw receive slot `k`
holds the `k`th bit received on the wire; unused slots remain zero. The mailbox's
integer representation is consequently a bit-reversed byte or word, rather
than the wire-order value. A host decoder must assemble consecutive groups of
eight slots in MSB-first wire order.

The model's `incoming t` is the Boolean value **consumed by the engine** at edge
`t`, with elapsed cycle zero after acceptance. The core transition to `t+1`
consumes `incoming (t+1)`. This convention is shared by the compiler theorem.
The physical sampler and peer-response delay must be related to that history
separately.

## Implementation and proof chain

The finite reference stores a phase, a half-period tick, the payload and sixteen
sample bits. Its counters advance without consulting the elapsed-time wire
contract. The compiler in `Pinwheel/Compile/SPITransaction.lean` makes each
half-period a timed action and captures input 0 on entry to the appropriate
phase. After 17 or 33 phases it enters halt. Idle outputs retain CPOL and keep
CS_N high. No instruction, SRAM controller or capture-register width is added.

The proof chain is reference waveform/captures → compiled execution →
canonical E64 decoding → paired image certificate → existing initialized
upload/package/session refinement → fresh interpreted RTL. Each arrow has its
own assumptions. In particular, the paired SRAM law and typed digital input
delivery remain explicit; a protocol theorem does not qualify the SRAM or pads.

The new library theorems quantify over all four modes, both lengths, every
half-period 1–256, every 16-bit payload, arbitrary two-channel input histories and
every elapsed cycle. Unused input 1 remains arbitrary.

| Claim | Checked owner |
| --- | --- |
| Finite phase/tick state tracks elapsed time and stops exactly at completion | `SPI.Transaction.run_control`, `busy_exact` |
| Pins match the elapsed-time waveform; each slot changes only at its designated edge | `SPI.Transaction.waveform_correct`, `capture_correct`, `run_samples` |
| Completed samples retain each designated observation, with unused slots false | `SPI.Transaction.samples_complete` |
| Every start/advance and complete compiled run agrees with the finite reference | `Compile.SPITransaction.start_simulation`, `advance_simulation`, `run_simulation` |
| Compiled pins, samples, stopped/completed control and returned result agree | `Compile.SPITransaction.waveform_correct`, `samples_correct`, `completed_result` |
| Every canonical E64 record decodes to its instruction and decoded execution agrees | `Compile.SPITransaction.decoded_agrees`, `decoded_run` |
| Every transaction has at most 34 executable positions including halt | `Compile.SPITransaction.position_bound` |

`test/SPITransactions.lean` checks twenty actual images: all eight mode/length
forms at `H=4`, and twelve additional mode/payload/period cases at `H=3,6,256`.
For each image it decodes all 256 records, checks indexed expansion and the
paired image checker, and rejects a changed capture parameter. The observed
maximum is 34 positions and 20 distinct canonical E64 records. The position
bound is universal; the dictionary capacity and concrete paired lowering are
checked for these fixtures and checked again for each actual host upload.
They are not a separate universal dictionary-cardinality theorem.

The reference and compiler theorems describe an uninterrupted accepted transfer.
Reset/abort and host ownership remain governed by the existing engine and
package lifecycle; the RTL gate separately checks an active-transfer reset and
recovery. Arbitrary SPI requests are not a new interface added to this compiler.

## Package and external timing

The [version-2 pad contract](../engine/whole-chip.md#protocol-pad-contract-version-2)
uses MOSI=`uio2`, SCLK=`uio3`, CS_N=`uio4`, and independent MISO=`uio0`.
The original package drove MOSI on the MISO observation pad. Its independent-input
simulation was insufficient to establish a realizable full-duplex SPI wire.
Resolved-wire checks must use enabled chip outputs and separate peer drivers
on the same SystemVerilog nets, and reject contention and driver-ownership faults.

The logical compiler accepts `H=1–256`. The package has a two-edge observation
delay; a peer that changes MISO in response to a setup edge needs enough
half-period for its response to reach the consumed history. The original
[mode-0 latency theorem](../input-latency.md) states the sufficient condition
`d + tco ≤ H`. It does not automatically prove the extended modes' external
timing contract. New resolved-peer runs establish only their declared finite
response/configuration cases. No physical frequency, setup/hold voltage margin,
metastability bound or external-device compliance is inferred from these runs.

The interactive peer has one additional callback interval. A setup transition
at chip edge `L` is observed by the peer's next callback; with configured delay
`k`, its new MISO drive is installed before edge `L+k+1`. The core consumes that
sample at `L+k+3`. This harness therefore needs `H ≥ k+3` for bits following a
setup edge. `H=4, k=0` and `H=4, k=1` are within that bound; `H=4, k=2` is an
intentional late-response case. The receipt must distinguish the callback
interval from the chip's two-register sampling delay. Treating `k` alone as the
entire wire response would give an incorrect boundary.

SPI peripheral role, arbitrary-length bursts, changing resident payloads and
concurrent protocols are outside this milestone. The new pin assignment also
creates a new digital candidate: historical A's physical evidence remains tied
to its original source and wiring.

## Recorded validation

The resolved-wire gate `spi-capabilities-five-pad-02` passes in **547.180 s**:

- Twenty SPI matrix cases cover all four modes, both lengths and `H=3,4,6,256`,
  with independent outgoing/reply bytes, continuous CS, clock/sample edge order,
  decoded receive results, two nondestructive reads and consumption.
- A further `H=4, k=1` reply succeeds. The `H=4, k=2` late reply produces
  `0xcb` instead of `0x96` and is rejected after a clean wire trace and mailbox
  checks. A canonical wrong-slot program produces `0x00` instead of `0x96` and
  is rejected through the same independent result decoder.
- External `rst_n` interrupts a two-byte transfer after one sampled bit. The
  engine stops, outputs release and mailbox/flags clear; reupload/start returns
  the correct two-byte reply.
- Nine existing UART TX/RX, mode-0 SPI, stretched I²C, trigger and malformed-upload
  recovery cases pass on the resolved bridge. I²C uses the declared drive/sense
  joins; UART and SPI leave those joins open.
- All **33 valid program uploads** have fresh kernel certificates; the deliberately
  malformed upload is a separate rejected control. All 253 frozen
  source inputs, copied compiler/metadata bytes, certificates, MLIR, RTL,
  executable, tools and behavioral SRAM models pass closeout identity checks.

The gate receipt SHA-256 is
`b162c9e1d3feac2ebcb5504931d21a4513fb668930223d37e8f2981c830dba96`.
Its chip MLIR and RTL are byte-identical to the separate
`spi-source-readback-01` interpretation. That check passes **1,082 equalities**,
the complete component/initialized-session proofs, standard-axiom audits, both
unchanged controls and six RTL/two axiom corruptions in **429.635 s**. All 254
frozen inputs remain unchanged. Its receipt SHA-256 is
`b884ea77f0e94b2e855cb5a72e31d2c86247485014e674922e4d41a78df45c6f`.

The first wire-gate attempt remains preserved as interrupted for retained-copy
identity hardening. Earlier probes expose a missing behavioral-model cache and
then a correct source-drift refusal after all nine legacy checks. These are
debug/provenance attempts, not contradictory hardware failures. The models were
recovered from the movable bundle with the exact pinned lock hashes; no original
bundle input changed.

This is digital evidence for the new five-pad candidate. Neither receipt accepts
A or reuses historical physical observations. No placement, routing or extraction
was performed. The full library/Python regression and manifest are recorded in
the [continuation closeout](../research/established-protocol-continuation.md).

## Reproduce

Install the pinned [development tools](../development.md) and the hash-checked
behavioral SRAM models (`python3 scripts/inspect-storage-macros.py`). The protocol
gate uses the validation-isolated paired controller; it needs no historical
physical receipt. Use fresh tags to preserve previous attempts:

```sh
lake build Pinwheel
lake env lean -DwarningAsError=true test/ChipPinMap.lean
lake env lean -DwarningAsError=true --run test/SPITransactions.lean build/spi-transactions
python3 -B scripts/check-spi-capabilities.py --tag spi-wire-example --matrix
python3 -B scripts/check-paired-readback.py --mode fresh --tag spi-source-example
python3 -B scripts/check-foundation.py --tag spi-foundation-example
python3 -B -m unittest discover -s test -p 'test_*.py'
```

The SPI gate retains compiler/metadata copies, canonical program JSON, exact
certificates, MLIR, RTL, the executable, logs and a source/tool/model-bound
receipt under `build/host/<tag>/`. It freezes consumed artifact hashes before
execution and rechecks them at closeout. Meaningful file/source/certificate
mutation tests require refusal without a passing receipt. Generated output and
the large validation directories remain local ignored artifacts.
