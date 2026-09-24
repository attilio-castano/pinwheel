# Bounded I²C register read

Implementation record: **2026-09-13**. The reference and compiler implement one combined seven-bit-address transaction on the same reactive instruction semantics:

```text
START → address/write → ACK → register index → ACK
      → repeated START → address/read → ACK → eight received bits → NACK → STOP
```

This follows the combined-format and controller-receiver behavior in [NXP UM10204 revision 7.0, section 3.1.10](https://www.nxp.com/docs/en/user-guide/UM10204.pdf). The scope remains one controller, a cooperating target, and ideal digital open-drain wires. Reserved address semantics, multiple-byte reads, arbitration, recovery, synchronization latency, analog rise times, and electrical compliance are outside this experiment.

## What the experiment changed

Keeping setup, clock-ready wait, guarded high, and falling-edge hold for all 36 clocks requires **155 logical instruction addresses**, including qualification, both START sequences, STOP, and halt. The existing 128-address expansion cannot hold this particular schedule. This is not a lower bound for every possible compiler or ISA.

Three ACK flags and eight received bits require eleven meaningful sample slots when retained separately. The read uses slots 0–7 in wire order for received data, slot 8 for write-address NACK, slot 9 for register-index NACK, and slot 10 for read-address NACK. Any NACK branches to STOP after completing its ACK low hold. Success exposes the received byte; timeout and bus fault release the lines.

The reactive engine and functional fetch adapter now parameterize their address and sample capacities. Defaults remain **128 addresses and eight samples**, preserving the existing UART/SPI/I²C write programs, counted programs, and PWL version-0 format. The read instantiates **256 addresses and 16 samples**. It adds no opcode, extra bookkeeping cycle, or second scheduler implementation. Timers and wait budgets remain 1–256 observations.

The four repeated-START phases release SDA while SCL is low, wait for observed SCL high, guard both lines high for a setup interval, and pull SDA low for the START hold. Stretching therefore applies to repeated START and STOP as well as data clocks. After STOP the bus-free hold is qualified like the interval before the first START: a low observation restarts the count and spends the wait budget instead of faulting. That revision (2026-09-17) lets the read run behind input registers; see [input latency](../input-latency.md).

## Proof and executable evidence

`I2C/RegisterRead.lean` is a phase-based reference independent of program addresses. `Compile/I2CRead.lean` emits the 155-instruction schedule. `I2CReadProofs.lean` proves one-step correspondence for every reference state and sampled bus, then complete-state correspondence for every configuration, request, input history, and run length. The relation includes pin commands, control, timers that affect execution, all sample slots, and results. Reference-only inactive counters are omitted by the state mapping.

The receive-status preservation theorem proves that receiving a bit cannot overwrite ACK flags. Reset on the shared engine clears samples and releases pins. The reference full-run theorem covers uninterrupted execution; reset/reload is checked separately. These claims establish compiler/reference correspondence, not universal completion against every target or physical I²C compliance.

The independent target and wire monitor use resolved wire edges and byte position, never the controller phase, PC, or compiler's bit generator. The suite passes **4,468 transactions and 1,092,960 observed cycles**: all returned bytes at phase durations 1 and 4, each first-NACK location or success, quiet/stretched buses, all register-index bytes, all 112 ordinary seven-bit addresses, and duration/budget 256 with 255 blocked observations per release. The example address `0x53`, register `0xA6`, return `0x96`, phase duration 4 and wait budget 8 takes **502 cycles quiet and 557 stretched**.

All four digital input combinations are forked near every observation of a stretched example and compared with the reference through timeout/guard/capture boundaries. Checks include reset priority, rejected busy reload, accepted stopped reload, STOP after NACK, receive-line release, final controller NACK, and finished-state retention. Six deliberate mutations remove/move capture, overwrite status, ignore NACK, omit repeated START, or drive a final ACK; each is rejected.

```sh
python3 scripts/check-i2c-read.py
```

The runner audits every public read-compiler theorem and writes coverage, the stretched wire trace, logs, and source/artifact hashes to ignored `build/i2c-read/`. Existing binary and reactive regression runners remain required after the capacity generalization.

## Hardware consequence

The physical execution-record experiment must support eight-bit addresses and four-bit sample destinations. The current PWL V0 format is unchanged and does not encode the wider read directly. A new load-image version is a separate interface decision; the hardware experiment can consume the compiled typed read and lower existing decoded V0 programs to the same execution-record semantics.

The [E64 record layout](../storage/execution-records.md) and [decoder/store measurement](../storage/execution-hardware.md) now implement this comparison. Both direct and indexed packed backends pass the same 4,468-transaction read matrix, and their circuit reads/writes/decoder outputs have structural proofs and independent RTL checks. The indexed candidate reduces storage and generic cell count while increasing selection depth. The complete reactive scheduler circuit, atomic physical loader, and electrical I/O timing remain separate integration work.
