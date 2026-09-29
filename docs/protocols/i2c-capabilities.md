# Bounded I²C writes and bus clear

This is the next [established-protocol capability](../research/established-protocol-continuation.md)
after the delivered four-mode SPI checkpoint `2837d3e`. Work is local on
`codex/i2c-capability-refinement`. The selected scope is one or two payload
bytes following a seven-bit write address, plus a separately loaded bus-clear
program. Existing instruction, storage, sampler and mailbox widths remain the
implementation boundary.

Delivered locally on 2026-09-29. Universal digital proofs, fresh upload
certificates, resolved-wire checks and current-source RTL interpretation pass.
The [manifest](../../physical/experiments/i2c-capability-results.json) binds the
implementation and receipts. Physical qualification remains separate.

## Write contract

The transaction begins with qualified bus-free time and START, then sends the
address/write byte and one or two payload bytes MSB-first. The target supplies
an independent ACK after each byte. The first NACK skips all later payload bytes
and proceeds to STOP. Three separate ACK flags suffice for the longer form,
within the existing sixteen capture slots. Timeout and unexpected clock-low
observations during a guarded high phase release both output drivers.

`I2C.WriteTransaction.Request` carries a seven-bit address, a bounded payload
count and sixteen payload bits. A one-byte request uses the low eight bits;
two bytes send the high byte first. Raw slots zero, one and two record address,
first-payload and second-payload NACK respectively: true means the target left
SDA high. Host engine completion means that the program reached halt, including
a completed STOP after NACK; the host must decode the flags to identify success
or the first rejected byte.

The fixed write image has 115 populated positions including halt. A successful
one-byte request executes eighteen bit/ACK clocks; a two-byte request executes
twenty-seven. The extra image positions are bypassed for the shorter form.
Payloads remain program literals; this adds no dynamic data FIFO.

The existing `I2C.Config` carries phase and wait counts from 1 to 256 logical
engine observations. Those are project timing and timeout choices; they do not
identify an electrical I²C speed grade. The universal compiler contract must
agree with an independent phase reference for every configuration, payload and
consumed bus history. It does not establish success against an arbitrary target.

## Recovery contract

[NXP UM10204 revision 7.0, section 3.1.16](https://www.nxp.com/docs/en/user-guide/UM10204.pdf)
describes nine clock pulses for a stuck-low SDA line. A device that keeps SCL
low, or fails to release SDA during those pulses, requires device hardware reset
or power cycling. Pinwheel's recovery program cannot control those device
signals or supplies; it must expose the failure and release its own drivers.

The selected digital policy uses nine controller clock-release attempts with
SDA continuously released, bounded waits for SCL, and guarded high periods.
The ninth high interval captures SDA in slot zero. A low observation completes
with `stillStuck`; a high observation proceeds to consecutive both-high
qualification, then completes with `recovered`. Both paths release the
controller's drivers. No controller-generated STOP or tenth clock rise is added.
Even an already-free bus gets nine pulses when this standalone program is
explicitly started.

The universal controller bound concerns its own phase progression and release
attempts. Arbitrary target SCL transitions can produce more raw wire edges.
Exactly nine observed rises is a separate finite wire-monitor check under the
declared peer behavior.

The recovery image has thirty positions including halt and uses only capture
slot zero. Its true value means released SDA, whereas true write flags mean
NACK. The host must interpret the mailbox in the context of the loaded program.

This is an explicitly requested standalone program, followed by an explicitly
started write after recovery succeeds. It does not automatically retry a write
whose target-side effects may already have occurred. A persistent blocking
interval has a configured timeout; intermittent bus interference does not
automatically imply a bound on total elapsed time.

## Package checks and completion gates

The [fixed pad contract](../engine/whole-chip.md#protocol-pad-contract-version-2)
joins SCL drive `uio2` to sense `uio0` and SDA drive `uio3` to sense `uio1`, with
digital pullups. Independent peers must observe the actual resolved nets and
reject an enabled high driver, conflicting ownership and unknown wire values.
The chip's two-stage sampler and interactive callback delay remain separate
timing assumptions.

Completion requires universal reference/compiler/canonical-E64 correspondence,
standard-axiom audits, capacity checks and fresh kernel certificates for actual
paired uploads. The wire gate must independently decode transmitted bytes and
ACKs, verify STOP after each first-NACK position, exercise bounded stretching,
distinguish recovered/stuck/clock-timeout cases and check mailbox retention,
consumption and reset/reload recovery. Meaningful altered capture, status,
drive and ordering controls must fail.

Fresh RTL interpretation and shared-engine regressions will bind the result to
the current source. If the emitted chip bytes remain identical to the SPI
checkpoint, that establishes reuse of the same digital implementation. It does
not transfer historical physical A's routing, timing or electrical evidence.

Multiple-byte reads, arbitration, multiple controllers, ten-bit/reserved-address
semantics, analog rise times, metastability and physical operating rates remain
outside this milestone. No placement, routing or extraction is allocated.

## Proof owners

| Contract | Source and principal results |
| --- | --- |
| Independent write phases and data | [`WriteTransaction.lean`](../../Pinwheel/I2C/WriteTransaction.lean) defines the request, MSB-first data, ACK slots, first-NACK branches and STOP phases. [`WriteTransactionProofs.lean`](../../Pinwheel/I2C/WriteTransactionProofs.lean) proves the requested-length bound, released ACK drive, first-NACK STOP, unused capture slots and the absent third ACK for one-byte requests. |
| Write compilation and canonical execution | [`I2CWriteTransactionProofs.lean`](../../Pinwheel/Compile/I2CWriteTransactionProofs.lean) proves `advance_simulation`, `run_simulation`, waveform/capture/result correspondence and `decoded_run` for every request, timing configuration and consumed bus history. [`I2CWriteTransaction.lean`](../../Pinwheel/Compile/I2CWriteTransaction.lean) owns the 115-position bound and canonical decoding agreement. |
| Independent recovery phases and bound | [`Recovery.lean`](../../Pinwheel/I2C/Recovery.lean) owns the nine-attempt controller bound and captured outcome. [`I2CRecoveryProofs.lean`](../../Pinwheel/Compile/I2CRecoveryProofs.lean) proves compiler simulation, canonical `decoded_run`, the 30-position bound, continuously released SDA, terminal release and unused halt records. |
| Concrete paired storage | [`I2CWriteTransactions.lean`](../../test/I2CWriteTransactions.lean) and [`I2CRecovery.lean`](../../test/I2CRecovery.lean) check concrete image decoding, indexed lowering and paired certificates. Actual wire uploads are independently kernel-certified again by the gate. |

These are digital compiler/reference claims. They do not convert the sampler's
arbitrary consumed history into a universal closed-loop theorem about external
targets or analog timing.

## Reproduce

Use the repository's pinned Lean toolchain and Python 3.12+. The wire gate also
needs the pinned CIRCT/OSS CAD tools and locked behavioral SRAM models described
in the [host workflow](../host-workflow.md).

```sh
lake build Pinwheel
python3 -B scripts/check-foundation.py --tag i2c-foundation-example
python3 -B scripts/check-i2c-capabilities.py --tag i2c-capabilities-example
python3 -B scripts/check-paired-readback.py --mode fresh --tag i2c-readback-example
python3 -B -m unittest discover -s test -p 'test_*.py'
python3 -O -B -m unittest discover -s test -p 'test_i2c_capabilities.py'
```

Choose fresh tags to preserve previous evidence. The wire runner freezes its
sources, tools, models, consumed copies, emitted artifacts and certificate
inputs before use, then checks their identity at closeout. Python receipt and
peer tests include optimized execution so validation does not depend on
removable Python assertions. Generated receipts remain local ignored artifacts;
the tracked manifest records identities rather than distributing those files.

## Delivered evidence — 2026-09-29

| Gate | Recorded result |
| --- | --- |
| Lean foundation | 240 imported modules, 18,070 declarations and 9,589 theorems audited with standard axioms only; 35 executable suites, one kernel suite and untrusted-axiom rejection pass. 329 frozen inputs match; 1417.024 s. |
| Resolved I²C package wires | 11 write and 12 bus-clear cases pass, including every first-NACK position, release on pulses 1–9, stuck SDA, bounded stretching and stuck-SCL timeout. Two guarded-high fault controls, active-write reset/reload and clear→write without an intervening chip reset pass. 33 fresh kernel certificates cover 29 positive/control uploads and four canonical altered programs rejected for the intended reasons. 264 frozen source inputs, tools, models, consumed copies and generated artifacts match; 458.911 s. |
| Fresh RTL meaning | 1,082 equalities, component and initialized-session proofs, standard-axiom audits, two unchanged controls, six RTL corruptions and two axiom injections pass. 261 frozen inputs match; 361.618 s. Emitted chip MLIR/RTL equal both the wire gate and the prior SPI checkpoint byte-for-byte. |
| Python regression | 648 tests: 646 pass and 2 platform skips. All 47 focused optimized tests pass; 218 frozen inputs match; 19.764 s. |

Receipt paths and SHA-256 digests:

- `build/host/i2c-capabilities-02/report.json`: `424a2a04ac205c7c0e0a634285e4bfab04573937ac5b9099069ac942edb3da28`.
- `build/validation/i2c-source-readback-01/report.json`: `d08dfa4dfb8cc8ef1bac879855f7750299cc4b0dd76b40cff31d0080e7bd8461`.
- `build/validation/i2c-foundation-01/report.json`: `14f62b2513860f637ae61912837b317220abd83a2dc725eebc13c34b7fd93256`.
- `build/validation/i2c-python-final-02/report.json`: `4482526985c2b9e5870f3791c193d17e5b0bb72388941fee37f316f47d2cfad4`.

Every checked write fixture uses 115 positions and 15 distinct E64 records.
Recovery uses 30 positions and at most thirty distinct records structurally;
its actual fixtures use 7 distinct records. The largest actual upload, including the intentional
mutants, uses 16 distinct records. The 32-record dictionary and 16-capture limits
remain unchanged. Capacity and paired lowering are checked again for every
actual upload, including the semantic negatives.

The independent peers observe address/payload bytes, ACK ownership, low/high
intervals and START/STOP directly on resolved SCL/SDA. The wrong capture and
terminal-status controls first pass those wire checks and retained/consumed
mailbox checks, then fail the intended semantic comparison. The swapped-address
control has ordinary engine completion but fails byte ordering; the enabled-high
SDA control fails the SystemVerilog open-drain check. These controls do not use
an earlier malformed-upload failure as evidence for a semantic defect.

An initial debug fault control pulled SCL low immediately after its first rise;
the two-stage sampler could miss the high pulse entirely. The corrected control
holds high for two callback intervals before forcing clock loss and produces
engine fault status 7 on both write and recovery. Both probes remain recorded
in the manifest. Debug probes used the prior SPI executable; the successful
final gate freshly emitted, compiled and certified its own inputs.

The first fresh wire receipt recorded only simulator launcher hashes. A final
rerun also binds actual executables, backend assets, VPI modules and bundled
shared libraries, checks inventory membership at closeout and pins the compiler
backend. System libraries, loader, shell and Python/Lean runtimes remain
environment assumptions. The superseded receipt remains preserved.

All 217 preexisting physical manifest/fixture artifacts match base
`2837d3e` byte-for-byte. Only their catalog README changes. This milestone adds
zero physical CAD seconds and zero routes; campaign use stays at 8,843.120
seconds, with three A routes used and two B routes reserved. The unchanged
chip bytes preserve the same digital implementation identity; they do not
accept historical physical A. The next local capability is UART supervisor and
one-entry result-buffer circuitry.
