# Buffered source and decoded-image execution

This continuation proves that independently interpreting the resident image
preserves the buffered source program's execution. It starts with parametric
mode-0 SPI, then uses a reactive four-byte I²C read to exercise waits, checked
phases, scratch decisions and terminal outcomes. The
[design explorer](../explorer/index.html#session) records that earlier proof
boundary. The later [initialized SPI refinement](buffered-spi-refinement.md)
now connects the supported SPI source to actual packed-circuit and digital SRAM
execution. The reactive I²C circuit relation remains open.

## What is proved

[SpiExecution.lean](../../Pinwheel/Hardware/Buffered/SpiExecution.lean) decodes
the four compact rows, loop controls, dictionary indices and all sixteen branch
entries without receiving the source configuration. The outer byte count comes
from the actual loop metadata. `decode_source` reconstructs the typed SPI
program for every supported configuration: one through four bytes and
half-periods of three through 256 edges.

`initialized_decode` also derives the decoded program from actual accepted
loading after cold initialization and a VALID cut. Its source-history premise
constrains accepted operands; image equality and the four-row count are derived.
`initialized_run` then equates source and decoded-image execution for arbitrary
buffered state, capacity, incoming samples and prefix length. This source state
is an explicit interpreter input, not a projection of the actual circuit cut.

[I2cSource.lean](../../Pinwheel/Hardware/Buffered/I2cSource.lean) constructs the
existing four-byte register-read source with phase period 4 and wait budget 32.
The independent decoder reads binary instruction fields, branch dictionary and
compact loop intervals. It does not receive the source syntax. `parse_succeeds`
proves this image decodes successfully. A kernel certificate checks virtual
fetch equality at all 1,024 representable source PCs, including out-of-program
positions. Fifty resident leaves represent 270 virtual entries.

The branch descriptor's fault STOP is separately connected to the source:
virtual address 265 maps to physical row 45 outside loops. Reserved instruction
bits and a wrong branch coordinate are rejected. The loop parser is bounded;
the theorem certifies this exact image rather than claiming validation of every
possible malformed loop encoding. I²C resident expansion is proved, while its
initialized accepted-loading/source-history composition remains open.

[DecodedExecution.lean](../../Pinwheel/Hardware/Buffered/DecodedExecution.lean)
proves that matching fetch, idle pins and last virtual address preserve START,
one-edge advancement and every execution prefix. I²C derives those premises
from its decoded image. The resulting theorem includes arbitrary input
histories, capacities and complete interpreter states, with successful,
timeout, fault and partial-result paths. It does not assume a successful peer
trace or matching post-edge observations.

These decoder theorems use the existing `Buffered` operational
semantics. They preserve countdown, two-stage sampling, pin commands, TX
consumption, RX prefix, scratch capture, branching and retained outcomes as
parts of the interpreter state. They are stronger than a finite replay, but
alone do not equate that state with the circuit's register representation.
The SPI continuation below supplies that separate relation for one admitted
mode-0 transfer.

## Circuit correspondence and remaining work

The existing initialized SRAM theorem compares the digital SRAM controller to
the independent packed-register Reactive circuit. The decoder results above
compare the source to an independently decoded-image interpreter.

For SPI, `SpiRefinement.initialized_run` in
[SpiSimulation.lean](../../Pinwheel/Hardware/Buffered/SpiSimulation.lean) now
derives the connection after cold initialization, actual source-constrained
accepted loading and an actually admitted START. It covers mode 0, one through
four bytes, half-periods of three through 256 edges, arbitrary 32-bit payloads,
admitted TX/RX lengths from zero through 32 bits, and every subsequent
command-zero raw-input prefix. TX underflow and RX-full faults preserve their
diagnostic prefixes; successful peer behavior is not assumed.

The relation maps virtual PC and duration to physical row, loop counters and
remaining duration; retains the original full TX word alongside its consumed
index; and packs the RX list in arrival order. The source seed aligns samplers
with the actual START edge. Stopped sampler registers are abstracted because
the source freezes after stopping while the circuit continues sampling. The
[SPI refinement study](buffered-spi-refinement.md) owns the assumptions,
admission argument, proof chain and focused gate. The explorer snapshot was
not regenerated for this continuation.

For reactive I²C, the next relation must cover wait readiness at the last
budgeted observation, qualification resets, terminal capture before branch
selection and virtual-to-physical branch coordinates. Its accepted-loading
composition is another required link. Exact typed/Python byte comparisons are
finite evidence about the compiler rather than a universal Python theorem.
Multiple-transfer/reset/release composition, serial delivery, native
evaluation, emitted RTL and physical timing keep their separate proof and
qualification boundaries.

## Reproduce

The focused source-pinned gate builds the complete library, audits every
declaration, rejects an injected custom axiom, executes SPI decoder controls
and compares fresh typed exports with canonical Python SRAM lowering:

```sh
python3 -B scripts/check-buffered-source-execution.py --tag <fresh-tag>
python3 -B scripts/build-explorer.py --check
python3 -B scripts/build-explorer.py
```

It compares sixteen SPI configurations (one through four bytes, half-periods
3, 4, 6 and 256) and the fixed four-byte I²C constructor, including every word,
control, dictionary index and descriptor plus geometry and buffer demands.
Logs and a hash-bound receipt remain under `build/validation/<fresh-tag>/`.
This decoder gate does not run CAD or check the later packed-state relation;
use the [separate SPI refinement gate](buffered-spi-refinement.md#reproduce)
for that continuation.

## Recorded validation

Local gate `buffered-source-execution-02` passes in 20.987 seconds: the default
build reaches 299 library modules; the whole-library audit checks 26,569
declarations and 14,357 theorems with standard axioms only. The injected custom
axiom is rejected. Five malformed SPI images and three positive geometry
controls pass, followed by seventeen typed/Python constructor comparisons and
four changed-field comparison controls. Report SHA-256 is
`0ae5f2a2066b9d1f65e7c9d5af1912cec663f93d670fda36c655a1c0a86510e5`.

The first run's audit rejected a generated native axiom in a local SPI pin
lemma. Replacing that tactic with an explicit bitwise proof removed the axiom;
the accepted fresh run audits the replacement. The failed run's diagnostic
remains under `build/validation/buffered-source-execution-01/`. These local
receipts establish integrity and reproducibility, not durable external custody.
