# Initialized buffered SPI source/circuit refinement

The supported mode-0 SPI source now has a kernel-checked execution relation to
the actual packed Reactive circuit and initialized digital SRAM controller.
`Pinwheel.Hardware.Buffered.SpiRefinement.initialized_run` in
[SpiSimulation.lean](../../Pinwheel/Hardware/Buffered/SpiSimulation.lean)
establishes it from accepted loading and an actual START, then preserves it for
every command-zero execution prefix. It derives pin and datapath agreement;
neither equality is an assumed post-edge observation.

This closes the SPI state-representation gap identified by the earlier
[source/image interpreter study](buffered-source-execution.md). Reactive I²C,
general compiler correctness, serial delivery, emitted RTL and physical
qualification retain their separate boundaries. No CAD result is added.

## Exact scope and assumptions

The theorem covers the canonical four-leaf `BufferedSPI.program`: a repeated
SHIFT/KEEP pair, release and HALT. Its configuration supports one through four
bytes and half-periods of three through 256 clock edges. The image contains
four stored rows, nested byte/bit loop controls and a zero branch dictionary.

The initial controller, SRAM contents and registered responses are arbitrary.
The caller supplies a cold-initialization edge, a loading history satisfying
`SpiSource.SourceHistory`, a VALID loading cut, and a START whose actual
`Reactive.starting` expression evaluates to one at that cut. Source history
constrains accepted row/dictionary writes and accepted COMMIT operands; it does
not assume the final resident image, impose one upload order, or turn rejected
writes into accepted evidence. The existing loading proofs derive resident
coverage, both instruction replicas, the START mirror and fetch readiness.

After START, `incoming : Nat → BitVec 2` is arbitrary and the prefix length is
any natural number. `SpiStart.clocks` constructs the suffix with initialization
and command zero, those raw samples, and other operands zero. The theorem
therefore concerns one admitted transfer with a fixed resident image. Later
upload, reset, RELEASE and additional START commands are outside this suffix.

The START payload is an arbitrary 32-bit word. Actual admission derives TX
length and RX reservation bounds of zero through 32 bits, a free nonretained
engine, VALID, matching program generation and space in the 16-bit transfer
counter. Logical bit lists use LSB-first consumption order. Lengths are not
required to fill the chosen SPI schedule: empty/short TX and insufficient RX
space are included as faults. The theorem does not assume a successful peer,
complete RX reservation, or a payload with unused high bits zero.

The SRAM boundary is the repository's digital latency-one model. The result
does not establish analog macro behavior, synchronizer resolution, electrical
sampling, routing, frequency or power. It also does not compose through the
sampled serial frontend, native evaluation, compiler/emitter implementation or
emitted RTL. Existing evidence for those layers keeps its original scope.

## Admission and represented state

[SpiStart.lean](../../Pinwheel/Hardware/Buffered/SpiStart.lean) constructs the
source request from actual START operands and the pre-edge generation/transfer
registers. `seed_admitted` obtains its running buffer slot through ordinary
`Transfer.prepare` and `Transfer.start`; the proof does not begin by assuming
an arbitrary matching running source slot. The source identity uses epoch zero
and the actual next transfer sequence. This is a representation for one
admitted transfer, rather than a proof of an entire host ownership lifecycle.

[SpiRelation.lean](../../Pinwheel/Hardware/Buffered/SpiRelation.lean) defines
`Running`, `Stopped` and their union `Related`. The relation includes:

- Source virtual PC and duration against physical row, byte/bit loop counters,
  current control and remaining duration.
- Exact request length, reservation, generation, transfer sequence and owner.
- The original full payload shifted by the consumed count. Packing only the
  unconsumed logical list would lose unused high hardware bits for short TX.
- RX length and the canonical packed received prefix, with false padding.
- Pin levels/output enables, zero SPI scratch state, and retained completion
  or fault state with canonical stopped coordinates.

The START edge needs explicit sampler alignment. Circuit START advances its
two sampler registers; source `Buffered.start` leaves its seed samplers alone.
The constructed seed therefore uses START's raw input as its first sampler and
the actual pre-START stage1 as its second. Every later entry observes pre-edge
stage2, including RX append on KEEP. During running, both sampler registers
match the source. After stopping, the source freezes while the circuit keeps
sampling, so `Stopped` deliberately omits sampler equality while retaining pins,
payload diagnostics, counts, owners and outcome.

TX is consumed on SHIFT before the next KEEP appends RX. An empty TX faults at
START; later underflow and RX-full faults retain exactly the prefix already
consumed/appended. HALT retains normal completion. Canonical SPI has no WAIT,
CHECK or QUALIFY instructions: this result does not extend the relation to
their timeout, qualification or branch behavior.

## Theorem chain

| Link | Checked statement and source |
| --- | --- |
| Accepted loading to exact source image | `SpiSource.initialized_source_reference` and `SpiGeometry.initialized_source_geometry` derive the resident source words, count, span and idle pins at the VALID cut. |
| Actual START admission | `SpiCircuit.starting_facts`, `SpiAdmission.starting_controls` and `SpiStart.seed_admitted` derive the START guards, finite bounds, reset coordinates and admitted source request. |
| START establishes representation | `SpiRefinement.start_related` in [SpiStartRefinement.lean](../../Pinwheel/Hardware/Buffered/SpiStartRefinement.lean) handles both available and empty TX. |
| One actual edge | `SpiRefinement.related_step` uses countdown, SHIFT, KEEP/RX, release, HALT and stopped-state lemmas against actual `Reactive.circuit.step` and `Buffered.advance`. |
| Every packed execution prefix | `SpiRefinement.related_run` and `started_run` induct over arbitrary raw-input histories and prefix lengths. |
| Initialized digital SRAM composition | `SpiRefinement.initialized_run` composes the derived relation with `SramCorrespondence.initialized_to_execution` and preserved resident/fetch invariants. |
| Actual-controller consequences | `RelatedSram.pins` and `RelatedSram.datapath` in [SpiSramRelation.lean](../../Pinwheel/Hardware/Buffered/SpiSramRelation.lean) recover pin and owned-prefix agreement from actual controller registers. |

The implementation separates packing, coordinate/word certificates, actual
entry controls, pin updates, datapath updates and source-interpreter equations.
Bounded loop/word certificates use ordinary `decide +kernel`; the execution
theorem quantifies over all allowed payloads, raw histories and prefix lengths.
No `native_decide`, custom axiom or admitted source/circuit relation supplies
the missing step.

## Proofs and executable checks

The kernel theorem establishes the universal digital statement above. The
focused executable suite separately advances the existing source interpreter
and actual Reactive equations, then compares their represented state. It
exercises zero/short TX, zero/short RX, final-bit exhaustion, byte rollover,
maximum duration and clocks after stopping. Distinguishing controls cover
START sampler alignment, stopped sampler abstraction and unused high TX bits;
independent state mutations target current-raw RX sampling, append index and
outer-loop rollover.

Those finite checks are regression evidence. They do not replace the universal
proof or prove the evaluator, serial transport, RTL or physical implementation.
The focused gate also audits all imported declarations against the permitted
standard axioms (`propext`, `Classical.choice`, `Quot.sound`) and requires an
injected custom axiom to fail. Audit totals include generated declarations;
they are not counts of distinct mathematical results.

## Reproduce

Use the pinned `lean-toolchain` and Python 3.12+ from a source checkout:

```sh
lake build Pinwheel.Hardware.Buffered.SpiSimulation
python3 -B scripts/check-buffered-spi-refinement.py --tag <fresh-tag>
```

The gate checks the toolchain, default library build, whole-library axiom audit,
injected-axiom rejection and independent execution/control suite. It freezes
Lean, test and checker source hashes and rechecks them at closeout. Every run
uses a fresh `build/validation/<fresh-tag>/` directory, preserving previous
attempts. It requires no CAD runtime or ignored physical checkpoint.

The executable suite can also be inspected directly:

```sh
lake env lean -DwarningAsError=true --run test/BufferedSpiRefinement.lean
```

## Validation record

The source-frozen focused run `spi-source-circuit-focused-20261016-01` passes
in **74.837 seconds**. Its default library build completes 324 Lake jobs; the
whole-library audit checks **27,366 declarations / 14,992 theorems** with
standard axioms only, and the injected custom axiom is rejected. Ten independent
execution cases compare **17,845 prefixes**. Two direct ordinary-Reactive
boundaries and three rejected state mutations pass, with the short-TX,
START-sampler and stopped-sampler counterexamples witnessed. Inputs are
unchanged at closeout. The [local focused receipt](../../build/validation/spi-source-circuit-focused-20261016-01/report.json)
has SHA-256
`3ac844b6a767065fc26d1d88c6c20a4ba51eb417aa71db090dcbf01e593c2f19`.

The [full Python receipt](../../build/validation/spi-source-circuit-python-20261016-01/report.json)
also passes with unchanged inputs: **1,151 tests, six expected skips**,
50.316 seconds in unittest and 50.880 seconds including its wrapper. Receipt
SHA-256 is
`b05c9cafaab89c0355941a12e2b1c249c86be77092d1cea3182c8848b4c965cb`.

The full foundation run `spi-source-circuit-foundation-20261016-01` passes in
**1,982.932 seconds**: 61 executable suites, one kernel suite, two independent
Python oracles and injected-axiom rejection. It covers all 322 production
modules; its 447 frozen source hashes still match at closeout. The
[local foundation receipt](../../build/validation/spi-source-circuit-foundation-20261016-01/report.json)
has SHA-256
`d13e3118165d4e7800186793ebeed78513a35477a94ceac7029f21838d01f4df`.
These ignored local receipts preserve the checked source identities; they are
not durable external artifact custody or physical qualification.
