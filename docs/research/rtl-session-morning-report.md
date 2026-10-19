# Source-to-RTL programmable sessions: morning report

Campaign launched October 17, 2026 at 8:09 a.m. Eastern
(`2026-10-17 12:09:39 UTC`), with a twelve-hour maximum. Branch:
`codex/buffered-rtl-sessions`. Baseline:
`cf8edbb2abc462e5a274a99240d62495f0ad7455`.

**Completed.** All six ordered targets, the programmable-image continuation and
their verification gates closed. Receipt verification finished at 9:59:42 a.m.
Eastern (`2026-10-17 13:59:42 UTC`), 1 hour 50 minutes 3 seconds after launch.
The full queue and continuation closed inside the twelve-hour maximum.
Main proof snapshot: `dc53cebb9ee06c35e5ba468b58fd002ebcc101c5`.
Evidence producer: `e4dd271f1faf9d558a0598b806a36d1e6ca52964`.

## Result

The campaign connects the typed programmable engine to freshly emitted RTL,
the actual serial package and digital SRAM feedback, and the actual Tiny Tapeout
pin/output-enable wrapper. It also extends initialized wire loading and reuse
from the fixed I²C image to independently certified program images. The same
circuit accepts a new certified image over the host wire interface and executes
the new source program. One concrete session uploads I²C, executes and releases
a retained result, warm-resets,
uploads SPI, and executes and releases again while carrying the same logical
allocator.

Program replacement happens only through reset plus actual wire loading. Reset
acts on the exact ordinary transfer state reached by the preceding source
prefix, including its buffers; the proof does not substitute a fresh allocator
or unrelated software state at the program switch.

The component certificates cover every represented next-register and output
equation for arbitrary binary inputs and raw states: thirteen frontend fields
and 389 bits, plus 117 controller fields and 3,151 bits. They cover nineteen
frontend and thirty-one controller outputs. No cold-state invariant is needed
for these equalities. Physically absent phantom word coordinates are extended
by zero in the typed interpretation; they do not create extra physical storage.
The resulting RTL-to-typed-package recurrence holds for every finite binary pin
history. The source-program interpretation has the static certification and
actual session-admission conditions described below.

The initialized session results then establish the installed image and VALID
from arbitrary controller state, both memory arrays and both registered Q
values. Actual cold reset and serial upload establish those premises. Finite
admitted session traces carry START, source execution, capture, retained reads,
retries, RELEASE, reuse, padding, reload, and cold interruptions inside request
or response frames. Each sampled pin edge advances the same controller/source
history. They do not cover every malformed or inadmissible host history.

## Closed proof scope

Names below are under `Pinwheel.Hardware.Buffered`, except generated artifact
certificate names, which live under `Pinwheel.Artifact`.

| Target | Checked connection | Scope |
| --- | --- | --- |
| Raw frontend | Generated `Buffered.Serial.next_correct` / `output_correct` | All 13 state fields and 19 outputs; raw emitted RTL rather than the older 370-bit optimized quotient. |
| Raw controller | Generated `BufferedSram.step_correct` / `observe_correct` | All 117 state fields and 31 outputs, through the checked typed source reference and imported RTL equations. |
| Actual package and memory wiring | `ArtifactPackageWiring`, `ArtifactPackageWiringSession` and generated combined certificate | Actual frozen wrapper descriptors, both independent memory Q inputs, feedback and digital memory law. |
| Actual Tiny Tapeout wrapper | `ArtifactTinyTapeoutWiringSession` and generated combined certificate | Actual pin mapping, output enables and encoded sampled histories. |
| Every timing pair | `I2cTiming.SerialWitness.initialized_two_fused_rounds`, artifact timing corollaries | All 65,536 duration/budget field pairs, initialized wire upload and two carried retained rounds. |
| Programmable loading | `GenericUpload.Serial.cold_install`, `GenericWireSession.initialized_session` / `initialized_exists` | Any independently certified representable image; concrete wire loading derives installed operands, coverage and VALID. |
| Mixed program reuse | `MixedSpiI2cWire.initialized_i2c_spi_switch`, artifact mixed corollaries | One nonempty I²C→warm reset→SPI history, one allocator, actual uploads and admitted STARTs. |

The controller proof reconnects the original typed expressions, prospective
next-state candidates, balanced row selection, dictionary expansion and storage
rewrites. Local graph partitions and SMT suggestions only propose lemmas; Lean
checks their proofs and their composition. The final component theorem has no
runtime image, VALID, admission, initialized-state or execution-agreement premise.

The reusable wrapper/session modules take component-correctness and memory-law
parameters. The generated combined certificate constructs all four component
correctness families from the fresh frontend/controller proofs and instantiates
the actual parsed wrappers. Its concrete digital-memory corollaries also
discharge the memory law. No supplied component-correctness premise remains in
those final corollaries.

An independent `ProgramImage` contains a source program, its static layout and
word/control/branch/dictionary encoding certificate. It does not contain a
runtime state or a trace agreement assumption. Representability remains bounded
by 64 physical rows and sixteen dictionary entries. Upload consists of sixteen
dictionary writes, the certified number of row writes, and COMMIT, each through
the actual request/capture/read transport. Arbitrary unused SRAM payload tail
cells are preserved; COMMIT may normalize inactive metadata.

The timing witnesses derive real START acceptance and retained timeouts for
every field pair, including zero. They end with logical epoch
`previous.epoch + 1`, next sequence `3`, hardware generation `1`, and transfer
`2`. The mixed witness sends 67 I²C upload transactions and 21 SPI upload
transactions. It ends with epoch `previous.epoch + 2`, next sequence `2`,
generation `3`, transfer `2`, and logical/hardware sequence offset `1`.
Its retained outcomes are an I²C timeout and an empty-TX SPI underflow. These
constructive diagnostic witnesses establish nonvacuity; successful external
peer progress is a separate claim.

Timing fields encode cycles minus one: zero represents one cycle and 255
represents 256. The typed theorem covers every field pair. The public Python
constructor's existing minimums remain three phase cycles and four wait cycles.

## Validation

The fresh full artifact gate passed in 805.959 seconds from `dc53ceb`. All 761
indexed committed inputs, 253 fresh library oleans, 9,224 frozen artifact inputs
and selected tool identities passed their closeout checks. The run recorded
9,173 commands. Its combined audit covered 90,928 declarations and 58,359
theorems, including generated private helpers; only `propext`,
`Classical.choice` and `Quot.sound` were allowed. An unused private custom axiom
was rejected. Both universal unchanged reimports passed, as did rejection of
five frontend, six controller and twelve wrapper corruptions, each independently
imported from actual changed SV. The repaired unchanged-controller control took
6.354 seconds.

The fresh foundation gate passed all 519 build jobs, with all 517 library modules
reachable from the default import. Its audit checked 34,651 declarations and
19,322 theorems with standard axioms only, and rejected an injected custom axiom.
All 64 executable suites, one kernel suite and both independent Python oracles
passed. All 71 command outcomes were as expected, including the deliberate axiom
rejection. The snapshot driver verified 649 listed inputs against `46db3cc`.
The gate took 2,567.965 seconds, or 2,571.990 seconds including snapshot closeout.
Each gate used an isolated committed-source archive; failed attempts and skips
remain explicit.

The final Python regression ran 1,212 tests with eight skip entries in
50.522 seconds (52.484 seconds including snapshot closeout), from source and
producer `dc53ceb`. All 2,680 archived regular source files and four committed
producer inputs passed membership checks before and after execution. The skips
cover absent local Icarus installations inside the isolated archive, macro and
saved Yosys fixtures, an unbuilt Lean export, and Linux process observations.
Several entries skip whole test classes, so subtracting eight from the run count
would not give a meaningful passed-test count. The separate accepted simulator
gate explicitly selects the installed tools and fills the finite RTL gap.

The native Lean toolchain is 4.33.1. Official checksum-pinned CIRCT firtool
1.159.0 and OSS CAD Suite tools were installed locally. The certificate path
uses native emission, CIRCT lowering, Yosys parsing/process normalization and Z3
suggestions, followed by Lean proof reconstruction. It performs no synthesis
mapping, ABC or physical implementation.

Archive hashes and selected installed executable/runtime hashes are recorded
separately. The receipts do not prove installed-payload membership in those
archives; host OS libraries, shell utilities and Python library initialization
remain runtime assumptions.

The independent finite simulator uses newly emitted frontend/controller RTL,
the frozen package/memory wrappers, and a public-pin bridge. Its explicit
synchronous digital SRAM model gives write priority, masked writes, pre-edge
read values, and held Q during writes/idle. Both banks and their Q values start
with different poison patterns. Frontend vectors check typed pre-edge outputs
and post-edge outputs/registers; separate SPI, JTAG and I²C peers check completed
protocol behavior and repeated retained reads.

This simulator gate passed in 45.700 seconds, from source `46db3cc` with producer
`1b204b4`. Frontend replay covered 69 cases and 53,775 edges, with 1,020,731
pre-edge output, 1,021,725 post-edge output and 699,075 register comparisons.
The separate package-peer corpus covered 107,064 physical edges and 151 complete
request/response pairs. SPI received 32 bits, JTAG 17 bits, and I²C 32 bits;
each retained result was read twice. Both emitted SV files match the full proof
run's fresh artifacts byte for byte. All 862 indexed runtime files, two pinned
archives, source/producer inputs and frozen artifacts were unchanged at closeout.

Independent review added default-import coverage for every production module,
strict ownership-based audits of generated private declarations, and first-use
artifact freezing. A frozen input cannot be re-registered with changed bytes.
Focused controls exercise source/producer membership, cache refusal, tool and
runtime changes, deliberate unused private axioms, and actual RTL/wiring
corruptions.

The first full gate is retained as failed: after both component certificates
passed, its universal unchanged-controller control exhausted Lean's deterministic
8,000,000-heartbeat comparison budget while expanding duplicated graphs. The
repair proves equalities one node at a time and composes the same universal
117-register/31-output statements. It does not raise the budget or weaken the
control. The fresh committed-source retry (`-02`) passed as reported above. The
earlier frontend attempt also remains failed because generated files lacked an
explicit Lean module root; commit `770d51b` fixed that producer setting before
the accepted frontend-only retry.

## Evidence and local changes

The [evidence manifest](evidence/rtl-session-20261017/manifest.json) binds each
receipt to its own historical source and producer commits. All indexed source
and producer bytes were independently checked against Git archives; every
reported archive hash was reproduced. Exact receipt bytes are retained in
deterministic `.json.gz` files, with both compressed and decompressed hashes.
Five accepted historical receipts and two failed attempts occupy 3,645,557
compressed bytes. The four final qualification receipts are:

| Gate | Source | Exact compressed receipt |
| --- | --- | --- |
| Full source-to-RTL sessions | `dc53ceb` | [Full](evidence/rtl-session-20261017/buffered-rtl-session-full-20261017-02.json.gz) |
| Foundation | `46db3cc` | [Foundation](evidence/rtl-session-20261017/rtl-session-foundation-20261017-01.json.gz) |
| Python regressions | `dc53ceb` | [Python](evidence/rtl-session-20261017/rtl-session-python-dc53ceb.json.gz) |
| Independent digital RTL simulation | `46db3cc`, producer `1b204b4` | [Simulator](evidence/rtl-session-20261017/buffered-rtl-sim-20261017-01.json.gz) |

The full, foundation and final Python listed inputs match committed `e4dd271`.
The simulator's broad archive inventory differs only in the later repaired full
proof-control helper, which its simulator path does not execute. Its actual
design, emitters and wrappers are unchanged, and both retained SV files were
rehashed and matched to the final full proof run. The earlier frontend-only
receipt remains accepted for its historical component scope; the manifest
records its later import/driver/test differences rather than promoting it to
final full-session evidence. Workspace differences in the two original dirty
documents are recorded separately.

Full local commands, generated certificates and failed probes remain under
`build/validation/` and `build/buffered-sram-artifact/`. Exploratory failures,
including the earlier whole-expression mutation normalization timeout and a
large non-sharing JSON checkpoint, remain local development artifacts and are
excluded from accepted gate evidence.

The earlier [controller reference note](rtl-session-controller-reference.md)
records a development stage; this report and the final accepted full receipt
supersede its then-open integration status.

The campaign adds proofs, artifact interpretation/certificate generators,
validation producers, tests and documentation. Existing engine semantics,
emitted RTL/ABI and physical wrapper sources are unchanged. The two documents
already dirty at intake remain untouched. Historical receipts and physical
artifacts remain unchanged. Commits are local; nothing was pushed or published.
The exporter independently verified all 2,607 baseline files; the only changed
pre-existing committed file is `Pinwheel.lean`, adding five proof-root imports.

## Remaining boundaries

This is a binary, sampled-edge proof and finite simulator qualification. The
trusted interpretation boundary includes restricted SV/wrapper parsing and
Yosys process normalization. Lean checks the imported equations and their link
to the typed source; it does not prove the general correctness of native
emission, CIRCT, Yosys or every Verilog construct. The independent simulator
provides additional finite evidence across a different execution path.

Digital SRAM correspondence uses an explicit single-port memory law. The closed
concrete digital-memory corollaries discharge that law for the supplied digital
model. Vendor macro timing, electrical behavior, metastability, asynchronous
input assumptions, clocks, SRAM silicon, synthesis mapping, placement/routing,
power and fabrication remain outside this campaign.

The generic session grammar requires concrete transport and actual admission
witnesses, and covers finite prefixes. The constructive witnesses derive those
guards for their selected diagnostic histories. There is no universal
termination or successful-peer theorem for arbitrary programs, or theorem that
every possible host request sequence has a source-session interpretation.
Hardware generation/transfer counters still saturate at 65,535; warm reload
requires room for reset and COMMIT, and logical cold-reset epochs are absent
from the wire ABI. These existing interface limits were not changed.

MISO and raw peer inputs are sampled before each clock edge; READY, busy and pads
are observed after it. The frozen receipt describes the pre-capture controller
state while capture clocks the controller again. Rejection is latched at command
dispatch. Wire OBSERVE exposes indexed status/RX diagnostics without a source
read identity field. The owned source-read interpretation and guarded RELEASE
do not establish stale-ID or cross-cold read authentication.
