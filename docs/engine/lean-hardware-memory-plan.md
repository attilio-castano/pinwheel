# Memory library and streaming accelerator campaign

The first reusable memory component will implement the existing exclusive
single-port command contract. The two existing RAM semantics must stay distinct:

| Existing module | Reusable behavior |
| --- | --- |
| `Hardware.Memory` | One enabled write and unconditional reads; read-first collisions; configurable modeled read latency |
| `Memory.Flops` | Decoded full-word writes and balanced combinational reads, proved against latency-zero memory |
| `Memory.Registered` | Output registers update on every edge, including writes; proved against latency-one memory |
| `Memory.SinglePort` | Exclusive idle/read/write: read updates Q, write holds Q, idle holds both memory and Q |
| `Memory.Sram` | A partial initialized-value model related to arbitrary initial physical memory; replicated read ports and broadcast writes |

`Memory.Registered` therefore cannot be used directly as an implementation of
`SinglePort.Contract`. Neither contract silently supplies reset, initialized
contents, response validity, backpressure or byte enables. Current capacities
are powers of two, so all address-bit patterns are legal.

## First implementation slice

1. Add a complete typed command interface: enable, write, address, write data
   and Q. Disabled commands decode to idle. Prove physical codec round trips.
2. Construct `CommandFlops` from the existing decoded word updates and balanced
   read mux. Update Q only on reads. Preserve the existing memory array on idle
   and preserve Q on idle and writes.
3. Prove the state transition for arbitrary input and register bits, then
   package both `SinglePort.Contract` and the shared `Implementation` certificate.
   Provide exact state encode/view correspondence without an initialization or
   reset assumption.
4. Check independent model/RTL replay, complete endpoint correspondence and
   state/output mutation rejection. Cover disabled writes, consecutive reads,
   same-address read/write/read sequences, all addresses and arbitrary initial
   arrays and Q.

The generic read mux currently lives in `Hardware.Execution.Memory`. Reuse it
first; a later move should preserve compatibility aliases and rerun its existing
clients. The command RAM adds no fictitious memory-clearing reset.

### Implemented command RAM

`CommandInterface`, `CommandFlops` and `CommandFlopsProofs` now supply the
interface, structural implementation and universal proofs above. `view` and
`encode` are inverse on every physical state. `contract` discharges
`SinglePort.Contract`; `implementation` uses the common hardware certificate
with `Valid = True`. `trace_correct` starts from arbitrary words and Q.
They are available from `Pinwheel.Hardware.Library`.

```sh
lake build Pinwheel.Hardware.Library
lake env lean -DwarningAsError=true --run test/MemoryCommandFlops.lean
lake env lean -DwarningAsError=true test/MemoryCommandContracts.lean
python3 scripts/check-memory-command.py --tag command-flops-local
python3 scripts/check-memory-command-artifact.py --tag command-artifact-local
python3 scripts/check-memory-command-artifact-negatives.py --tag command-negatives-local \
  --positive-report build/memory-command-artifact/command-artifact-local/report.json
```

The retained `build/memory-command/command-flops-01/report.json` passed four
address/data width configurations: 1/1, 1/8, 2/8 and 3/17. Across 1,412 edges,
an independent Python array oracle matched Lean structural replay and every
emitted RTL register plus pre/post-edge Q. Twelve actual RTL mutations were
rejected: ignored enable, reads on write edges and cleared held Q. Generic
synthesis used 8, 36, 106 and 430 cells respectively; these are not physical
area or timing results.

Synthesized RTL starts uninitialized. Full writes and a read establish its
state before Q is compared (1,396 checked edges). Unsynthesized RTL is also
checked throughout that prefix from explicitly chosen arbitrary words and Q.
The separate Lean oracle test covers 4,100 exhaustive state/input combinations,
9 directed edges and a 240-edge trace; the declaration audit checks 427 memory
declarations for standard axioms only. Semantic zero widths are tested in Lean;
the HDL emitter requires positive address and data widths.

Complete imported-RTL correspondence passed for the same four configurations
in `build/memory-command-artifact/payload-matrix-01/report.json`. The generated
`memory_trace` theorem relates every raw-input trace from arbitrary initial
words/Q to the command specification; `command_step` supplies the original
single-port command transition. Every register and output is included, and
the generated declarations pass the standard-axiom audit. Yosys and the
restricted JSON interpretation remain trusted.

`build/memory-command-artifact-negatives/payload-matrix-01/report.json`
binds that positive receipt and rejects an inverted output and an inverted
word next-state expression at Lean's semantic proof stage. Each rejection is
paired with a separately kernel-checked concrete mismatch. The earlier
constant-output experiment was rejected during parsing after dead-state
removal; it is retained as a failed harness attempt and is not counted as a
semantic negative control.

## Streaming adapter and accelerator

Add a request/response adapter with one outstanding read and a held response
under downstream stalls. Reset cancels pending responses while preserving the
array. Reuse the common typed implementation and stream handshake operations,
with a memory-specific snapshot ledger. Then move a bounded range from one
source memory through proved stream components into a separate destination
memory.

The central completion theorem should establish that after `N` completed writes,
each address in the destination range contains the transform of the corresponding
initial source value; all other destination addresses are unchanged. Assumptions
include initialized source coverage and nonwrapping ranges. Reset may leave a
written prefix, but must suppress stale responses and further writes from the
aborted transfer. Eventual completion requires explicit service assumptions.

The executable `Memory.StreamModel` is implemented and tested. It reuses Q as
the held response and adds one pending bit. Both reads and writes wait behind
a blocked response; an old response may retire while a new read is accepted.
The proved ledger records each read's pre-edge memory value and conserves it
as delivered responses plus at most one pending response. Writes have no
response. Reset masks both handshakes and preserves the complete memory state,
including Q, while starting a new response-accounting epoch. Its tests cover
6,424 exhaustive cases, 11 directed edges and a 240-edge trace.

`Memory.StreamInterface`, `StreamFlops` and `StreamFlopsProofs` now implement
the physical adapter and its all-state refinement. The circuit instantiates
the command memory through expression substitution and adds exactly one bit.
The fixed-initial-state reset certificate is not applied to its state-preserving
reset. Its raw-state tests cover 18,464 exhaustive cases plus 13 directed and
240 trace edges; the retained audit checks 753 memory declarations.

```sh
lake build Pinwheel.Hardware.Library
lake env lean -DwarningAsError=true --run test/MemoryStreamModel.lean
lake env lean -DwarningAsError=true --run test/MemoryStreamFlops.lean
lake env lean -DwarningAsError=true test/MemoryStreamContracts.lean
python3 scripts/check-memory-stream.py --tag stream-memory-local
python3 scripts/check-memory-stream-artifact.py --tag stream-artifact-local
python3 scripts/check-memory-stream-artifact-negatives.py --tag stream-negatives-local \
  --positive-report build/memory-stream-artifact/stream-artifact-local/report.json
```

`build/memory-stream/stream-flops-01/report.json` passed the four command-memory
configurations. An independent Python array/pending-bit oracle records accepted
read snapshots, delivered responses and reset epochs. Every emitted register
and pre/post output agrees; synthesized outputs agree after a reset and full
initial writes establish observable state. All twelve actual RTL faults were
rejected: ignored response stalls, dropped pending state and a word incorrectly
cleared by reset.

Imported RTL certification passed in
`build/memory-stream-artifact/payload-matrix-01/report.json`: 133 local
equalities and all 36 typed register/output endpoints across the four cases.
The composed theorems cover arbitrary-state traces, traces after protocol reset,
preservation of every memory word and Q, and clearing of pending. The matching
`build/memory-stream-artifact-negatives/payload-matrix-01/report.json`
rejects active-response inversion, pending/word next-state corruption and a
word erased by reset. Each rejection includes a kernel-checked concrete
counterexample. The RTL interpretation trust boundary is unchanged.

### First transfer controller

Use separate source and destination memories, a common address width, and
`Stream.Map wi wo` for the transform. That existing API already packages the
pure function, register-free expression and universal correctness proof.
The first reusable circuit has explicit source read-request/response ports and
destination write-request/ready ports. A composed theorem connects it to two
`StreamFlops` memories.

Runtime commands carry source base, destination base and an `a+1`-bit length.
Accept start only while idle. Check both nonwrapping ranges without truncated
addition: `length ≤ 2^a - base`. Invalid commands pulse error and send no memory
request; zero length pulses done immediately at its acceptance edge. A start
held valid is accepted again whenever ready, following ordinary handshake
semantics. Busy commands cannot replace the latched configuration.

`Memory.TransferRange` implements the checked range codec, nonwrapping and
injective indexing, and incremental destination-prefix update algebra.
`Patched` describes the current memory independently of its representation;
`patch_step` extends that invariant after one accepted write. The copy
specialization transforms a fixed source snapshot and preserves every
destination word outside the written prefix. It does not assume in-place
source stability. Tests cover 682 raw range encodings and 43,203 prefix checks,
including zero/full-depth ranges, all small source/destination arrays and
modular transforms. Its 84 declarations pass the standard-axiom audit.

The serial controller has Idle, IssueRead and Transfer phases. IssueRead waits
for the source read acceptance. Transfer couples source-response retirement to
destination-write acceptance and applies `Map` combinationally. Source Q holds
the payload under stalls; no additional payload register is needed. A completed
write increments the index and either issues the next read or pulses done.
Reset wins over every handshake, clears protocol state and preserves both
arrays/Q values. Unused physical phase encodings must have explicit safe
recovery behavior.

The main invariant relates each committed write to the initial source snapshot
and the destination's written prefix. The remaining destination addresses keep
their initial values. Reset preserves the committed prefix and cancels the
uncommitted read. Open-controller progress requires source request/response and
destination service assumptions; the concrete serialized two-memory composition
should complete in two edges per word after start acceptance.

A closed demonstration needs a host loader/readback interface so destination
storage remains observable after synthesis. That wrapper must drain host reads
before accepting start, block host traffic while busy and define host/start
arbitration. It is a separate step after controller and composition proofs.

External SRAM remains a supplied implementation contract. Digital trace proofs
do not independently qualify a macro's electrical behavior. Byte enables,
non-power-of-two depth, multiple outstanding reads and shared source/destination
storage are later extensions with explicit semantics.
