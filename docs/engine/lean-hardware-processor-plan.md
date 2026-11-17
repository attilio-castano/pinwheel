# Processor integration contract

The processor is the next integration test for the library. This record freezes
the semantic target and first execution environment; decoder, mapping and device
contracts are developed before CPU construction.

## ISA target and execution environment

Use the official **Unprivileged ISA release 20260120, RV32I version 2.1**.
The [official specification PDF](https://docs.riscv.org/reference/isa/v20260120/_attachments/riscv-unprivileged.pdf)
is archived in the ignored build cache and pinned by `tools/riscv-isa.json`:
4,580,174 bytes, SHA-256
`06bb3c23074f72060a0ec061a80933af948cae7ceafdcd9d1fe177b05fd150bc`.
The manifest retains title, release, target chapter and CC-BY-4.0 attribution.
Fresh checkouts obtain the exact same source with:

```sh
python3 scripts/fetch-riscv-specification.py
```

The fetcher verifies existing and downloaded bytes and refuses to replace a
mismatched cache. Source identity and the execution-environment choices below are
fixed. Decoder, checked mapping and device implementations remain open gates.

Implement all 40 base instructions, including precise ECALL/EBREAK outcomes,
legal HINTs and conservative FENCE behavior. Keep `x0` zero while still performing
loads and faults whose destination is `x0`. Effective addresses wrap modulo
2^32. JALR clears target bit zero before alignment checks; untaken branches do
not raise target-alignment faults. FENCE reserved fields need their specified
conservative handling, rather than blanket illegal-instruction rejection.
These requirements come from the [RV32I chapter](https://docs.riscv.org/reference/isa/v20260120/unpriv/rv32.html).

The following are frozen project execution-environment choices, to be encoded explicitly:

| Concern | First implementation contract |
| --- | --- |
| Core | Single hart, multicycle, serialized memory access; polling peripherals |
| Reset | PC and integer registers zero; clear pending control and terminal status; preserve memories |
| Initialization | Program/image and initialized-data coverage are explicit loader assumptions |
| Address space | Distinct executable/readable code ROM and readable/writable nonexecutable RAM; checked disjoint regions and full access footprints before narrowing; map below |
| Data representation | Little endian; signed and unsigned byte/halfword loads; byte-masked stores preserve other bytes |
| Misalignment | Precise fatal data-access trap, checked before mapping; no partial store |
| Unsupported encodings | Precise terminal illegal-instruction event, while accepting legal base HINT/FENCE encodings |
| ECALL and EBREAK | Distinct terminal events with faulting PC; no implicit syscall ABI or privileged trap handler |
| Access failures | Explicit address/access-kind event; no destination-register write or partial memory/device effect |
| Scope | No privileged modes, interrupts, caches, speculation, CSRs or optional ISA extensions |

The code ROM is loaded only while execution is quiescent. Self-modifying code
and instruction-cache synchronization are outside this first environment;
[FENCE.I belongs to Zifencei](https://docs.riscv.org/reference/isa/v20260120/unpriv/zifencei.html).
TransferRange's nonwrapping admission rule must not replace ISA address arithmetic.

## Frozen memory map and MMIO contract

These addresses, capacities, permissions and fault choices belong to this
execution environment; they are not mandated by RV32I. ROM and RAM contain
`2^a` 32-bit words, default `a = 10` (4 KiB). ROM/reset base is zero; RAM and
peripheral bases are elaboration parameters. The default map is:

| Region | Inclusive default range | Permitted operations |
| --- | --- | --- |
| Code ROM | `0x00000000–0x00000fff` | Aligned instruction fetch; byte/halfword/word loads |
| Data RAM | `0x00010000–0x00010fff` | Byte/halfword/word loads and stores; no execution |
| GPIO | `0x40000000–0x400000ff` | Defined aligned word registers only |
| Timer | `0x40000100–0x400001ff` | Defined aligned word registers only |
| UART | `0x40000200–0x400002ff` | Defined aligned word registers only |

All other addresses fault. A checked layout requires word-aligned bases,
positive capacities, widened interval ends at most `2^32`, and pairwise
disjoint regions. After modular ISA address calculation, admission checks
alignment, the entire byte footprint and permissions before any local word-index
narrowing. Subword MMIO accesses, register holes and unsupported directions
fault with no device effect. MMIO never enters the RAM read-modify-write adapter.

| Register | Access | Defined operation |
| --- | --- | --- |
| GPIO `+0x00 INPUT` | Read | Sample 32 digital input bits on the access edge |
| GPIO `+0x04 OUTPUT` | Read/write | Read or replace the 32-bit output register |
| Timer `+0x00 COUNT` | Read | Read the pre-edge 32-bit cycle count |
| UART `+0x00 STATUS` | Read | Bits 0/1/2/3: TX ready, RX valid, overrun, framing error; other bits zero |
| UART `+0x04 TXDATA` | Write | Start transmitting the low eight bits if idle; upper bits ignored; busy faults |
| UART `+0x08 RXDATA` | Read | Consume and zero extend the buffered byte; empty faults |
| UART `+0x0c CLEAR` | Write | Write-one-to-clear error bits 2 and 3; other written bits ignored |

The timer increments modulo `2^32` on every nonreset edge, including CPU stalls
and terminal halt. No timer write, compare register or interrupt is provided.
UART has one active transmitter and one received-byte slot. A new valid arrival
to an occupied slot drops the new byte and sets overrun. Busy/empty faults keep
each instruction bounded; firmware polls status. With exclusive CPU ownership,
TX readiness cannot disappear without a CPU write, and RX availability cannot
disappear without a CPU read.

UART uses 8N1, LSB first, idle high, with an elaboration-time even clock divisor
`D ≥ 4`. A successful TX write starts a frame lasting `10D` clock periods. RX
checks start/stop samples, accepts complete bytes, and records framing errors.
The serial proof must specify its sampled digital input waveform. Analog input
synchronization, metastability and oscillator tolerance require separate physical
assumptions; no physical qualification is implied by this environment choice.

MMIO is a dedicated, always-ready single-edge operation on the current device
state and sampled inputs, returning success/value/effect or a precise fault.
It is not a held ready/valid response whose timer or GPIO payload can change
while blocked. The CPU's MMIO access, irreversible device effect and matching
retirement/trap share an edge. RAM retains the separate request/response adapter;
the core holds the pending instruction and asserts response-ready throughout
the RAM wait state, except during reset, so RAM acknowledgement/write and
retirement/trap also coincide.

Nonreset reads and admission checks use pre-edge state. Autonomous timer/serial
progression is determined from that same pre-edge state and combined with the
CPU operation. A newly started TX frame is installed on the commit edge and is
not advanced as though it had already been active. Consequently:

- Timer reads return the old count, then the counter increments.
- RX consumption plus arrival returns the old byte and retains the new byte.
- RX-empty reads concurrent with arrival fault; the new byte becomes available afterward.
- TX-busy writes concurrent with frame completion fault; TX becomes ready afterward.
- New overrun/framing errors win over simultaneous software clearing.
- Loads to `x0` still perform device reads, consumption and faults.

Reset takes priority over all access, retirement and autonomous activity. It
clears PC/registers, pending control and terminal status; preserves ROM, RAM and
RAM Q; clears GPIO output, timer, UART buffering/errors/serial control; and drives
TX idle high. It cancels pending work without completion, suppressing tick/arrival
processing on that edge. Prior stores and already transmitted serial bits remain
historical effects. Peripheral reset is an explicit event, not rollback.

## Fault ordering and program initialization

Use this priority: reset; fetch alignment then fetch permissions/range; decoder
legality and exact ECALL/EBREAK; instruction-specific checks; successful commit.
Data alignment precedes mapping, followed by MMIO size/register/readiness checks.
JALR clears target bit zero before the taken-target alignment check. A misaligned
taken jump/branch traps on that instruction and suppresses its link write; an
aligned but inaccessible target allows the jump to retire, then faults on the
following fetch at the target PC. Untaken branches do not check target alignment.
These target-fault distinctions follow the pinned RV32I chapter §§2.2 and 2.5.

Terminal records retain faulting PC, optional fetched instruction, cause and
relevant address/access kind. These are monitor outputs, not privileged CSRs.
Reserved or unsupported instruction encodings produce this environment's
illegal-instruction outcome; that policy is distinct from unspecified ISA
behavior for some reserved encodings. All legal base HINTs are accepted. FENCE
conservatively treats reserved fields as ordinary FENCE, ignoring unused rs1/rd
as required by §2.7. Serialized accesses allow it to retire after earlier accesses
complete; it does not wait for an accepted UART byte's final physical bit.

Program tests retain exact ROM images, placement, length and hashes, explicitly
filling unused ROM words with zero (illegal if executed). They explicitly load
every RAM word, initially zero except initialized data. Loading occurs only while
the CPU is quiescent with exclusive loader ownership, and execution starts only
after loading completes and pending memory work drains. Boot code establishes
stack/ABI conventions; reset registers remain zero. Warm reset preserves RAM;
reinitialization requires another loading operation. These image assumptions are
separate from the generic arbitrary-memory theorems.

## Checked address routing

`Processor.AddressMap` implements the frozen routing policy. `check` validates a
raw configuration and constructs a `Layout` carrying its bounds and disjointness
proof. `route` accepts only this checked layout and returns either a precise
misalignment/access fault or a `Hit` containing alignment, complete-footprint
and permission evidence. Fetch alignment is always four bytes; a malformed
non-word fetch then faults on permissions.

Local word indices and byte offsets are exact naturals. Their bounds justify
conversion to `BitVec` addresses, and reconstruction/no-alias theorems recover
the original full address from region, narrowed word address and offset. The
module also proves unique routing, exact fault classifications, successful
routing completeness, ROM/RAM/MMIO permissions and compatibility with the
byte adapter's alignment/within-word requirements. Peripheral word accesses
route throughout their windows; register holes/directions belong to MMIO.

```sh
lake build Pinwheel.Hardware.Processor.AddressMap
lake env lean -DwarningAsError=true --run test/ProcessorAddressMap.lean
```

The independent Nat-table oracle passes 6,885 layout checks, 130,428 accesses
and 21 explicit boundary/policy probes, including layouts ending exactly at
`2^32`, invalid wrapping/overlapping regions, permission failures and prior
architectural address wrapping. The 288-declaration audit uses standard axioms
only.

`Processor.AddressDecode` now implements the routing decisions as ordinary
typed expressions, reusing the generic `AddressWindow` full-footprint check.
Thirty-three-bit endpoints preserve the upper bound `2^32` before local address
narrowing. Static kind/size specializations and the runtime two-bit controls
have universal agreement proofs with `AddressMap.route`. Runtime kinds0/1/2
mean fetch/load/store; sizes0/1/2 mean byte/half/word. Either control3 returns
code7 for malformed controls. Ordinary result codes0–4 select the five regions,
5 is misalignment and6 is access fault. MMIO register holes remain device checks.

```sh
lake build Pinwheel.Hardware.Processor.AddressDecode
lake env lean -DwarningAsError=true --run test/HardwareAddressDecode.lean
```

The shared window/routing campaign checks 505 window configurations, 43,275
footprints and 103,888 runtime routing cases with an independent integer/table
oracle. Eleven actual expression faults are rejected; all 187 audited declarations
use standard axioms only. CPU integration and emitted RTL validation remain open.

## Instruction representation and decoding

`Processor.RV32I.Instruction` represents all 40 RV32I instructions and their raw
immediate fields. Byte offsets and sign extension are explicit: B/J encodings
append their implicit low zero before extension, and U immediates append twelve
zeros. `Processor.RV32I.Decode` checks the complete opcode/funct combination,
including full shift funct7 and exact ECALL/EBREAK words. Unsupported extensions
and the remaining reserved encodings are rejected by this execution environment.
Ordinary FENCE accepts its reserved operand/control fields and retains them for
lossless encoding; the execution layer supplies conservative ordering behavior.

The independent `Matches` relation characterizes accepted words. Universal
theorems relate decoding to that relation, prove unique decoding, both encode/
decode round trips and encoder injectivity, and specify the immediate fields.
These are pure instruction contracts. The structural decoder below implements
them with existing expression forms.

```sh
lake build Pinwheel.Hardware.Processor.RV32I.Decode
lake env lean -DwarningAsError=true --run test/RV32IDecode.lean
```

The independent Nat decoder/builder campaign checks 381,095 words, including
192,549 rejected illegal/unsupported words, every instruction kind, complete
opcode/funct control combinations, all 12-bit immediate fields and boundary/
neighbor cases. Nine concrete decoder faults are rejected. The audit covers
3,499 declarations with standard axioms only.

`Processor.RV32I.DecodeCircuit` supplies a reusable expression bundle and a
stateless circuit with one 32-bit input and nine outputs. Its six-bit tag is zero
for illegal/unsupported words; stable tags1–40 identify the complete instruction
kind. The other outputs are valid, rd/rs1/rs2, the reconstructed 32-bit immediate,
and FENCE mode/predecessor/successor fields. Invalid and inapplicable fields are
zero. FENCE's retained rd/rs1 are data, not architectural register-access enables.

Universal proofs establish exact agreement with `Decode` for every raw word,
tag inversion/uniqueness, zero-on-invalid behavior and expression substitution.
The independent Nat-field oracle checks 381,095 words, all forty tags and all
nine fields, plus 512 input/register-dependent binding cases. Fourteen actual
expression faults are rejected; all 824 audited declarations use standard axioms.

```sh
lake build Pinwheel.Hardware.Processor.RV32I.DecodeCircuit
lake env lean -DwarningAsError=true --run test/RV32IDecodeCircuit.lean
```

The generic `WordALU`, its RV32I adapter and `RegisterFile` now supply proved
arithmetic and pre-edge register access for the datapath. The register file
stores only x1–x31 and has reset-priority writes; its read outputs remain pre-edge
values until the clock edge, including during reset. Structural instruction
execution, physical CPU control and whole-CPU RTL evidence remain next steps.

## Executable instruction semantics

`Processor.RV32I.Semantics` defines architectural state with storage only for
x1–x31, so x0 is intrinsically zero. It specifies modular arithmetic, signed and
unsigned comparisons, low-five-bit register shifts, precise control transfer,
ECALL/EBREAK and illegal-instruction traps. JALR clears bit zero before checking
four-byte alignment; untaken branches do not fault on unused targets, and a
misaligned taken target performs no link write. Target accessibility remains a
later fetch check, as required by the frozen environment.

Loads, stores and FENCE produce explicit pending intents rather than invisible
effects. A context binds the original architectural state and raw word to its
decoded instruction. `Pending.Issued` additionally binds every captured address,
operand and destination to actual instruction execution; `step_pending_issued`
establishes it. Indexed replies prevent acknowledging one operation kind as
another. `respond` preserves the exact pending request on stalls and commits
writeback/PC or a precise trap only when the appropriate response is accepted.
Load extension is architectural, including loads targeting x0; stores and device
effects must be performed by their provider on the same accepted edge.

```sh
lake build Pinwheel.Hardware.Processor.RV32I.Semantics
lake env lean -DwarningAsError=true --run test/RV32ISemantics.lean
```

The independent integer/array oracle passes 174,023 instruction and response
checks and rejects 13 semantic faults. All 551 audited declarations use standard
axioms only. This establishes instruction semantics and response-commit lemmas,
not a processor implementation: fetch checks, memory/device effects, response
ownership, reset and FENCE service remain controller/integration obligations.

## Structural execution datapath

`Processor.RV32I.ExecuteCircuit` composes the instruction decoder and word ALU
as a reusable expression bundle with four inputs and twelve outputs. The inputs
are the raw instruction, PC and two pre-edge source operands. Five result classes
select immediate retirement, pending load, pending store, pending FENCE and trap.
The remaining fields carry next PC, writeback, memory intent or precise trap data.
Inactive fields are zero. Loads targeting x0 still produce a complete memory
intent, and misaligned taken targets suppress link writeback.

Universal evaluation covers arbitrary instruction/PC/operand bits. Architectural
correspondence additionally binds the PC and operands to the architectural
register file at the decoded source indices. `circuit_retirement` reconstructs
the entire resulting architectural state from actual next-PC/writeback outputs.
`circuit_pending` and `circuit_load` recover actual memory intent and destination,
and `circuit_trap` recovers the precise cause, address and unchanged origin.
Expression substitution preserves these results for larger datapaths.

```sh
lake build Pinwheel.Hardware.Processor.RV32I.ExecuteCircuitProofs
lake env lean -DwarningAsError=true --run test/RV32IExecuteCircuit.lean
```

The independent Nat/Int oracle checks 231,148 raw cases, including 140,874 illegal
words, all forty instruction kinds and all twelve output fields. It includes
663 x0 loads and 5,289 target-alignment faults. Another 3,072 coherent register-array
cases, 100 dependent program steps and 512 binding checks cover operand overlap,
loops and links. Twenty-two actual expression faults are rejected. All 636 audited
declarations use standard axioms only. The physical core below composes this
datapath with the register file and controller. Connected memory/device effects
and whole-system RTL validation remain integration work.

## Serialized controller and architectural events

`Processor.CoreModel` gives the instruction semantics an explicit cycle protocol:
fetch request, owned fetch response, execution, data request, owned deferred data
response, local FENCE service and terminal trap. The default boot PC and all
registers are zero. Fetch alignment is checked before offering a request;
permission/range faults remain the fetch provider's responsibility. Pending data
retains `Pending.Issued` and the unchanged origin state.

Data service has two explicit paths. Deferred service accepts a RAM intent and
later completes it on an owned response edge. Atomic service delivers the reply
and retires/traps on the request edge, allowing MMIO effects to occur at the same
architectural commit point. Unowned response inputs are ignored. Reset suppresses
offers/completions, cancels ownership and resets the CPU; the connected providers
must synchronously cancel their pending replies while preserving memory. Untagged
replies cannot distinguish a stale response offered after a later new request.

The fixed event stream retains raw instruction words, actual completion path,
intent/reply and resulting architectural state. `Meaning`/`Rule` specify event
legality through the instruction semantics independently of the controller step.
Event refinement, exact architectural-state replay and no-event/no-update are
proved from the controller invariant. Cancellation-aware ledgers account for
fetches, deferred requests and instructions. `word_conservation` additionally
preserves the ordered raw-word sequence through completion, cancellation and
the single held instruction; it does not identify ROM contents independently.

A decreasing rank proves completion within five supplied service opportunities
from fetch-request state. Reset is excluded; external readiness and response
delivery are not assumed inevitable. Terminal traps remain quiet until reset.
FENCE receives local service after all serialized prior accesses complete and
does not wait for UART physical transmission.

```sh
lake build Pinwheel.Hardware.Processor.CoreModel
lake env lean -DwarningAsError=true --run test/ProcessorCoreModel.lean
```

The campaign checks 27,720 adversarial protocol edges and 9,600 independently
scheduled integer/array program edges, including repeated raw words and reset
cancellation. Fourteen semantic faults are rejected; all 729 audited declarations
use standard axioms only. The oracle chooses traffic from its own numeric
controller and changes integer RAM only on acknowledgement. This is a pure core
model refined to the local ISA semantics. The physical core now implements this
cycle contract. Actual ROM/RAM/MMIO provider correspondence, external ISA
differential validation and RTL/artifact proofs remain integration gates.

## Physical serialized core

`Processor.CoreCircuit` composes the proved decoder/execution bundles and the
generic register file using expression substitution. Thirty-one stored integer
registers and six controller registers hold phase, PC, instruction and precise
fault metadata. Seven phases implement fetch offer/reply, execution, data
offer/reply, local FENCE and terminal trap. Reserved phase 7 holds without effects
until reset. A held instruction and unchanged architectural registers keep data
requests stable through stalls.

`CoreInterface` has twelve input and thirty output ports. Outputs expose fetch
and data handshakes, actual retirement/writeback, immediate traps and held
terminal faults. Inactive output fields are zero. Atomic data service completes
on the request edge, while deferred service completes on response acceptance.
Data fault code 1 is misalignment and codes 2/3 are access faults. Loads to x0
still access the provider. FENCE retires locally without a register write.

`CoreCertified.implementation` proves every next-state register and output
against `CoreModel` under an explicit representation invariant. The projection
erases inactive instruction/fault metadata and reconstructs pending provenance
from the held instruction and architectural state. Coverage represents every
valid controller-model state. Synchronous reset recovers every raw register image,
including reserved phases, and clears all thirty-seven physical registers.
Finite trace and final-state equality follow through `DecodedImplementation`.
Separate request-stability proofs show that bus-facing outputs depend on reset
and held state independently of response/service pins.

```sh
lake build Pinwheel.Hardware.Processor.CoreCertified Pinwheel.Hardware.Processor.CoreCircuitRequests
lake env lean -DwarningAsError=true --run test/ProcessorCoreCircuit.lean
```

The integrated audit covers 805 declarations, including the complete interface,
public/private core proofs and test helpers, using standard axioms only.
The controller-oracle campaign checks 6,248 complete register/pre/post-output
edges, eight arbitrary-register phase/reset fixtures and five actual expression
faults. Cases include atomic/deferred service, all raw data fault codes, unowned
replies, stalls, PC wraparound and reset during each instruction stage.

The core certificate takes provider values as explicit inputs. Connected ROM
contents, RAM/MMIO ownership, actual architectural event transport and external
ISA agreement have their own obligations. Artifact transport theorems take a
complete correspondence certificate for the actual imported RTL as a premise.

## Connected ROM/RAM/MMIO model

`Processor.SystemModel` connects the serialized core to a checked ROM image,
the exclusive byte-RAM adapter and atomic MMIO. ROM words are supplied explicitly.
RAM words and Q may start arbitrarily. `SystemModelProofs.Valid` combines core
validity and the RAM snapshot invariant with exact fetch and deferred-request
ownership. Initial states satisfy it, every edge preserves it and reset recovers
arbitrary system states while retaining RAM words and Q.

`ram_response` derives the actual completing value from the addressed RAM word.
`ram_completion` binds that request/response and memory effect to the same core
completion edge. `ram_completion_count` excludes orphan RAM completion events.
`mmio_completion` binds the actual device request and pre-edge response to atomic
core completion, with autonomous timer/serial events recorded afterward.
Finite core/RAM event paths, complete MMIO replay and the actual RAM-write fold
through reset connect the component histories.

```sh
lake build Pinwheel.Hardware.Processor.SystemModelProofs
lake env lean -DwarningAsError=true --run test/ProcessorSystemModel.lean
```

The independent numeric firmware/provider oracle checks 8,000 firmware edges,
2,448 fault/boundary edges, 25,920 reset/restart edges and 5,152 fabricated-state
reset/restart edges. It compares complete core, fetch, RAM/Q/pending, device,
output and event state, including an occurrence ledger for repeated requests.
Ten actual composition faults are rejected after identical positive fixtures
pass. All 415 audited declarations use standard axioms only. This closes provider
ownership and effect accounting at the executable model layer. Structural system
correspondence, an explicit loader and firmware-driven RTL validation remain
the next integration gates.

`Memory.ByteAdapterLoader` now provides the physical loading primitive around
the existing byte-RAM registers. Exclusive loader mode masks adapter responses
and cancels pending CPU work. Accepted writes update full words, preserving Q
and retained metadata. External reset blocks loading and retains memory. Its
all-raw step/output and reset certificates, 7,680 independent integer-array edges
and five actual expression-fault controls establish the component behavior.
The system wrapper must hold the core quiescent, load the complete image and
release execution only after coverage is established.

## Structural system and emitted firmware replay

`Processor.SystemCircuit` composes the existing physical core, byte-RAM adapter,
atomic MMIO and three fetch-response registers through `SystemWiring`. Its ROM
is an explicit elaboration-time function. The four-word RAM example has sixty
registers, six external inputs and thirty-seven outputs. Serial byte events
remain frontend inputs at this integration boundary.

`SystemExport` retains the four component modules and exposes every raw register
through a typed tap. The generated top contains named connections and wire
declarations. The bus uses the canonical `SystemWiring` expressions. Universal
proofs establish that cached staged evaluation has the same complete next state,
outputs, finite traces and final raw state as `SystemCircuit` for arbitrary raw
bits. Actual feedback uses the core's request subset, with a proof that response
inputs cannot change those request endpoints. The 225-declaration standard-axiom
audit and 128 dirty-state/control cases exercise the complete bus and register map.

```sh
lake build Pinwheel.Hardware.Processor.SystemExportProofs
lake env lean -DwarningAsError=true --run test/ProcessorSystemCircuit.lean
python3 -B test/test_processor_system_boot.py
python3 -B scripts/check-processor-system-boot.py --tag emitted-boot-local
```

The thirteen-instruction byte program reaches EBREAK after fifty-two edges,
including its first reset edge. It retires twelve instructions, performs one
byte store, checks signed/unsigned loads and an x0 load, reads back GPIO output,
samples the pre-edge timer and executes FENCE. The emitted RTL matches all sixty
post-edge registers and all thirty-seven pre/post outputs on every edge.
Four actual RTL changes corrupt active writeback, retired PC, RAM store commit
and GPIO store commit. Each produces a concrete mismatch after its complete
binary trace passes parsing and its active condition is checked. Eleven portable
tests reject malformed traces, descriptor omissions, register aliases and
same-width wiring swaps.

`build/processor-system-boot/emitted-boot-01/report.json` records nineteen
successful commands, eighty-four source hashes, forty-six tool/runtime hashes
and fifty-one retained artifacts. Its SHA-256 is
`da527a3481192b16f26944667696c6cea3eeb38892f9d05dba71e656d46d345b`.
This campaign explicitly forces all sixty startup registers, including nonzero
RAM words and Q. It validates emitted RTL from that supplied image. Reset-driven
loading and synthesized firmware replay are covered by the cold-loading campaign
below. Whole-system model correspondence and an imported-system artifact
certificate remain open gates.

## Cold reset, loading and synthesized firmware

`Processor.LoadableSystem` holds the core, fetch path and MMIO in reset throughout
exclusive loader mode. Its RAM uses `ByteAdapterLoader`, with external reset
blocking writes and ordinary loader edges accepting full words. Two status
outputs expose loader readiness and execution release. The wrapper retains the
same sixty registers and adds four loader inputs. Complete staged step/output,
trace and final-state equality are proved for arbitrary raw state. The four-leaf
export proves agreement of every bus input and fetch update with the canonical
wrapper, including the distinct external/effective reset paths.

```sh
lake build Pinwheel.Hardware.Processor.LoadableSystemStagedProofs \
  Pinwheel.Hardware.Processor.LoadableSystemExportProofs
lake env lean -DwarningAsError=true --run test/ProcessorLoadableSystemCircuit.lean
python3 -B test/test_processor_loadable_system_boot.py
python3 -B scripts/check-processor-loadable-system-boot.py --tag cold-boot-local
```

The cold firmware campaign performs two external resets and four accepted loader
writes before releasing the processor. Emitted and flattened generic synthesized
RTL both match the fifty-nine-edge trace across all thirty-nine external pre/post
outputs. The testbench drives clocks and inputs from initially uninitialized DUT
registers. The synthesis gate checks both graphs for initialization attributes
and initialization cells.

Raw emitted state becomes defined through reset, explicit loader writes and
normal request capture. A fixed schedule derived from those handshakes checks
3,407 register observations and leaves 133 earlier RAM/Q/inactive metadata
observations unconstrained. All sixty registers are defined and checked from
cycle 17 onward. External observations require complete binary values on every
edge. The complete trace must pass parsing before a semantic fault is reported.
Five actual RTL corruptions exercise loader data, active writeback, retired PC,
RAM store commit and GPIO store commit. Thirteen portable tests exercise topology,
definedness, parser and mutation-witness failures. The combined wrapper/export
audit covers 183 standard-axiom declarations and 256 dirty-state feedback cases.

`build/processor-loadable-system-boot/cold-boot-01/report.json` records twenty-four
successful commands, ninety-six source hashes, forty-six selected CAD tool/runtime
hashes and seventy-four retained artifacts. Its SHA-256 is
`fa46b14071ed5268b4f29c445a9faa1731af64986e4b4be95caea3b632294476`.
Generic synthesis contains 6,800 cell records, including four `$scopeinfo`
records. Comparative area/timing and imported-system artifact correspondence
remain open. The native Lean compiler boundary is recorded separately by the
FastEmit provenance campaign.

## Atomic peripheral model

`Processor.MmioModel` implements the frozen GPIO, timer and UART-register
contract as one atomic accepted CPU operation per edge. It assumes checked
word addressing and has no response backpressure. Reads sample the pre-edge
state. CPU faults preserve CPU-controlled state, while independent timer and
serial effects still occur on that edge. Reset clears all device state and
suppresses the CPU response, tick, arrival and completion effects.

The ordering is CPU access, timer tick, completion of a pre-existing TX byte,
RX arrival after any CPU consume, then new framing error. This gives the specified
consume/arrival, busy/completion and W1C/new-error behavior. Serial completion,
byte arrival and framing errors are explicit frontend inputs; the model does not
yet derive them from UART wires.

Fixed events retain the actual request, sampled GPIO and response, plus timer,
serial and reset effects. Checked replay validates responses and event
preconditions and reconstructs the entire peripheral state across arbitrary
histories. Initial coverage and event refinement are proved independently of
CPU progress: timer ticks do not establish instruction retirement.

```sh
lake build Pinwheel.Hardware.Processor.MmioModel
lake env lean -DwarningAsError=true --run test/ProcessorMmioModel.lean
```

The independent oracle passes 49,152 register accesses, 34,944 simultaneous/
reset edges and 8,192 cross-reset history edges. Fourteen concrete result/event
corruptions are rejected; all 394 audited declarations use standard axioms only.
`MmioInterface`/`MmioCircuit` now implement this contract with eleven inputs,
seven outputs and eight registers. Request-ready is deasserted only during reset;
response-valid and the response value belong to the same atomic operation edge.
Raw device selector3 produces a register-hole fault with no CPU effect while
ordinary timer/serial activity continues. Unused response codes/data and inactive
TX output data are zero. All outputs are masked during reset; all eight registers
clear at the reset edge. Inactive TX/RX storage bytes otherwise retain their bits.

`MmioCircuitProofs` proves complete step/output projection for every raw state
and input, with `DecodedImplementation.Valid = True`. The noninjective view
forgets inactive byte metadata; exact reset and physical retention proofs are
separate from that projection. Actual response pins feed event extraction.
Transport to `MmioModel` events explicitly requires an admitted device selector
(or reset), so a malformed selector's visible fault is never silently reinterpreted
as a legitimate model request. Trace/final-state and admitted-event replay are
universal finite-history theorems.

```sh
lake build Pinwheel.Hardware.Processor.MmioCircuitProofs
lake env lean -DwarningAsError=true --run test/ProcessorMmioCircuit.lean
```

The independent Nat/array oracle checks 28,672 raw control/state edges and 8,192
history edges, every post-register and every pre/post output, actual responses,
admitted events and retained metadata. Nine actual expression faults are rejected;
all 670 audited declarations use standard axioms only.

`build/processor-mmio/mmio-matrix-01/report.json` passes independent replay of
1,117 edges in both emitted and synthesized RTL, plus 144 emitted raw-state edges
across sixteen dirty startup images. The integer/ordered-event oracle checks
all eight emitted registers and all seven pre/post outputs. Synthesized replay
starts with a synchronous reset and forces no registers; raw emitted segments
cover otherwise unreachable startup values such as the timer's wrap boundary.
The campaign covers all 512 device/register/direction combinations, simultaneous
events, invalid selectors and reset. Each nonreset operation has exactly one
atomic response, including faults; timer ticks are counted separately.

Twelve actual RTL faults produce concrete mismatches in complete binary traces.
Unknown values, malformed/truncated traces and tool failures do not count as
negative success. Eighteen portable oracle/driver tests pass. The receipt closes
45 source, 46 recorded CAD-tool and 206 artifact identities and all 54 commands.
The 497 generic cells are a resource measurement, not a matched baseline or timing
result. Serial frontend events remain input pins.

```sh
python3 scripts/check-processor-mmio.py --tag mmio-local
```

`MmioRefinement` transports actual response pins and admitted event histories
through an explicit complete `Artifact.Correspondence`. Its corruption test
changes the physical timer-read value, checks failed replay and proves that this
changed circuit cannot carry the correspondence certificate. The transport audit
covers 22 declarations with standard axioms only.

`build/processor-mmio-artifact/mmio-artifact-01/report.json` now supplies the
certificate for the emitted MMIO RTL. Eight registers and seven output endpoints
are covered by 82 local equalities. Arbitrary-state trace/final-state projection,
reset clearing/masking, actual responses and admitted-event replay are checked
in the generated final module. The 891-declaration audit uses standard axioms.
The receipt closes 56 source, 48 recorded CAD-tool and 38 artifact hashes.

`build/processor-mmio-artifact-negatives/mmio-negatives-01/report.json` rejects
five actual RTL faults through semantic proof failures and kernel-checked
counterexamples. The controls cover a faulting GPIO write, overwriting full RX,
clearing a new framing error, returning the post-tick timer and retaining GPIO
on reset. Each witness checks all eleven inputs, eight registers and seven
outputs on both source and imported graphs, then the differing endpoint values.
The run closes 57 source, 48 tool and 131 artifact hashes and binds a copy of the
complete positive receipt. Parser errors and resource failures cannot count as
semantic rejection.

```sh
python3 scripts/check-processor-mmio-artifact.py --tag mmio-artifact-local
python3 scripts/check-processor-mmio-artifact-negatives.py --tag mmio-negatives-local \
  --positive-report build/processor-mmio-artifact/mmio-artifact-local/report.json
```

These certificates cover the imported unsynthesized binary RTL under the existing
Yosys `proc`/`pmuxtree` and restricted JSON interpretation boundary. Lean is
version-pinned. UART framing and processor integration remain open.

## Sampled digital UART model

`Hardware.Uart.Model` supplies a reusable 8N1 frontend model parameterized by a
checked even divisor D of at least four. Accepted TX bytes drive start-low after
the acceptance edge, followed by eight LSB-first data bits and stop-high. Universal
theorems give exactly ten D-period symbols and completion on the closing edge.
Busy offers cannot replace a frame, and completion returns to idle before a later
offer can be accepted. Ordered accepted/completed/canceled/pending byte histories
account for reset and repeated equal bytes.

RX validates start at D/2, samples data bit k at D/2+(k+1)D and checks stop at
D/2+9D. `RxSchedule` states equalities on the sampled input waveform, from which
decoding and absence of early arrival follow. A canonical periodic 8N1 waveform
satisfies that schedule. A high start-midpoint sample is ignored as a glitch.
A low stop sample emits one framing error and waits for high before rearming.
Reset suppresses pulses, clears both machines and drives TX idle-high.

```sh
lake build Pinwheel.Hardware.Uart.Model
lake env lean -DwarningAsError=true --run test/HardwareUartModel.lean
```

An independent TX bitstream/RX countdown oracle checks all 256 bytes at divisors
4, 6, 10 and 32 over 392,192 frame edges. It also checks 72,034 malformed-frame,
reset, back-to-back and randomized edges, plus 65 timing-parameter cases.
Ten executable faults are rejected after the unchanged model passes each exact
mutation fixture, adding 1,310 positive fixture edges. All 411 audited declarations
use standard axioms only.

`Uart.Structural` now implements this model with six physical registers and
four input/six output pins. Counters have width `log2(10D)+1`, with a universal
strict bound on the frame endpoint. RX uses fixed sample-count comparisons and
TX uses fixed symbol thresholds. Step/output correspondence is proved under the
phase/counter invariant. Every raw edge establishes that invariant, while malformed
units suppress spurious completion/arrival/error events and recover their active
control. Separate reset proofs clear all raw storage and drive TX idle-high.

```sh
lake build Pinwheel.Hardware.Uart.CircuitProofs
lake env lean -DwarningAsError=true --run test/HardwareUartCircuit.lean
```

The independent physical oracle checks 49,152 raw edges, 87,152 complete-frame
edges, 34,470 race/history edges and 1,544 positive fault fixtures. Every register
and pre/post output is checked. Ten actual expression faults are rejected at each
divisor 4, 6, 10 and 32. All 693 audited declarations use standard axioms only.

`Processor.SerialModel` now composes the MMIO model and sampled UART. Its
CPU-only TX update supplies the UART offer on the same edge as an accepted
TXDATA write. Completion clears the held MMIO slot together with the active
frame. A busy write on that edge faults before completion clears the slot.
RX arrivals enter the receive slot after software consumption, with explicit
accepted/dropped events and error-clear priorities.

Universal proofs establish ownership preservation, arbitrary-state reset,
same-edge acceptance, completion clearing and ordered TX/RX histories. Repeated
equal bytes retain distinct admission occurrences. The actual CPU/timer/serial
event history reconstructs the full device state across resets.

```sh
lake build Pinwheel.Hardware.Processor.SerialModelProofs
lake env lean -DwarningAsError=true --run test/ProcessorSerialModel.lean
```

An independent numeric MMIO dispatcher and wire-period/countdown UART oracle
check 287,688 complete-state, pre/post-output and event edges. The campaign covers
all 256 bytes at divisor 4, boundaries at divisors 6/10/32, reset cuts, repeated
equal transmissions, full-duplex races and wrapping timers. Ten actual composition
faults are rejected after 474 unchanged baseline fixture edges pass. All 189
audited declarations use standard axioms only.

Structural serial composition and emitted UART RTL remain integration steps.
Synchronous digital samples, input synchronization, metastability and oscillator
tolerance remain explicit environment assumptions.

## Reuse and missing library contracts

Reuse typed `Expr`/`Circuit`, complete interfaces, register banks, whole-word RAM
implementations, request/response accounting, reset preservation, hierarchy,
`Implementation`, and imported RTL correspondence.

`Memory.ByteAccess` now supplies pure little-endian word operations, raw
size/alignment classification, sign extension and byte-preservation/readback
proofs. `Memory.ByteAdapterModel` now adds one-outstanding transactions, fault
no-access, request/response accounting and reset cancellation around owned word
RAM. A store's memory effect coincides with response acceptance; merely offering
or stalling that response performs no write. Its physical circuit now has
universal state-projection, reset and snapshot-invariant proofs; emitted and
synthesized RTL replay passes three depths, and imported unsynthesized artifact
certificates cover all 50 state/output endpoints plus actual-event replay and
reset recovery. Four actual RTL faults fail semantic proofs with kernel-checked
counterexamples. A RAM read-modify-write implementation requires
exclusive ownership and must not be reused blindly for MMIO. GPIO, timer and
UART need separate observable-effect implementations for the frozen contract above.

`Memory.ByteAdapterEffects` proves the pure RAM adapter's atomic completion
events, including actual read values, stores and faults. Replaying them
reconstructs final memory contents under the snapshot invariant; reset preserves
prior stores and cancels pending work without a completion event. This gives a
component-level event contract to reuse, not a CPU architectural relation.
`ByteAdapterRefinement` now transports it through the physical circuit using
actual response pins and retained requests, with arbitrary-memory initial
coverage and reset recovery. Imported-RTL transport still requires a complete
artifact correspondence certificate as an explicit premise, now discharged by
the three-depth byte artifact campaign.

Keep `Timed.Refinement` for RTL-to-cycle-model equality. `Timed.Events` now
supplies the generic event-path refinement for internal cycles, fixed extraction,
finite-prefix safety, initial coverage and a separate finite service-count bound.
The transfer example checks actual memory effects and completion/abort markers;
it does not establish the CPU-specific architectural relation. Events must expose
actual reads, writes, device effects, retirement, traps, reset and environment
changes. Fixed extraction from observations, initial-state coverage, instruction
accounting and architectural-state agreement prevent a vacuous retirement proof.

A store or device effect may not be hidden until a later retirement pulse. Align
irreversible effects with architectural commit in the first implementation, or
prove a separate linearization theorem with a pending-instruction abstract state.
Reset between effect and notification must preserve the already-performed effect.
Timer ticks occur during CPU stalls too; simultaneous sampling and ticking need
an atomic edge specification or a proved equivalent ordering.

Finite event-prefix safety and progress are separate theorems. Progress targets
instruction retirement or trap, not merely a timer event. It needs a decreasing
internal rank plus independently stated memory-service assumptions; bounded
service yields a cycle bound.

## Implementation gates

1. Specification hash, execution environment, memory map, fault priorities and
   reset/effect ordering are frozen above. The checked map and decoder contracts
   are implemented and independently tested. Structural address routing is
   proved; structural instruction decoding is also complete.
2. Byte-access preservation, fault atomicity, decoder coverage and executable
   instruction semantics are proved. Structural byte RAM, MMIO and digital UART
   components are proved. Their complete processor/serial composition remains.
3. Complete physical core cycle refinement and arbitrary-state reset recovery are
   proved. Connect them through provider ownership and actual architectural events
   to the system's architectural and conditional-progress refinements.
4. Differentially replay architectural effects against pinned
   [Sail](https://github.com/riscv/sail-riscv) or
   [Spike](https://github.com/riscv-software-src/riscv-isa-sim), with an explicit
   environment adapter; run applicable [architecture tests](https://github.com/riscv/riscv-arch-test)
   and record exclusions.
5. Extend RTL replay and artifact correspondence through memory effects,
   retirement and reset. Include actual corruptions of sign extension, `x0`
   access handling, JALR alignment, byte stores, duplicate effects and stale responses.
6. Run loaded polling programs using the peripheral contracts and compare synthesis
   with a straightforward independent implementation under matching constraints.

The core model's finite-prefix architectural refinement does not establish a
physical processor implementation, external ISA compliance, physical timing or
fabrication result.
