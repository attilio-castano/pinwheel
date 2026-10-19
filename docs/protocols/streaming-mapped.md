# Standard-cell correspondence for streaming sessions

This stage carries the programmable SPI, JTAG, stretched I²C and autonomous
UART results through an actual standard-cell mapping. It checks the mapped
frontend, both queue-depth cores, the package connections and the Tiny Tapeout
pad logic. Mapping adds no protocol-specific RTL, pins or host commands.

Fresh committed-source qualification and immutable export **passed** for source
and producer `7715ba61c9a837aa96916e823f65c8e7b6a653d9`. The
[evidence manifest](../research/evidence/streaming-mapped-continuation-20261017/manifest.json)
binds the accepted receipts, checked proof sources, native journals and complete
costs. The accepted scope is the two-state digital correspondence described
below; placement, electrical behavior and physical timing remain separate.

## What the proof connects

| Boundary | Evidence required |
| --- | --- |
| Source program and host session → typed circuit | Existing compiler, initialization, runtime, timing and ownership theorems |
| Typed circuit → emitted raw component | Fresh raw readback certificates covering every register and output |
| Raw component → preserved word hierarchy | Actual source-cell, input, output and complete flip-flop correspondence |
| Each mapped word module → its source operation | Actual Liberty functions and connected gates, checked by native Lean |
| Mapped frontend and core → package | Actual instance ports, feedback, raw inputs and direct clock connections |
| Package → mapped Tiny Tapeout interface | Actual mapped pad gates and complete engine/pad equations |
| Complete device → initialized sessions | The preceding certificates instantiated in the physical session factory |

The producers are [streaming_mapped_component.py](../../scripts/streaming_mapped_component.py),
[streaming_mapped_wrapper.py](../../scripts/streaming_mapped_wrapper.py) and
[streaming_mapped_composition.py](../../scripts/streaming_mapped_composition.py).
They generate candidate Lean definitions and proofs. A producer returning
success, a Yosys equivalence assumption or an operation's module name does not
establish the result: the native kernel must accept the generated joins and
their complete axiom audit.

The source word reader admits explicit unsigned operations and widths. The
mapping flow preserves their module boundaries and retains every source
flip-flop. The interpreter reconstructs instantiated module bodies, actual
port directions, widths, aliases, primitive pins and output roots. A word's
name or descriptor can suggest its expected operation; it supplies no Boolean
function. Each physical top-level instance uses its actual connected inputs.
Its output equation is proved before another instance can use it.

Arithmetic uses the actual mapped full-adder's sum and carry functions, checked
for all eight Boolean inputs, then a kernel-checked ripple connection proof.
Bitwise and mux proofs separate static pin renaming from small Boolean truth
checks. Wide comparisons and reductions normalize the actual gates into
checked Boolean clauses or trees with complete input coverage. They do not
enumerate all values of a wide word. These paths use structural proofs and
`decide +kernel`; `bv_decide`, `native_decide`, admitted proofs and custom
axioms are excluded. The audit includes private declarations and proof-bearing
definitions, allowing only `propext`, `Classical.choice` and `Quot.sound`.

## State, initialization and session scope

The component results are universal over every Boolean input and every packed
register value. They include every flip-flop D input and public output, rather
than checking only reachable states, a reset trace or externally visible pins.
The required retained inventory is 1,403 frontend bits plus 4,636 core bits at
depth two or 4,792 core bits at depth four: 6,039 or 6,195 bits per package.
There is no state quotient, constant-state assumption or omitted counter.

The generated namespaces are `Pinwheel.Artifact.StreamingMappedFrontend`,
`Pinwheel.Artifact.StreamingMappedCoreD2` and
`Pinwheel.Artifact.StreamingMappedCoreD4`. Their `step_correct` and
`observe_correct` theorems relate the interpreted mapped behavior to the typed
circuit for every field. Package and pad certificates compose those functions
without assuming that the two components already agree with the source.

The physical step, observation and finite-run equalities inherit that arbitrary
prestate scope. Concrete boot results additionally start with an arbitrary
package state and process an actual cold input and sampled upload waveform;
they derive installation instead of assuming a loaded image or VALID bit.
The concrete I²C boot uses the supported seven-row image. The concrete UART
boot APIs select `Q=4,12,128`. The broader UART source/compiler profile remains
`4≤Q≤128`; the three concrete boot waveforms do not by themselves prove a
physical upload waveform for every other rate.

Source runtime results retain their stated trace and admission conditions.
Ownership, exact acknowledgments, replay, retained faults and warm cancellation
are inherited from the checked session model. Progress requires the named
eventual host-service and peer-readiness conditions. Unbounded waits do not
become termination guarantees through mapping. UART frame results retain the
start/data/stop sample-center assumptions and the host-quiet condition. The
source [StreamingUARTFirstTerminal.lean](../../Pinwheel/Program/StreamingUARTFirstTerminal.lean)
also proves the first terminal prefix for every profile `4≤Q≤128`: every
strictly earlier processed prefix remains busy. Counting processed frame
inputs from the first raw LOW at index zero, a good frame first terminates at
`38*Q+4`, a bad stop at `38*Q+3`, and a false start at `2*Q+3`, under their
respective sample-center and quiet-host conditions.

The mapped public-BUSY corollaries include the actual cold/upload/START prefix
from arbitrary register contents, for the three concrete boot profiles
`Q=4,12,128`. They observe output bit 5 with the chip active and the host link
deselected, so pad masking cannot manufacture a BUSY drop. Each theorem proves
BUSY is high at every earlier frame prefix and first becomes low at the stated
prefix. The finite peer checks the corresponding edge chronology separately;
it does not supply a premise of the proof.

The final composition requires the following 22 declarations in **each** of
`Pinwheel.Artifact.StreamingMappedSessionD2` and
`Pinwheel.Artifact.StreamingMappedSessionD4`, making 44 concrete APIs:

| Scope | Required declaration names |
| --- | --- |
| Components and physical recurrence | `components_correct`, `physical_step_correct`, `physical_observe_correct`, `physical_run_correct` |
| Source runtime | `source_runtime_step_correct`, `source_runtime_run_correct`, `source_runtime_observe_correct` |
| Upload, continuation and reset | `initialized_upload_correct`, `initialized_runtime_correct`, `physical_warm_reset_correct` |
| Concrete I²C | `concrete_i2c_initialized`, `concrete_i2c_runtime`, `concrete_i2c_custody`, `concrete_i2c_progress` |
| Concrete UART | `concrete_uart_initialized`, `concrete_uart_runtime`, `concrete_uart_custody` |
| UART framing and quiet host | `uart_frame_correct`, `uart_false_start_correct`, `uart_bad_stop_correct`, `uart_host_quiet_correct`, `uart_arming_correct` |

The coordinator additionally requires `uart_first_terminal_correct`,
`uart_bad_stop_first_terminal_correct` and
`uart_false_start_first_terminal_correct` in each namespace. These six mapped
timing declarations bring the total to 50 checked APIs. They are generated by
[streaming_mapped_uart_timing.py](../../scripts/streaming_mapped_uart_timing.py)
and retain the three-profile concrete-boot boundary above.

These are checked declarations with their actual types. Their names do not
remove the premises of individual theorems. The final coordinator also checks
typed universal component equalities, complete imported dependencies and the
rejection of an injected private axiom.

## Interpretation assumptions

The restricted JSON and Liberty readers remain explicit trust boundaries,
alongside the selected Lean toolchain, Python, native runtimes and host system.
The cell library is pinned by SHA-256
`34163f3e7de9f854afac57332ba06f1739b78e7ac35660a8a5ddd39c570124ad`.
Its admitted scope is the 26 selected single-output combinational cell types
and `sg13cmos5l_dfrbpq_1`. The Boolean grammar admits declared identifiers,
constants, inversion, AND, OR, XOR and parentheses with explicit precedence.

[streaming_mapped_runtime.py](../../scripts/streaming_mapped_runtime.py) adds a
separate audit of the selected CIRCT and OSS CAD runtime files against their
fixed SHA-pinned archives. It streams regular archive members without
extracting them, checks every selected alias and its relative resolution, and
requires archive payloads, recorded tool identities and current installed bytes
to match. The worker, parent and exporter must independently reproduce this
narrow result as `cad_selected_archive_membership_verified=True`. Counts derive
from the selected runtime inventory rather than a fixed expected total.
Lean, Lake, Python and operating-system code remain outside these CAD archives;
unselected installed files have no membership claim. The broader historical
`installed_payload_archive_membership_proved=False` flag remains unchanged.

The sequential model is simultaneous positive-edge sampling. Every physical
flip-flop uses the direct top-level clock; `RESET_B` is tied to inactive HIGH.
Initialization is ordinary logic on D, not an assumed power-up value. The
interpreter refuses unsupported parameters or cells, latches, derived clocks,
clock-as-data, functional X/Z, undriven nets, multiple drivers and combinational
cycles. Inert netname metadata may contain X without making X a functional
value. Unknown hierarchy must be reconstructed from its definition; it cannot
be accepted as a black box with a useful name.

All claims are two-state digital claims. They do not model metastability,
analog thresholds, Verilog unknown propagation, setup/hold behavior, clock
distribution, asynchronous-domain safety or electrical pad behavior.

## Cost and independent checks

The proof-oriented mapping is measured as its own artifact. It preserves word
boundaries and all state bits, so its cell count and area must not be borrowed
from the earlier globally optimized mapping. That earlier cost-only mapping
removed or aliased some state bits and had no mapped equivalence certificate.

The complete cost inventory must include the mapped frontend, core, actual
package and outer pad gates, all program and queue storage, staging, CRC,
receipt cache and export state. [streaming_mapped_cost.py](../../scripts/streaming_mapped_cost.py)
counts actual cells and sums their areas from the pinned Liberty. This is a
standard-cell area sum, not a placed footprint. Its longest combinational path
is an unweighted gate count, not a delay or guaranteed Fmax. Earlier ABC
combinational Liberty estimates remain separately labelled estimates for
their own mapped artifacts.

Independent native simulation must consume the complete proved mapped device
and the selected cell models. Public-wire peers test protocol behavior,
receipt chronology and distinguishing mutations; their finite traces are
additional evidence rather than a replacement for universal equations.
Functional pin, logic, clock and state mutations must be labelled by the gate
that rejects them: structural parser refusal and kernel rejection are distinct.

## Accepted receipts and reproduction

All three accepted gates select the same source commit above. The full gate
regenerated its own partial raw input stage, mapped artifacts and proofs,
froze actual inputs before use, and checked source, tool/runtime and library
identities at closeout. The immutable export used tag
`streaming-mapped-export-7715ba6-20261017-01` and preserved the sealed UART
baseline, both intake documents and their combined patch.

| Gate and retained receipt | Accepted result |
| --- | --- |
| [streaming-mapped-full-7715ba6-20261017-01](../research/evidence/streaming-mapped-continuation-20261017/streaming-mapped-full-7715ba6-20261017-01.json.gz) | Three complete component joins, 176 word certificates, 50 session/timing APIs; final audit of 59,755 declarations and 38,632 theorems with standard axioms only; 3,521.367 seconds |
| [streaming-mapped-foundation-7715ba6-20261017-01](../research/evidence/streaming-mapped-continuation-20261017/streaming-mapped-foundation-7715ba6-20261017-01.json.gz) | 638 modules, 43,823 audited declarations, 25,060 theorems, 65 executable suites and 8 kernel suites; injected untrusted axiom rejected |
| [streaming-mapped-python-7715ba6-20261017-01](../research/evidence/streaming-mapped-continuation-20261017/streaming-mapped-python-7715ba6-20261017-01.json.gz) | 1,682 tests with 8 expected skips; 97.330 seconds for tests |

The mapped native diagnostic ran 28 processes with successful exits and
1,025,364 sampled wire edges. At each queue depth it checked 24 selected UART
cases, 10 I²C cases, one 32,768-bit duplex SPI transfer and one 4,097-bit JTAG
scan. The mapped UART set is a selected diagnostic; the separate sealed UART
corpus covers all 256 payloads at the three concrete rates. The actual mapped
sampler FF-pin control is distinguished by its one-edge-early public BUSY
transition. Complete binary trace hashes, lengths and sequential cycle IDs
are checked against the native process journals.

The accepted complete-device cost is:

| Queue depth | FF bits | Combinational cells | Total cells | Liberty cell area (µm²) | Unweighted gate depth |
| --- | --- | --- | --- | --- | --- |
| 2 | 6,039 | 28,415 | 34,454 | 717,340.9194 | 127 |
| 4 | 6,195 | 28,909 | 35,104 | 733,797.5274 | 127 |

The CAD membership audit matched 733 selected CIRCT files and 627 selected
OSS files, including three exact aliases to regular archive members. Its
limited provenance scope and remaining runtime assumptions are stated above.
The manifest SHA-256 is
`d50a079ef12df6ab4882266aeab676c2962c62bbed736e428f2612cfc286b6f4`.
Its export contains three compressed receipts and 21 compact proof, audit,
cost and journal files, plus the preserved intake patch.

Use a checkout at the accepted commit with the pinned native tools installed.
The full command below uses the locally retained pinned Liberty; adjust that
absolute input path if reproducing in another checkout. Every run needs a
fresh tag. The Foundation wrapper selects `HEAD`, so its checkout must be at
the accepted commit to reproduce this source identity.

```sh
python3 -B scripts/check-streaming-mapped.py \
  --tag morning-mapped-full-review-01 \
  --source-commit 7715ba61c9a837aa96916e823f65c8e7b6a653d9 \
  --producer-commit 7715ba61c9a837aa96916e823f65c8e7b6a653d9 \
  --liberty "$PWD/build/validation/streaming-mapped-full-7715ba6-20261017-01/inputs/cells.lib"
python3 -B scripts/check-foundation-snapshot.py \
  --tag morning-mapped-foundation-review-01
python3 -B scripts/check-python-snapshot.py \
  --tag morning-mapped-python-review-01 \
  --source-commit 7715ba61c9a837aa96916e823f65c8e7b6a653d9
```

The exporter deliberately refuses to overwrite the existing evidence
destination. New acceptance must retain fresh artifacts and receipts; these
exported receipts are historical evidence rather than inputs that replace a
new gate.

Placement, routing, extracted timing, CDC closure, physical signoff and silicon
operation remain separate work.
