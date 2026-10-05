# Initialized continuous UART package proof plan

Planned and implemented 2026-09-30 after opening
[draft PR 8](https://github.com/attilio-castano/pinwheel/pull/8) against `main`.
The starting candidate is commit `07be98c`. All six proof checkpoints below are
kernel checked, and fresh integrated validation passed on 2026-10-05. The
[initialized session study](../protocols/uart-session.md) owns the implemented
claim, proof APIs and new receipts. The original
[UART study](../protocols/uart-supervisor.md) retains its delivered circuitry and
historical evidence boundaries.

| Completed checkpoint | Proof owners |
| --- | --- |
| 1. Package transport | `PairedStreamPackage` |
| 2. Initialized upload and ARM | `PairedStreamBootstrap`, `PairedStreamOwnership`, `PairedStreamMailboxInit`, `PairedStreamArm` |
| 3. Continuous quiet session | `PairedStreamSession` |
| 4. First-edge and delay alignment | `BufferedSupervisorPhase`, `PairedStreamArm`, `PairedStreamUART` |
| 5. Declared lifecycle and immutable origins | `PairedStreamDormant`, `PairedStreamLifecycle`, `PairedStreamOrigin`, `PairedStreamProgram` |
| 6. Pin timing and candidate transport | `PairedStreamUART.initialized_continuous_uart`, `PairedStreamProgram.retained_initialized_lifecycle` |

## Target claim

Starting from arbitrary represented power-up state, an actual reset/release
sequence and certified upload establish a UART boundary. For every finite
prefix of the declared lifecycle, the emitted `paired-stream` package has the
same observations and result receipts as the composed reference. Resident
segments and STOP use the independent UART receiver, supervisor policy and
retained-result model. Initial power-up and later reset/upload edges use the
generic package reference. Arbitrary power-up outputs are not interpreted as
UART results, and a new certified boundary establishes each subsequent epoch.

Initialization and certified serial upload must establish the relation. A
preservation theorem must then derive core/receiver correspondence, effective
controls, program ownership, memory coverage and mailbox behavior at every edge.
These facts must not remain assumptions supplied separately on every edge.

Safety and reception progress are separate claims. The safety theorem permits
arbitrary receive values, host consumption and overrun clearing. The later
wire-level reception theorem adds the existing sufficient timing and sampler-age
conditions, and quiet consumed commands during uninterrupted rearm windows.

## Explicit domain and external premises

- A lawful `Memory.SinglePort.Contract` for the exact memory implementation,
  including contents and registered Q. Initial contents and Q are arbitrary.
  Derive requested data from accepted writes and proved read coverage; never
  assume the desired Q value on each edge.
- The actual sampled reset/release and serial command delivery contracts.
  Establish initialization through pins and adapter state rather than assuming
  the controller and mailbox already equal their reset states.
- A canonical UART program and its paired-image certificate for each UART
  upload admitted into the session. Prove admission and resident-image ownership
  from the delivered transcript. A certificate is checked at the upload boundary,
  not replaced by a recurring assumption that execution is correct.
- A declared lifetime for UART interpretation. Certified UART replacement can
  begin another UART epoch. A replacement with another protocol ends the current
  UART epoch; old retained packets remain generic packets with their original
  ownership. Initial UART upload cannot justify UART typing after arbitrary
  later program replacement.
- For the reception-progress corollary only: `StreamLink.Safe`, the declared
  sampler latency envelope and matching external waveform. Physical validity of
  that envelope remains an external qualification obligation.

Rejected commands are behavior to prove, including commands offered between
frames. Loader staging-pending and mailbox-valid are distinct: an unread result
does not block arming or automatic rearming. Serial STOP/reset preserve the
mailbox; external reset flushes it. Generic timeout/fault packets stay in the raw
packet layer unless their interpretation is separately justified.

## State relation to establish and preserve

The relation should contain:

1. Actual SRAM/controller state agrees with the tracked loader ledger and its
   runtime/coverage invariant. The certified resident image is attached to the
   current execution epoch.
2. During a certified UART epoch, the E64 execution state is the compiler lift
   of a well-formed independent receiver state. Busy, mode and samples follow
   from that full relation; they are not independent premises.
3. The supervisor enabled bit, sampled pin state and serial receiver state agree
   with their reference state. Effective start/reset commands are derived from
   the policy and actual decoded inputs.
4. Full host-observer state, including synchronized consume/clear controls,
   `wasActive`, result pages and flags, agrees with the package reference.
   Its projected raw-packet mailbox agrees with the abstract retained buffer.
5. Proof-only receipt history records acceptance, delivery, drop and flush by
   occurrence. A retained packet keeps a ghost program/epoch origin through
   STOP, reset and replacement. No hardware tag or counter is added.

Raw packets should be the primary mailbox representation. Apply a UART outcome
projection only when its origin was a certified UART epoch. This handles equal
successive bytes and prevents relabeling an older unread packet after COMMIT.

## Implementation checkpoints

| Checkpoint | Work and completion criterion |
| --- | --- |
| 1. Stream package transport | Define an interpreted closed package with the supervisor state, lawful SRAM, existing adapters and observer, and status-bit overlay. Prove step, observation, run and trace transport from the emitted stream package. All package outputs are covered. |
| 2. Initialized upload and arm | Adapt the existing reset/release and serial-upload admission proofs to the stream package. From arbitrary represented state, a delivered certified UART upload and delivered raw ARM command 6/payload 1 establish the relation. Prove ARM admission, defined instruction words, resident certificate, disabled-to-enabled transition and the actual mailbox state; do not assume admission. |
| 3. Continuous quiet session | Prove one-edge preservation and induction over arbitrary finite histories with consumed command 0, no initialization or execution reset, and no mailbox flush after settled reset release. Receive/page/consume/clear pins remain arbitrary. Derive `CoreCorresponds` and the observer controls before applying `observer_step`. Compare directly to the pre-step `BufferedSupervisor`, proving rearming and buffer behavior through arbitrarily many completions. |
| 4. First-edge and delay alignment | Prove the arm/warm-up alignment explicitly: actual ARM sets `wasActive = true`, whereas `uninterrupted_delay` starts it false. Align the first receipt and initial buffer, then shift arrivals and consume/clear histories together. Do not discard a retained packet's first consumer event during this alignment. |
| 5. Complete UART lifecycle | Extend preservation to rejected commands, nonquiet rearm delays, STOP, serial reset, external reset and certified UART reload/rearm. Derive the effective resident-program rule internally. Track retained-packet origins across epochs and account for coincident completion/control events. This closes the initialized UART session theorem for the declared lifecycle domain. |
| 6. Pin timing and artifact closeout | Derive consumed receive observations from the actual sampler, then compose the strong stream timing theorem on uninterrupted windows. Transport the initialized session result to the same emitted core/package and bound fresh proof/validation receipts to that candidate. |

The first meaningful deliverable is checkpoints 1–3: an initialized, certified,
automatically repeating UART session proved for every finite quiet-command
prefix, with arbitrary consumer stalls and exact result accounting. It is a
bounded intermediate theorem; lifecycle closure and pin timing remain subsequent
checkpoints. Checkpoint 3 uses the pre-step reference directly; checkpoint 4
separately connects it to the existing post-step `Rx.Stream` model.

During checkpoint 5, `PairedCertified.Rule` already permits rejection command 6
and all commands except initialization and replacement COMMIT. Derive that rule
from the effective command policy inside a resident-image segment. Initialization
and accepted replacement create boundaries with newly established relations;
they must not be silently excluded from the lifecycle theorem.

STOP or serial reset coincident with completion needs the ordinary pre-edge
mailbox transition. `receiver_reset_retains` has a no-arrival premise and cannot
justify unconditional retention on that boundary. Pending arrivals and the old
sample registers must be accounted for before reset/rearm changes execution.

## Existing proof owners to reuse

| Owner | Relevant bridge |
| --- | --- |
| [PairedStream](../../Pinwheel/Hardware/Storage/PairedStream.lean) | `wrap_correct`, `emitted_core_correct`, `mapped_step`, `mapped_observe`, `emitted_package_correct`; policy and effective inputs. Component equality is the transport layer, not the initialized behavior theorem. |
| [PairedPackage](../../Pinwheel/Hardware/Storage/PairedPackage.lean) | Pattern for `step_physical`, `observe_physical`, `retained_run` and `retained_trace`; its state/register types must be adapted for the stream wrapper. |
| [PairedSession](../../Pinwheel/Hardware/Storage/PairedSession.lean) | `reset_prepares`, `upload_admitted`, `retained_initialized_session`; actual reset/release, serial delivery and accepted image installation. |
| [PairedCoverage](../../Pinwheel/Hardware/Storage/PairedCoverage.lean), [PairedRuntime](../../Pinwheel/Hardware/Storage/PairedRuntime.lean), [PairedCertified](../../Pinwheel/Hardware/Storage/PairedCertified.lean) | Accepted-write coverage, runtime invariants and resident-image context preservation. |
| [PairedTimed](../../Pinwheel/Hardware/Storage/PairedTimed.lean) and [PairedHost](../../Pinwheel/Hardware/Storage/PairedHost.lean) | E64 state refinement, lawful-memory transport, package observations and initialized commit segments. Adapt their inputs to the effective supervisor commands. |
| [UARTRxProofs](../../Pinwheel/Compile/UARTRxProofs.lean), [hardware UARTRx](../../Pinwheel/Hardware/UARTRx.lean) | `reset_simulation`, `step_simulation`, `direct_step`; canonical E64-to-independent-receiver bridge. |
| [BufferedSupervisor](../../Pinwheel/UART/BufferedSupervisor.lean) | `CoreCorresponds`, `observer_step`, `observer_active`, `decoded_step`, `wellFormed_step`, delayed stream and receipt lemmas. Their premises must follow from the package relation. |
| [HostResultBuffer](../../Pinwheel/Hardware/HostResultBuffer.lean) | Generic packet refinement, `history_order`, `history_accounting`; retained/delivered/dropped/flushed occurrence accounting. |
| [Chip](../../Pinwheel/Hardware/Chip.lean) and [StreamLinkProofs](../../Pinwheel/UART/StreamLinkProofs.lean) | `consumed_delayed`, `session_delivers`, `receive_series`; actual sampler phase and the strong uninterrupted reception domain. |

Suggested new modules are a stream-package transport module and a stream-session
refinement module beside `PairedStream.lean`. Add focused tests for the new
relation and theorem boundaries. Final names should follow the proved dependency
structure; avoid refactoring existing circuit expressions to make a proof easier.

## Completion and verification

- Kernel-check the initialized relation, preservation theorem and all-prefix
  trace/receipt theorem with standard approved axioms only. No `sorry`, custom
  axioms, `native_decide` or `bv_decide`.
- No public per-edge `CoreCorresponds`, desired-memory-Q, activation-alignment
  or mailbox-control assumptions. Derive them from initialization, certified
  image ownership, memory law and actual consumed inputs.
- Cover the declared lifecycle and prove that repeated completion occurrences
  are accounted for, including identical bytes, consume-plus-arrival,
  clear-plus-drop, STOP/reset-plus-completion and unread results across reload.
- Prove reception-progress only on windows satisfying the stronger stream bound
  and quiet-command conditions. Arbitrary stalls imply accounting, not lossless
  delivery; no FIFO or flow-control change is part of this work.
- Use incremental Lean checks during lemma development. At the final checkpoint,
  run the foundation/axiom audit, focused lifecycle tests, existing resolved-wire
  controls and fresh RTL readback with create-only tags. Bind the successful
  receipts and check emitted candidate bytes; preserve old receipts unchanged.
- If a proof exposes a circuit/specification mismatch, record the counterexample
  and make the required implementation change explicit rather than weakening
  the intended claim or adding the missing behavior as a premise.

Closing this plan proves digital session composition under the declared memory
and delivery contracts. SRAM internal qualification, fast-corner characterization,
package power, analog sampling, board-frequency claims, new protocol families
and additional CAD/routing remain separate work.
