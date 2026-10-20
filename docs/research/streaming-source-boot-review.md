# Streaming source and boot proof review

Review scope: committed source through `328df31`, plus the frozen
`Hardware/Streaming/InitializedCustody.lean` convenience seam. This is a source
and theorem-interface review. It does not report acceptance of the pending
fresh RTL, mapping, simulator or foundation campaign receipts.

## Result

No circular source/circuit agreement, assumed VALID result, assumed successful
loader acceptance, or assumed delivered command history was found in the
concrete SPI/JTAG initialization chain. The earlier missing exported
boot-to-START custody seam is supplied by `InitializedCustody.Pipeline`.

| Boundary | Evidence | Premises and effect |
| --- | --- | --- |
| Static source to words | `StreamingCompile.Compiled`, `encode_canonical`, `compiled_row` | The finite certificate contains source shape, canonicality and exact encoding, with no runtime agreement field. |
| Arbitrary power-up to loader state | `Initialization.cold_values`; `InitializedSession.cold_correct` | An actual cold edge clears every represented core and frontend register. |
| Physical requests to source-bound commands | `BootPins.spi_check`, `jtag_check`, `check_sound`; `BootControl.step_correct` | Kernel-checked traces include request CRCs, sequence checks, real dispatch, all response-work clocks, and exact receipt reads. Status reduction is allowed only under the checked non-bulk control condition. |
| Actual loader acceptance and installation | `BootCorrespondence.delivery_effects`, `Related.step`, `spi_initialized`, `jtag_initialized` | Rejection is derived to be false from actual free metadata. Ordered writes establish coverage, COMMIT establishes VALID, and compilation supplies source binding. |
| Actual command grammar | `BootUpload.history_eq`, `spi_upload`, `jtag_upload` | The actual frontend/core history is proved to contain the complete ordered `Initialization.Upload` followed by COMMIT. The history is not an input premise. |
| Initialized runtime | `SourceRefinement.step_correct`; `InputCorrespondence.source_step`; `SessionCorrespondence.run_correct` | Every represented register and public output follows the independent source session, with one engine clock per physical sample. Structural bounds are initialized and inductively preserved. |
| Reached ownership and receipts | `InitializedCustody.started_run`, `spi_session`, `jtag_session`; `Reached` corollaries | Concrete boot derives host control safety and core bounds. An actual circuit START flag establishes custody and an empty owner cut; subsequent runtime preserves exact bit traces and receipts. An actual RELEASE flag implies bit conservation and acknowledgement. |
| Public pads | `PublicPins.physical_embed`, `engine_embed` | Every source sample has a concrete Tiny Tapeout pad encoding, including reset. |

SPI boot has 1,225 upload/read clocks plus its cold edge; JTAG has 3,430 plus
its cold edge. These concrete images use duration field 3, corresponding to
four declared low/high cycles. Initialization is depth-universal; the runtime
representation theorem requires address width at most 3, and artifact
qualification targets address widths 1 and 2 (queue depths 2 and 4).

## Claim boundaries

- `RuntimeTrace` is an operational input grammar: it excludes cold reset,
  warm-reset command 15, WRITE 1 and COMMIT 2. Reset/reload has separate
  theorems; this grammar is not a claim about every arbitrary raw pin history.
- Concrete initialization closes SPI/JTAG boot nonvacuity. Long-transfer
  completion against independent physical peers remains separate finite
  simulator evidence. The source bit/custody proofs are universal within
  their stated runtime and service contracts.
- `ServiceHistory` gives a finite work bound under continuously supplied
  boundary credit. The separate eventual-service extension allows finite
  stalls and assumes fairness; it provides no real-time stall bound.
- A staged TX reservation admitted before terminal completion may finish
  after retention. Unused accepted TX remains owned and blocks drained
  RELEASE; explicit reset is the cancellation boundary.
- Raw component and wrapper interpretation, two-state sampling, emitted
  artifact provenance and complete proof-closure audits are distinct from
  mapped-netlist equivalence, electrical/CDC analysis and physical signoff.

## Checks performed

The strict local closure audit including boot, public pins and initialized
custody passed for 6,654 declarations and 3,512 theorems, including private
declarations, with only the standard axiom allowlist. No frozen source was
edited during the review.

The default import graph reached all 559 production modules before the final
custody and eventual-service additions. Integration now includes custody, core
and joint-session eventual service, and exact LOW/stable-sample timing in the
default imports; `check-foundation.py` rejects unreachable production modules.
The generated actual-TT/raw factory now exports concrete boot, runtime, custody
and eventual-service APIs at both depths. Its regression configuration includes
`StreamingParity` and the kernel `StreamingCompile` suite.

Against campaign baseline `31816bb`, existing buffered/storage hardware and
physical sources remain byte-identical. The only changed pre-existing selected
code is the default import file and the foundation regression coordinator.
Both intake document hashes still match the campaign plan; neither was edited.
