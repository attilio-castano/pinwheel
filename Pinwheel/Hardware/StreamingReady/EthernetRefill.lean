import Pinwheel.Hardware.StreamingReady.EthernetSession
import Pinwheel.Program.StreamingEthernetRefill
import Pinwheel.Program.StreamingReadySessionService

/-! Host refill policies share the same digital wire guarantee. -/
namespace Pinwheel.Hardware.StreamingReady.EthernetRefill
open Pinwheel.Program.StreamingReady Pinwheel.Program.StreamingEthernetCore
open Pinwheel.Program.StreamingEthernetFrame Pinwheel.Program.StreamingEthernetRefill
open Pinwheel.Hardware.StreamingReady.InitializedCustody

/-- From the first reservation to HALT, a certified host schedule drives
the exact frame at six clocks per cell and drops enable at the final idle. -/
theorem wire_exact (startup : Package.State 1) (policy : Policy) (highWidth : Nat)
    (execution : Executed policy highWidth) (credit : checkCredit policy highWidth = true) :
    let head := alignmentPins policy highWidth
    let actual := (EthernetSession.beforeWire startup).run (Package.Components.typed 1)
      (head.map SessionCorrespondence.pins)
    PublicPins.driveTrace actual (activePins policy highWidth) =
      frameBits.flatMap cellPins ++ [txPins false, idlePins] := by
  have split : alignmentPins policy highWidth ++ activePins policy highWidth = bodyPins policy highWidth :=
    List.take_append_drop _ _
  have runtime := (SessionService.runtimeTrace_append program false
    Pinwheel.Program.StreamingEthernetSchedule.preloaded _ _).mp (split.symm ▸ execution.body_runtime)
  have alignedReached := (EthernetSession.beforeWire_matches startup).run
    (alignmentPins policy highWidth) (by decide) runtime.1
  have padsEq := PublicPins.driveTrace_eq (Initialization.compiledImage image)
    (aligned policy highWidth) (activePins policy highWidth) (by decide)
    (by simpa only [compiled_pending, aligned] using runtime.2) alignedReached.custody.structural
  dsimp only
  rw [alignedReached.package]
  have sourceWire := Pinwheel.Program.StreamingEthernetCredit.session_frame_exact (aligned policy highWidth)
    (activePins policy highWidth) frameBits credit
  rw [compiled_pending] at padsEq
  exact padsEq.trans sourceWire.2.1

theorem owner_released (startup : Package.State 1) (policy : Policy) (highWidth : Nat)
    (execution : Executed policy highWidth) :
    let wireEnd := (EthernetSession.beforeWire startup).run (Package.Components.typed 1)
      ((bodyPins policy highWidth).map SessionCorrespondence.pins)
    let after := wireEnd.run (Package.Components.typed 1)
      ((Pinwheel.Program.StreamingEthernetSchedule.releaseClocked highWidth).map SessionCorrespondence.pins)
    wireEnd = SessionCorrespondence.values (Initialization.compiledImage image) (complete policy highWidth) ∧
    after = SessionCorrespondence.values (Initialization.compiledImage image) (released policy highWidth) ∧
    (complete policy highWidth).core.phase = .completed ∧ (complete policy highWidth).core.drained = true ∧
    (complete policy highWidth).core.txAccepted = 576 ∧ (complete policy highWidth).core.txConsumed = 576 ∧
    (released policy highWidth).core.phase = .free ∧ (released policy highWidth).core.transfer = 1 ∧
    (released policy highWidth).host.code = 0 := by
  have endReached := (EthernetSession.beforeWire_matches startup).run
    (bodyPins policy highWidth) (by decide) execution.body_runtime
  have afterReached := endReached.run _ (by decide) execution.release_runtime
  exact ⟨endReached.package, afterReached.package, execution.completed, execution.drained,
    execution.accepted, execution.consumed, execution.free, execution.transfer, execution.releasedCode⟩

end Pinwheel.Hardware.StreamingReady.EthernetRefill
