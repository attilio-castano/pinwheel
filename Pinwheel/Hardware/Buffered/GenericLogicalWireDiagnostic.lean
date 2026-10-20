import Pinwheel.Hardware.Buffered.GenericLogicalWireWitness

/-! The reusable logical round constructor accepts any proved source stop,
including entry faults. Such a diagnostic premise is separate from the static
program representation certificate and is never used for runtime refinement. -/
namespace Pinwheel.Hardware.Buffered.GenericLogicalWire.Witness
open Pinwheel.Hardware Pinwheel.Program SerialWire Serial.Frames SerialSourceSession
open SerialSessionWitness (ReleaseConditions sourceRun_stopped retained_of_stopped releaseWord release_fields released_transfer started_transfer released_generation started_generation)
variable {p : Program.Buffered.Program} {layout : GenericCertificate.Layout p}
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem stopped_release_conditions {before payload source} (release : Transaction before)
    (related : Refinement.RelatedSram p layout payload before.controller source)
    (reason : Pinwheel.Engine.Reactive.Stop) (stopped : source.core.control = .stopped reason) (sequence : BitVec 16)
    (word : release.request.word = releaseWord sequence (before.controller.core .generation) (before.controller.core .transfer)) :
    ReleaseConditions release := by
  have frame := SerialSourceRequest.frame_source before source related release.request.word
    release.request.assert release.request.close release.request.samples release.request.available
    release.request.low release.request.bits release.request.idle
  have sourceHeld := sourceRun_stopped p source reason stopped release.request.pins
  have framedRelated : Refinement.RelatedSram p layout payload release.framed.controller source := by
    have result := frame.2
    change Refinement.RelatedSram p layout payload release.framed.controller
      (SerialSourceRead.sourceRun p source release.request.pins) at result
    rw [sourceHeld] at result
    exact result
  have fields := release_fields sequence (before.controller.core .generation) (before.controller.core .transfer)
  refine ⟨?_, ?_, retained_of_stopped framedRelated reason stopped, ?_, ?_⟩
  · rw [word]
    exact fields.1
  · rw [word]
    exact Serial.Encoding.encode_accepted .release sequence _
  · rw [word, fields.2.1, SerialUpload.request_generation]
  · rw [word, fields.2.2, SerialUpload.request_transfer]
  done

noncomputable opaque assembleStoppedRound (before : SerialPackage.State) (logical : Transfer.State) (offset : Nat)
    (installed : Refinement.InstalledSram p layout before.controller)
    (aligned : LogicalSession.Aligned before.controller logical offset) (available : Available before.record)
    (start : Transaction before) (release : Transaction start.after)
    (accepted : Reactive.starting.eval (start.framed.coreInputs start.dispatch) start.framed.controller.core = 1)
    (opcode : start.request.word.extractLsb' 144 4 = 3#4)
    (reason : Pinwheel.Engine.Reactive.Stop)
    (stopped : (SerialStartAdmission.sourceAfter p start).core.control = .stopped reason)
    (sequence : BitVec 16)
    (word : release.request.word = releaseWord sequence
      (start.after.controller.core .generation) (start.after.controller.core .transfer)) : LogicalRound (p := p) (layout := layout) before logical offset := by
  let started := logicalStartTrace (p := p) start logical offset opcode accepted
  have post := started.preserves ⟨available, installed, aligned⟩
  have oldTrace := SerialStartAdmission.start_trace (program := p) start opcode accepted
  have oldPost := oldTrace.preserves ⟨available, installed, ⟨aligned.phase, aligned.retained⟩⟩
  have conditions := stopped_release_conditions release oldPost.2 reason stopped sequence word
  let released := logicalReleaseTrace (p := p) release (start.request.word.extractLsb' 0 32) (localAfter (p := p) start logical) offset conditions
  let trace := appendLogicalTrace started released
  have transfer := released_transfer release sequence word
  exact ⟨start, release, _, trace, trace.preserves ⟨available, installed, aligned⟩,
    (localReleased_epoch release post.2 conditions).trans (localAfter_epoch start logical offset aligned accepted),
    by rw [transfer]; exact started_transfer start accepted,
    (released_generation release sequence word).trans (started_generation start accepted)⟩
  done

end Pinwheel.Hardware.Buffered.GenericLogicalWire.Witness
