import Pinwheel.Hardware.Buffered.I2cTimingSerialInstallation
import Pinwheel.Hardware.Buffered.SerialUploadReset

/-! Actual wire reset/reload for symbolic timing fields.  Warm reset retains
the transfer sequence and consumes two generation numbers including COMMIT. -/
namespace Pinwheel.Hardware.Buffered.I2cTiming.SerialUpload
open Pinwheel.Hardware SerialWire Serial.Frames
open _root_.Pinwheel.Hardware.Buffered.SerialUpload
  (ResetKind resetGeneration reset_transaction_progress tailCommands tail_run tail_quiet
   loader_transfer_run request_transfer request_generation reset_progress reset_operands)
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

theorem reload_controller_run {duration budget before} (transaction : Transaction before)
    (loading : Loading duration budget transaction.after) :
    transaction.delivered.controller.run
      (tailCommands transaction ++ transaction.after.commands loading.pins) = loading.after.controller := by
  simp only [SramState.State.run,List.foldl_append]
  change (transaction.delivered.controller.run (tailCommands transaction)).run _ = _
  rw [tail_run,loading.controller_run]

theorem wire_install (duration budget : Fin 256) {before} (transaction : Transaction before)
    (kind : ResetKind) (sequence : BitVec 16) (word : transaction.request.word = kind.word sequence)
    (loading : Loading duration budget transaction.after)
    (space : resetGeneration kind (transaction.framed.controller.core .generation) ≠ 65535) :
    Refinement.InstalledSram (source duration budget) (layout duration budget) loading.after.controller ∧
      Buffered.SerialUpload.Complete
        (resetGeneration kind (transaction.framed.controller.core .generation)) loading.after.controller ∧
      Available loading.after.record ∧
      loading.after.controller.core .transfer =
        (match kind with | .cold => 0 | .warm => before.controller.core .transfer) ∧
      before.run (transaction.pins ++ loading.pins) = loading.after := by
  have progress := reset_transaction_progress transaction kind sequence word
  have result := loading.result progress space transaction.exact.1
  have closed := transaction.request.closed
  rw [word] at closed
  have input := reset_operands transaction.framed transaction.dispatch kind sequence closed transaction.dispatchIdle.1
  have provenance := history_append duration budget transaction.delivered.controller
    (tailCommands transaction) (transaction.after.commands loading.pins)
    (quiet_history duration budget _ _ (tail_quiet transaction)) (by rw [tail_run]; exact result.2.1)
  have installed := I2cTiming.Upload.reset_installed duration budget transaction.framed.controller
    (transaction.framed.coreInputs transaction.dispatch) (input.resetting _)
    (tailCommands transaction ++ transaction.after.commands loading.pins) provenance
  change (transaction.delivered.controller.run
    (tailCommands transaction ++ transaction.after.commands loading.pins)).core .valid = 1 →
      Refinement.InstalledSram (source duration budget) (layout duration budget)
        (transaction.delivered.controller.run
          (tailCommands transaction ++ transaction.after.commands loading.pins)) at installed
  rw [reload_controller_run] at installed
  have transfer := loader_transfer_run transaction.delivered.controller
    (tailCommands transaction ++ transaction.after.commands loading.pins) (by
      intro i member
      rcases List.mem_append.mp member with tail | load
      · have q := tail_quiet transaction i tail
        exact ⟨q.1,by simp [q.2],by simp [q.2]⟩
      · exact result.2.2.1 i load)
  rw [reload_controller_run] at transfer
  refine ⟨installed result.1.valid,result.1,result.2.2.2,?_,?_⟩
  · rw [transfer]
    cases kind with
    | cold => exact (Lifecycle.cold_counters transaction.framed.controller
        (transaction.framed.coreInputs transaction.dispatch) input).2
    | warm => exact (Lifecycle.warm_transfer transaction.framed.controller
        (transaction.framed.coreInputs transaction.dispatch) input.1 input.2).trans (request_transfer transaction)
  · simp only [SerialPackage.State.run,List.foldl_append]
    change (before.run transaction.pins).run loading.pins = _
    rw [transaction.run_pins,loading.run_pins]

theorem warm_install (duration budget : Fin 256) {before} (transaction : Transaction before)
    (sequence : BitVec 16) (word : transaction.request.word = ResetKind.warm.word sequence)
    (loading : Loading duration budget transaction.after)
    (bound : (before.controller.core .generation).toNat ≤ 65533) :
    Refinement.InstalledSram (source duration budget) (layout duration budget) loading.after.controller ∧
      loading.after.controller.core .phase = 0 ∧ loading.after.controller.core .retained = 0 ∧
      (loading.after.controller.core .generation).toNat = (before.controller.core .generation).toNat + 2 ∧
      loading.after.controller.core .transfer = before.controller.core .transfer ∧
      Available loading.after.record ∧ before.run (transaction.pins ++ loading.pins) = loading.after := by
  have result := wire_install duration budget transaction .warm sequence word loading
    (Buffered.SerialUpload.warm_space transaction sequence word bound)
  have closed := transaction.request.closed
  rw [word] at closed
  have input := Buffered.SerialUpload.warm_operands transaction.framed transaction.dispatch
    sequence closed transaction.dispatchIdle.1
  have generation := Lifecycle.warm_generation transaction.framed.controller
    (transaction.framed.coreInputs transaction.dispatch) input.1 input.2
  rw [(reset_progress _ _ .warm input).generation,request_generation] at generation
  have finalGeneration := result.2.1.generation
  rw [request_generation] at finalGeneration
  exact ⟨result.1,result.2.1.phase,result.2.1.retained,by omega,result.2.2.2.1,
    result.2.2.1,result.2.2.2.2⟩

end Pinwheel.Hardware.Buffered.I2cTiming.SerialUpload
