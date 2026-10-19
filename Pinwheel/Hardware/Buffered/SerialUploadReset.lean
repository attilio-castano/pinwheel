import Pinwheel.Hardware.Buffered.SerialUploadInstallation
import Pinwheel.Hardware.Buffered.SerialUploadConcrete

/-! Warm and cold reset opcodes are themselves delivered by sampled frames.
The frontend still captures and reads its reset receipt before the 67-command
reload. Only warm reload requires finite generation room. -/
namespace Pinwheel.Hardware.Buffered.SerialUpload
open Pinwheel.Hardware SerialWire Serial.Frames
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

inductive ResetKind where
  | warm | cold
  deriving DecidableEq

def ResetKind.operation : ResetKind → Serial.Encoding.Operation
  | .warm => .warm | .cold => .cold

def ResetKind.word (kind : ResetKind) (sequence : BitVec 16) : BitVec 160 :=
  match kind with
  | .warm => Serial.Encoding.encode .warm sequence 0#0
  | .cold => Serial.Encoding.encode .cold sequence 0#0

def ResetInput (kind : ResetKind) (i : Values Reactive.Input) : Prop :=
  match kind with
  | .warm => i .initialize = 0 ∧ i .command = 7
  | .cold => i .initialize = 1

theorem warm_operands (s : SerialPackage.State) (pin : SerialPackage.Pins)
    (sequence : BitVec 16) (closed : Closed (ResetKind.warm.word sequence) s.record)
    (cold : pin.cold = false) : ResetInput .warm (s.coreInputs pin) := by
  have opcode : Serial.requestOpcode s.record = 7 := by
    simpa [Serial.requestOpcode, closed.request, ResetKind.word, Serial.Encoding.Operation.code] using
      Serial.Encoding.encode_opcode .warm sequence 0#0
  have accepted : codeOf (ResetKind.warm.word sequence) = 0 :=
    Serial.Encoding.encode_accepted .warm sequence 0#0
  change s.coreInputs pin .initialize = 0 ∧ s.coreInputs pin .command = 7
  constructor <;> rw [s.record_coreInputs]
  all_goals simp [Serial.State.coreInput, Serial.deliver, SerialPackage.State.inputs,
    SerialPackage.Pins.inputs, cold, closed.dispatch, closed.code, accepted, opcode,
    Serial.requestField_eq, closed.request]
  unfold ResetKind.word Serial.Encoding.encode
  simp (disch := decide) only [Serial.Encoding.Operation.code,
    BitVec.extractLsb'_append_eq_of_add_le, BitVec.extractLsb'_append_eq_of_le]
  rfl
  done

theorem cold_operands (s : SerialPackage.State) (pin : SerialPackage.Pins)
    (sequence : BitVec 16) (closed : Closed (ResetKind.cold.word sequence) s.record)
    (cold : pin.cold = false) : ResetInput .cold (s.coreInputs pin) := by
  have opcode : Serial.requestOpcode s.record = 8 := by
    simpa [Serial.requestOpcode, closed.request, ResetKind.word, Serial.Encoding.Operation.code] using
      Serial.Encoding.encode_opcode .cold sequence 0#0
  have accepted : codeOf (ResetKind.cold.word sequence) = 0 :=
    Serial.Encoding.encode_accepted .cold sequence 0#0
  change s.coreInputs pin .initialize = 1
  rw [s.record_coreInputs]
  simp [Serial.State.coreInput, Serial.deliver, SerialPackage.State.inputs,
    SerialPackage.Pins.inputs, cold, closed.dispatch, closed.code, accepted, opcode]
  done

theorem reset_operands (s : SerialPackage.State) (pin : SerialPackage.Pins)
    (kind : ResetKind) (sequence : BitVec 16) (closed : Closed (kind.word sequence) s.record)
    (cold : pin.cold = false) : ResetInput kind (s.coreInputs pin) := by
  cases kind
  case warm => exact warm_operands s pin sequence closed cold
  case cold => exact cold_operands s pin sequence closed cold
  done

def resetGeneration (kind : ResetKind) (generation : BitVec 16) : BitVec 16 :=
  match kind with
  | .cold => 0
  | .warm => if generation = 65535 then generation else generation - 65535

theorem ResetInput.resetting {kind i} (input : ResetInput kind i) (s : SramState.State) :
    Reactive.resetting.eval i s.core = 1 := by
  cases kind
  case warm =>
    simp only [ResetInput] at input
    simp [Reactive.resetting, Reactive.cold, Reactive.warm, Reactive.cmd, Reactive.both,
      Reactive.either, Expr.eval, input.1, input.2]
  case cold =>
    simp only [ResetInput] at input
    simp [Reactive.resetting, Reactive.cold, Reactive.either, Expr.eval, input]
  done

theorem reset_progress (s : SramState.State) (i : Values Reactive.Input) (kind : ResetKind)
    (input : ResetInput kind i) : TableProgress (resetGeneration kind (s.core .generation)) 0 (s.step i) := by
  have resetting : Reactive.resetting.eval i s.core = 1 := by
    cases kind
    case warm => simp [ResetInput] at input; simp [Reactive.resetting, Reactive.cold, Reactive.warm,
      Reactive.cmd, Reactive.both, Reactive.either, Expr.eval, input.1, input.2]
    case cold => simp [ResetInput] at input; simp [Reactive.resetting, Reactive.cold, Reactive.either, Expr.eval, input]
  have cleared := Lifecycle.reset_ownership s i resetting
  refine ⟨cleared.2.2, cleared.2.1, by omega, by intro k impossible; omega, ?_⟩
  cases kind
  case cold => exact (Lifecycle.cold_counters s i input).1
  case warm =>
    simp only [ResetInput] at input
    have noCommit := I2cCanonicalUpload.no_commit s i (by simp [input.2])
    rw [Lifecycle.generation_step]
    by_cases full : s.core .generation = 65535#16
    all_goals simp [input.1, input.2, resetGeneration, noCommit, full]
  done

def tailCommands {before} (transaction : Transaction before) : List (Values Reactive.Input) :=
  (fun {w} (port : Reactive.Input w) => transaction.delivered.coreInputs transaction.capture port) ::
    transaction.captured.commands transaction.read.pins

theorem tail_run {before} (transaction : Transaction before) :
    transaction.delivered.controller.run (tailCommands transaction) = transaction.after.controller := by
  change transaction.captured.controller.run (transaction.captured.commands transaction.read.pins) = _
  rw [← transaction.captured.run_controller]
  rfl
  done

theorem tail_quiet {before} (transaction : Transaction before) :
    ∀ i ∈ tailCommands transaction, Serial.Frames.Quiet i := by
  intro i member
  rcases List.mem_cons.mp member with equal | read
  · subst i
    exact transaction.capture_quiet
  · exact transaction.read_quiet i read
  done

theorem reset_transaction_progress {before} (transaction : Transaction before)
    (kind : ResetKind) (sequence : BitVec 16)
    (word : transaction.request.word = kind.word sequence) :
    TableProgress (resetGeneration kind (transaction.framed.controller.core .generation)) 0
      transaction.after.controller := by
  have closed := transaction.request.closed
  rw [word] at closed
  have input := reset_operands transaction.framed transaction.dispatch kind sequence closed transaction.dispatchIdle.1
  exact transaction_invariant transaction (fun _ => True)
    (TableProgress (resetGeneration kind (transaction.framed.controller.core .generation)) 0)
    True.intro (fun _ _ _ _ => True.intro)
    (fun _ => reset_progress _ _ kind input) (fun _ i h quiet => h.quiet i quiet)
  done

theorem reload_controller_run {before} (transaction : Transaction before) (loading : Loading transaction.after) :
    transaction.delivered.controller.run
      (tailCommands transaction ++ transaction.after.commands loading.pins) = loading.after.controller := by
  simp only [SramState.State.run, List.foldl_append]
  change (transaction.delivered.controller.run (tailCommands transaction)).run _ = _
  rw [tail_run, loading.controller_run]
  done

theorem request_generation {before} (transaction : Transaction before) :
    transaction.framed.controller.core .generation = before.controller.core .generation := by
  have held := quiet_run_hold before.controller (before.commands transaction.request.pins) transaction.request.quiet
  rw [← before.run_controller] at held
  exact held.generation
  done

theorem loader_transfer_run (s : SramState.State) (inputs : List (Values Reactive.Input))
    (all : ∀ i ∈ inputs, LifecycleUpload.Input i) :
    (s.run inputs).core .transfer = s.core .transfer := by
  induction inputs generalizing s
  case nil => rfl
  case cons i rest ih =>
    exact (ih (s.step i) (fun j member => all j (List.mem_cons_of_mem _ member))).trans
      (LifecycleUpload.transfer_step s i (all i (by simp)))
  done

theorem request_transfer {before} (transaction : Transaction before) :
    transaction.framed.controller.core .transfer = before.controller.core .transfer := by
  have held := loader_transfer_run before.controller (before.commands transaction.request.pins)
    (by intro i member; have q := transaction.request.quiet i member;
        exact ⟨q.1, by simp [q.2], by simp [q.2]⟩)
  rw [← before.run_controller] at held
  exact held
  done

theorem wire_install {before} (transaction : Transaction before)
    (kind : ResetKind) (sequence : BitVec 16)
    (word : transaction.request.word = kind.word sequence)
    (loading : Loading transaction.after)
    (space : resetGeneration kind (transaction.framed.controller.core .generation) ≠ 65535) :
    Refinement.InstalledSram I2cSource.source I2cCertificate.layout loading.after.controller ∧
      Complete (resetGeneration kind (transaction.framed.controller.core .generation)) loading.after.controller ∧
      Serial.Frames.Available loading.after.record ∧
      loading.after.controller.core .transfer =
        (match kind with | .cold => 0 | .warm => before.controller.core .transfer) ∧
      before.run (transaction.pins ++ loading.pins) = loading.after := by
  have progress := reset_transaction_progress transaction kind sequence word
  have result := loading.result progress space transaction.exact.1
  have closed := transaction.request.closed
  rw [word] at closed
  have input := reset_operands transaction.framed transaction.dispatch kind sequence closed transaction.dispatchIdle.1
  have source := history_append transaction.delivered.controller
    (tailCommands transaction) (transaction.after.commands loading.pins)
    (quiet_history _ _ (tail_quiet transaction)) (by rw [tail_run]; exact result.2.1)
  have installed := I2cReload.reset_installed transaction.framed.controller
    (transaction.framed.coreInputs transaction.dispatch) (input.resetting _)
    (tailCommands transaction ++ transaction.after.commands loading.pins) source
  rw [I2cReloadSession.loading_run] at installed
  change (transaction.delivered.controller.run
    (tailCommands transaction ++ transaction.after.commands loading.pins)).core .valid = 1 →
      Refinement.InstalledSram I2cSource.source I2cCertificate.layout
        (transaction.delivered.controller.run
          (tailCommands transaction ++ transaction.after.commands loading.pins)) at installed
  rw [reload_controller_run] at installed
  have transfer := loader_transfer_run transaction.delivered.controller
    (tailCommands transaction ++ transaction.after.commands loading.pins) (by
      intro i member
      rcases List.mem_append.mp member with tail | load
      · have q := tail_quiet transaction i tail
        exact ⟨q.1, by simp [q.2], by simp [q.2]⟩
      · exact result.2.2.1 i load)
  rw [reload_controller_run] at transfer
  refine ⟨installed result.1.valid, result.1, result.2.2.2, ?_, ?_⟩
  · rw [transfer]
    cases kind
    case cold => exact (Lifecycle.cold_counters transaction.framed.controller
      (transaction.framed.coreInputs transaction.dispatch) input).2
    case warm =>
      exact (Lifecycle.warm_transfer transaction.framed.controller
        (transaction.framed.coreInputs transaction.dispatch) input.1 input.2).trans (request_transfer transaction)
  · simp only [SerialPackage.State.run, List.foldl_append]
    change (before.run transaction.pins).run loading.pins = _
    rw [transaction.run_pins, loading.run_pins]
  done

theorem warm_space {before} (transaction : Transaction before) (sequence : BitVec 16)
    (word : transaction.request.word = ResetKind.warm.word sequence)
    (bound : (before.controller.core .generation).toNat ≤ 65533) :
    resetGeneration .warm (transaction.framed.controller.core .generation) ≠ 65535 := by
  have closed := transaction.request.closed
  rw [word] at closed
  have input := warm_operands transaction.framed transaction.dispatch sequence closed transaction.dispatchIdle.1
  have space := I2cCanonicalUpload.warm_space transaction.framed.controller
    (transaction.framed.coreInputs transaction.dispatch) input.1 input.2
    (by rw [request_generation]; exact bound)
  intro full
  exact space ((reset_progress _ _ .warm input).generation.trans full)
  done

theorem warm_install {before} (transaction : Transaction before) (sequence : BitVec 16)
    (word : transaction.request.word = ResetKind.warm.word sequence)
    (loading : Loading transaction.after)
    (bound : (before.controller.core .generation).toNat ≤ 65533) :
    Refinement.InstalledSram I2cSource.source I2cCertificate.layout loading.after.controller ∧
      loading.after.controller.core .phase = 0 ∧ loading.after.controller.core .retained = 0 ∧
      (loading.after.controller.core .generation).toNat = (before.controller.core .generation).toNat + 2 ∧
      loading.after.controller.core .transfer = before.controller.core .transfer ∧
      Available loading.after.record ∧ before.run (transaction.pins ++ loading.pins) = loading.after := by
  have result := wire_install transaction .warm sequence word loading (warm_space transaction sequence word bound)
  have closed := transaction.request.closed
  rw [word] at closed
  have input := warm_operands transaction.framed transaction.dispatch sequence closed transaction.dispatchIdle.1
  have generation := Lifecycle.warm_generation transaction.framed.controller
    (transaction.framed.coreInputs transaction.dispatch) input.1 input.2
  rw [(reset_progress _ _ .warm input).generation, request_generation] at generation
  have finalGeneration := result.2.1.generation
  rw [request_generation] at finalGeneration
  refine ⟨result.1, result.2.1.phase, result.2.1.retained, ?_, result.2.2.2.1,
    result.2.2.1, result.2.2.2.2⟩
  omega
  done

theorem wire_cold_install {before} (transaction : Transaction before) (sequence : BitVec 16)
    (word : transaction.request.word = ResetKind.cold.word sequence)
    (loading : Loading transaction.after) :
    Refinement.InstalledSram I2cSource.source I2cCertificate.layout loading.after.controller ∧
      loading.after.controller.core .phase = 0 ∧ loading.after.controller.core .retained = 0 ∧
      loading.after.controller.core .generation = 1 ∧ loading.after.controller.core .transfer = 0 ∧
      Available loading.after.record ∧ before.run (transaction.pins ++ loading.pins) = loading.after := by
  have result := wire_install transaction .cold sequence word loading (by simp [resetGeneration])
  refine ⟨result.1, result.2.1.phase, result.2.1.retained, ?_, result.2.2.2.1,
    result.2.2.1, result.2.2.2.2⟩
  exact BitVec.eq_of_toNat_eq result.2.1.generation
  done

theorem wire_cold_exists (before : SerialPackage.State) (available : Available before.record)
    (sequence : Nat → BitVec 16 := BitVec.ofNat 16) (raw : BitVec 2 := 0) :
    ∃ transaction : Transaction before, ∃ loading : Loading transaction.after,
      transaction.request.word = ResetKind.cold.word (sequence 0) ∧
      Refinement.InstalledSram I2cSource.source I2cCertificate.layout loading.after.controller ∧
      loading.after.controller.core .phase = 0 ∧ loading.after.controller.core .retained = 0 ∧
      loading.after.controller.core .generation = 1 ∧ loading.after.controller.core .transfer = 0 ∧
      Available loading.after.record ∧ before.run (transaction.pins ++ loading.pins) = loading.after := by
  let transaction := concrete before available (ResetKind.cold.word (sequence 0)) raw
  let loading := concreteLoading transaction.after transaction.exact.1 (fun n => sequence (n+1)) raw
  exact ⟨transaction, loading, concrete_word .., wire_cold_install transaction _ (concrete_word ..) loading⟩
  done

theorem wire_warm_exists (before : SerialPackage.State) (available : Available before.record)
    (bound : (before.controller.core .generation).toNat ≤ 65533)
    (sequence : Nat → BitVec 16 := BitVec.ofNat 16) (raw : BitVec 2 := 0) :
    ∃ transaction : Transaction before, ∃ loading : Loading transaction.after,
      transaction.request.word = ResetKind.warm.word (sequence 0) ∧
      Refinement.InstalledSram I2cSource.source I2cCertificate.layout loading.after.controller ∧
      loading.after.controller.core .phase = 0 ∧ loading.after.controller.core .retained = 0 ∧
      (loading.after.controller.core .generation).toNat = (before.controller.core .generation).toNat + 2 ∧
      loading.after.controller.core .transfer = before.controller.core .transfer ∧
      Available loading.after.record ∧ before.run (transaction.pins ++ loading.pins) = loading.after := by
  let transaction := concrete before available (ResetKind.warm.word (sequence 0)) raw
  let loading := concreteLoading transaction.after transaction.exact.1 (fun n => sequence (n+1)) raw
  exact ⟨transaction, loading, concrete_word .., warm_install transaction _ (concrete_word ..) loading bound⟩
  done

end Pinwheel.Hardware.Buffered.SerialUpload
