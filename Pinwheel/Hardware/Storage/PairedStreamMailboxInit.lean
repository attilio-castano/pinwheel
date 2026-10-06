import Pinwheel.Hardware.Storage.PairedStreamBootstrap
import Pinwheel.Hardware.HostResultBuffer
import Pinwheel.Hardware.Storage.PairedStreamDormant

/-! Mailbox custody at the stream bootstrap boundary. Reset flushes the old
physical packet; a disabled loader upload creates no execution completion.
No earlier packet is relabeled as a UART result. -/
namespace Pinwheel.Hardware.Storage.PairedStreamMailboxInit
open Pinwheel.Hardware
set_option backward.isDefEq.respectTransparency false

def preparedResult (idle : Chip.Pins) : HostResult.State :=
  { resetFirst := true, resetSecond := true,
    pageFirst := idle.uiIn.extractLsb' 3 2, pageSecond := idle.uiIn.extractLsb' 3 2,
    controlFirst := idle.uiIn.extractLsb' 5 2, controlSecond := idle.uiIn.extractLsb' 5 2 }

theorem observer_reset_five (reset idle : Chip.Pins) (hr : reset.rstN = false)
    (hi : idle.rstN = true) (o₀ o₁ o₂ o₃ o₄ : Values Loader.Machine.Output)
    (initial : HostResult.State) :
    HostResult.next idle o₄ (HostResult.next idle o₃
      (HostResult.next reset o₂ (HostResult.next reset o₁ (HostResult.next reset o₀ initial)))) =
      preparedResult idle := by
  simp [HostResult.next, HostResult.resetting, hr, hi, preparedResult]
  done

theorem reset_result (memory : Memory.SinglePort.Contract S 9 64)
    (initial : PairedStreamPackage.State S) (reset idle : Chip.Pins)
    (hr : reset.rstN = false) (hi : idle.rstN = true) :
    ((PairedStreamPackage.interpreted memory).run initial
      [reset, reset, reset, idle, idle]).result = preparedResult idle := by
  exact observer_reset_five reset idle hr hi _ _ _ _ _ initial.result

def Empty (result : HostResult.State) : Prop :=
  HostResultBuffer.project result = {} ∧ result.wasActive = false

theorem prepared_empty (idle : Chip.Pins) : Empty (preparedResult idle) := by
  simp [Empty, preparedResult, HostResultBuffer.project]

theorem reset_empty (memory : Memory.SinglePort.Contract S 9 64)
    (initial : PairedStreamPackage.State S) (reset idle : Chip.Pins)
    (hr : reset.rstN = false) (hi : idle.rstN = true) :
    Empty ((PairedStreamPackage.interpreted memory).run initial
      [reset, reset, reset, idle, idle]).result := by
  rw [reset_result memory initial reset idle hr hi]
  exact prepared_empty idle

theorem mode_initialize (s : PairedCoverage.Tracked) (i : Loader.Machine.Inputs)
    (hi : i.init = true) : (PairedCoverage.advance s i.values).registers .mode = 0 := by
  simp only [PairedCoverage.advance, Circuit.step, PairedController.body, PairedController.next,
    PairedRunning.nextMode_wire _ _ (PairedCoverage.graph_equations i.values s),
    PairedController.nextModeExpr, Expr.eval]
  simp [PairedController.either,
    PairedRunning.resetting_wire _ _ (PairedCoverage.graph_equations i.values s),
    PairedController.resettingExpr, Expr.eval,
    PairedUpload.init_value _ _ (PairedCoverage.graph_equations i.values s),
    show PairedCoverage.graphInputs i.values s (.base .init) = i.values .init from rfl,
    Loader.Machine.Inputs.values, hi]
  done

theorem core_mode_initialize (memory : Memory.SinglePort.Contract S 9 64)
    (s : PairedStreamPackage.State S) (pins : Chip.Pins)
    (hi : (PairedStreamPackage.effective s).init = true) :
    ((PairedStreamPackage.interpreted memory).step pins s).core.1 .mode = 0 := by
  exact mode_initialize ⟨s.core.1, memory.view s.core.2, {}⟩ (PairedStreamPackage.effective s) hi

theorem reset_mode (memory : Memory.SinglePort.Contract S 9 64)
    (initial : PairedStreamPackage.State S) (reset idle : Chip.Pins) (hr : reset.rstN = false) :
    ((PairedStreamPackage.interpreted memory).run initial
      [reset, reset, reset, idle, idle]).core.1 .mode = 0 := by
  apply core_mode_initialize
  change (!reset.rstN : Bool) = true
  simp [hr]
  done

theorem core_inactive (memory : Memory.SinglePort.Contract S 9 64)
    (s : PairedStreamPackage.State S) (mode : s.core.1 .mode = 0)
    (command : (PairedStreamPackage.effective s).command ≠ 5) :
    PairedStreamPackage.coreOutput memory s (.core .busy) = 0 ∧
      PairedStreamPackage.coreOutput memory s (.control .start) = 0 := by
  let storage : PairedCoverage.Tracked := ⟨s.core.1, memory.view s.core.2, {}⟩
  change PairedController.busy.eval (PairedCoverage.graphInputs
      (PairedStreamPackage.effective s).values storage) storage.registers = 0 ∧
    PairedController.start.eval (PairedCoverage.graphInputs
      (PairedStreamPackage.effective s).values storage) storage.registers = 0
  simp only [BitVec.ofNat_eq_ofNat] at mode command
  simp [PairedControl.busy_value _ _ (PairedCoverage.graph_equations (PairedStreamPackage.effective s).values storage),
    show storage.registers .mode = 0#3 from mode,
    PairedRunning.start_wire _ _ (PairedCoverage.graph_equations (PairedStreamPackage.effective s).values storage),
    PairedController.startExpr, PairedController.both, PairedController.cmd, Expr.eval,
    show PairedCoverage.graphInputs (PairedStreamPackage.effective s).values storage (.base .command) =
      (PairedStreamPackage.effective s).command from rfl, command]
  done

theorem dormant_inactive (memory : Memory.SinglePort.Contract S 9 64)
    (s : PairedStreamPackage.State S) (storage : PairedStreamOwnership.Tracked)
    (h : PairedStreamDormant.Dormant memory s storage)
    (start : (PairedStreamPackage.rawInput s).command ≠ 5)
    (arm : (PairedStreamPackage.rawInput s).command ≠ 6) :
    PairedStreamPackage.coreOutput memory s (.core .busy) = 0 ∧
      PairedStreamPackage.coreOutput memory s (.control .start) = 0 := by
  have pass := PairedStreamOwnership.disabled_pass storage (PairedStreamPackage.rawInput s) h.2.1 arm
  have eff : PairedStreamPackage.effective s = PairedStreamPackage.rawInput s :=
    (congrArg PairedStream.Transition.effective
      (PairedStreamBootstrap.policy_agrees memory s storage h.1)).trans pass.1
  exact core_inactive memory s
    ((congrArg (fun pair : Values PairedController.Register × Memory.Sram.State 9 64 =>
      pair.1 .mode) h.1.1).trans h.2.2) (by rw [eff]; exact start)

theorem empty_iff (result : HostResult.State) :
    Empty result ↔ result.valid = false ∧ result.overrun = false ∧ result.wasActive = false := by
  cases hv : result.valid <;> cases ho : result.overrun <;>
    simp [Empty, HostResultBuffer.project, hv, ho]

theorem observer_empty_next (pins : Chip.Pins) (o : Values Loader.Machine.Output)
    (host : HostResult.State) (h : Empty host)
    (busy : o (.core .busy) = 0) (start : o (.control .start) = 0) :
    Empty (HostResult.next pins o host) := by
  rw [empty_iff] at h ⊢
  simp [HostResult.next, HostResult.arriving, HostResult.occupied, h.1, h.2.1, h.2.2, busy, start]

theorem empty_run (memory : Memory.SinglePort.Contract S 9 64)
    (s : PairedStreamPackage.State S) (storage : PairedStreamOwnership.Tracked)
    (h : PairedStreamDormant.Dormant memory s storage) (empty : Empty s.result)
    (pins : List Chip.Pins)
    (commands : PairedStreamDormant.LoaderHistory (Chip.consumed s.adapters pins)) :
    Empty ((PairedStreamPackage.interpreted memory).run s pins).result := by
  induction pins generalizing s storage with
  | nil => exact empty
  | cons i rest ih =>
    simp only [PairedHost.consumed_cons, PairedStreamDormant.LoaderHistory, List.forall_mem_cons] at commands
    have inactive := dormant_inactive memory s storage h commands.1.1 commands.1.2
    exact ih ((PairedStreamPackage.interpreted memory).step i s)
      (PairedStreamOwnership.advance storage (PairedStreamPackage.rawInput s))
      (PairedStreamDormant.dormant_next memory s storage h i commands.1.1 commands.1.2)
      (observer_empty_next i (PairedStreamPackage.coreOutput memory s) s.result empty inactive.1 inactive.2)
      commands.2

/-- The qualified transcript establishes the resident program and leaves no
old packet to assign a UART origin. Observer synchronizers remain actual state. -/
theorem initialized_upload (p : Execution.Image) (image : PairedImage.Image)
    (cert : PairedImage.Corresponds p image)
    (memory : Memory.SinglePort.Contract S 9 64) (initial : PairedStreamPackage.State S)
    (reset idle : Chip.Pins) (hr : reset.rstN = false) (hi : idle.rstN = true)
    (hc : idle.uiIn.getLsbD 2 = true) (d₀ d₁ : BitVec 64)
    (uploadPins : List Chip.Pins) (a b : Chip.Pins)
    (hd : Serial.Session (uploadPins.map Chip.wired)
      (Loader.Machine.uploadCommands (PairedImage.upload image) d₀ d₁)) :
    let prepared := (PairedStreamPackage.interpreted memory).run initial
      [reset, reset, reset, idle, idle]
    let uploaded := (PairedStreamPackage.interpreted memory).run prepared (uploadPins ++ [a, b])
    ∃ storage : PairedStreamOwnership.Tracked, PairedStreamBootstrap.Related memory uploaded storage ∧
      PairedTimed.Related p image storage.inner (Engine.Reactive.reset p) ∧
      storage.enabled = false ∧ storage.inner.registers .pending = 0 ∧ Empty uploaded.result := by
  dsimp only
  obtain ⟨storage, hs, stopped, disabled, count, fire, first, second⟩ :=
    PairedStreamBootstrap.reset_prepares memory initial reset idle hr hi hc
  have delivered := Chip.session_delivers _ count fire first second uploadPins a b _ hd
  have dormant : PairedStreamDormant.Dormant memory
      ((PairedStreamPackage.interpreted memory).run initial [reset, reset, reset, idle, idle]) storage :=
    ⟨hs, disabled, (congrArg (fun pair : Values PairedController.Register × Memory.Sram.State 9 64 =>
      pair.1 .mode) hs.1).symm.trans (reset_mode memory initial reset idle hr)⟩
  have admitted := PairedStreamOwnership.upload_admitted p image cert d₀ d₁ _ storage stopped disabled delivered
  exact ⟨_, PairedStreamBootstrap.run_storage memory _ storage hs _, admitted.1, admitted.2,
    PairedStreamOwnership.upload_pending_false p image cert d₀ d₁ _ storage stopped disabled delivered,
    empty_run memory _ storage dormant (reset_empty memory initial reset idle hr hi) _
      (PairedStreamDormant.upload_history image d₀ d₁ _ delivered)⟩
  done

end Pinwheel.Hardware.Storage.PairedStreamMailboxInit
