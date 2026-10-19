import Pinwheel.Hardware.Buffered.LifecycleAdmission

/-! Loader histories contain no reset or START. They cannot allocate a transfer
or leave the idle, unowned state. Generation accounting counts actual accepted
COMMIT edges, including histories with repeated or rejected uploads. -/
namespace Pinwheel.Hardware.Buffered.LifecycleUpload
open Pinwheel.Hardware

structure Input (i : Values Reactive.Input) : Prop where
  cold : i .initialize = 0
  start : i .command ≠ 3#3
  warm : i .command ≠ 7#3

private theorem reactive_idle (i : Values Reactive.Input) (r : Values Reactive.Register)
    (cold : i .initialize = 0) (noStart : i .command ≠ 3#3) (noWarm : i .command ≠ 7#3)
    (phase : r .phase = 0) (retained : r .retained = 0) :
    Reactive.circuit.step i r .phase = 0 ∧ Reactive.circuit.step i r .retained = 0 := by
  have reset : Reactive.resetting.eval i r = 0 := by
    simp [Reactive.resetting, Reactive.cold, Reactive.warm, Reactive.both,
      Reactive.either, Reactive.cmd, Expr.eval, cold, noWarm]
  have start : Reactive.starting.eval i r = 0 := by
    simp [Reactive.starting, Reactive.both, Reactive.cmd, Expr.eval, noStart]
  have dispatch : Reactive.dispatch.eval i r = 0 := by
    simp [Reactive.dispatch, Reactive.terminalEdge, Reactive.isPhase,
      Reactive.both, Reactive.either, Expr.eval, phase]
  have entering : Reactive.entering.eval i r = 0 := by
    simp [Reactive.entering, Reactive.both, Reactive.either, Expr.eval, start, dispatch]
  have stopping : Reactive.stopping.eval i r = 0 := by
    simp [Reactive.stopping, Reactive.heldFault, Reactive.heldTimeout,
      Reactive.entryFailed, Reactive.entryComplete, Reactive.isPhase,
      Reactive.both, Reactive.either, Expr.eval, phase, entering]
  have releasing : Reactive.releasing.eval i r = 0 := by
    simp [Reactive.releasing, Reactive.both, Expr.eval, retained]
  constructor
  all_goals simp [Circuit.step, Reactive.circuit, Reactive.next, Reactive.clearOwner,
    Reactive.either, Expr.eval, reset, entering, stopping, releasing, phase, retained]

theorem idle_step (s : SramState.State) (i : Values Reactive.Input) (input : Input i)
    (phase : s.core .phase = 0) (retained : s.core .retained = 0) :
    (s.step i).core .phase = 0 ∧ (s.step i).core .retained = 0 := by
  have noStart : Lifecycle.effectiveInputs s i .command ≠ 3 := by
    intro h
    exact input.start ((Lifecycle.effective_command_nonloader s i 3
      (by decide) (by decide) (by decide)).mp h)
  have noWarm : Lifecycle.effectiveInputs s i .command ≠ 7 := by
    intro h
    exact input.warm ((Lifecycle.effective_command_nonloader s i 7
      (by decide) (by decide) (by decide)).mp h)
  have h := reactive_idle (Lifecycle.effectiveInputs s i) (Lifecycle.effectiveState s i)
    input.cold noStart noWarm phase retained
  exact ⟨(Lifecycle.scalar_step s i .phase trivial).trans h.1,
    (Lifecycle.scalar_step s i .retained trivial).trans h.2⟩

theorem transfer_step (s : SramState.State) (i : Values Reactive.Input) (input : Input i) :
    (s.step i).core .transfer = s.core .transfer := by
  have noStart : Sram.starting.eval (s.inputs i) s.registers = 0 := by
    rw [Lifecycle.starting_effective, Lifecycle.starting_direct]
    simp [Reactive.starting, Reactive.both, Reactive.cmd, Expr.eval, input.start]
  simp [Lifecycle.transfer_step, input.cold, noStart]

def commitCount (s : SramState.State) : List (Values Reactive.Input) → Nat
  | [] => 0
  | i :: rest => (if Sram.committing.eval (s.inputs i) s.registers = 1#1 then 1 else 0) +
      commitCount (s.step i) rest

theorem generation_step (s : SramState.State) (i : Values Reactive.Input) (input : Input i) :
    ((s.step i).core .generation).toNat = (s.core .generation).toNat +
      (if Sram.committing.eval (s.inputs i) s.registers = 1#1 then 1 else 0) := by
  by_cases commit : Sram.committing.eval (s.inputs i) s.registers = 1#1
  · rw [if_pos commit]
    exact Lifecycle.commit_generation_sequence s i commit
  · simp [Lifecycle.generation_step, input.cold, input.warm, commit]

theorem run (s : SramState.State) (inputs : List (Values Reactive.Input))
    (allInputs : ∀ i ∈ inputs, Input i) (phase : s.core .phase = 0)
    (retained : s.core .retained = 0) :
    (s.run inputs).core .phase = 0 ∧ (s.run inputs).core .retained = 0 ∧
      (s.run inputs).core .transfer = s.core .transfer ∧
      ((s.run inputs).core .generation).toNat = (s.core .generation).toNat + commitCount s inputs := by
  induction inputs generalizing s
  case nil => exact ⟨phase, retained, rfl, by simp [SramState.State.run, commitCount]⟩
  case cons i rest ih =>
    have input := allInputs i (by simp)
    have idle := idle_step s i input phase retained
    have tail := ih (s.step i)
      (fun j member => allInputs j (List.mem_cons.mpr (Or.inr member))) idle.1 idle.2
    refine ⟨tail.1, tail.2.1, tail.2.2.1.trans (transfer_step s i input), ?_⟩
    change (((s.step i).run rest).core .generation).toNat = _
    rw [tail.2.2.2, generation_step s i input]
    simp only [commitCount]
    omega

end Pinwheel.Hardware.Buffered.LifecycleUpload
