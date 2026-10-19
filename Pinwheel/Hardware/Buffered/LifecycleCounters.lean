import Pinwheel.Hardware.Buffered.LifecycleCircuit

/-! Finite generation/transfer accounting for actual SRAM controller edges.
Counters saturate instead of wrapping. Cold initialization starts a new host
epoch outside the wire identity; no cross-cold-reset replay exclusion is claimed. -/
namespace Pinwheel.Hardware.Buffered.Lifecycle
open Pinwheel.Hardware

theorem reactive_generation_step (i : Values Reactive.Input) (r : Values Reactive.Register) :
    Reactive.circuit.step i r .generation =
      if i .initialize = 1 then 0 else
      if Reactive.committing.eval i r = 1 ∨ (i .command = 7 ∧ r .generation ≠ 65535) then
        r .generation - 65535 else r .generation := by
  have hc : i .initialize = 0#1 ∨ i .initialize = 1#1 := by bv_omega
  have hm : Reactive.committing.eval i r = 0#1 ∨ Reactive.committing.eval i r = 1#1 := by bv_omega
  rcases hc with hc | hc
  all_goals rcases hm with hm | hm
  all_goals by_cases hw : i .command = 7#3
  all_goals by_cases hg : r .generation = 65535#16
  all_goals simp [Circuit.step, Reactive.circuit, Reactive.next, Reactive.cold, Reactive.warm,
    Reactive.either, Reactive.both, Reactive.cmd, Reactive.space, Reactive.increment,
    Expr.eval, hc, hm, hw, hg]
  done

theorem generation_step (s : SramState.State) (i : Values Reactive.Input) :
    (s.step i).core .generation =
      if i .initialize = 1 then 0 else
      if Sram.committing.eval (s.inputs i) s.registers = 1 ∨
          (i .command = 7 ∧ s.core .generation ≠ 65535) then
        s.core .generation - 65535 else s.core .generation := by
  rw [scalar_step s i .generation trivial, reactive_generation_step, ← committing_effective,
    effective_cold]
  simp only [effective_command_nonloader s i 7 (by decide) (by decide) (by decide)]
  rfl
  done

theorem transfer_step (s : SramState.State) (i : Values Reactive.Input) :
    (s.step i).core .transfer =
      if i .initialize = 1 then 0 else
      if Sram.starting.eval (s.inputs i) s.registers = 1 then
        s.core .transfer - 65535 else s.core .transfer := by
  rw [scalar_step s i .transfer trivial]
  change (if effectiveInputs s i .initialize = 1 then 0 else
    if Reactive.starting.eval (effectiveInputs s i) (effectiveState s i) = 1 then
      effectiveState s i .transfer - 65535 else effectiveState s i .transfer) = _
  rw [effective_cold, ← starting_effective]
  rfl
  done

theorem cold_counters (s : SramState.State) (i : Values Reactive.Input)
    (cold : i .initialize = 1) :
    (s.step i).core .generation = 0 ∧ (s.step i).core .transfer = 0 := by
  simp [generation_step, transfer_step, cold]
  done

theorem generation_saturated (s : SramState.State) (i : Values Reactive.Input)
    (cold : i .initialize = 0) (full : s.core .generation = 65535) :
    (s.step i).core .generation = 65535 := by
  have blocked := Reactive.exhausted_generation_rejects_commit
    (effectiveInputs s i) (effectiveState s i) full
  rw [← committing_effective] at blocked
  simp [generation_step, cold, full, blocked]
  done

theorem transfer_saturated (s : SramState.State) (i : Values Reactive.Input)
    (cold : i .initialize = 0) (full : s.core .transfer = 65535) :
    (s.step i).core .transfer = 65535 := by
  have blocked := Reactive.exhausted_transfer_rejects_start
    (effectiveInputs s i) (effectiveState s i) full
  rw [← starting_effective] at blocked
  simp [transfer_step, cold, full, blocked]
  done

end Pinwheel.Hardware.Buffered.Lifecycle
