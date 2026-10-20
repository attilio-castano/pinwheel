import Pinwheel.Hardware.Buffered.LifecycleCounters
import Pinwheel.Hardware.Buffered.SpiCircuit

/-! Admission and reset facts for the actual SRAM controller. A wire identity is
the finite generation/transfer pair; cold initialization does not authenticate
a host epoch. -/
namespace Pinwheel.Hardware.Buffered.Lifecycle
open Pinwheel.Hardware

theorem starting_facts (s : SramState.State) (i : Values Reactive.Input)
    (starting : Sram.starting.eval (s.inputs i) s.registers = 1) :
    SpiCircuit.StartingFacts i s.core := by
  rw [starting_effective, starting_direct] at starting
  exact SpiCircuit.starting_facts i s.core starting
  done

theorem start_transfer_sequence (s : SramState.State) (i : Values Reactive.Input)
    (starting : Sram.starting.eval (s.inputs i) s.registers = 1) :
    ((s.step i).core .transfer).toNat = (s.core .transfer).toNat + 1 := by
  have facts := starting_facts s i starting
  rw [transfer_step, facts.cold]
  simp only [show (0 : BitVec 1) ≠ 1 from by decide, if_false, starting, if_true]
  exact Reactive.increment16_no_wrap _ (by
    intro full
    have bound := facts.transfer
    rw [full] at bound
    exact (by decide : ¬ (65535 : Nat) < 65535) bound)
  done

theorem resetting_cold (s : SramState.State) (i : Values Reactive.Input)
    (cold : i .initialize = 1) :
    Reactive.resetting.eval (effectiveInputs s i) (effectiveState s i) = 1 := by
  rw [resetting_effective]
  simp [Reactive.resetting, Reactive.cold, Reactive.either, Expr.eval, cold]
  done

theorem resetting_warm (s : SramState.State) (i : Values Reactive.Input)
    (cold : i .initialize = 0) (warm : i .command = 7) :
    Reactive.resetting.eval (effectiveInputs s i) (effectiveState s i) = 1 := by
  rw [resetting_effective]
  simp [Reactive.resetting, Reactive.cold, Reactive.warm, Reactive.both,
    Reactive.either, Reactive.cmd, Expr.eval, cold, warm]
  done

theorem reset_ownership (s : SramState.State) (i : Values Reactive.Input)
    (reset : Reactive.resetting.eval i s.core = 1) :
    (s.step i).core .valid = 0 ∧ (s.step i).core .retained = 0 ∧
      (s.step i).core .phase = 0 := by
  have h := Reactive.warm_invalidates_ownership (effectiveInputs s i) (effectiveState s i)
    (by rw [resetting_effective]; exact reset)
  simpa only [← scalar_step s i .valid trivial, ← scalar_step s i .retained trivial,
    ← scalar_step s i .phase trivial] using h
  done

theorem warm_transfer (s : SramState.State) (i : Values Reactive.Input)
    (cold : i .initialize = 0) (warm : i .command = 7) :
    (s.step i).core .transfer = s.core .transfer := by
  have hs : Reactive.starting.eval i s.core = 0 := by
    simp [Reactive.starting, Reactive.both, Reactive.cmd, Expr.eval, warm]
  rw [transfer_step, starting_effective, starting_direct, hs]
  simp [cold]
  done

theorem committing_facts (s : SramState.State) (i : Values Reactive.Input)
    (committing : Sram.committing.eval (s.inputs i) s.registers = 1) :
    i .initialize = 0 ∧ s.core .generation ≠ 65535 := by
  have accepted := committing
  rw [committing_effective] at accepted
  have hc : effectiveInputs s i .initialize ≠ 1 := by
    intro cold
    simp [Reactive.committing, Reactive.free, Reactive.resetting, Reactive.cold,
      Reactive.either, Reactive.both, Expr.eval, cold] at accepted
  have hg : effectiveState s i .generation ≠ 65535 := by
    intro full
    rw [Reactive.exhausted_generation_rejects_commit _ _ full] at accepted
    exact (by decide : (0 : BitVec 1) ≠ 1) accepted
  exact ⟨(BitVec.eq_zero_or_eq_one _).resolve_right hc, hg⟩
  done

theorem commit_generation_sequence (s : SramState.State) (i : Values Reactive.Input)
    (committing : Sram.committing.eval (s.inputs i) s.registers = 1) :
    ((s.step i).core .generation).toNat = (s.core .generation).toNat + 1 := by
  have facts := committing_facts s i committing
  rw [generation_step, facts.1]
  simp only [show (0 : BitVec 1) ≠ 1 from by decide, if_false, committing, true_or, if_true]
  exact Reactive.increment16_no_wrap _ facts.2
  done

theorem warm_generation (s : SramState.State) (i : Values Reactive.Input)
    (cold : i .initialize = 0) (warm : i .command = 7) :
    ((s.step i).core .generation).toNat = min 65535 ((s.core .generation).toNat + 1) := by
  have reset := resetting_warm s i cold warm
  have hm : Sram.committing.eval (s.inputs i) s.registers = 0 := by
    rw [committing_effective]
    simp [Reactive.committing, Reactive.free, Reactive.both, Expr.eval, reset]
  rw [generation_step, cold]
  simp only [show (0 : BitVec 1) ≠ 1 from by decide, if_false, hm, false_or,
    warm, true_and]
  split
  · rename_i notFull
    rw [Reactive.increment16_no_wrap _ notFull]
    have bound := (s.core .generation).isLt
    have unequal : (s.core .generation).toNat ≠ 65535 := by
      intro equal
      exact notFull (BitVec.eq_of_toNat_eq equal)
    omega
  · rename_i full
    have equal := Classical.not_not.mp full
    rw [equal]
    decide
  done

theorem transfer_monotone (s : SramState.State) (i : Values Reactive.Input)
    (cold : i .initialize = 0) :
    (s.core .transfer).toNat ≤ ((s.step i).core .transfer).toNat := by
  by_cases start : Sram.starting.eval (s.inputs i) s.registers = 1#1
  · rw [start_transfer_sequence s i start]
    omega
  · simp [transfer_step, cold, start]
  done

theorem generation_monotone (s : SramState.State) (i : Values Reactive.Input)
    (cold : i .initialize = 0) :
    (s.core .generation).toNat ≤ ((s.step i).core .generation).toNat := by
  by_cases commit : Sram.committing.eval (s.inputs i) s.registers = 1#1
  · rw [commit_generation_sequence s i commit]
    omega
  · by_cases warm : i .command = 7#3
    · rw [warm_generation s i cold warm]
      have bound := (s.core .generation).isLt
      omega
    · simp [generation_step, cold, commit, warm]
  done

theorem release_exact (i : Values Reactive.Input) (r : Values Reactive.Register)
    (cold : i .initialize = 0) (command : i .command = 4) (retained : r .retained = 1)
    (generation : i .expectedGeneration = r .generation)
    (transfer : i .expectedTransfer = r .transfer) : Reactive.releasing.eval i r = 1 := by
  simp [Reactive.releasing, Reactive.resetting, Reactive.cold, Reactive.warm,
    Reactive.both, Reactive.either, Reactive.cmd, Expr.eval, cold, command, retained,
    generation, transfer]
  done

theorem release_stale_generation (s : SramState.State) (i : Values Reactive.Input)
    (stale : i .expectedGeneration ≠ s.core .generation) :
    Reactive.releasing.eval (effectiveInputs s i) (effectiveState s i) = 0 := by
  rw [releasing_effective]
  exact Reactive.stale_generation_cannot_release i s.core stale
  done

theorem release_stale_transfer (s : SramState.State) (i : Values Reactive.Input)
    (stale : i .expectedTransfer ≠ s.core .transfer) :
    Reactive.releasing.eval (effectiveInputs s i) (effectiveState s i) = 0 := by
  rw [releasing_effective]
  exact Reactive.stale_transfer_cannot_release i s.core stale
  done

end Pinwheel.Hardware.Buffered.Lifecycle
