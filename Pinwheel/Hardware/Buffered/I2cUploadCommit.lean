import Pinwheel.Hardware.Buffered.I2cUploadPrefix

namespace Pinwheel.Hardware.Buffered.I2cCanonicalUpload
open Pinwheel.Hardware
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

private theorem band_one : ∀ a b : BitVec 1, a &&& b = 1 ↔ a = 1 ∧ b = 1 := by
  decide +kernel

private theorem foldl_one (xs : List α) (f : α → Reactive.E 1) (acc : Reactive.E 1)
    (i : Values Reactive.Input) (s : Values Reactive.Register) :
    (xs.foldl (fun a k => Reactive.both a (f k)) acc).eval i s = 1 ↔
      acc.eval i s = 1 ∧ ∀ k ∈ xs, (f k).eval i s = 1 := by
  induction xs generalizing acc with
  | nil => simp
  | cons a rest ih =>
    rw [List.foldl_cons, ih]
    simp only [Reactive.both, Expr.eval, band_one, List.mem_cons, forall_eq_or_imp, and_assoc]
    done

theorem covered_prefix (i : Values Reactive.Input) (r : Values Reactive.Register)
    (count : i .count = 50) (covered : ∀ k : Fin 64, k.val < 50 → (r .written).getLsbD k.val = true) :
    Reactive.covered.eval i r = 1 := by
  unfold Reactive.covered
  rw [foldl_one]
  refine ⟨rfl, ?_⟩
  intro k _
  have wide : (BitVec.ofNat 7 k.val).toNat = k.val := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    have bound := k.isLt
    omega
  by_cases live : k.val < 50
  · have bit := covered k live
    have slice : (r .written).extractLsb' k.val 1 = 1#1 := by
      apply eq_of_beq
      exact (BitVec.getLsbD_eq_extractLsb' _ _).symm.trans bit
    simp [Reactive.either, Expr.eval, count, wide, slice]
  · simp [Reactive.either, Expr.eval, count, wide, live]
  done

theorem dictionary_full (s : SramState.State)
    (covered : ∀ k : Fin 16, (s.registers .branchWritten).getLsbD k.val = true) :
    s.registers .branchWritten = 65535 := by
  apply (BitVec.eq_of_getLsbD_eq_iff).2
  intro k hk
  have bit := covered ⟨k, hk⟩
  simpa only [show (65535 : BitVec 16) = BitVec.allOnes 16 from rfl,
    BitVec.getLsbD_allOnes, hk, decide_true] using bit
  done

theorem commit_accepted (s : SramState.State)
    (phase : s.core .phase = 0) (retained : s.core .retained = 0)
    (pending : s.core .pending = 1) (space : s.core .generation ≠ 65535)
    (covered : ∀ k : Fin 64, k.val < 50 → (s.core .written).getLsbD k.val = true)
    (dictionary : s.registers .branchWritten = 65535) :
    Sram.committing.eval (s.inputs commitInput) s.registers = 1 := by
  rw [Lifecycle.committing_effective]
  have command : Lifecycle.effectiveInputs s commitInput .command = 2#3 := by
    simp [Lifecycle.effectiveInputs, SharedBranches.mappedInput, SharedBranches.inputExpr,
      SharedBranches.cmd, SharedBranches.tableCovered, SharedBranches.both, Expr.eval,
      SramExecution.selectedShared, Sram.registerExpr, commitInput, dictionary]
  have free : Reactive.free.eval (Lifecycle.effectiveInputs s commitInput)
      (Lifecycle.effectiveState s commitInput) = 1 := by
    simp [Reactive.free, Reactive.resetting, Reactive.cold, Reactive.warm, Reactive.cmd,
      Reactive.busy, Reactive.both, Reactive.either, Expr.eval, command,
      show Lifecycle.effectiveInputs s commitInput .initialize = 0 from rfl,
      show Lifecycle.effectiveState s commitInput .phase = 0 from phase,
      show Lifecycle.effectiveState s commitInput .retained = 0 from retained]
  have coverage := covered_prefix (Lifecycle.effectiveInputs s commitInput)
    (Lifecycle.effectiveState s commitInput) rfl covered
  simp [Reactive.committing, Reactive.countValid, Reactive.spanValid, Reactive.space,
    Reactive.both, Reactive.cmd, Expr.eval, free, command, coverage,
    show Lifecycle.effectiveState s commitInput .pending = 1 from pending,
    show Lifecycle.effectiveState s commitInput .generation ≠ 65535#16 from space,
    show Lifecycle.effectiveInputs s commitInput .count = 50 from rfl,
    show Lifecycle.effectiveInputs s commitInput .virtualSpan = 270 from rfl]
  done

theorem commit_valid (s : SramState.State)
    (accepted : Sram.committing.eval (s.inputs commitInput) s.registers = 1) :
    (s.step commitInput).core .valid = 1 := by
  have reset := reset_zero s commitInput rfl (by decide)
  have noWriting := SramCoverage.commit_no_writing (s.inputs commitInput) s.registers accepted
  change SramCoverage.writing.eval (s.inputs commitInput) s.registers = 0#1 at noWriting
  change Sram.circuit.step (s.inputs commitInput) s.registers (.core .valid) = 1
  rw [SramCoverage.valid_step]
  simp [reset, noWriting, accepted]
  done

end Pinwheel.Hardware.Buffered.I2cCanonicalUpload
