import Pinwheel.Hardware.Buffered.I2cUploadControl

namespace Pinwheel.Hardware.Buffered.I2cCanonicalUpload
open Pinwheel.Hardware
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

private theorem band_one : ∀ a b : BitVec 1, a &&& b = 1 ↔ a = 1 ∧ b = 1 := by
  decide +kernel

private theorem pack_selected_bit (n : Nat) (f : Fin n → SharedBranches.E 1)
    (i : Values SharedBranches.Input) (s : Values SharedBranches.Register) (k : Fin n) :
    ((SharedBranches.pack f).eval i s).getLsbD k.val = ((f k).eval i s).getLsbD 0 := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    cases n with
    | zero => exact Fin.elim0 k
    | succ n =>
      cases n with
      | zero => have hk : k = 0 := Fin.ext (by omega); subst k; rfl
      | succ n =>
        cases k using Fin.cases with
        | zero => simp only [SharedBranches.pack, Expr.eval, Fin.val_zero, BitVec.getLsbD_append]; rfl
        | succ k =>
          have hnot : ¬ (k.val+1 < 1) := by omega
          simpa only [SharedBranches.pack, Expr.eval, BitVec.getLsbD_append, Fin.val_succ,
            hnot, if_false, Nat.add_sub_cancel] using
            ih (n+1) (by omega) (fun j => f j.succ) k
          done

theorem written_here (s : SramState.State) (i : Values Reactive.Input)
    (reset : SramCoverage.resetting.eval (s.inputs i) s.registers = 0)
    (writing : SramCoverage.writing.eval (s.inputs i) s.registers = 1)
    (row : Sram.rowWriting.eval (s.inputs i) s.registers = 1)
    (k : Fin 64) (address : i .address = BitVec.ofNat 6 k.val) :
    ((s.step i).core .written).getLsbD k.val = true := by
  rw [SramCoverage.resetting, SramCoverage.control_correct] at reset
  rw [SramCoverage.writing, SramCoverage.control_correct] at writing
  rw [Sram.rowWriting, SramCoverage.control_correct] at row
  change ((Sram.control SharedBranches.rowWrittenNext).eval (s.inputs i) s.registers).getLsbD k.val = true
  rw [SramCoverage.control_correct]
  simp only [SharedBranches.rowWrittenNext, Expr.eval, reset, writing,
    show (0 : BitVec 1) ≠ 1 from by decide, ↓reduceIte]
  rw [pack_selected_bit]
  simp [SharedBranches.both, Expr.eval, row, SramCoverage.baseInput,
    SramState.State.inputs, address]
  done

theorem table_here (s : SramState.State) (i : Values Reactive.Input)
    (reset : SramCoverage.resetting.eval (s.inputs i) s.registers = 0)
    (writing : SramCoverage.writing.eval (s.inputs i) s.registers = 1)
    (table : Sram.tableWriting.eval (s.inputs i) s.registers = 1)
    (k : Fin 16) (address : (i .address).extractLsb' 0 4 = BitVec.ofNat 4 k.val) :
    ((s.step i).registers .branchWritten).getLsbD k.val = true := by
  rw [SramCoverage.resetting, SramCoverage.control_correct] at reset
  rw [SramCoverage.writing, SramCoverage.control_correct] at writing
  rw [Sram.tableWriting, SramCoverage.control_correct] at table
  change ((Sram.control SharedBranches.branchWrittenNext).eval (s.inputs i) s.registers).getLsbD k.val = true
  rw [SramCoverage.control_correct]
  simp only [SharedBranches.branchWrittenNext, Expr.eval, reset, writing,
    show (0 : BitVec 1) ≠ 1 from by decide, ↓reduceIte]
  rw [pack_selected_bit]
  simp [SharedBranches.both, Expr.eval, table, SramCoverage.baseInput,
    SramState.State.inputs, address]
  done

theorem written_keep (s : SramState.State) (i : Values Reactive.Input)
    (reset : SramCoverage.resetting.eval (s.inputs i) s.registers = 0)
    (writing : SramCoverage.writing.eval (s.inputs i) s.registers = 1)
    (pending : s.core .pending = 1) (k : Fin 64)
    (old : (s.core .written).getLsbD k.val = true) :
    ((s.step i).core .written).getLsbD k.val = true := by
  change s.registers (.core .pending) = 1#1 at pending
  change (s.registers (.core .written)).getLsbD k.val = true at old
  rw [SramCoverage.resetting, SramCoverage.control_correct] at reset
  rw [SramCoverage.writing, SramCoverage.control_correct] at writing
  change ((Sram.control SharedBranches.rowWrittenNext).eval (s.inputs i) s.registers).getLsbD k.val = true
  rw [SramCoverage.control_correct]
  simp only [SharedBranches.rowWrittenNext, Expr.eval, reset, writing,
    show (0 : BitVec 1) ≠ 1 from by decide, ↓reduceIte]
  rw [pack_selected_bit]
  simp [SharedBranches.firstWriting, SharedBranches.both, Expr.eval, writing,
    SramCoverage.controlState, pending]
  split <;> simp [old]
  done

theorem table_keep (s : SramState.State) (i : Values Reactive.Input)
    (reset : SramCoverage.resetting.eval (s.inputs i) s.registers = 0)
    (writing : SramCoverage.writing.eval (s.inputs i) s.registers = 1)
    (pending : s.core .pending = 1) (k : Fin 16)
    (old : (s.registers .branchWritten).getLsbD k.val = true) :
    ((s.step i).registers .branchWritten).getLsbD k.val = true := by
  change s.registers (.core .pending) = 1#1 at pending
  rw [SramCoverage.resetting, SramCoverage.control_correct] at reset
  rw [SramCoverage.writing, SramCoverage.control_correct] at writing
  change ((Sram.control SharedBranches.branchWrittenNext).eval (s.inputs i) s.registers).getLsbD k.val = true
  rw [SramCoverage.control_correct]
  simp only [SharedBranches.branchWrittenNext, Expr.eval, reset, writing,
    show (0 : BitVec 1) ≠ 1 from by decide, ↓reduceIte]
  rw [pack_selected_bit]
  simp [SharedBranches.firstWriting, SharedBranches.both, Expr.eval, writing,
    SramCoverage.controlState, pending]
  split <;> simp [old]
  done

end Pinwheel.Hardware.Buffered.I2cCanonicalUpload
