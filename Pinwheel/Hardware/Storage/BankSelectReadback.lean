import Pinwheel.Hardware.Storage.BankSelect

namespace Pinwheel.Hardware.Storage.Backend.BankSelect.Readback
open Loader

inductive StageInput (width : Nat) : Nat → Type where
  | value : StageInput width width

def stageValues (v : BitVec width) : Values (StageInput width)
  | _, .value => v

def indexStage (b : Bool) : Expr (StageInput 8) Register 6 := bankIndex b (.input .value)
def wordStage (b : Bool) : Expr (StageInput 6) Register 64 := bankWord b (.input .value)

theorem control_read_correct (i : Machine.Inputs) (s : State) :
    Backend.Readback.wordRead.eval (Backend.Readback.wordInputs (selected.eval i.values s.values)
      (Backend.Readback.indexRead.eval
        (Backend.Readback.readInputs (selected.eval i.values s.values) (target.eval i.values s.values)) s.values)) s.values =
      (successor false).eval i.values s.values := by
  simpa only [Backend.Readback.selected, Backend.Readback.target, selected, target,
    successor, Bool.false_eq_true, reduceIte, lift_eq, Backend.successor] using
    Backend.Readback.read_correct i s
  done

set_option backward.isDefEq.respectTransparency false in
theorem late_read_correct (i : Values Machine.Input) (s : Values Register) :
    (if selected.eval i s = 1 then
      (wordStage true).eval (stageValues ((indexStage true).eval (stageValues (target.eval i s)) s)) s
    else (wordStage false).eval (stageValues ((indexStage false).eval (stageValues (target.eval i s)) s)) s) =
      (successor true).eval i s := by
  simp only [successor, reduceIte, lateRead, indexStage, wordStage, bankWord, bankIndex,
    Execution.readTree_correct, Expr.eval, stageValues]
  simp only [Backend.Readback.word]
  split
  all_goals split <;> rfl
  done

end Pinwheel.Hardware.Storage.Backend.BankSelect.Readback
