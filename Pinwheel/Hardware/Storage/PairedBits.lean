import Pinwheel.Hardware.Storage.PairedRuntime

/-! Bit-level observations of the retained paired datapath, including the
same-edge capture used by branch selection. -/
namespace Pinwheel.Hardware.Storage.PairedBits
open Pinwheel.Hardware PairedController
set_option backward.isDefEq.respectTransparency false

def samples (word : BitVec 16) : Reactive.Samples :=
  Vector.ofFn fun k => word[k.val]

theorem pack_bit (n : Nat) (f : Fin n → E 1) (g : Values GraphInput)
    (s : Values Register) (k : Fin n) :
    ((pack f).eval g s)[k.val] = ((f k).eval g s)[0] := by
  induction n with
  | zero => exact Fin.elim0 k
  | succ n ih =>
    cases n
    case succ n =>
      cases k using Fin.cases
      all_goals simp [pack, Expr.eval, BitVec.getElem_append, ih]
    case zero => simp [show k = 0 from Fin.ext (by omega), pack]

theorem slice_one (x : BitVec w) (offset : Nat) :
    x.extractLsb' offset 1 = BitVec.ofBool (x.getLsbD offset) := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp [show i = 0 from by omega]

theorem capture_bit (descriptor : E 6) (old : E 16) (g : Values GraphInput)
    (s : Values Register) (k : Fin 16) :
    ((capture descriptor old).eval g s)[k.val] =
      (Engine.Reactive.capture (samples (old.eval g s))
        (Execution.getCapture (descriptor.eval g s)) (incoming.eval g s))[k.val] := by
  simp only [capture, pack_bit, both, bit, Expr.eval]
  by_cases he : (descriptor.eval g s)[0] = true <;>
    by_cases hd : ((descriptor.eval g s).extractLsb' 2 4).toFin = k <;>
    simp_all [slice_one, Execution.getCapture, Engine.Reactive.capture,
      Engine.capture, samples, Reactive.slot_eq, ← BitVec.getLsbD_eq_getElem]
  cases (descriptor.eval g s).getLsbD 1 <;> simp
  done

theorem capture_samples (descriptor : E 6) (old : E 16) (g : Values GraphInput)
    (s : Values Register) :
    samples ((capture descriptor old).eval g s) =
      Engine.Reactive.capture (samples (old.eval g s))
        (Execution.getCapture (descriptor.eval g s)) (incoming.eval g s) := by
  exact Vector.ext (fun k hk => by
    simpa only [samples, Vector.getElem_ofFn] using capture_bit descriptor old g s ⟨k, hk⟩)

theorem samples_read (word : BitVec 16) (address : BitVec 4) :
    word.extractLsb' address.toNat 1 = BitVec.ofBool (samples word)[address.toNat] := by
  simp [slice_one, samples, ← BitVec.getLsbD_eq_getElem]

theorem samples_zero : samples 0 = Vector.replicate 16 false := by
  simp [samples, Vector.ext_iff]

theorem incoming_value (g : Values GraphInput) (s : Values Register)
    (h : PairedSemantics.Equations bindings g s) : incoming.eval g s = g (.base .incoming) := by
  simpa only [incoming, incomingExpr, Expr.eval, BitVec.extractLsb'_append_eq_right] using
    congrArg (fun v : BitVec 64 => v.extractLsb' 0 2)
      (h .incoming (.concat (.lit (0 : BitVec 62)) incomingExpr) (by simp [bindings]))

theorem exited_wire (g : Values GraphInput) (s : Values Register)
    (h : PairedSemantics.Equations bindings g s) : exited.eval g s = exitedExpr.eval g s := by
  simpa only [exited, Expr.eval, BitVec.extractLsb'_append_eq_right] using
    congrArg (fun v : BitVec 64 => v.extractLsb' 0 16)
      (h .exited (.concat (.lit (0 : BitVec 48)) exitedExpr) (by simp [bindings]))

theorem branch_wire (g : Values GraphInput) (s : Values Register)
    (h : PairedSemantics.Equations bindings g s) : branch.eval g s = branchExpr.eval g s := by
  simpa only [branch, Expr.eval, BitVec.extractLsb'_append_eq_right] using
    congrArg (fun v : BitVec 64 => v.extractLsb' 0 1)
      (h .branch (.concat (.lit (0 : BitVec 63)) branchExpr) (by simp [bindings]))

theorem terminal_samples (g : Values GraphInput) (s : Values Register)
    (h : PairedSemantics.Equations bindings g s) (hm : s .mode = 3) :
    samples (exited.eval g s) = Engine.Reactive.capture (samples (s .samples))
      (Execution.getCapture ((s .cached).extractLsb' 6 6)) (g (.base .incoming)) := by
  simp only [exited_wire g s h, exitedExpr, isMode, Expr.eval, hm, decide_true,
    BitVec.ofBool_true, if_true, capture_samples, incoming_value g s h]
  done

theorem branch_capture (g : Values GraphInput) (s : Values Register)
    (h : PairedSemantics.Equations bindings g s) (hm : s .mode = 3) :
    branch.eval g s = BitVec.ofBool
      (Engine.Reactive.capture (samples (s .samples))
        (Execution.getCapture ((s .cached).extractLsb' 6 6)) (g (.base .incoming)))[
          ((s .cached).extractLsb' 16 4).toNat] := by
  simp only [branch_wire g s h, branchExpr, both, isMode, Expr.eval,
    hm, decide_true, BitVec.ofBool_true, Execution.readTree_correct]
  rw [samples_read, terminal_samples g s h hm]
  exact BitVec.allOnes_and
  done

end Pinwheel.Hardware.Storage.PairedBits
