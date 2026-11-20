import Pinwheel.Hardware.Stream.Encoding
import Std.Data.String.ToNat

namespace Pinwheel.Hardware.Stream

inductive CellReg (width count : Nat) : Nat → Type where
  | valid (k : Fin count) : CellReg width count 1
  | data (k : Fin count) : CellReg width count width

def CellReg.position : CellReg w n b → Fin (n + n)
  | .valid k => ⟨k.val, by omega⟩
  | .data k => ⟨n + k.val, by omega⟩

def CellReg.signal (k : Fin (n + n)) : Sigma (CellReg w n) :=
  if h : k.val < n then ⟨1, .valid ⟨k.val, h⟩⟩
  else ⟨w, .data ⟨k.val - n, by omega⟩⟩

theorem CellReg.signal_position (r : CellReg w n b) : signal r.position = ⟨b, r⟩ := by
  cases r <;> simp [signal, position, Nat.not_lt_of_ge (Nat.le_add_right n _)]

theorem CellReg.position_signal (k : Fin (n + n)) :
    (signal (w := w) k).2.position = k := by
  by_cases h : k.val < n
  · exact congrArg (fun p : Sigma (CellReg w n) => p.2.position) (dif_pos h)
  · have hs : signal (w := w) k = ⟨w, .data ⟨k.val - n, by omega⟩⟩ := dif_neg h
    have hp := congrArg (fun p : Sigma (CellReg w n) => p.2.position) hs
    exact hp.trans (Fin.ext (by simp only [position]; omega))

def CellReg.interface (w n : Nat) : Interface (CellReg w n) where
  size := n + n
  signal := signal
  position := position
  signal_position := signal_position
  label := fun r => "slot_" ++ Nat.repr r.position.val
  unique := by
    intro a b h
    simp only [position_signal, String.append_right_inj] at h
    exact Fin.ext (Nat.repr_injective h)

def cells (q : List (BitVec w)) : Values (CellReg w n)
  | _, .valid k => BitVec.ofBool (q[k.val]?.isSome)
  | _, .data k => q[k.val]?.getD 0

def cellValid (w n k : Nat) : Expr I (CellReg w n) 1 :=
  if h : k < n then .reg (.valid ⟨k, h⟩) else .lit 0

def cellData (w n k : Nat) : Expr I (CellReg w n) w :=
  if h : k < n then .reg (.data ⟨k, h⟩) else .lit 0

@[simp] theorem cellValid_eval (q : List (BitVec w)) (hq : q.length ≤ n)
    (i : Values I) (k : Nat) :
    (cellValid w n k).eval i (cells q) = BitVec.ofBool q[k]?.isSome := by
  simp only [cellValid]
  split <;> simp_all [Expr.eval, cells]
  rw [List.getElem?_eq_none (by omega)]
  rfl

@[simp] theorem cellData_eval (q : List (BitVec w)) (hq : q.length ≤ n)
    (i : Values I) (k : Nat) :
    (cellData w n k).eval i (cells q) = q[k]?.getD 0 := by
  simp only [cellData]
  split <;> simp_all [Expr.eval, cells]
  rw [List.getElem?_eq_none (by omega)]
  rfl

end Pinwheel.Hardware.Stream
