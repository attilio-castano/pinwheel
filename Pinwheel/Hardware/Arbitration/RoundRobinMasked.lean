import Pinwheel.Hardware.Arbitration.RoundRobinCircuit
import Pinwheel.Hardware.Stream.Encoding

/-! A two-pass round-robin value selector. One prefix-OR cursor decoder masks
the first ascending priority pass; the unmasked pass handles wraparound.
Cursor wires must encode exactly one current position. Request wires, selected
values and the fallback may be arbitrary typed expressions.
-/
namespace Pinwheel.Hardware.Arbitration.RoundRobinMasked

open RoundRobinCircuit

set_option backward.isDefEq.respectTransparency false

def anyWire (bits : α → Expr I R 1) (xs : List α) : Expr I R 1 :=
  xs.foldr (fun x rest => (bits x).bor rest) (.lit 0)

/-- Descending prefixes share their tails in the emitted expression DAG. -/
def cursorPrefix (cursor : Fin (n+1) → Expr I R 1) (k : Fin (n+1)) : Expr I R 1 :=
  anyWire cursor (((List.finRange (n+1)).filter (fun j => j.val ≤ k.val)).reverse)

def maskedRequest (cursor request : Fin (n+1) → Expr I R 1) (k : Fin (n+1)) : Expr I R 1 :=
  .band (request k) (cursorPrefix cursor k)

def selection (cursor request : Fin (n+1) → Expr I R 1)
    (value : Fin (n+1) → Expr I R w) (fallback : Expr I R w) : Expr I R w :=
  .mux (anyWire (maskedRequest cursor request) (List.finRange (n+1)))
    (priority (maskedRequest cursor request) value fallback (List.finRange (n+1)))
    (priority request value fallback (List.finRange (n+1)))

def maskedBits (cursor : Fin (n+1)) (request : Fin (n+1) → Bool) (k : Fin (n+1)) : Bool :=
  request k && decide (cursor.val ≤ k.val)

theorem ascending_minimal (bits : Fin (n+1) → Bool) (winner target : Fin (n+1))
    (h : (List.finRange (n+1)).find? bits = some winner) (ht : bits target = true) :
    winner.val ≤ target.val := by
  obtain ⟨_, index, hi, he, hbefore⟩ := List.find?_eq_some_iff_getElem.mp h
  have heval : index = winner.val := by simpa using congrArg Fin.val he
  by_cases hle : winner.val ≤ target.val
  · exact hle
  · have hn := hbefore target.val (by omega)
    simp [ht] at hn

theorem grant_of_minimal (cursor winner : Fin (n+1)) (request : Fin (n+1) → Bool)
    (hw : request winner = true)
    (hmin : ∀ target, request target = true →
      RoundRobin.distance cursor winner ≤ RoundRobin.distance cursor target) :
    RoundRobin.grant cursor request = some winner := by
  cases hg : RoundRobin.grant cursor request with
  | none =>
    have hn := (RoundRobin.grant_none_iff cursor request).mp hg winner
    simp [hw] at hn
  | some actual =>
    have hd := Nat.le_antisymm (RoundRobin.grant_priority hg hw)
      (hmin actual (RoundRobin.grant_requested hg))
    congr 1
    apply Fin.ext
    simp only [RoundRobin.distance] at hd
    split at hd <;> split at hd <;> omega

theorem grant_two_pass (cursor : Fin (n+1)) (request : Fin (n+1) → Bool) :
    ((List.finRange (n+1)).find? (maskedBits cursor request)).orElse
      (fun _ => (List.finRange (n+1)).find? request) = RoundRobin.grant cursor request := by
  cases hm : (List.finRange (n+1)).find? (maskedBits cursor request) with
  | none =>
    have below : ∀ target, request target = true → ¬ cursor.val ≤ target.val := by
      intro target ht
      simpa [maskedBits, ht] using List.find?_eq_none.mp hm target (by simp)
    simp only [Option.orElse_none]
    cases ha : (List.finRange (n+1)).find? request with
    | none =>
      apply ((RoundRobin.grant_none_iff cursor request).mpr ?_).symm
      exact fun k => by simpa using List.find?_eq_none.mp ha k (by simp)
    | some winner =>
      apply (grant_of_minimal cursor winner request (List.find?_some ha) ?_).symm
      intro target ht
      simp only [RoundRobin.distance, if_neg (below winner (List.find?_some ha)), if_neg (below target ht)]
      exact Nat.add_le_add_left (ascending_minimal request winner target ha ht) _
  | some winner =>
    simp only [Option.orElse_some]
    have hw := List.find?_some hm
    simp only [maskedBits, Bool.and_eq_true, decide_eq_true_eq] at hw
    apply (grant_of_minimal cursor winner request hw.1 ?_).symm
    intro target ht
    by_cases habove : cursor.val ≤ target.val
    · have hmin := ascending_minimal (maskedBits cursor request) winner target hm
        (by simp [maskedBits, ht, habove])
      simp only [RoundRobin.distance, if_pos hw.2, if_pos habove]
      omega
    · simp only [RoundRobin.distance, if_pos hw.2, if_neg habove]
      omega

theorem anyWire_eval (bits : α → Expr I R 1) (xs : List α) (i : Values I) (s : Values R)
    (f : α → Bool) (h : ∀ x, (bits x).eval i s = BitVec.ofBool (f x)) :
    (anyWire bits xs).eval i s = BitVec.ofBool (xs.any f) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change ((bits x).bor (anyWire bits xs)).eval i s = _
    simp [h, ih]

theorem prefix_eval (cursor : Fin (n+1) → Expr I R 1) (position k : Fin (n+1))
    (i : Values I) (s : Values R)
    (h : ∀ j, (cursor j).eval i s = BitVec.ofBool (j == position)) :
    (cursorPrefix cursor k).eval i s = BitVec.ofBool (decide (position.val ≤ k.val)) := by
  rw [cursorPrefix, anyWire_eval _ _ _ _ _ h]
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp [List.any_eq_true]

theorem maskedRequest_eval (cursor request : Fin (n+1) → Expr I R 1)
    (position : Fin (n+1)) (bits : Fin (n+1) → Bool) (i : Values I) (s : Values R)
    (hc : ∀ j, (cursor j).eval i s = BitVec.ofBool (j == position))
    (hr : ∀ j, (request j).eval i s = BitVec.ofBool (bits j)) (k : Fin (n+1)) :
    (maskedRequest cursor request k).eval i s = BitVec.ofBool (maskedBits position bits k) := by
  simp [maskedRequest, Expr.eval, prefix_eval cursor position k i s hc, hr, maskedBits]

/-- The selector works for arbitrary value and fallback expressions. Its only
cursor assumption is exact one-hot encoding; requests need no further invariant. -/
theorem selection_eval (cursor request : Fin (n+1) → Expr I R 1)
    (value : Fin (n+1) → Expr I R w) (fallback : Expr I R w)
    (position : Fin (n+1)) (bits : Fin (n+1) → Bool) (i : Values I) (s : Values R)
    (hc : ∀ j, (cursor j).eval i s = BitVec.ofBool (j == position))
    (hr : ∀ j, (request j).eval i s = BitVec.ofBool (bits j)) :
    (selection cursor request value fallback).eval i s =
      match RoundRobin.grant position bits with
      | none => fallback.eval i s
      | some winner => (value winner).eval i s := by
  rw [selection, Expr.eval, anyWire_eval _ _ _ _ _ (maskedRequest_eval cursor request position bits i s hc hr)]
  rw [priority_eval _ _ _ _ _ _ _ (maskedRequest_eval cursor request position bits i s hc hr),
    priority_eval _ _ _ _ _ _ _ hr, ← List.isSome_find?, ← grant_two_pass]
  cases (List.finRange (n+1)).find? (maskedBits position bits) <;>
    cases (List.finRange (n+1)).find? bits <;> rfl

theorem raw_selection_eval (cursor request : Fin (n+1) → Expr I R 1)
    (value : Fin (n+1) → Expr I R w) (fallback : Expr I R w)
    (position : Fin (n+1)) (i : Values I) (s : Values R)
    (hc : ∀ j, (cursor j).eval i s = BitVec.ofBool (j == position)) :
    (selection cursor request value fallback).eval i s =
      match RoundRobin.grant position (fun j => (request j).eval i s == 1) with
      | none => fallback.eval i s
      | some winner => (value winner).eval i s :=
  selection_eval cursor request value fallback position _ i s hc
    (fun j => (bit_roundtrip ((request j).eval i s)).symm)

def circuit (n : Nat) : Circuit (Inputs n) NoRegister (Outputs n) where
  next := fun r => nomatch r
  output := fun p => match p with
    | .at k => selection (fun c => .input (cursorPort c)) (fun r => .input (requestPort r))
        (fun r => .lit (selectedValue r (.at k))) (.lit 0)

theorem output_eq (cursor : Fin (n+1)) (request : Fin (n+1) → Bool) (p : Outputs n w) :
    (circuit n).observe (inputValues cursor request) NoRegister.values p =
      outputValues (RoundRobin.grant cursor request) p := by
  cases p with
  | «at» k =>
    simp only [Circuit.observe, circuit]
    rw [selection_eval _ _ _ _ _ _ _ _ (input_cursor cursor request) (input_request cursor request)]
    cases RoundRobin.grant cursor request <;> rfl

theorem raw_output_eq (inputs : Values (Inputs n)) (cursor : Fin (n+1))
    (h : CursorEncoding inputs cursor) (p : Outputs n w) :
    (circuit n).observe inputs NoRegister.values p =
      outputValues (RoundRobin.grant cursor (fun k => inputs (requestPort k) == 1)) p :=
  (congrArg (fun v : Values (Inputs n) => (circuit n).observe v NoRegister.values p)
    (input_encoding_eq inputs cursor h)).trans (output_eq cursor _ p)

/-- Existing grant and one-hot contracts transfer through this pointwise equality. -/
theorem observe_eq_rotated (inputs : Values (Inputs n)) (cursor : Fin (n+1))
    (h : CursorEncoding inputs cursor) (p : Outputs n w) :
    (circuit n).observe inputs NoRegister.values p =
      (RoundRobinCircuit.circuit n).observe inputs NoRegister.values p :=
  (raw_output_eq inputs cursor h p).trans (RoundRobinCircuit.raw_output_eq inputs cursor h p).symm

end Pinwheel.Hardware.Arbitration.RoundRobinMasked
