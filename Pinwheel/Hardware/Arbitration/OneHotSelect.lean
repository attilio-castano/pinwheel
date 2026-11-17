import Pinwheel.Hardware.Arbitration.RoundRobinMasked

/-! Share a round-robin winner decoder across arbitrary-width value selections.
Winner expressions depend only on the request/cursor wires and requester index,
so the emitter's operation cache can reuse them across data and control outputs.
-/
namespace Pinwheel.Hardware.Arbitration.OneHotSelect

set_option backward.isDefEq.respectTransparency false

def winner (cursor request : Fin (n+1) → Expr I R 1) (k : Fin (n+1)) : Expr I R 1 :=
  RoundRobinMasked.selection cursor request (fun j => .lit (BitVec.ofBool (j == k))) (.lit 0)

def anyWinner (cursor request : Fin (n+1) → Expr I R 1) : Expr I R 1 :=
  RoundRobinMasked.anyWire (winner cursor request) (List.finRange (n+1))

def wordOr (x y : Expr I R w) : Expr I R w := .inv (.band (.inv x) (.inv y))

def gather (grant : α → Expr I R 1) (value : α → Expr I R w) : List α → Expr I R w
  | [] => .lit 0
  | x :: xs => wordOr (.mux (grant x) (value x) (.lit 0)) (gather grant value xs)

def selection (cursor request : Fin (n+1) → Expr I R 1)
    (value : Fin (n+1) → Expr I R w) (fallback : Expr I R w) : Expr I R w :=
  .mux (anyWinner cursor request) (gather (winner cursor request) value (List.finRange (n+1))) fallback

theorem winner_eval (cursor request : Fin (n+1) → Expr I R 1)
    (position : Fin (n+1)) (bits : Fin (n+1) → Bool) (i : Values I) (s : Values R)
    (hc : ∀ j, (cursor j).eval i s = BitVec.ofBool (j == position))
    (hr : ∀ j, (request j).eval i s = BitVec.ofBool (bits j)) (k : Fin (n+1)) :
    (winner cursor request k).eval i s = BitVec.ofBool (RoundRobin.grant position bits == some k) := by
  rw [winner, RoundRobinMasked.selection_eval _ _ _ _ position bits i s hc hr]
  cases RoundRobin.grant position bits <;> rfl

theorem anyWinner_eval (cursor request : Fin (n+1) → Expr I R 1)
    (position : Fin (n+1)) (bits : Fin (n+1) → Bool) (i : Values I) (s : Values R)
    (hc : ∀ j, (cursor j).eval i s = BitVec.ofBool (j == position))
    (hr : ∀ j, (request j).eval i s = BitVec.ofBool (bits j)) :
    (anyWinner cursor request).eval i s = BitVec.ofBool (RoundRobin.grant position bits).isSome := by
  rw [anyWinner, RoundRobinMasked.anyWire_eval _ _ _ _ _ (winner_eval cursor request position bits i s hc hr)]
  congr 1
  apply Bool.eq_iff_iff.mpr
  cases RoundRobin.grant position bits <;> simp [List.any_eq_true]

def chosenValue [DecidableEq α] (chosen : Option α) (xs : List α) (value : α → BitVec w) : BitVec w :=
  match chosen with
  | none => 0
  | some k => if k ∈ xs then value k else 0

theorem gather_eval [DecidableEq α] (grant : α → Expr I R 1) (value : α → Expr I R w)
    (chosen : Option α) (xs : List α) (i : Values I) (s : Values R)
    (h : ∀ j, (grant j).eval i s = BitVec.ofBool (chosen == some j)) :
    (gather grant value xs).eval i s = chosenValue chosen xs (fun k => (value k).eval i s) := by
  cases chosen with
  | none =>
    induction xs with
    | nil => rfl
    | cons x xs ih => simp [gather, wordOr, Expr.eval, h, ih, chosenValue]
  | some k =>
    induction xs with
    | nil => rfl
    | cons x xs ih =>
      simp only [gather, wordOr, Expr.eval, h, BitVec.not_and, BitVec.not_not, chosenValue]
      rw [ih]
      by_cases hx : k = x
      · by_cases hm : k ∈ xs <;> simp_all [chosenValue]
      · have hb : (k == x) = false := beq_eq_false_iff_ne.mpr hx
        simp [chosenValue, hx, hb]

/-- Values and fallback may depend on any inputs/registers; requests are free.
Only the cursor encoding is constrained. -/
theorem selection_eval (cursor request : Fin (n+1) → Expr I R 1)
    (value : Fin (n+1) → Expr I R w) (fallback : Expr I R w)
    (position : Fin (n+1)) (bits : Fin (n+1) → Bool) (i : Values I) (s : Values R)
    (hc : ∀ j, (cursor j).eval i s = BitVec.ofBool (j == position))
    (hr : ∀ j, (request j).eval i s = BitVec.ofBool (bits j)) :
    (selection cursor request value fallback).eval i s =
      match RoundRobin.grant position bits with
      | none => fallback.eval i s
      | some k => (value k).eval i s := by
  rw [selection, Expr.eval, anyWinner_eval cursor request position bits i s hc hr]
  rw [gather_eval _ _ _ _ _ _ (winner_eval cursor request position bits i s hc hr)]
  cases RoundRobin.grant position bits <;> simp [chosenValue]

theorem raw_selection_eval (cursor request : Fin (n+1) → Expr I R 1)
    (value : Fin (n+1) → Expr I R w) (fallback : Expr I R w)
    (position : Fin (n+1)) (i : Values I) (s : Values R)
    (hc : ∀ j, (cursor j).eval i s = BitVec.ofBool (j == position)) :
    (selection cursor request value fallback).eval i s =
      match RoundRobin.grant position (fun j => (request j).eval i s == 1) with
      | none => fallback.eval i s
      | some k => (value k).eval i s :=
  selection_eval cursor request value fallback position _ i s hc
    (fun j => (RoundRobinCircuit.bit_roundtrip ((request j).eval i s)).symm)

theorem selection_eq_masked (cursor request : Fin (n+1) → Expr I R 1)
    (value : Fin (n+1) → Expr I R w) (fallback : Expr I R w)
    (position : Fin (n+1)) (i : Values I) (s : Values R)
    (hc : ∀ j, (cursor j).eval i s = BitVec.ofBool (j == position)) :
    (selection cursor request value fallback).eval i s =
      (RoundRobinMasked.selection cursor request value fallback).eval i s :=
  (raw_selection_eval cursor request value fallback position i s hc).trans
    (RoundRobinMasked.raw_selection_eval cursor request value fallback position i s hc).symm

end Pinwheel.Hardware.Arbitration.OneHotSelect
