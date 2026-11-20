import Pinwheel.Hardware.Stream.Registers

namespace Pinwheel.Hardware.Stream

def streamOutputs (r v : Expr I R 1) (d : Expr I R w) :
    {b : Nat} → Out w b → Expr I R b
  | _, .at ⟨0, _⟩ => r
  | _, .at ⟨1, _⟩ => v
  | _, .at ⟨2, _⟩ => d
  | _, .at ⟨k + 3, h⟩ => False.elim (by change k + 3 < 3 at h; omega)

namespace Fifo

/-- Shift on downstream ready, even when empty. Valid encoded empty slots are
zero, so this agrees with shifting only on a dequeue without an extra control. -/
def shiftedValid (w depth k : Nat) : Expr (In w) (CellReg w depth) 1 :=
  .mux (.input ready) (cellValid w depth (k + 1)) (cellValid w depth k)

def shiftedData (w depth k : Nat) : Expr (In w) (CellReg w depth) w :=
  .mux (.input ready) (cellData w depth (k + 1)) (cellData w depth k)

def appendHere (w depth k : Nat) : Expr (In w) (CellReg w depth) 1 :=
  .band (.input valid) (.band (.inv (shiftedValid w depth k))
    (if k = 0 then .lit 1 else shiftedValid w depth (k - 1)))

def circuit (w depth : Nat) : Circuit (In w) (CellReg w depth) (Out w) where
  next := fun r => match r with
    | .valid k => .mux (.input reset) (.lit 0)
        ((appendHere w depth k).bor (shiftedValid w depth k))
    | .data k => .mux (.input reset) (.lit 0)
        (.mux (appendHere w depth k) (.input payload) (shiftedData w depth k))
  output := streamOutputs
    (.mux (.input reset) (.lit 0)
      ((Expr.inv (cellValid w depth (depth - 1))).bor (.input ready)))
    (.mux (.input reset) (.lit 0) (cellValid w depth 0))
    (.mux (.input reset) (.lit 0) (cellData w depth 0))

def rest (i : Input α) (q : List α) : List α := if i.ready then q.tail else q

theorem rest_length (i : Input α) (q : List α) : (rest i q).length ≤ q.length := by
  cases hd : i.ready <;> simp [rest, hd]

@[simp] theorem shiftedValid_eval (i : Input (BitVec w)) (q : List (BitVec w))
    (h : q.length ≤ depth) (k : Nat) :
    (shiftedValid w depth k).eval (inputValues i) (cells q) =
      BitVec.ofBool ((rest i q)[k]?.isSome) := by
  cases hd : i.ready <;> simp [shiftedValid, Expr.eval, inputValues, ready,
    cellValid_eval q h, rest, hd, List.getElem?_tail]

@[simp] theorem shiftedData_eval (i : Input (BitVec w)) (q : List (BitVec w))
    (h : q.length ≤ depth) (k : Nat) :
    (shiftedData w depth k).eval (inputValues i) (cells q) = (rest i q)[k]?.getD 0 := by
  cases hd : i.ready <;> simp [shiftedData, Expr.eval, inputValues, ready,
    cellData_eval q h, rest, hd, List.getElem?_tail]

@[simp] theorem slotValid (q : List α) (k : Nat) :
    q[k]?.isSome = decide (k < q.length) := by
  by_cases h : k < q.length <;> simp [h]

theorem append_position (q : List α) (k : Nat) :
    ((!q[k]?.isSome) && (if k = 0 then true else q[k-1]?.isSome)) =
      decide (k = q.length) := by
  apply Bool.eq_iff_iff.mpr
  by_cases hk : k = 0 <;> simp only [hk, if_true, if_false, slotValid,
    Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not]
  all_goals try simp only [and_true]
  all_goals omega

@[simp] theorem appendHere_eval (i : Input (BitVec w)) (q : List (BitVec w))
    (h : q.length ≤ depth) (k : Nat) :
    (appendHere w depth k).eval (inputValues i) (cells q) =
      BitVec.ofBool (i.offered.isSome && decide (k = (rest i q).length)) := by
  have hs : (if k = 0 then Expr.lit 1 else shiftedValid w depth (k - 1)).eval
      (inputValues i) (cells q) =
      BitVec.ofBool (if k = 0 then true else (rest i q)[k - 1]?.isSome) := by
    by_cases hk : k = 0 <;> simp [hk, Expr.eval, shiftedValid_eval i q h]
  simp only [appendHere, Expr.eval, inputValues, valid, shiftedValid_eval i q h,
    hs, BitVec.not_ofBool, BitVec.ofBool_and_ofBool, append_position]

theorem queue_slot (q : List α) (o : Option α) (k depth : Nat) (hk : k < depth) :
    (if q.length < depth then q ++ o.toList else q)[k]? =
      if k = q.length then o else q[k]? := by
  by_cases he : k = q.length <;> by_cases hl : q.length < depth <;>
    simp [he, hl, List.getElem?_append]
  · cases o <;> rfl
  · omega
  · intro hge
    have hgt : q.length < k := by omega
    cases o <;> simp [List.getElem?_eq_none (by omega : q.length ≤ k)] <;> omega

theorem fifo_step (i : Input (BitVec w)) (q : List (BitVec w)) (h : q.length ≤ depth)
    (r : CellReg w depth b) :
    (circuit w depth).step (inputValues i) (cells q) r = cells ((queue depth).step i q) r := by
  cases r with
  | valid k =>
    simp only [Circuit.step, circuit, Expr.eval, eval_bor, inputValues, reset,
      appendHere_eval i q h, shiftedValid_eval i q h, cells, queue]
    cases i.reset <;> simp [-slotValid]
    rw [queue_slot _ _ _ depth k.isLt]
    rw [← rest]
    by_cases hk : k.val = (rest i q).length <;> simp [hk]
  | data k =>
    simp only [Circuit.step, circuit, Expr.eval, inputValues, reset, payload,
      appendHere_eval i q h, shiftedData_eval i q h, cells, queue]
    cases i.reset <;> simp [-slotValid]
    rw [queue_slot _ _ _ depth k.isLt]
    rw [← rest]
    by_cases hk : k.val = (rest i q).length <;> cases i.offered <;> simp [hk]

theorem ready_correct (i : Input α) (q : List α) (h : q.length ≤ depth) (hd : 0 < depth) :
    (!q[depth - 1]?.isSome || i.ready) = decide ((rest i q).length < depth) := by
  apply Bool.eq_iff_iff.mpr
  cases hr : i.ready <;> simp [hr, rest]
  all_goals omega

theorem fifo_output (i : Input (BitVec w)) (q : List (BitVec w))
    (h : q.length ≤ depth) (hd : 0 < depth) (o : Out w b) :
    (circuit w depth).observe (inputValues i) (cells q) o =
      outputValues ((queue depth).component.observe i q) o := by
  cases o with
  | «at» k =>
    match k with
    | ⟨0, _⟩ =>
      dsimp only [outputPorts]
      cases hr : i.reset <;> simp [Circuit.observe, circuit, streamOutputs, Expr.eval,
        inputValues, reset, ready, cellValid_eval q h, outputValues, Machine.component,
        queue, hr]
      congr 1
      apply Bool.eq_iff_iff.mpr
      cases i.ready <;> simp <;> omega
    | ⟨1, _⟩ =>
      dsimp only [outputPorts]
      cases hr : i.reset <;> simp [Circuit.observe, circuit, streamOutputs, Expr.eval,
        inputValues, reset, cellValid_eval q h, outputValues, Machine.component, queue, hr]
      cases q <;> rfl
    | ⟨2, _⟩ =>
      dsimp only [outputPorts]
      cases hr : i.reset <;> simp [Circuit.observe, circuit, streamOutputs, Expr.eval,
        inputValues, reset, cellData_eval q h, outputValues, Machine.component, queue, hr]
      cases q <;> rfl
    | ⟨k + 3, hk⟩ => exact False.elim (by change k + 3 < 3 at hk; omega)

theorem reset_step (i : Input (BitVec w)) (s : Values (CellReg w depth))
    (hr : i.reset = true) (r : CellReg w depth b) :
    (circuit w depth).step (inputValues i) s r = cells [] r := by
  cases r <;> simp [circuit, Circuit.step, Expr.eval, inputValues, reset, hr, cells]

end Fifo
end Pinwheel.Hardware.Stream
