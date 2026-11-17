import Pinwheel.Hardware.Stream.Backend

namespace Pinwheel.Hardware.Stream.BackendAPI

set_option backward.isDefEq.respectTransparency false

variable {a : Machine (BitVec wi) (BitVec wm) S} {b : Machine (BitVec wm) (BitVec wo) T}

private def leftPins (y : Circuit (In wm) R₂ (Out wo)) (i : Values (In wi))
    (r : Values (Joint R₁ R₂)) : Values (In wi) := fun p => (serialLeft y p).eval i r

private def rightPins (x : Circuit (In wi) R₁ (Out wm)) (i : Values (In wi))
    (r : Values (Joint R₁ R₂)) : Values (In wm) := fun p => (serialRight x p).eval i r

private theorem ready_eq (y : Backend b e) (i : Values (In wi))
    (r : Values (Joint R y.Register)) (h : y.proof.Rel (fun p => r (.right p)) s) :
    (serialReady y.circuit).eval i r = BitVec.ofBool (b.ready (decodeInput i).ready s) := by
  simp only [serialReady, Expr.eval_bind, Expr.eval]
  have probe := probe_eval (R := Joint R y.Register) (r := Expr.input (ready (w := wi))) i r
    (decodeInput i).ready (bit_roundtrip _).symm (w := wm)
  rw [probe]
  simpa [pins, decode_encode, Machine.component,Circuit.component,Circuit.observe,inReady,outputValues] using
    congrFun (congrFun (y.proof.observe (inputValues ⟨false,none,(decodeInput i).ready⟩) _ s h) 1) inReady

private theorem offer_eq (x : Backend a e) (i : Values (In wi))
    (r : Values (Joint x.Register R)) (h : x.proof.Rel (fun p => r (.left p)) s)
    (o : Out wm v) :
    (serialOffer x.circuit o).eval i r = outputValues ⟨a.ready false s, a.offer s⟩ o := by
  simp only [serialOffer, Expr.eval_bind, Expr.eval]
  have probe := probe_eval (R := Joint x.Register R) (r := Expr.lit 0) i r false rfl (w := wi)
  rw [show (fun {v} (p : In wi v) => (probeInput (Expr.lit 0) p).eval i r) = @inputValues wi ⟨false,none,false⟩ from probe]
  exact congrFun (congrFun (x.proof.observe _ _ _ h) v) o |>.trans (by simp [pins,decode_encode,Machine.component])

private theorem left_decode (y : Backend b e) (i : Values (In wi))
    (r : Values (Joint R y.Register)) (h : y.proof.Rel (fun p => r (.right p)) s) :
    decodeInput (leftPins y.circuit i r) = b.leftInput (decodeInput i) s := by
  unfold decodeInput leftPins
  simp [serialLeft, inputExpr, reset, valid, payload, ready, Expr.eval, Machine.leftInput, ready_eq y i r h,
    decodeInput]
  exact (fun (v : Bool) => show (BitVec.ofBool v == 1) = v by cases v <;> rfl) _

private theorem right_decode (x : Backend a e) (i : Values (In wi))
    (r : Values (Joint x.Register R)) (h : x.proof.Rel (fun p => r (.left p)) s) :
    decodeInput (rightPins x.circuit i r) = a.rightInput (decodeInput i) s := by
  have hv := offer_eq x i r h outValid
  have hd := offer_eq x i r h outData
  change Input.mk _ (if _ = 1 then some _ else none) _ = _
  simp only [rightPins, serialRight, valid, reset, payload, ready, inputExpr, Expr.eval, hv, hd,
    Machine.rightInput, decodeInput]
  cases ho : a.offer s <;> rfl

private theorem next_left (x : Circuit (In wi) R₁ (Out wm)) (y : Circuit (In wm) R₂ (Out wo))
    (i : Values (In wi)) (r : Values (Joint R₁ R₂)) :
    (fun {v} (p : R₁ v) => (serialCircuit x y).step i r (.left p)) =
      (fun {v} (p : R₁ v) => x.step (leftPins y i r) (fun q => r (.left q)) p) := by
  funext _ p
  exact Expr.eval_bind _ _ _ _ _

private theorem next_right (x : Circuit (In wi) R₁ (Out wm)) (y : Circuit (In wm) R₂ (Out wo))
    (i : Values (In wi)) (r : Values (Joint R₁ R₂)) :
    (fun {v} (p : R₂ v) => (serialCircuit x y).step i r (.right p)) =
      (fun {v} (p : R₂ v) => y.step (rightPins x i r) (fun q => r (.right q)) p) := by
  funext _ p
  exact Expr.eval_bind _ _ _ _ _

/-- Serial wiring preserves any component state relations, including projections
that forget inactive storage. Each leaf sees the same reset edge as the caller. -/
def serial (x : Backend a es) (y : Backend b et) : Backend (a.serial b) (es,et) where
  Register := Joint x.Register y.Register
  registers := Joint.interface x.registers y.registers
  circuit := serialCircuit x.circuit y.circuit
  proof := {
    Rel := fun r s => x.proof.Rel (fun p => r (.left p)) s.1 ∧ y.proof.Rel (fun p => r (.right p)) s.2
    step := by
      intro i r s h
      obtain ⟨hx,hy⟩ := h
      have l := x.proof.step (leftPins y.circuit i r) _ _ hx
      have t := y.proof.step (rightPins x.circuit i r) _ _ hy
      simp only [Circuit.component,pins] at l t ⊢
      rw [left_decode y i r hy] at l
      rw [right_decode x i r hx] at t
      exact ⟨(next_left _ _ i r) ▸ l, (next_right _ _ i r) ▸ t⟩
    observe := by
      intro i r s h
      have l := x.proof.observe (leftPins y.circuit i r) _ _ h.1
      have t := y.proof.observe (rightPins x.circuit i r) _ _ h.2
      simp only [pins,Circuit.component,left_decode y i r h.2,right_decode x i r h.1] at l t
      funext v o
      match o with
      | .at ⟨0,_⟩ | .at ⟨1,_⟩ | .at ⟨2,_⟩ =>
        simp only [pins,Circuit.component,Circuit.observe,serialCircuit,streamOutputs,Expr.eval_bind,Expr.eval]
        first
        | refine Eq.trans (congrFun (congrFun l _) inReady) ?_
        | refine Eq.trans (congrFun (congrFun t _) outValid) ?_
        | refine Eq.trans (congrFun (congrFun t _) outData) ?_
        all_goals cases hr : (decodeInput i).reset <;>
          simp [Machine.component,Machine.leftInput,Machine.rightInput,Machine.serial,hr,outputValues,inReady,outValid,outData]
      | .at ⟨k+3,hk⟩ => exact False.elim (by change k+3 < 3 at hk; omega) }
  recover := by
    intro i r hr
    exact ⟨(next_left _ _ i r) ▸ x.recover _ _ hr, (next_right _ _ i r) ▸ y.recover _ _ hr⟩

end Pinwheel.Hardware.Stream.BackendAPI
