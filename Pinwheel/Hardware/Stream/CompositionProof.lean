import Pinwheel.Hardware.Stream.ElasticCircuit

namespace Pinwheel.Hardware.Stream

set_option backward.isDefEq.respectTransparency false

theorem serialReady_eval (b : Certified wm wo) (i : Input (BitVec wi))
    (r : Values R) (s : b.State) (hs : b.contract.Valid s) :
    (serialReady (R := R) b.circuit).eval (inputValues i) (Joint.values r (b.encode s)) =
      BitVec.ofBool (b.machine.ready i.ready s) := by
  simp only [serialReady, Expr.eval_bind, Expr.eval, Joint.values]
  rw [probe_eval _ _ _ i.ready rfl]
  exact b.output_eq ⟨false, none, i.ready⟩ s hs inReady

theorem serialOffer_eval (a : Certified wi wm) (i : Input (BitVec wi))
    (s : a.State) (r : Values R) (hs : a.contract.Valid s) (o : Out wm v) :
    (serialOffer a.circuit o).eval (inputValues i) (Joint.values (a.encode s) r) =
      outputValues ⟨a.machine.ready false s, a.machine.offer s⟩ o := by
  simp only [serialOffer, Expr.eval_bind, Expr.eval, Joint.values]
  rw [probe_eval _ _ _ false rfl]
  exact a.output_eq ⟨false, none, false⟩ s hs o

theorem serialLeft_eval (b : Certified wm wo) (i : Input (BitVec wi))
    (r : Values R) (s : b.State) (hs : b.contract.Valid s) :
    (fun {v} (p : In wi v) => (serialLeft b.circuit p).eval (inputValues i)
      (Joint.values r (b.encode s))) = @inputValues wi (b.machine.leftInput i s) := by
  apply input_ext
  · rfl
  · rfl
  · exact serialReady_eval b i r s hs
  · rfl

theorem serialRight_eval (a : Certified wi wm) (i : Input (BitVec wi))
    (s : a.State) (r : Values R) (hs : a.contract.Valid s) :
    (fun {v} (p : In wm v) => (serialRight a.circuit p).eval (inputValues i)
      (Joint.values (a.encode s) r)) = @inputValues wm (a.machine.rightInput i s) := by
  apply input_ext
  · rfl
  · exact serialOffer_eval a i s r hs outValid
  · rfl
  · exact serialOffer_eval a i s r hs outData

def Certified.serial (a : Certified wi wm) (b : Certified wm wo) : Certified wi wo where
  Register := Joint a.Register b.Register
  registers := Joint.interface a.registers b.registers
  circuit := serialCircuit a.circuit b.circuit
  State := a.State × b.State
  machine := a.machine.serial b.machine
  function := b.function ∘ a.function
  contract := a.contract.serial b.contract
  encode := fun s => Joint.values (a.encode s.1) (b.encode s.2)
  initial := (a.initial, b.initial)
  initial_valid := ⟨a.initial_valid, b.initial_valid⟩
  initial_empty := by simp [Contract.serial, a.initial_empty, b.initial_empty]
  step_eq := by
    intro i s h v p
    cases p with
    | left p =>
      simp only [Circuit.step, serialCircuit, Expr.eval_bind, Expr.eval, Joint.values]
      rw [serialLeft_eval b i (a.encode s.1) s.2 h.2]
      exact a.step_eq _ _ h.1 p
    | right p =>
      simp only [Circuit.step, serialCircuit, Expr.eval_bind, Expr.eval, Joint.values]
      rw [serialRight_eval a i s.1 (b.encode s.2) h.1]
      exact b.step_eq _ _ h.2 p
  output_eq := by
    intro i s h v o
    cases o with
    | «at» k =>
      match k with
      | ⟨0, _⟩ =>
        dsimp only [outputPorts]
        simp only [Circuit.observe, serialCircuit, streamOutputs, Expr.eval_bind, Expr.eval, Joint.values]
        rw [serialLeft_eval b i (a.encode s.1) s.2 h.2]
        exact (a.output_eq _ _ h.1 inReady).trans (by
          cases hr : i.reset <;> simp [Machine.component, Machine.serial, Machine.leftInput, outputValues, inReady, hr])
      | ⟨1, _⟩ =>
        dsimp only [outputPorts]
        simp only [Circuit.observe, serialCircuit, streamOutputs, Expr.eval_bind, Expr.eval, Joint.values]
        rw [serialRight_eval a i s.1 (b.encode s.2) h.1]
        exact (b.output_eq _ _ h.2 outValid).trans (by
          cases hr : i.reset <;> simp [Machine.component, Machine.serial, Machine.rightInput, outputValues, outValid, hr])
      | ⟨2, _⟩ =>
        dsimp only [outputPorts]
        simp only [Circuit.observe, serialCircuit, streamOutputs, Expr.eval_bind, Expr.eval, Joint.values]
        rw [serialRight_eval a i s.1 (b.encode s.2) h.1]
        exact (b.output_eq _ _ h.2 outData).trans (by
          cases hr : i.reset <;> simp [Machine.component, Machine.serial, Machine.rightInput, outputValues, outData, hr])
      | ⟨k + 3, hk⟩ => exact False.elim (by change k + 3 < 3 at hk; omega)
  reset_eq := by
    intro i s h v p
    cases p with
    | left p =>
      simp only [Circuit.step, serialCircuit, Expr.eval_bind, Expr.eval, Joint.values]
      exact a.reset_eq (fun p => (serialLeft b.circuit p).eval i s) _ h p
    | right p =>
      simp only [Circuit.step, serialCircuit, Expr.eval_bind, Expr.eval, Joint.values]
      exact b.reset_eq (fun p => (serialRight a.circuit p).eval i s) _ h p

end Pinwheel.Hardware.Stream
