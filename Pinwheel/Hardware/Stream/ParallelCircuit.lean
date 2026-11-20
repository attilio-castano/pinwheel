import Pinwheel.Hardware.Stream.CompositionProof
import Pinwheel.Hardware.Stream.ForkJoin

namespace Pinwheel.Hardware.Stream.Parallel

set_option backward.isDefEq.respectTransparency false

def rightOffer (b : Circuit (In wi) S (Out wb)) (o : Out wb v) : Expr (In wi) (Joint R S) v :=
  (b.output o).bind (probeInput (.lit 0)) (fun p => .reg (.right p))

def leftDown (b : Circuit (In wi) S (Out wb)) : Expr (In wi) (Joint R S) 1 :=
  .band (.input ready) (rightOffer b outValid)

def rightDown (a : Circuit (In wi) R (Out wa)) : Expr (In wi) (Joint R S) 1 :=
  .band (.input ready) (serialOffer a outValid)

def leftCan (a : Circuit (In wi) R (Out wa)) (b : Circuit (In wi) S (Out wb)) :
    Expr (In wi) (Joint R S) 1 :=
  (a.output inReady).bind (probeInput (leftDown b)) (fun p => .reg (.left p))

def rightCan (a : Circuit (In wi) R (Out wa)) (b : Circuit (In wi) S (Out wb)) :
    Expr (In wi) (Joint R S) 1 :=
  (b.output inReady).bind (probeInput (rightDown a)) (fun p => .reg (.right p))

def gateInput (grant downstream : Expr (In wi) R 1) : {w : Nat} → In wi w → Expr (In wi) R w :=
  inputExpr (.input reset) (.band (.input valid) grant) downstream (.mux grant (.input payload) (.lit 0))

def circuit (a : Circuit (In wi) R (Out wa)) (b : Circuit (In wi) S (Out wb)) :
    Circuit (In wi) (Joint R S) (Out (wa + wb)) where
  next := fun p => match p with
    | .left p => (a.next p).bind (gateInput (rightCan a b) (leftDown b)) (fun p => .reg (.left p))
    | .right p => (b.next p).bind (gateInput (leftCan a b) (rightDown a)) (fun p => .reg (.right p))
  output :=
    let both := Expr.band (serialOffer a outValid) (rightOffer b outValid)
    streamOutputs
      (.mux (.input reset) (.lit 0) (.band (leftCan a b) (rightCan a b)))
      (.mux (.input reset) (.lit 0) both)
      (.mux (.input reset) (.lit 0) (.mux both
        (.concat (serialOffer a outData) (rightOffer b outData)) (.lit 0)))

theorem rightOffer_eval (b : Certified wi wb) (i : Input (BitVec wi)) (r : Values R)
    (s : b.State) (hs : b.contract.Valid s) (o : Out wb v) :
    (rightOffer b.circuit o).eval (inputValues i) (Joint.values r (b.encode s)) =
      outputValues ⟨b.machine.ready false s, b.machine.offer s⟩ o := by
  simp only [rightOffer, Expr.eval_bind, Expr.eval, Joint.values]
  rw [probe_eval _ _ _ false rfl]
  exact b.output_eq ⟨false, none, false⟩ s hs o

theorem leftDown_eval (b : Certified wi wb) (i : Input (BitVec wi)) (r : Values R)
    (s : b.State) (hs : b.contract.Valid s) :
    (leftDown b.circuit).eval (inputValues i) (Joint.values r (b.encode s)) =
      BitVec.ofBool (leftReady b.machine i.ready s) := by
  simp only [leftDown, Expr.eval, rightOffer_eval b i r s hs, inputValues, ready,
    outputValues, outValid, leftReady, BitVec.ofBool_and_ofBool]

theorem rightDown_eval (a : Certified wi wa) (i : Input (BitVec wi)) (s : a.State)
    (r : Values R) (hs : a.contract.Valid s) :
    (rightDown a.circuit).eval (inputValues i) (Joint.values (a.encode s) r) =
      BitVec.ofBool (leftReady a.machine i.ready s) := by
  simp only [rightDown, Expr.eval, serialOffer_eval a i s r hs, inputValues, ready,
    outputValues, outValid, leftReady, BitVec.ofBool_and_ofBool]

theorem leftCan_eval (a : Certified wi wa) (b : Certified wi wb) (i : Input (BitVec wi))
    (s : a.State × b.State) (ha : a.contract.Valid s.1) (hb : b.contract.Valid s.2) :
    (leftCan a.circuit b.circuit).eval (inputValues i) (Joint.values (a.encode s.1) (b.encode s.2)) =
      BitVec.ofBool (a.machine.ready (leftReady b.machine i.ready s.2) s.1) := by
  simp only [leftCan, Expr.eval_bind, Expr.eval, Joint.values]
  rw [probe_eval _ _ _ _ (leftDown_eval b i (a.encode s.1) s.2 hb)]
  exact a.output_eq ⟨false, none, leftReady b.machine i.ready s.2⟩ s.1 ha inReady

theorem rightCan_eval (a : Certified wi wa) (b : Certified wi wb) (i : Input (BitVec wi))
    (s : a.State × b.State) (ha : a.contract.Valid s.1) (hb : b.contract.Valid s.2) :
    (rightCan a.circuit b.circuit).eval (inputValues i) (Joint.values (a.encode s.1) (b.encode s.2)) =
      BitVec.ofBool (b.machine.ready (leftReady a.machine i.ready s.1) s.2) := by
  simp only [rightCan, Expr.eval_bind, Expr.eval, Joint.values]
  rw [probe_eval _ _ _ _ (rightDown_eval a i s.1 (b.encode s.2) ha)]
  exact b.output_eq ⟨false, none, leftReady a.machine i.ready s.1⟩ s.2 hb inReady

theorem gateInput_eval (grant downstream : Expr (In wi) R 1) (i : Input (BitVec wi))
    (s : Values R) (g d : Bool) (hg : grant.eval (inputValues i) s = BitVec.ofBool g)
    (hd : downstream.eval (inputValues i) s = BitVec.ofBool d) :
    (fun {w} (p : In wi w) => (gateInput grant downstream p).eval (inputValues i) s) =
      @inputValues wi ⟨i.reset, forkOffer i.offered g, d⟩ := by
  apply input_ext
  · rfl
  · cases g <;> cases hi : i.offered <;> simp [gateInput, inputExpr, valid, Expr.eval, hg, inputValues, forkOffer, hi]
  · exact hd
  · cases g <;> cases hi : i.offered <;> simp [gateInput, inputExpr, payload, Expr.eval, hg, inputValues, forkOffer, hi]

end Pinwheel.Hardware.Stream.Parallel

namespace Pinwheel.Hardware.Stream
set_option backward.isDefEq.respectTransparency false

/-- A typed fork, two independently advancing branches, and an ordered join.
The extra invariant relates transaction frontiers, not physical register layouts. -/
def Certified.parallel (a : Certified wi wa) (b : Certified wi wb) : Certified wi (wa + wb) where
  Register := Joint a.Register b.Register
  registers := Joint.interface a.registers b.registers
  circuit := Parallel.circuit a.circuit b.circuit
  State := a.State × b.State
  machine := Parallel.machine a.machine b.machine BitVec.append
  function := fun x => a.function x ++ b.function x
  contract := Parallel.contract a.contract b.contract BitVec.append
  encode := fun s => Joint.values (a.encode s.1) (b.encode s.2)
  initial := (a.initial, b.initial)
  initial_valid := ⟨a.initial_valid, b.initial_valid, by rw [a.initial_empty, b.initial_empty]; rfl⟩
  initial_empty := by simp [Parallel.contract, a.initial_empty]
  step_eq := by
    intro i s h w p
    cases p with
    | left p =>
      simp only [Circuit.step, Parallel.circuit, Expr.eval_bind, Expr.eval, Joint.values]
      rw [Parallel.gateInput_eval _ _ _ _ _ _
        (Parallel.rightCan_eval a b i s h.1 h.2.1) (Parallel.leftDown_eval b i (a.encode s.1) s.2 h.2.1)]
      exact a.step_eq _ _ h.1 p
    | right p =>
      simp only [Circuit.step, Parallel.circuit, Expr.eval_bind, Expr.eval, Joint.values]
      rw [Parallel.gateInput_eval _ _ _ _ _ _
        (Parallel.leftCan_eval a b i s h.1 h.2.1) (Parallel.rightDown_eval a i s.1 (b.encode s.2) h.1)]
      exact b.step_eq _ _ h.2.1 p
  output_eq := by
    intro i s h w o
    cases o with
    | «at» k =>
      match k with
      | ⟨0, _⟩ =>
        dsimp only [outputPorts]
        simp only [Circuit.observe, Parallel.circuit, streamOutputs, Expr.eval,
          Parallel.leftCan_eval a b i s h.1 h.2.1, Parallel.rightCan_eval a b i s h.1 h.2.1]
        cases hr : i.reset <;> simp [inputValues, reset, Machine.component, Parallel.machine, outputValues, hr]
      | ⟨1, _⟩ | ⟨2, _⟩ =>
        dsimp only [outputPorts]
        simp only [Circuit.observe, Parallel.circuit, streamOutputs, Expr.eval,
          serialOffer_eval a i s.1 (b.encode s.2) h.1,
          Parallel.rightOffer_eval b i (a.encode s.1) s.2 h.2.1]
        cases hr : i.reset <;> cases ha : a.machine.offer s.1 <;> cases hb : b.machine.offer s.2 <;>
          simp [inputValues, reset, Machine.component, Parallel.machine, outputValues, outValid, outData,
            joinOffer, hr, ha, hb]
      | ⟨k + 3, hk⟩ => exact False.elim (by change k + 3 < 3 at hk; omega)
  reset_eq := by
    intro i s h w p
    cases p with
    | left p =>
      simp only [Circuit.step, Parallel.circuit, Expr.eval_bind, Expr.eval, Joint.values]
      exact a.reset_eq (fun p => (Parallel.gateInput (Parallel.rightCan a.circuit b.circuit) (Parallel.leftDown b.circuit) p).eval i s) _ h p
    | right p =>
      simp only [Circuit.step, Parallel.circuit, Expr.eval_bind, Expr.eval, Joint.values]
      exact b.reset_eq (fun p => (Parallel.gateInput (Parallel.leftCan a.circuit b.circuit) (Parallel.rightDown a.circuit) p).eval i s) _ h p

end Pinwheel.Hardware.Stream
