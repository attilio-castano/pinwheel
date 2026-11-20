import Pinwheel.Hardware.Stream.Certified
import Pinwheel.Hardware.NetlistTools

namespace Pinwheel.Hardware.Stream

inductive DataInput (width : Nat) : Nat → Type where
  | data : DataInput width width

def dataValues (v : BitVec w) : Values (DataInput w) := fun p => match p with | .data => v

/-- Any combinational function may be installed in a mapped stage, provided its
expression's semantics is proved. Sequential transport proofs do not inspect it. -/
structure Map (wi wo : Nat) where
  expression : Expr (DataInput wi) NoRegister wo
  function : BitVec wi → BitVec wo
  correct : ∀ v, expression.eval (dataValues v) NoRegister.values = function v

def Map.identity (w : Nat) : Map w w := ⟨.input .data, id, fun _ => rfl⟩

def Map.apply (m : Map wi wo) (e : Expr I R wi) : Expr I R wo :=
  m.expression.bind (fun p => match p with | .data => e) (fun p => nomatch p)

@[simp] theorem Map.apply_eval (m : Map wi wo) (e : Expr I R wi) (i : Values I) (s : Values R) :
    (m.apply e).eval i s = m.function (e.eval i s) := by
  rw [Map.apply, Expr.eval_bind, ← m.correct]
  congr 1
  · funext b p; cases p; rfl
  · funext b p; cases p

namespace Elastic

def circuit (m : Map wi wo) : Circuit (In wi) (CellReg wo 1) (Out wo) :=
  let canLoad := (Expr.inv (.reg (.valid 0))).bor (.input ready)
  { next := fun p => match p with
      | .valid _ => .mux (.input reset) (.lit 0) (.mux canLoad (.input valid) (.reg (.valid 0)))
      | .data _ => .mux (.input reset) (.lit 0) (.mux canLoad
          (.mux (.input valid) (m.apply (.input payload)) (.lit 0)) (.reg (.data 0)))
    output := streamOutputs
      (.mux (.input reset) (.lit 0) canLoad)
      (.mux (.input reset) (.lit 0) (.reg (.valid 0)))
      (.mux (.input reset) (.lit 0) (.reg (.data 0))) }

theorem step_eq (m : Map wi wo) (i : Input (BitVec wi)) (s : Option (BitVec wo))
    (r : CellReg wo 1 b) :
    (circuit m).step (inputValues i) (cells s.toList) r =
      cells ((elastic m.function).step i s).toList r := by
  cases r <;> rename_i k
  all_goals have hk : k = 0 := Fin.ext (by omega)
  all_goals subst k
  all_goals cases hr : i.reset <;> cases hv : i.offered <;> cases hd : i.ready <;> cases s <;>
    simp [Circuit.step, circuit, Expr.eval, inputValues, reset, ready, valid, payload,
      cells, elastic, hr, hv, hd]

theorem output_eq (m : Map wi wo) (i : Input (BitVec wi)) (s : Option (BitVec wo))
    (o : Out wo b) :
    (circuit m).observe (inputValues i) (cells s.toList) o =
      outputValues ((elastic m.function).component.observe i s) o := by
  cases o with
  | «at» k =>
    match k with
    | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ =>
      dsimp only [outputPorts]
      cases hr : i.reset <;> cases hd : i.ready <;> cases s <;>
        simp [Circuit.observe, circuit, streamOutputs, Expr.eval, inputValues,
          reset, ready, cells, outputValues, Machine.component, elastic, hr, hd]
    | ⟨k + 3, h⟩ => exact False.elim (by change k + 3 < 3 at h; omega)

def certified (m : Map wi wo) : Certified wi wo where
  Register := CellReg wo 1
  registers := CellReg.interface wo 1
  circuit := circuit m
  State := Option (BitVec wo)
  machine := elastic m.function
  function := m.function
  contract := elasticContract m.function
  encode := fun s => cells s.toList
  initial := none
  initial_valid := True.intro
  initial_empty := rfl
  step_eq := fun i s _ _ r => step_eq m i s r
  output_eq := fun i s _ _ o => output_eq m i s o
  reset_eq := by
    intro i s h b r
    cases r <;> simp [Circuit.step, circuit, Expr.eval, h, cells]

end Elastic
end Pinwheel.Hardware.Stream
