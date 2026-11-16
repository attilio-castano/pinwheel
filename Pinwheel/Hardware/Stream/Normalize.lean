import Pinwheel.Hardware.Stream.Artifact

namespace Pinwheel.Hardware.Stream

set_option backward.isDefEq.respectTransparency false

theorem bit_roundtrip (x : BitVec 1) : BitVec.ofBool (x == 1) = x := by
  revert x
  decide +kernel

def normalizeInput : {b : Nat} → In w b → Expr (In w) R b :=
  inputExpr (.input reset) (.input valid) (.input ready)
    (.mux (.input valid) (.input payload) (.lit 0))

theorem normalize_eval (i : Values (In w)) (s : Values R) :
    (fun {b} (p : In w b) => (normalizeInput p).eval i s) = @inputValues w (decodeInput i) := by
  apply input_ext
  · exact (bit_roundtrip (i reset)).symm
  · change i valid = BitVec.ofBool (if i valid = 1 then some (i payload) else none).isSome
    by_cases h : i valid = 1
    · simp [h]
    · simpa only [if_neg h, Option.isSome_none, beq_eq_false_iff_ne.mpr h] using (bit_roundtrip (i valid)).symm
  · exact (bit_roundtrip (i ready)).symm
  · change (if i valid = 1 then i payload else 0) =
      (if i valid = 1 then some (i payload) else none).getD 0
    split <;> rfl

def normalizeCircuit (c : Circuit (In wi) R (Out wo)) : Circuit (In wi) R (Out wo) where
  next := fun r => (c.next r).bind normalizeInput (.reg)
  output := fun o => (c.output o).bind normalizeInput (.reg)

theorem normalize_step (c : Circuit (In wi) R (Out wo)) (i : Values (In wi)) (s : Values R) (r : R b) :
    (normalizeCircuit c).step i s r = c.step (inputValues (decodeInput i)) s r := by
  simp only [normalizeCircuit, Circuit.step, Expr.eval_bind, normalize_eval, Expr.eval]

theorem normalize_observe (c : Circuit (In wi) R (Out wo)) (i : Values (In wi)) (s : Values R) (o : Out wo b) :
    (normalizeCircuit c).observe i s o = c.observe (inputValues (decodeInput i)) s o := by
  simp only [normalizeCircuit, Circuit.observe, Expr.eval_bind, normalize_eval, Expr.eval]

theorem normalize_steps (c : Circuit (In wi) R (Out wo)) (i : Values (In wi)) (s : Values R) :
    (fun {b} (r : R b) => (normalizeCircuit c).step i s r) =
      (fun {b} (r : R b) => c.step (inputValues (decodeInput i)) s r) :=
  funext fun _ => funext fun r => normalize_step c i s r

theorem normalize_observations (c : Circuit (In wi) R (Out wo)) (i : Values (In wi)) (s : Values R) :
    (fun {b} (o : Out wo b) => (normalizeCircuit c).observe i s o) =
      (fun {b} (o : Out wo b) => c.observe (inputValues (decodeInput i)) s o) :=
  funext fun _ => funext fun o => normalize_observe c i s o

/-- Normalize only the external interface. This makes every raw digital input
history representable, including arbitrary data bits while valid is low. -/
def Certified.normalized (c : Certified wi wo) : Certified wi wo :=
  { c with
    circuit := normalizeCircuit c.circuit
    step_eq := by
      intro i s h b r
      simpa only [normalize_step, decode_encode] using c.step_eq i s h r
    output_eq := by
      intro i s h b o
      simpa only [normalize_observe, decode_encode] using c.output_eq i s h o
    reset_eq := by
      intro i s h b r
      rw [normalize_step]
      exact c.reset_eq _ s (by change BitVec.ofBool (i reset == 1) = 1; rw [bit_roundtrip, h]) r }

def Certified.rawSimulator (c : Certified wi wo) :
    Timed.Component (Values (In wi)) (Values c.Register) (Output (BitVec wo)) :=
  ⟨fun i s => c.normalized.circuit.step i s,
   fun i s => decodeOutput (c.normalized.circuit.observe i s)⟩

def Certified.rawModel (c : Certified wi wo) :
    Timed.Component (Values (In wi)) c.State (Output (BitVec wo)) :=
  ⟨fun i s => c.machine.step (decodeInput i) s,
   fun i s => c.machine.component.observe (decodeInput i) s⟩

def Certified.rawRefinement (c : Certified wi wo) : Timed.Refinement c.rawSimulator c.rawModel where
  Rel := c.refinement.Rel
  step := by
    intro i r s h
    have hs := c.refinement.step (decodeInput i) r s h
    simpa only [Certified.rawSimulator, Certified.rawModel, Certified.normalized,
      normalize_steps, Certified.simulator, Machine.component] using hs
  observe := by
    intro i r s h
    have ho := c.refinement.observe (decodeInput i) r s h
    simpa only [Certified.rawSimulator, Certified.rawModel, Certified.normalized,
      normalize_observations, Certified.simulator] using ho

/-- Arbitrary digital pin histories after one cold-reset edge, from arbitrary
register bits. No condition is imposed on payload when in_valid is low. -/
theorem Certified.raw_initialized_trace (c : Certified wi wo) (initial : Values c.Register)
    (resetInput : Values (In wi)) (hr : resetInput reset = 1)
    (inputs : List (Values (In wi))) :
    c.rawSimulator.trace (c.rawSimulator.step resetInput initial) inputs =
      c.rawModel.trace c.initial inputs := by
  apply c.rawRefinement.trace_eq
  exact ⟨c.initial_valid, funext fun b => funext fun p => c.normalized.reset_eq resetInput initial hr p⟩

end Pinwheel.Hardware.Stream
