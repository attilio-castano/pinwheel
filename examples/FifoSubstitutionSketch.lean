import Pinwheel.Hardware.Library

/-! Design sketch. A client supplies a FIFO that implements the existing cycle
specification. A backend chooses its physical state relation and reset proof. -/
namespace FifoSubstitutionSketch
open Pinwheel.Hardware Stream

def pins (m : Machine (BitVec wi) (BitVec wo) S) :
    Timed.Component (Values (In wi)) S (Values (Out wo)) :=
  ⟨fun i s => m.step (decodeInput i) s,
   fun i s => outputValues (m.component.observe (decodeInput i) s)⟩

structure Backend (m : Machine (BitVec wi) (BitVec wo) S) (empty : S) where
  Register : Nat → Type
  registers : Interface Register
  circuit : Circuit (In wi) Register (Out wo)
  proof : Timed.Refinement circuit.component (pins m)
  recover : ∀ (i : Values (In wi)) (r : Values Register), i reset = 1 →
    proof.Rel (circuit.step i r) empty

abbrev Fifo (width depth : Nat) := Backend (queue depth (α := BitVec width)) []

def shift (w d : Nat) (hd : 0 < d) : Fifo w d :=
  let c := fifoCertified w d hd
  { Register := c.Register
    registers := c.registers
    circuit := c.normalized.circuit
    proof := c.implementation.refinement
    recover := fun i r h => ⟨c.initial_valid,
      funext fun _ => funext fun p => c.normalized.reset_eq i r h p⟩ }

/-- The same expression builds a lane for either representation. -/
def lane (fifo : Fifo w d) (extra : Nat) :=
  serialCircuit fifo.circuit (Design.pipeline (increment w) extra).flatten.normalized.circuit

theorem interchangeable (a b : Fifo w d) (ra : Values a.Register) (rb : Values b.Register)
    (i : Values (In w)) (hr : i reset = 1) (traffic : List (Values (In w))) :
    a.circuit.component.trace (a.circuit.step i ra) traffic =
      b.circuit.component.trace (b.circuit.step i rb) traffic :=
  (a.proof.trace_eq _ [] (a.recover i ra hr) traffic).trans
    (b.proof.trace_eq _ [] (b.recover i rb hr) traffic).symm

/-- Record only transfers at the pre-edge pins. History.advance starts a new
epoch at every reset, including resets in the middle of traffic. -/
def observedHistory (c : Circuit (In wi) R (Out wo)) (r : Values R)
    (h : History (BitVec wi) (BitVec wo)) : List (Values (In wi)) → History (BitVec wi) (BitVec wo)
  | [] => h
  | i :: rest => observedHistory c (c.step i r)
      (h.advance (decodeInput i) (decodeOutput (c.observe i r))) rest

variable {m : Machine (BitVec wi) (BitVec wo) S} {empty : S} {f : BitVec wi → BitVec wo}

private theorem history_eq (a : Backend m empty) (r : Values a.Register) (s : S)
    (rel : a.proof.Rel r s) (h : History (BitVec wi) (BitVec wo)) (traffic : List (Values (In wi))) :
    observedHistory a.circuit r h traffic =
      (runHistory m.component s h (traffic.map (fun (j : Values (In wi)) => decodeInput j))).2 := by
  induction traffic generalizing r s h with
  | nil => rfl
  | cons i rest ih =>
    have obs : decodeOutput (a.circuit.observe i r) = m.component.observe (decodeInput i) s :=
      (congrArg decodeOutput (a.proof.observe i r s rel)).trans (decode_outputValues _)
    simpa only [observedHistory, List.map_cons, runHistory, obs, pins, Circuit.component, Machine.component] using
      ih _ _ (a.proof.step i r s rel) (h.advance (decodeInput i) (m.component.observe (decodeInput i) s))

/-- The client gets an ordered account of physical transfers after cold reset.
The logical pending suffix is observable indirectly by later draining. -/
theorem transactions (a : Backend m empty) (k : Contract m.component f)
    (valid : k.Valid empty) (start : k.pending empty = []) (r : Values a.Register)
    (i : Values (In wi)) (hr : i reset = 1) (traffic : List (Values (In wi))) :
    let h := observedHistory a.circuit (a.circuit.step i r) {} traffic
    let result := runHistory m.component empty {} (traffic.map (fun (j : Values (In wi)) => decodeInput j))
    h.inputs.map f = h.outputs ++ k.pending result.1 := by
  simpa only [history_eq a _ _ (a.recover i r hr)] using
    k.history empty {} valid (by simp [start]) (traffic.map (fun (j : Values (In wi)) => decodeInput j))

/-- Acceptance criterion for the proposed serial composition rule. This is a
statement to discharge for the wired lane, not an assumption on a FIFO. -/
def LaneLaw (fifo : Fifo w d) (extra : Nat) : Prop :=
  let c := lane fifo extra
  let empty : List (BitVec w) × PipelineState (BitVec w) extra := ([], pipelineEmpty extra)
  ∀ (r : Values (Joint fifo.Register (Design.pipeline (increment w) extra).flatten.Register))
    (i : Values (In w)), i reset = 1 → ∀ traffic : List (Values (In w)),
    let h := observedHistory c (c.step i r) {} traffic
    let result := runHistory (buffered (increment w).function d extra).component empty {}
      (traffic.map (fun (j : Values (In w)) => decodeInput j))
    h.inputs.map (fun x => x + 1) =
      h.outputs ++ (bufferedContract (increment w).function d extra).pending result.1

end FifoSubstitutionSketch
