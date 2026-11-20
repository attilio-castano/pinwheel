import Pinwheel.Hardware.Stream.Compose

namespace Pinwheel.Hardware.Stream

theorem input_ext {i j : Values (In w)} (hr : i reset = j reset)
    (hv : i valid = j valid) (hd : i ready = j ready) (hp : i payload = j payload) :
    @i = @j := by
  funext b p
  cases p with
  | «at» k =>
    match k with
    | ⟨0, _⟩ => exact hr
    | ⟨1, _⟩ => exact hv
    | ⟨2, _⟩ => exact hd
    | ⟨3, _⟩ => exact hp
    | ⟨k + 4, h⟩ => exact False.elim (by change k + 4 < 4 at h; omega)

theorem probe_eval (i : Values I) (s : Values R) (r : Expr I R 1) (d : Bool)
    (h : r.eval i s = BitVec.ofBool d) :
    (fun {b} (p : In w b) => (probeInput r p).eval i s) =
      @inputValues w ⟨false, none, d⟩ := by
  apply input_ext
  · rfl
  · rfl
  · exact h
  · rfl

/-- A reusable component includes a transaction theorem and an implementation
relation. The register representation is private to the component's proofs. -/
structure Certified (wi wo : Nat) where
  Register : Nat → Type
  registers : Interface Register
  circuit : Circuit (In wi) Register (Out wo)
  State : Type
  machine : Machine (BitVec wi) (BitVec wo) State
  function : BitVec wi → BitVec wo
  contract : Contract machine.component function
  encode : State → Values Register
  initial : State
  initial_valid : contract.Valid initial
  initial_empty : contract.pending initial = []
  step_eq : ∀ i s, contract.Valid s → ∀ {b} (r : Register b),
    circuit.step (inputValues i) (encode s) r = encode (machine.step i s) r
  output_eq : ∀ i s, contract.Valid s → ∀ {b} (o : Out wo b),
    circuit.observe (inputValues i) (encode s) o = outputValues (machine.component.observe i s) o
  reset_eq : ∀ (i : Values (In wi)) (s : Values Register), i reset = 1 → ∀ {b} (r : Register b),
    circuit.step i s r = encode initial r

def fifoCertified (width depth : Nat) (hd : 0 < depth) : Certified width width where
  Register := CellReg width depth
  registers := CellReg.interface width depth
  circuit := Fifo.circuit width depth
  State := List (BitVec width)
  machine := queue depth
  function := id
  contract := queueContract depth
  encode := cells
  initial := []
  initial_valid := Nat.zero_le depth
  initial_empty := rfl
  step_eq := fun i s h _ r => Fifo.fifo_step i s h r
  output_eq := fun i s h => Fifo.fifo_output i s h hd
  reset_eq := by
    intro i s h b r
    cases r <;> simp [Fifo.circuit, Circuit.step, Expr.eval, h, cells]

end Pinwheel.Hardware.Stream
