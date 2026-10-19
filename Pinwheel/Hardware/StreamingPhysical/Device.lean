import Pinwheel.Hardware.StreamingPhysical.Contraction

/-! Full-state, zero-delay sequential devices. Every Q bit is an arbitrary
source input on one clock; positive-clock/reset certificates are separate. -/
namespace Pinwheel.Hardware.StreamingPhysical

structure Device (inputs registers outputs : Nat) where
  network : Network
  dimensions : network.inputs = inputs + registers
  next : Fin registers → Atom
  output : Fin outputs → Atom
  nextBound : ∀ index, (next index).Bounded (network.inputs + network.nodes)
  outputBound : ∀ index, (output index).Bounded (network.inputs + network.nodes)

def Device.environment (inputs : Fin inputCount → Bool) (state : Fin registers → Bool)
    (wire : Nat) : Bool :=
  if first : wire < inputCount then inputs ⟨wire,first⟩
  else if present : wire - inputCount < registers then state ⟨wire - inputCount,present⟩
  else false

def Device.step (device : Device inputs registers outputs) (input : Fin inputs → Bool)
    (state : Fin registers → Bool) (index : Fin registers) : Bool :=
  (device.next index).eval (device.network.value (Device.environment input state))

def Device.observe (device : Device inputs registers outputs) (input : Fin inputs → Bool)
    (state : Fin registers → Bool) (index : Fin outputs) : Bool :=
  (device.output index).eval (device.network.value (Device.environment input state))

/-- Only structural endpoint atoms are compared; no execution, trace, or final
value agreement is a field of this certificate. -/
structure Device.Correspondence (reference actual : Device inputs registers outputs) where
  data : Contraction reference.network actual.network
  next : ∀ index, (actual.next index).rename data.image = reference.next index
  output : ∀ index, (actual.output index).rename data.image = reference.output index

theorem Device.Correspondence.step {reference actual : Device inputs registers outputs}
    (certificate : Device.Correspondence reference actual) (input : Fin inputs → Bool)
    (state : Fin registers → Bool) (index : Fin registers) :
    actual.step input state index = reference.step input state index :=
  (certificate.data.atom _ _ (actual.nextBound index)).trans
    (congrArg (Atom.eval (reference.network.value (Device.environment input state))) (certificate.next index))

theorem Device.Correspondence.observe {reference actual : Device inputs registers outputs}
    (certificate : Device.Correspondence reference actual) (input : Fin inputs → Bool)
    (state : Fin registers → Bool) (index : Fin outputs) :
    actual.observe input state index = reference.observe input state index :=
  (certificate.data.atom _ _ (actual.outputBound index)).trans
    (congrArg (Atom.eval (reference.network.value (Device.environment input state))) (certificate.output index))

def Device.run (device : Device inputs registers outputs) (state : Fin registers → Bool) :
    List (Fin inputs → Bool) → (Fin registers → Bool)
  | [] => state
  | input :: rest => device.run (device.step input state) rest

theorem Device.Correspondence.run {reference actual : Device inputs registers outputs}
    (certificate : Device.Correspondence reference actual) (state : Fin registers → Bool)
    (incoming : List (Fin inputs → Bool)) :
    actual.run state incoming = reference.run state incoming := by
  induction incoming generalizing state with
  | nil => rfl
  | cons input rest induction =>
    exact (induction (actual.step input state)).trans
      (congrArg (fun next => reference.run next rest) (funext (certificate.step input state)))

end Pinwheel.Hardware.StreamingPhysical
