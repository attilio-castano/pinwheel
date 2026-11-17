import Pinwheel.Hardware.Timed

namespace Pinwheel.Hardware.Stream.Multiport

/-- A synchronous frame of independent ready/valid input and output channels. -/
structure Input (inputs outputs : Nat) (α : Type) where
  reset : Bool
  offered : Fin inputs → Option α
  ready : Fin outputs → Bool

structure Output (inputs outputs : Nat) (β : Type) where
  ready : Fin inputs → Bool
  offered : Fin outputs → Option β

def accepted (i : Input n m α) (o : Output n m β) (source : Fin n) : List α :=
  if i.reset then [] else if o.ready source then (i.offered source).toList else []

def emitted (i : Input n m α) (o : Output n m β) (destination : Fin m) : List β :=
  if i.reset then [] else if i.ready destination then (o.offered destination).toList else []

def forDestination (route : α → Fin m) (destination : Fin m) (xs : List α) : List α :=
  xs.filter (fun x => route x == destination)

def fromSource (origin : β → Fin n) (source : Fin n) (xs : List β) : List β :=
  xs.filter (fun x => origin x == source)

/-- Origin may be logical provenance erased by a later physical refinement.
The contract permits arbitration to interleave different sources freely. -/
structure Contract (c : Timed.Component (Input n m α) S (Output n m β))
    (route : α → Fin m) (origin : β → Fin n) (transform : Fin n → α → β) where
  pending : S → Fin n → Fin m → List β
  Valid : S → Prop
  preserved : ∀ i s, Valid s → Valid (c.step i s)
  reset_empty : ∀ i s, i.reset = true → ∀ source destination, pending (c.step i s) source destination = []
  balance : ∀ i s, Valid s → i.reset = false → ∀ source destination,
    pending s source destination ++
      (forDestination route destination (accepted i (c.observe i s) source)).map (transform source) =
    fromSource origin source (emitted i (c.observe i s) destination) ++
      pending (c.step i s) source destination

structure History (n m : Nat) (α β : Type) where
  inputs : Fin n → List α := fun _ => []
  outputs : Fin m → List β := fun _ => []

def History.advance (h : History n m α β) (i : Input n m α) (o : Output n m β) : History n m α β :=
  if i.reset then {}
  else ⟨fun source => h.inputs source ++ accepted i o source,
        fun destination => h.outputs destination ++ emitted i o destination⟩

def runHistory (c : Timed.Component (Input n m α) S (Output n m β)) :
    S → History n m α β → List (Input n m α) → S × History n m α β
  | s, h, [] => (s, h)
  | s, h, i :: rest => runHistory c (c.step i s) (h.advance i (c.observe i s)) rest

/-- Every source/destination flow is conserved and ordered within its reset
epoch. There is deliberately no total ordering between distinct flows. -/
theorem Contract.history {c : Timed.Component (Input n m α) S (Output n m β)}
    (k : Contract c route origin transform) (s : S) (h : History n m α β)
    (hs : k.Valid s)
    (hh : ∀ source destination,
      (forDestination route destination (h.inputs source)).map (transform source) =
        fromSource origin source (h.outputs destination) ++ k.pending s source destination)
    (inputs : List (Input n m α)) :
    let result := runHistory c s h inputs
    ∀ source destination,
      (forDestination route destination (result.2.inputs source)).map (transform source) =
        fromSource origin source (result.2.outputs destination) ++ k.pending result.1 source destination := by
  induction inputs generalizing s h with
  | nil => exact hh
  | cons i rest ih =>
    apply ih _ _ (k.preserved i s hs)
    intro source destination
    have hprev := hh source destination
    have hstep := k.balance i s hs
    simp only [forDestination, fromSource] at hprev hstep
    cases hr : i.reset <;>
      simp [History.advance, hr, forDestination, fromSource, List.filter_append,
        List.map_append, hprev, List.append_assoc, hstep, k.reset_empty i s]

end Pinwheel.Hardware.Stream.Multiport
