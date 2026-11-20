import Pinwheel.Hardware.TimedPairs

/-! Transaction contracts for a synchronous ready/valid interface.
Transfers use pre-edge observations. Reset cancels transfers and begins a new epoch.
No assumption of eventual downstream readiness is hidden in the safety contract. -/
namespace Pinwheel.Hardware.Stream

structure Input (α : Type) where
  reset : Bool
  offered : Option α
  ready : Bool
  deriving Repr, DecidableEq

structure Output (α : Type) where
  ready : Bool
  offered : Option α
  deriving Repr, DecidableEq

def accepted (i : Input α) (o : Output β) : List α :=
  if i.reset then [] else if o.ready then i.offered.toList else []

def emitted (i : Input α) (o : Output β) : List β :=
  if i.reset then [] else if i.ready then o.offered.toList else []

/-- A local conservation law. Pending values are in delivery order and include
all accepted transactions, including those still upstream of a mapped stage. -/
structure Contract (c : Timed.Component (Input α) S (Output β)) (f : α → β) where
  pending : S → List β
  Valid : S → Prop
  preserved : ∀ i s, Valid s → Valid (c.step i s)
  reset_empty : ∀ i s, i.reset = true → pending (c.step i s) = []
  balance : ∀ i s, Valid s → i.reset = false →
    pending s ++ (accepted i (c.observe i s)).map f =
      emitted i (c.observe i s) ++ pending (c.step i s)

structure History (α β : Type) where
  inputs : List α := []
  outputs : List β := []

def History.advance (h : History α β) (i : Input α) (o : Output β) : History α β :=
  if i.reset then ⟨[], []⟩
  else ⟨h.inputs ++ accepted i o, h.outputs ++ emitted i o⟩

def runHistory (c : Timed.Component (Input α) S (Output β)) :
    S → History α β → List (Input α) → S × History α β
  | s, h, [] => (s, h)
  | s, h, i :: rest => runHistory c (c.step i s) (h.advance i (c.observe i s)) rest

/-- The end-to-end statement used by every implementation of the contract. -/
theorem Contract.history {c : Timed.Component (Input α) S (Output β)} {f : α → β}
    (k : Contract c f) (s : S) (h : History α β)
    (hs : k.Valid s) (hh : h.inputs.map f = h.outputs ++ k.pending s)
    (is : List (Input α)) :
    let result := runHistory c s h is
    result.2.inputs.map f = result.2.outputs ++ k.pending result.1 := by
  induction is generalizing s h with
  | nil => exact hh
  | cons i rest ih =>
    apply ih _ _ (k.preserved i s hs)
    cases hr : i.reset <;> simp [History.advance, hr, List.map_append, hh,
      List.append_assoc, k.balance i s hs, k.reset_empty i s]

end Pinwheel.Hardware.Stream
