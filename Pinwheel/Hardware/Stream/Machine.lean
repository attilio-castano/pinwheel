import Pinwheel.Hardware.Stream.Contract

namespace Pinwheel.Hardware.Stream

/-- The output offer depends only on stored state. Ready may depend on downstream
ready but not on the input offer. A chain therefore has an acyclic ready path. -/
structure Machine (α β S : Type) where
  ready : Bool → S → Bool
  offer : S → Option β
  step : Input α → S → S

def Machine.component (m : Machine α β S) : Timed.Component (Input α) S (Output β) where
  step := m.step
  observe := fun i s => if i.reset then ⟨false, none⟩ else ⟨m.ready i.ready s, m.offer s⟩

def Machine.leftInput (b : Machine β γ T) (i : Input α) (t : T) : Input α :=
  { i with ready := b.ready i.ready t }

def Machine.rightInput (a : Machine α β S) (i : Input α) (s : S) : Input β :=
  ⟨i.reset, a.offer s, i.ready⟩

def Machine.serial (a : Machine α β S) (b : Machine β γ T) : Machine α γ (S × T) where
  ready := fun r s => a.ready (b.ready r s.2) s.1
  offer := fun s => b.offer s.2
  step := fun i s => (a.step (b.leftInput i s.2) s.1, b.step (a.rightInput i s.1) s.2)

/-- Composition reorders the pending abstraction, not the transactions: items
already downstream precede the mapped upstream queue. -/
def Contract.serial {a : Machine α β S} {b : Machine β γ T} {f : α → β} {g : β → γ}
    (ka : Contract a.component f) (kb : Contract b.component g) :
    Contract (a.serial b).component (g ∘ f) where
  pending := fun s => kb.pending s.2 ++ (ka.pending s.1).map g
  Valid := fun s => ka.Valid s.1 ∧ kb.Valid s.2
  preserved := fun i s h => ⟨ka.preserved _ _ h.1, kb.preserved _ _ h.2⟩
  reset_empty := by
    intro i s hr
    have ha := ka.reset_empty (b.leftInput i s.2) s.1 hr
    have hb := kb.reset_empty (a.rightInput i s.1) s.2 hr
    change kb.pending (b.component.step (a.rightInput i s.1) s.2) ++
      (ka.pending (a.component.step (b.leftInput i s.2) s.1)).map g = []
    simp only [ha, hb, List.map_nil, List.nil_append]
  balance := by
    intro i s hs hr
    have ha := congrArg (List.map g) (ka.balance (b.leftInput i s.2) s.1 hs.1 hr)
    have hb := kb.balance (a.rightInput i s.1) s.2 hs.2 hr
    simp only [accepted, emitted, Machine.component, Machine.leftInput, Machine.rightInput,
      Machine.serial, hr, Bool.false_eq_true, if_false, List.map_append, List.map_map] at ha hb ⊢
    rw [List.append_assoc, ha, ← List.append_assoc, hb, List.append_assoc]

end Pinwheel.Hardware.Stream
