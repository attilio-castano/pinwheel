import Pinwheel.Hardware.Stream.Machine

namespace Pinwheel.Hardware.Stream

/-- Logical FIFO, including replacement of a full queue on a dequeue edge. -/
def queue (depth : Nat) : Machine α α (List α) where
  ready := fun r q => decide ((if r then q.tail else q).length < depth)
  offer := List.head?
  step := fun i q =>
    if i.reset then [] else
    let rest := if i.ready then q.tail else q
    if rest.length < depth then rest ++ i.offered.toList else rest

def queueContract (depth : Nat) : Contract (queue depth (α := α)).component id where
  pending := id
  Valid := fun q => q.length ≤ depth
  reset_empty := by intros; simp_all [Machine.component, queue]
  preserved := by
    intro i q h
    simp only [Machine.component, queue]
    cases i.reset <;> cases i.ready <;> cases i.offered <;> simp
    all_goals first | omega | (split <;> simp_all <;> omega)
  balance := by
    intro i q h hr
    cases q <;> cases hi : i.offered <;> cases hd : i.ready <;>
      simp [Machine.component, queue, accepted, emitted, hr, hi, hd]
    all_goals split <;> simp_all

def elastic (f : α → β) : Machine α β (Option β) where
  ready := fun r s => s.isNone || r
  offer := id
  step := fun i s => if i.reset then none else if s.isNone || i.ready then i.offered.map f else s

def elasticContract (f : α → β) : Contract (elastic f).component f where
  pending := Option.toList
  Valid := fun _ => True
  preserved := by intros; trivial
  reset_empty := by intros; simp_all [Machine.component, elastic]
  balance := by
    intro i s _ hr
    cases s <;> cases hi : i.offered <;> cases hd : i.ready <;>
      simp [Machine.component, elastic, accepted, emitted, hr, hi, hd]

theorem elastic_stalled (f : α → β) (i : Input α) (s : Option β)
    (hr : i.reset = false) (hd : i.ready = false) (hv : s.isSome = true) :
    (elastic f).offer ((elastic f).step i s) = s := by
  cases s <;> simp_all [elastic]

theorem queue_stalled (depth : Nat) (i : Input α) (q : List α)
    (hr : i.reset = false) (hd : i.ready = false) (hv : q ≠ []) :
    (queue depth).offer ((queue depth).step i q) = q.head? := by
  cases q <;> simp_all [queue]
  split <;> rfl

end Pinwheel.Hardware.Stream
