import Pinwheel.Hardware.Stream.Queue

namespace Pinwheel.Hardware.Stream

/-- Change the transaction representation without changing the handshake. -/
def mapInput (f : α → β) (i : Input α) : Input β :=
  ⟨i.reset, i.offered.map f, i.ready⟩

theorem queue_map_step (f : α → β) (depth : Nat) (i : Input α) (q : List α) :
    (queue depth).step (mapInput f i) (q.map f) = ((queue depth).step i q).map f := by
  cases i with
  | mk reset offered ready =>
    cases reset <;> cases ready <;> cases offered <;> simp [queue, mapInput, List.map_tail]
    all_goals split <;> simp_all

theorem queue_map_ready (f : α → β) (depth : Nat) (ready : Bool) (q : List α) :
    (queue depth).ready ready (q.map f) = (queue depth).ready ready q := by
  cases ready <;> simp [queue]

theorem queue_map_offer (f : α → β) (depth : Nat) (q : List α) :
    (queue depth).offer (q.map f) = ((queue depth).offer q).map f := by
  simp [queue]

theorem queue_map_observe (f : α → β) (depth : Nat) (i : Input α) (q : List α) :
    (queue depth).component.observe (mapInput f i) (q.map f) =
      ⟨((queue depth).component.observe i q).ready,
       ((queue depth).component.observe i q).offered.map f⟩ := by
  cases hr : i.reset <;> simp [Machine.component, mapInput, hr, queue_map_ready, queue_map_offer]

end Pinwheel.Hardware.Stream
