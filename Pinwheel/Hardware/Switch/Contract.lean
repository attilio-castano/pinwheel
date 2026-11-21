import Pinwheel.Hardware.Switch.Model
import Pinwheel.Hardware.Stream.Multiport

namespace Pinwheel.Hardware.Switch


def ofFrame (i : Stream.Multiport.Input (n + 1) m (Packet m α)) : Input n m α := ⟨i.reset, i.offered, i.ready⟩

def frameComponent (depth : Nat) :
    Timed.Component (Stream.Multiport.Input (n + 1) m (Packet m α)) (State n m α) (Stream.Multiport.Output (n + 1) m (Delivery n m α)) where
  step := fun i => step depth (ofFrame i)
  observe := fun i s => let o := observe depth (ofFrame i) s; ⟨o.ready, o.offered⟩

def pendingFlow (s : State n m α) (source : Fin (n + 1)) (destination : Fin m) : List (Delivery n m α) :=
  ((s.slots destination).toList.filter (fun d => d.source == source)) ++
    ((s.queues source).filter (fun p => p.destination == destination)).map (fun p => ⟨source, p⟩)

def flowContract (depth : Nat) : Stream.Multiport.Contract (frameComponent (n := n) (m := m) (α := α) depth)
    Packet.destination Delivery.source (fun source packet => ⟨source, packet⟩) where
  pending := pendingFlow
  Valid := Valid depth
  preserved := fun i s h => valid_preserved depth (ofFrame i) s h
  reset_empty := by
    intro i s hr source destination
    change pendingFlow (step depth (ofFrame i) s) source destination = []
    rw [reset_state depth (ofFrame i) s hr]
    rfl
  balance := by
    intro i s hs hr source destination
    have hq := congrArg (fun xs : List (Packet m α) =>
      (xs.filter (fun p => p.destination == destination)).map (fun p => (⟨source, p⟩ : Delivery n m α)))
      (queue_balance depth (ofFrame i) s source (hs.1 source) hr)
    have ho := congrArg (fun xs : List (Delivery n m α) => xs.filter (fun d => d.source == source))
      (slot_balance depth (ofFrame i) s destination hr)
    simp only [List.filter_append, List.map_append] at hq ho
    rw [transfer_exchange] at hq
    simp only [pendingFlow, Stream.Multiport.forDestination, Stream.Multiport.fromSource,
      Stream.Multiport.accepted, Stream.Multiport.emitted, frameComponent, ofFrame, observe,
      hr, Bool.false_eq_true, if_false]
    simp only [acceptedAt, observe, ofFrame, hr, Bool.false_eq_true, if_false] at hq
    simp only [emittedAt, ofFrame, hr, Bool.false_eq_true, if_false] at ho
    rw [List.append_assoc, hq, ← List.append_assoc, ho, List.append_assoc]

/-- Complete per-flow conservation and ordering for arbitrary traffic and reset
epochs, starting with empty queues and output slots. Source provenance is logical. -/
theorem transactions (depth : Nat) (inputs : List (Stream.Multiport.Input (n + 1) m (Packet m α))) :
    let result := Stream.Multiport.runHistory (frameComponent depth) initial {} inputs
    ∀ source destination,
      (Stream.Multiport.forDestination Packet.destination destination (result.2.inputs source)).map
        (fun p => (⟨source, p⟩ : Delivery n m α)) =
      Stream.Multiport.fromSource Delivery.source source (result.2.outputs destination) ++
        pendingFlow result.1 source destination :=
  (flowContract depth).history initial {} (initial_valid depth) (fun _ _ => rfl) inputs

end Pinwheel.Hardware.Switch
