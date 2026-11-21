import Pinwheel.Hardware.Stream.BackendSerial

namespace Pinwheel.Hardware.Stream.BackendAPI

private abbrev Pointed (wi wo : Nat) := (S : Type) × Machine (BitVec wi) (BitVec wo) S × S

private def prepend (m : Map wi wo) (down : Pointed wo wo) : Pointed wi wo :=
  ⟨_, (elastic m.function).serial down.2.1, (none,down.2.2)⟩

private theorem pipeline_spec (m : Map wi wo) (n : Nat) :
    (let c := (Design.pipeline m n).flatten
     (⟨c.State,c.machine,c.initial⟩ : Pointed wi wo)) =
      ⟨_, pipeline m.function n, pipelineEmpty n⟩ := by
  induction n generalizing wi with
  | zero => rfl
  | succ n ih => exact congrArg (prepend m) (ih (Map.identity wo))

private def Evidence (c : Circuit (In wi) R (Out wo)) (p : Pointed wi wo) :=
  (ref : Timed.Refinement c.component (pins p.2.1)) ×'
    ∀ (i : Values (In wi)) (r : Values R), i reset = 1 → ref.Rel (c.step i r) p.2.2

private def pipelineEvidence (m : Map wi wo) (n : Nat) :
    Evidence (Design.pipeline m n).flatten.normalized.circuit ⟨_,pipeline m.function n,pipelineEmpty n⟩ :=
  let c := (Design.pipeline m n).flatten
  (pipeline_spec m n) ▸ (show Evidence c.normalized.circuit ⟨_,c.machine,c.initial⟩ from
    ⟨c.implementation.refinement, fun i r hr => ⟨c.initial_valid,
      funext fun _ => funext fun p => c.normalized.reset_eq i r hr p⟩⟩)

def mappedPipeline (m : Map wi wo) (extra : Nat) :
    Backend (pipeline m.function extra) (pipelineEmpty extra) where
  Register := (Design.pipeline m extra).flatten.Register
  registers := (Design.pipeline m extra).flatten.registers
  circuit := (Design.pipeline m extra).flatten.normalized.circuit
  proof := (pipelineEvidence m extra).1
  recover := (pipelineEvidence m extra).2

def bufferedMap (fifo : Fifo wi depth) (m : Map wi wo) (extra : Nat) :
    Backend (buffered m.function depth extra) ([],pipelineEmpty extra) :=
  serial fifo (mappedPipeline m extra)

private theorem empty_pipeline (f : α → β) (n : Nat) :
    (pipelineContract f n).Valid (pipelineEmpty n) ∧
    (pipelineContract f n).pending (pipelineEmpty n) = [] := by
  induction n generalizing α with
  | zero => exact ⟨trivial,rfl⟩
  | succ n ih => exact ⟨⟨trivial,(ih id).1⟩, by simp [pipelineContract,pipelineEmpty,Contract.serial,elasticContract,(ih id).2]⟩

theorem buffered_transactions (fifo : Fifo wi d) (m : Map wi wo) (n : Nat)
    (r : Values (bufferedMap fifo m n).Register) (i : Values (In wi)) (hr : i reset = 1)
    (traffic : List (Values (In wi))) :
    let c := bufferedMap fifo m n
    let h := observedHistory c.circuit (c.circuit.step i r) {} traffic
    let result := runHistory (buffered m.function d n).component ([],pipelineEmpty n) {}
      (traffic.map (fun (j : Values (In wi)) => decodeInput j))
    h.inputs.map m.function = h.outputs ++ (bufferedContract m.function d n).pending result.1 :=
  transactions (bufferedMap fifo m n) (bufferedContract m.function d n)
    ⟨Nat.zero_le _,(empty_pipeline m.function n).1⟩
    (by simp [bufferedContract,Contract.serial,queueContract,(empty_pipeline m.function n).2]) r i hr traffic

end Pinwheel.Hardware.Stream.BackendAPI
