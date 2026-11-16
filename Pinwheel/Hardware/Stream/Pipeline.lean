import Pinwheel.Hardware.Stream.Queue

namespace Pinwheel.Hardware.Stream

/-- `extra` counts stages after the first mapped stage, so every pipeline has
positive latency. The state is a product of independently owned stage states. -/
def PipelineState (β : Type) : Nat → Type
  | 0 => Option β
  | n + 1 => Option β × PipelineState β n

def pipeline (f : α → β) : (extra : Nat) → Machine α β (PipelineState β extra)
  | 0 => elastic f
  | n + 1 => (elastic f).serial (pipeline id n)

def pipelineContract (f : α → β) : (extra : Nat) → Contract (pipeline f extra).component f
  | 0 => elasticContract f
  | n + 1 => (elasticContract f).serial (pipelineContract id n)

def pipelineEmpty : (extra : Nat) → PipelineState β extra
  | 0 => none
  | n + 1 => (none, pipelineEmpty n)

theorem pipeline_capacity (f : α → β) (n : Nat) (s : PipelineState β n) :
    ((pipelineContract f n).pending s).length ≤ n + 1 := by
  induction n generalizing α with
  | zero => cases s <;> simp [pipelineContract, elasticContract]
  | succ n ih =>
    simp only [pipelineContract, Contract.serial, List.length_append, List.length_map,
      elasticContract]
    have hp := ih id s.2
    cases s.1 <;> simp <;> omega

def buffered (f : α → β) (depth extra : Nat) : Machine α β (List α × PipelineState β extra) :=
  (queue depth).serial (pipeline f extra)

def bufferedContract (f : α → β) (depth extra : Nat) : Contract (buffered f depth extra).component f :=
  (queueContract depth).serial (pipelineContract f extra)

theorem buffered_capacity (f : α → β) (depth extra : Nat) (s : List α × PipelineState β extra)
    (h : (bufferedContract f depth extra).Valid s) :
    ((bufferedContract f depth extra).pending s).length ≤ depth + (extra + 1) := by
  have hp := pipeline_capacity f extra s.2
  simp only [bufferedContract, Contract.serial, queueContract, List.length_append,
    List.length_map, id_eq] at h ⊢
  omega

end Pinwheel.Hardware.Stream
