import Pinwheel.Hardware.Storage.PairedEntry

/-! Reachable E64 control states retain the operation that installed their mode. -/
namespace Pinwheel.Hardware.Storage.PairedReference
open Pinwheel.Hardware

def Coherent (p : Execution.Image) (s : Reactive.Model) : Prop :=
  match s.control with
  | .stopped _ => True
  | .active pc _ => ∃ a, p.fetch pc = .action a
  | .waiting pc _ => ∃ w, p.fetch pc = .wait w
  | .checked pc _ => ∃ a, p.fetch pc = .checked a
  | .qualifying pc _ _ => ∃ q, p.fetch pc = .qualify q

theorem enter (p : Execution.Image) (pc : Fin 256) (slots : Reactive.Samples) (i : BitVec 2) :
    Coherent p (Engine.Reactive.enter p pc slots i) := by
  cases h : p.fetch pc <;> simp [Engine.Reactive.enter, h, Coherent, Engine.Reactive.stop]

theorem next (p : Execution.Image) (pc : Fin 256) (slots : Reactive.Samples) (i : BitVec 2) :
    Coherent p (Engine.Reactive.next p pc slots i) := by
  unfold Engine.Reactive.next
  split <;> first | exact enter _ _ _ _ | trivial

theorem jump (p : Execution.Image) (pc : Fin 256) (slots : Reactive.Samples) (i : BitVec 2) :
    Coherent p (Engine.Reactive.jump p pc slots i) := by
  unfold Engine.Reactive.jump
  split <;> first | exact enter _ _ _ _ | trivial

theorem dispatch (p : Execution.Image) (pc : Fin 256) (f : Engine.Reactive.Finish 255 15)
    (slots : Reactive.Samples) (i : BitVec 2) :
    Coherent p (Engine.Reactive.dispatch p pc f slots i) := by
  cases f <;> first | exact next _ _ _ _ | exact jump _ _ _ _

theorem advance (p : Execution.Image) (s : Reactive.Model) (i : BitVec 2) (h : Coherent p s) :
    Coherent p (Engine.Reactive.advance p s i) := by
  rcases s with ⟨control, pins, slots⟩
  cases control <;> simp only [Engine.Reactive.advance] at ⊢
  all_goals first | exact h | skip
  all_goals try (obtain ⟨op, hop⟩ := h; simp only [hop])
  all_goals repeat first
    | exact next _ _ _ _
    | exact dispatch _ _ _ _ _
    | assumption
    | exact ⟨_, hop⟩
    | trivial
    | split
  done

theorem step (p : Execution.Image) (s : Reactive.Model) (r b : Bool) (i : BitVec 2)
    (h : Coherent p s) : Coherent p (Engine.Reactive.step p s r b i) := by
  unfold Engine.Reactive.step
  repeat first | exact h | exact advance _ _ _ h | exact enter _ _ _ _ | trivial | split
  done

end Pinwheel.Hardware.Storage.PairedReference
