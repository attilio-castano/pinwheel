import Pinwheel.Hardware.Buffered.GenericEntryTransfer

/-! Terminal dispatch equations for the unchanged Buffered source interpreter.
Normalized checked destinations are selected after terminal scratch capture. -/
namespace Pinwheel.Hardware.Buffered.GenericInterpreter
open Pinwheel.Hardware Pinwheel.Program Pinwheel.Engine.Reactive

def dispatchState (p : Program.Buffered.Program) (s : Program.Buffered.State)
    (target : Option Program.Buffered.PC) (slots : Vector Bool 16) (sampled : Inputs) :
    Program.Buffered.State :=
  match target with
  | none => Program.Buffered.terminal p Refinement.capacity
      {s with core := {s.core with samples := slots}} .fault
  | some pc => GenericEntry.entered p s pc slots sampled

theorem jump_filter (p : Program.Buffered.Program) (s : Program.Buffered.State)
    (target : Program.Buffered.PC) (slots : Vector Bool 16) (sampled : Inputs) :
    Fetch.jump (Program.Buffered.lower p s) target slots sampled =
      match (some target).filter (fun pc => decide (pc.val ≤ p.last.val)) with
      | none => Fetch.stop (Program.Buffered.lower p s) .fault slots
      | some target => Fetch.enter (Program.Buffered.lower p s) target slots sampled := by
  by_cases within : target.val ≤ p.last.val
  all_goals simp [Fetch.jump, Program.Buffered.lower, Option.filter, within]

theorem finish_dispatch (p : Program.Buffered.Program) (s : Program.Buffered.State)
    (pc : Program.Buffered.PC) (finish : Program.Buffered.Finish)
    (normalized : Engine.Reactive.Finish 1023 15)
    (normalization : finish.eval pc = some normalized)
    (slots : Vector Bool 16) (sampled : Inputs) :
    Fetch.dispatch (Program.Buffered.lower p s) pc normalized slots sampled =
      match Program.Buffered.finishTarget p pc finish slots with
      | none => Fetch.stop (Program.Buffered.lower p s) .fault slots
      | some target => Fetch.enter (Program.Buffered.lower p s) target slots sampled := by
  cases finish
  case branch sample yes no =>
    cases yesEq : yes.eval pc
    case none => simp [Program.Buffered.Finish.eval, yesEq] at normalization
    case some yesPC =>
      cases noEq : no.eval pc
      case none => simp [Program.Buffered.Finish.eval, yesEq, noEq] at normalization
      case some noPC =>
        have same : normalized = .branch sample yesPC noPC := by
          simpa [Program.Buffered.Finish.eval, yesEq, noEq] using normalization.symm
        subst normalized
        cases selected : slots[sample.val]
        · simpa only [Fetch.dispatch, Program.Buffered.finishTarget, selected,
            Bool.false_eq_true, ↓reduceIte, noEq] using jump_filter p s noPC slots sampled
        · simpa only [Fetch.dispatch, Program.Buffered.finishTarget, selected,
            ↓reduceIte, yesEq] using jump_filter p s yesPC slots sampled
  case jump target =>
    have same : normalized = .jump target := by
      simpa [Program.Buffered.Finish.eval] using normalization.symm
    subst normalized
    exact jump_filter p s target slots sampled
  case sequential =>
    have same : normalized = .sequential := by
      simpa [Program.Buffered.Finish.eval] using normalization.symm
    subst normalized
    by_cases within : pc.val < p.last.val
    · have bound : pc.val + 1 ≤ p.last.val := by omega
      simp [Fetch.dispatch, Fetch.next, Program.Buffered.lower, Program.Buffered.finishTarget,
        Program.Buffered.sequentialTarget, within, bound, Option.filter]
    · simp [Fetch.dispatch, Fetch.next, Program.Buffered.lower, Program.Buffered.finishTarget,
        Program.Buffered.sequentialTarget, within, Option.filter]
  all_goals done

theorem active_dispatch (p : Program.Buffered.Program) (s : Program.Buffered.State)
    (pc : Program.Buffered.PC) (owner : Program.Buffered.owned s = true)
    (control : s.core.control = .active pc 0) (raw : Inputs) :
    Program.Buffered.advance p Refinement.capacity s raw =
      dispatchState p {s with samplerFirst := raw, samplerSecond := s.samplerFirst}
        (Program.Buffered.sequentialTarget p pc) s.core.samples s.samplerSecond := by
  by_cases within : pc.val < p.last.val
  all_goals simp [Program.Buffered.advance, owner, control, busy, Fetch.advance, Fetch.next,
    Program.Buffered.entryTarget, Program.Buffered.sequentialTarget, within, dispatchState,
    GenericEntry.entered, Program.Buffered.settle, Program.Buffered.terminal,
    Program.Buffered.lower, Fetch.stop]
  all_goals rfl
  all_goals done

theorem wait_dispatch (p : Program.Buffered.Program) (s : Program.Buffered.State)
    (pc : Program.Buffered.PC) (remaining : Fin 256)
    (instruction : Program.Buffered.Instruction) (wait : Wait)
    (owner : Program.Buffered.owned s = true)
    (control : s.core.control = .waiting pc remaining)
    (fetch : p.fetch pc = some instruction) (operation : instruction.operation = .wait wait)
    (ready : wait.condition.ready s.samplerSecond = true) (raw : Inputs) :
    Program.Buffered.advance p Refinement.capacity s raw =
      dispatchState p {s with samplerFirst := raw, samplerSecond := s.samplerFirst}
        (Program.Buffered.sequentialTarget p pc) s.core.samples s.samplerSecond := by
  rcases instruction with ⟨op, append, levels, enabled⟩
  cases operation
  by_cases within : pc.val < p.last.val
  all_goals simp [Program.Buffered.advance, owner, control, busy, Fetch.advance, Fetch.next,
    Program.Buffered.lower, fetch, Program.Buffered.normalize, ready,
    Program.Buffered.entryTarget, Program.Buffered.sequentialTarget, within, dispatchState,
    GenericEntry.entered, Program.Buffered.settle, Program.Buffered.terminal, Fetch.stop]
  all_goals rfl

theorem qualify_dispatch (p : Program.Buffered.Program) (s : Program.Buffered.State)
    (pc : Program.Buffered.PC) (waitLeft : Fin 256)
    (instruction : Program.Buffered.Instruction) (qualify : Qualify)
    (owner : Program.Buffered.owned s = true)
    (control : s.core.control = .qualifying pc 0 waitLeft)
    (fetch : p.fetch pc = some instruction) (operation : instruction.operation = .qualify qualify)
    (ready : qualify.condition.ready s.samplerSecond = true) (raw : Inputs) :
    Program.Buffered.advance p Refinement.capacity s raw =
      dispatchState p {s with samplerFirst := raw, samplerSecond := s.samplerFirst}
        (Program.Buffered.sequentialTarget p pc) s.core.samples s.samplerSecond := by
  rcases instruction with ⟨op, append, levels, enabled⟩
  cases operation
  by_cases within : pc.val < p.last.val
  all_goals simp [Program.Buffered.advance, owner, control, busy, Fetch.advance, Fetch.next,
    Program.Buffered.lower, fetch, Program.Buffered.normalize, ready,
    Program.Buffered.entryTarget, Program.Buffered.sequentialTarget, within, dispatchState,
    GenericEntry.entered, Program.Buffered.settle, Program.Buffered.terminal, Fetch.stop]
  all_goals rfl

theorem checked_dispatch (p : Program.Buffered.Program) (s : Program.Buffered.State)
    (pc : Program.Buffered.PC) (instruction : Program.Buffered.Instruction)
    (action : Action 15) (guard : Check) (terminal : Option (Capture 15))
    (finish : Program.Buffered.Finish) (normalized : Engine.Reactive.Finish 1023 15)
    (owner : Program.Buffered.owned s = true)
    (control : s.core.control = .checked pc 0)
    (fetch : p.fetch pc = some instruction)
    (operation : instruction.operation = .checked action guard terminal finish)
    (normalization : finish.eval pc = some normalized)
    (ready : guard.ready s.samplerSecond = true) (raw : Inputs) :
    Program.Buffered.advance p Refinement.capacity s raw =
      dispatchState p {s with samplerFirst := raw, samplerSecond := s.samplerFirst}
        (Program.Buffered.finishTarget p pc finish (capture s.core.samples terminal s.samplerSecond))
        (capture s.core.samples terminal s.samplerSecond) s.samplerSecond := by
  have lowered : (Program.Buffered.lower p s).fetch pc =
      some (.checked ⟨{action with
        pins := Program.Buffered.keepPins action.pins s.core.pins
          instruction.preserveLevels instruction.preserveEnabled}, guard, terminal, normalized⟩) := by
    simp [Program.Buffered.lower, fetch, Program.Buffered.normalize, operation, normalization]
  have target : Program.Buffered.entryTarget p s s.samplerSecond =
      Program.Buffered.finishTarget p pc finish (capture s.core.samples terminal s.samplerSecond) := by
    rcases instruction with ⟨op, append, levels, enabled⟩
    cases operation
    simp [Program.Buffered.entryTarget, control, fetch, ready]
  simp [Program.Buffered.advance, owner, control, busy, Fetch.advance, lowered, ready, target]
  rw [finish_dispatch p s pc finish normalized normalization
    (capture s.core.samples terminal s.samplerSecond) s.samplerSecond]
  cases targetEq : Program.Buffered.finishTarget p pc finish
    (capture s.core.samples terminal s.samplerSecond)
  all_goals simp [dispatchState, GenericEntry.entered, Program.Buffered.settle,
    Program.Buffered.terminal, Program.Buffered.lower, Fetch.stop]
  all_goals rfl

end Pinwheel.Hardware.Buffered.GenericInterpreter
