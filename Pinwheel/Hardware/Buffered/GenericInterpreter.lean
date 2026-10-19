import Pinwheel.Hardware.Buffered.SpiInterpreter

/-! Phase equations for the actual Buffered source interpreter. No packed
circuit or agreement assumption occurs in these source-side equations. -/
namespace Pinwheel.Hardware.Buffered.GenericInterpreter
open Pinwheel.Program Pinwheel.Engine.Reactive

theorem wait_countdown (p : Program.Buffered.Program) (capacity : Transfer.Capacity)
    (s : Program.Buffered.State) (pc : Program.Buffered.PC) (remaining : Fin 256)
    (instruction : Program.Buffered.Instruction) (wait : Wait)
    (owner : Program.Buffered.owned s = true)
    (control : s.core.control = .waiting pc remaining)
    (fetch : p.fetch pc = some instruction) (operation : instruction.operation = .wait wait)
    (blocked : wait.condition.ready s.samplerSecond = false)
    (positive : 0 < remaining.val) (incoming : Inputs) :
    Program.Buffered.advance p capacity s incoming =
      {s with
        core := {s.core with control := .waiting pc ⟨remaining.val - 1, by omega⟩}
        samplerFirst := incoming
        samplerSecond := s.samplerFirst} := by
  rcases instruction with ⟨op, append, levels, enabled⟩
  cases operation
  simp [Program.Buffered.advance, owner, busy, control, Fetch.advance,
    Program.Buffered.lower, fetch, Program.Buffered.normalize, blocked,
    Program.Buffered.entryTarget, Program.Buffered.settle, positive]
  done

theorem wait_timeout (p : Program.Buffered.Program) (capacity : Transfer.Capacity)
    (s : Program.Buffered.State) (pc : Program.Buffered.PC)
    (instruction : Program.Buffered.Instruction) (wait : Wait)
    (owner : Program.Buffered.owned s = true)
    (control : s.core.control = .waiting pc 0)
    (fetch : p.fetch pc = some instruction) (operation : instruction.operation = .wait wait)
    (blocked : wait.condition.ready s.samplerSecond = false) (incoming : Inputs) :
    Program.Buffered.advance p capacity s incoming =
      Program.Buffered.terminal p capacity
        {s with samplerFirst := incoming, samplerSecond := s.samplerFirst} .timeout := by
  rcases instruction with ⟨op, append, levels, enabled⟩
  cases operation
  simp [Program.Buffered.advance, owner, busy, control, Fetch.advance,
    Program.Buffered.lower, fetch, Program.Buffered.normalize,
    blocked, Program.Buffered.entryTarget, Program.Buffered.settle,
    Program.Buffered.terminal, Fetch.stop]

theorem wait_ready (p : Program.Buffered.Program) (capacity : Transfer.Capacity)
    (s : Program.Buffered.State) (pc : Program.Buffered.PC) (remaining : Fin 256)
    (instruction : Program.Buffered.Instruction) (wait : Wait)
    (owner : Program.Buffered.owned s = true)
    (control : s.core.control = .waiting pc remaining)
    (fetch : p.fetch pc = some instruction) (operation : instruction.operation = .wait wait)
    (ready : wait.condition.ready s.samplerSecond = true)
    (bound : pc.val < p.last.val) (incoming : Inputs) :
    Program.Buffered.advance p capacity s incoming =
      let target : Program.Buffered.PC := ⟨pc.val + 1, by have := p.last.isLt; omega⟩
      Program.Buffered.settle p capacity
        (Program.Buffered.entryEffects p capacity
          {s with
            core := Fetch.enter (Program.Buffered.lower p s) target s.core.samples s.samplerSecond
            samplerFirst := incoming
            samplerSecond := s.samplerFirst}
          target s.samplerSecond) := by
  rcases instruction with ⟨op, append, levels, enabled⟩
  cases operation
  simp [Program.Buffered.advance, owner, busy, control, Fetch.advance, Fetch.next,
    Program.Buffered.lower, fetch, Program.Buffered.normalize, ready,
    Program.Buffered.entryTarget, Program.Buffered.sequentialTarget, bound]
  done

theorem qualify_blocked (p : Program.Buffered.Program) (capacity : Transfer.Capacity)
    (s : Program.Buffered.State) (pc : Program.Buffered.PC) (remaining waitLeft : Fin 256)
    (instruction : Program.Buffered.Instruction) (qualify : Qualify)
    (owner : Program.Buffered.owned s = true)
    (control : s.core.control = .qualifying pc remaining waitLeft)
    (fetch : p.fetch pc = some instruction)
    (operation : instruction.operation = .qualify qualify)
    (blocked : qualify.condition.ready s.samplerSecond = false)
    (positive : 0 < waitLeft.val) (incoming : Inputs) :
    Program.Buffered.advance p capacity s incoming =
      {s with
        core := {s.core with control := .qualifying pc qualify.durationMinusOne ⟨waitLeft.val - 1, by omega⟩}
        samplerFirst := incoming
        samplerSecond := s.samplerFirst} := by
  rcases instruction with ⟨op, append, levels, enabled⟩
  cases operation
  simp [Program.Buffered.advance, owner, busy, control, Fetch.advance,
    Program.Buffered.lower, fetch, Program.Buffered.normalize, blocked,
    Program.Buffered.entryTarget, Program.Buffered.settle, positive]
  done

theorem qualify_progress (p : Program.Buffered.Program) (capacity : Transfer.Capacity)
    (s : Program.Buffered.State) (pc : Program.Buffered.PC) (remaining waitLeft : Fin 256)
    (instruction : Program.Buffered.Instruction) (qualify : Qualify)
    (owner : Program.Buffered.owned s = true)
    (control : s.core.control = .qualifying pc remaining waitLeft)
    (fetch : p.fetch pc = some instruction)
    (operation : instruction.operation = .qualify qualify)
    (ready : qualify.condition.ready s.samplerSecond = true)
    (positive : 0 < remaining.val) (incoming : Inputs) :
    Program.Buffered.advance p capacity s incoming =
      {s with
        core := {s.core with control := .qualifying pc ⟨remaining.val - 1, by omega⟩ qualify.budgetMinusOne}
        samplerFirst := incoming
        samplerSecond := s.samplerFirst} := by
  rcases instruction with ⟨op, append, levels, enabled⟩
  cases operation
  simp [Program.Buffered.advance, owner, busy, control, Fetch.advance,
    Program.Buffered.lower, fetch, Program.Buffered.normalize, ready,
    Program.Buffered.entryTarget, Program.Buffered.settle, positive,
    show remaining.val ≠ 0 by omega]
  done

theorem qualify_timeout (p : Program.Buffered.Program) (capacity : Transfer.Capacity)
    (s : Program.Buffered.State) (pc : Program.Buffered.PC) (remaining : Fin 256)
    (instruction : Program.Buffered.Instruction) (qualify : Qualify)
    (owner : Program.Buffered.owned s = true)
    (control : s.core.control = .qualifying pc remaining 0)
    (fetch : p.fetch pc = some instruction)
    (operation : instruction.operation = .qualify qualify)
    (blocked : qualify.condition.ready s.samplerSecond = false) (incoming : Inputs) :
    Program.Buffered.advance p capacity s incoming =
      Program.Buffered.terminal p capacity
        {s with samplerFirst := incoming, samplerSecond := s.samplerFirst} .timeout := by
  rcases instruction with ⟨op, append, levels, enabled⟩
  cases operation
  simp [Program.Buffered.advance, owner, busy, control, Fetch.advance,
    Program.Buffered.lower, fetch, Program.Buffered.normalize, blocked,
    Program.Buffered.entryTarget, Program.Buffered.settle,
    Program.Buffered.terminal, Fetch.stop]
  done

theorem checked_fault (p : Program.Buffered.Program) (capacity : Transfer.Capacity)
    (s : Program.Buffered.State) (pc : Program.Buffered.PC) (remaining : Fin 256)
    (instruction : Program.Buffered.Instruction) (action : Action 15) (guard : Check)
    (terminal : Option (Capture 15)) (finish : Program.Buffered.Finish)
    (owner : Program.Buffered.owned s = true)
    (control : s.core.control = .checked pc remaining)
    (fetch : p.fetch pc = some instruction)
    (operation : instruction.operation = .checked action guard terminal finish)
    (blocked : guard.ready s.samplerSecond = false) (incoming : Inputs) :
    Program.Buffered.advance p capacity s incoming =
      Program.Buffered.terminal p capacity
        {s with samplerFirst := incoming, samplerSecond := s.samplerFirst} .fault := by
  rcases instruction with ⟨op, append, levels, enabled⟩
  cases operation
  cases normalization : finish.eval pc
  all_goals simp [Program.Buffered.advance, owner, busy, control, Fetch.advance,
    Program.Buffered.lower, fetch, Program.Buffered.normalize, blocked, normalization,
    Program.Buffered.entryTarget, Program.Buffered.settle,
    Program.Buffered.terminal, Fetch.stop]
  all_goals done

end Pinwheel.Hardware.Buffered.GenericInterpreter
