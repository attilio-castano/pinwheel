import Pinwheel.Hardware.Buffered.GenericInterpreter

/-! Checked source clocks preserve arbitrary scratch until a terminal capture
is due; guards and eager finish normalization remain explicit operands. -/
namespace Pinwheel.Hardware.Buffered.GenericInterpreter
open Pinwheel.Program Pinwheel.Engine.Reactive

theorem checked_countdown (p : Program.Buffered.Program) (capacity : Transfer.Capacity)
    (s : Program.Buffered.State) (pc : Program.Buffered.PC) (remaining : Fin 256)
    (instruction : Program.Buffered.Instruction) (action : Action 15) (guard : Check)
    (terminal : Option (Capture 15)) (finish : Program.Buffered.Finish)
    (normalized : Finish 1023 15)
    (owner : Program.Buffered.owned s = true)
    (control : s.core.control = .checked pc remaining)
    (fetch : p.fetch pc = some instruction)
    (operation : instruction.operation = .checked action guard terminal finish)
    (normalization : finish.eval pc = some normalized)
    (ready : guard.ready s.samplerSecond = true)
    (positive : 0 < remaining.val) (incoming : Inputs) :
    Program.Buffered.advance p capacity s incoming =
      {s with
        core := {s.core with control := .checked pc ⟨remaining.val - 1, by omega⟩}
        samplerFirst := incoming
        samplerSecond := s.samplerFirst} := by
  rcases instruction with ⟨op, append, levels, enabled⟩
  cases operation
  simp [Program.Buffered.advance, owner, busy, control, Fetch.advance,
    Program.Buffered.lower, fetch, Program.Buffered.normalize, ready, normalization,
    Program.Buffered.entryTarget, Program.Buffered.settle, positive,
    show remaining.val ≠ 0 by omega]
  done

end Pinwheel.Hardware.Buffered.GenericInterpreter
