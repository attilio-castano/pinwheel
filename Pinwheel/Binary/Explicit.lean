import Pinwheel.Binary.RecordProofs

namespace Pinwheel.Binary
open Engine.Reactive
open Engine.Reactive.Counted

def literalSample (c : Capture) : Sample := ⟨c.input, .literal c.destination⟩

def literalFinish : Finish → Successor
  | .sequential => .sequential
  | .jump pc => .jump (.absolute pc)
  | .branch sample yes no => .branch (.literal sample) (.absolute yes) (.absolute no)

def literal : Instruction → Template
  | .action a => .action (.literal a.pins) a.durationMinusOne (a.capture.map literalSample)
  | .wait w => .wait (.literal w.pins) w.condition w.budgetMinusOne
  | .checked a => .checked (.literal a.action.pins) a.action.durationMinusOne a.guard
      (a.action.capture.map literalSample) (a.terminalCapture.map literalSample) (literalFinish a.finish)
  | .qualify q => .qualify (.literal q.pins) q.condition q.durationMinusOne q.budgetMinusOne
  | .halt => .halt

def putInstruction (i : Instruction) : List Byte := putTemplate (literal i)

/-- Explicit images admit only literal operands, even if a dynamic operand happened to
resolve to the same instruction in the initial environment. -/
def getInstruction : Reader Instruction := do
  let t ← getTemplate
  match t.eval #v[0, 0] (Vector.replicate 2 0) 0 with
  | none => fun _ => none
  | some i => if t == literal i then return i else fun _ => none

theorem literal_finish_eval (f : Finish) (env : Environment) (pc : Fin 128) :
    (literalFinish f).eval env pc = some f := by
  cases f <;> rfl
  done

theorem literal_sample_eval (c : Option Capture) (env : Environment) :
    (c.map literalSample).map (·.eval env) = c := by
  cases c <;> rfl
  done

theorem literal_eval (i : Instruction) (data : Vector (BitVec 8) 2)
    (env : Environment) (pc : Fin 128) :
    (literal i).eval data env pc = some i := by
  cases i <;> simp [literal, Template.eval, PinExpr.eval, -Option.map_map, literal_sample_eval, literal_finish_eval]
  done

theorem instruction_law (i : Instruction) (rest : List Byte) :
    getInstruction (putInstruction i ++ rest) = some (i, rest) := by
  simp [getInstruction, putInstruction, Bind.bind, Pure.pure, StateT.bind, StateT.pure,
    template_law, literal_eval]
  done

end Pinwheel.Binary
