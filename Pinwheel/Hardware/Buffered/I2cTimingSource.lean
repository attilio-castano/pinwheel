import Pinwheel.Hardware.Buffered.I2cCertificate
import Pinwheel.Hardware.Buffered.GenericWord

/-! Symbolic duration and wait-budget operands for the existing four-byte I²C
source. Retiming changes leaf operands while retaining the counted graph. -/
namespace Pinwheel.Hardware.Buffered.I2cTiming
open Pinwheel.Hardware Pinwheel.Program Pinwheel.Engine.Reactive
open Pinwheel.Engine.Reactive.Counted
set_option maxRecDepth 10000

def retime (duration budget : Fin 256) (instruction : Program.Buffered.Instruction) :
    Program.Buffered.Instruction :=
  {instruction with operation := match instruction.operation with
    | .drive action => .drive {action with durationMinusOne := duration}
    | .shift output enable invert action =>
        .shift output enable invert {action with durationMinusOne := duration}
    | .keep levels enabled action => .keep levels enabled {action with durationMinusOne := duration}
    | .wait wait => .wait {wait with budgetMinusOne := budget}
    | .checked action guard terminal finish =>
        .checked {action with durationMinusOne := duration} guard terminal finish
    | .qualify qualify => .qualify {qualify with durationMinusOne := duration, budgetMinusOne := budget}
    | .halt => .halt
    | .fault reason => .fault reason}

def mapCode (f : α → β) : Schedule α → Schedule β
  | .emit instruction => .emit (f instruction)
  | .seq first rest => .seq (mapCode f first) (mapCode f rest)
  | .repeat count body => .repeat count (mapCode f body)

theorem map_span (f : α → β) (code : Schedule α) : (mapCode f code).span = code.span := by
  induction code <;> simp_all [mapCode, Schedule.span]

theorem map_locate (f : α → β) (code : Schedule α) (env : Environment) (pc : Nat) :
    (mapCode f code).locate env pc =
      (code.locate env pc).map (fun found => (f found.1, found.2)) := by
  induction code generalizing env pc
  all_goals simp_all [mapCode, Schedule.locate, map_span]
  all_goals split <;> rfl

def source (duration budget : Fin 256) : Program.Buffered.Program :=
  BufferedI2C.program duration budget

theorem code_retime (duration budget : Fin 256) :
    (source duration budget).code = mapCode (retime duration budget) I2cSource.source.code := by
  rfl

theorem fetch_retime (duration budget : Fin 256) (pc : Program.Buffered.PC) :
    (source duration budget).fetch pc = (I2cSource.source.fetch pc).map (retime duration budget) := by
  simp only [Program.Buffered.Program.fetch, code_retime, map_locate, Option.map_map]
  rfl

theorem retime_finish (duration budget : Fin 256)
    (map : Program.Buffered.PC → GenericLayout.Coordinates) (instruction : Program.Buffered.Instruction) :
    GenericLayout.instructionFinish map (retime duration budget instruction) =
      GenericLayout.instructionFinish map instruction := by
  cases operation : instruction.operation
  all_goals simp [retime, GenericLayout.instructionFinish, operation]

end Pinwheel.Hardware.Buffered.I2cTiming
