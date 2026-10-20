import Pinwheel.Hardware.Buffered.GenericEffects

/-! Source entry-success premises and the final retained outcome after HALT
settles. The raw entry-effects result intentionally leaves HALT unchanged. -/
namespace Pinwheel.Hardware.Buffered.GenericEffects
open Pinwheel.Program Pinwheel.Engine.Reactive

theorem result_success_shift_available (instruction : Program.Buffered.Instruction)
    (e : Transfer.Execution) (sampled : Inputs) (pin : Fin 3) (enable invert : Bool)
    (action : Action 15) (operation : instruction.operation = .shift pin enable invert action)
    (success : (result instruction e sampled).outcome = none) :
    e.txConsumed < e.request.tx.length := by
  by_cases available : e.txConsumed < e.request.tx.length
  · exact available
  · simp [result, operation, consumes, available] at success

def finalOutcome (instruction : Program.Buffered.Instruction) (e : Transfer.Execution)
    (sampled : Inputs) : Option Transfer.Outcome :=
  match instruction.operation with
  | .halt => some .complete
  | .fault reason => some reason.outcome
  | _ => (result instruction e sampled).outcome

theorem finalOutcome_halt (instruction : Program.Buffered.Instruction)
    (e : Transfer.Execution) (sampled : Inputs) (operation : instruction.operation = .halt) :
    finalOutcome instruction e sampled = some .complete := by
  simp only [finalOutcome, operation]

theorem finalOutcome_fault (instruction : Program.Buffered.Instruction)
    (e : Transfer.Execution) (sampled : Inputs) (reason : Program.Buffered.Failure)
    (operation : instruction.operation = .fault reason) :
    finalOutcome instruction e sampled = some reason.outcome := by
  simp only [finalOutcome, operation]

end Pinwheel.Hardware.Buffered.GenericEffects
