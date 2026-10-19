import Pinwheel.Hardware.Buffered.GenericSample

/-! Consequences of the source entry outcome used when constructing running
and retained-stop representations. -/
namespace Pinwheel.Hardware.Buffered.GenericEntryFlags
open Pinwheel.Hardware Pinwheel.Program

theorem final_none (instruction : Program.Buffered.Instruction) (e : Transfer.Execution)
    (sampled : Engine.Reactive.Inputs)
    (success : GenericEffects.finalOutcome instruction e sampled = none) :
    runs instruction = true ∧
      (GenericEncoding.instruction instruction).kind ≠ 3#3 ∧
      (GenericEncoding.instruction instruction).kind ≠ 4#3 ∧
      (GenericEffects.result instruction e sampled).outcome = none := by
  rcases instruction with ⟨operation, append, preserveLevels, preserveEnabled⟩
  cases operation <;> simp_all [GenericEffects.finalOutcome, runs,
    GenericEncoding.instruction, GenericEncoding.action, GenericEncoding.empty]

theorem terminal_receive (instruction : Program.Buffered.Instruction) (e : Transfer.Execution)
    (sampled : Engine.Reactive.Inputs) (terminal : runs instruction = false) :
    (GenericEffects.result instruction e sampled).receive = false := by
  rcases instruction with ⟨operation, append, preserveLevels, preserveEnabled⟩
  cases operation <;> simp_all [runs, GenericEffects.result]

theorem final_some_phase (instruction : Program.Buffered.Instruction) (e : Transfer.Execution)
    (sampled : Engine.Reactive.Inputs) (outcome : Transfer.Outcome)
    (stopped : GenericEffects.finalOutcome instruction e sampled = some outcome) :
    (if BitVec.ofBool (timesOut instruction) = (1 : BitVec 1) then (6 : BitVec 3)
      else if BitVec.ofBool (completes instruction) = (1 : BitVec 1) then 5 else 7) =
      Refinement.stopPhase outcome := by
  rcases instruction with ⟨operation, append, preserveLevels, preserveEnabled⟩
  cases operation
  case fault reason =>
    cases reason <;> cases outcome <;> simp_all [GenericEffects.finalOutcome, timesOut, completes,
      Program.Buffered.Failure.outcome, Refinement.stopPhase]
  all_goals cases append
  all_goals by_cases available : e.txConsumed < e.request.tx.length
  all_goals by_cases room : e.rx.length < e.request.rxLimit
  all_goals simp_all [GenericEffects.finalOutcome, GenericEffects.result,
    GenericEffects.consumes, timesOut, completes, Refinement.stopPhase]
  all_goals cases outcome <;> simp_all

end Pinwheel.Hardware.Buffered.GenericEntryFlags
