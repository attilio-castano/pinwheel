import Pinwheel.Hardware.Buffered.SpiInterpreter

/-! Source-only summaries of actual Buffered entry effects. Consumption occurs
before RX append, and an RX-full fault retains any bit consumed on that entry.
The summary is proved against `Buffered.entryEffects`, not postulated. -/
namespace Pinwheel.Hardware.Buffered.GenericEffects
open Pinwheel.Program Pinwheel.Engine.Reactive

def consumes : Program.Buffered.Operation → Bool
  | .shift .. => true
  | _ => false

def sample (instruction : Program.Buffered.Instruction) (sampled : Inputs) : Bool :=
  sampled[(instruction.append.getD 0).val]

structure Result where
  consume : Bool
  receive : Bool
  sample : Bool
  outcome : Option Transfer.Outcome
  deriving DecidableEq, Repr

def Result.execution (result : Result) (e : Transfer.Execution) : Transfer.Execution :=
  {e with
    txConsumed := if result.consume then e.txConsumed + 1 else e.txConsumed
    rx := if result.receive then e.rx ++ [result.sample] else e.rx}

def result (instruction : Program.Buffered.Instruction) (e : Transfer.Execution)
    (sampled : Inputs) : Result :=
  let bit := sample instruction sampled
  match instruction.operation with
  | .fault reason => ⟨false, false, bit, some reason.outcome⟩
  | .halt => ⟨false, false, bit, none⟩
  | operation =>
    if consumes operation && !decide (e.txConsumed < e.request.tx.length) then
      ⟨false, false, bit, some .fault⟩
    else match instruction.append with
      | none => ⟨consumes operation, false, bit, none⟩
      | some _ => if e.rx.length < e.request.rxLimit then
          ⟨consumes operation, true, bit, none⟩
        else ⟨consumes operation, false, bit, some .fault⟩

def replaceExecution (s : Program.Buffered.State) (e : Transfer.Execution) : Program.Buffered.State :=
  {s with buffers := {s.buffers with slot := .running e}}

def applyResult (p : Program.Buffered.Program) (capacity : Transfer.Capacity)
    (s : Program.Buffered.State) (e : Transfer.Execution) (result : Result) : Program.Buffered.State :=
  let updated := replaceExecution s (result.execution e)
  match result.outcome with
  | none => updated
  | some outcome => Program.Buffered.terminal p capacity updated outcome

theorem replace_self (s : Program.Buffered.State) (e : Transfer.Execution)
    (running : s.buffers.slot = .running e) : replaceExecution s e = s := by
  unfold replaceExecution
  rw [← running]

theorem shift_append_full (p : Program.Buffered.Program) (capacity : Transfer.Capacity)
    (s : Program.Buffered.State) (e : Transfer.Execution) (pc : Program.Buffered.PC)
    (instruction : Program.Buffered.Instruction) (pin : Fin 3) (enable invert : Bool)
    (action : Action 15) (input : Fin 2) (sampled : Inputs)
    (healthy : s.core.control ≠ .stopped .fault)
    (fetch : p.fetch pc = some instruction)
    (operation : instruction.operation = .shift pin enable invert action)
    (append : instruction.append = some input)
    (running : s.buffers.slot = .running e) (owner : e.request.identity = s.owner)
    (available : e.txConsumed < e.request.tx.length)
    (full : ¬ e.rx.length < e.request.rxLimit) :
    Program.Buffered.entryEffects p capacity s pc sampled =
      Program.Buffered.terminal p capacity
        (replaceExecution s {e with txConsumed := e.txConsumed + 1}) .fault := by
  simp [Program.Buffered.entryEffects, healthy, fetch, operation, append,
    Program.Buffered.consumed, Program.Buffered.appended, Transfer.step,
    Transfer.Command.identity, Transfer.Slot.identity, Transfer.admittedStep,
    running, owner, List.getElem?_eq_getElem available, full, Transfer.reject, replaceExecution]
  done

theorem entryEffects_result (p : Program.Buffered.Program) (capacity : Transfer.Capacity)
    (s : Program.Buffered.State) (e : Transfer.Execution) (pc : Program.Buffered.PC)
    (instruction : Program.Buffered.Instruction) (sampled : Inputs)
    (healthy : s.core.control ≠ .stopped .fault)
    (fetch : p.fetch pc = some instruction)
    (running : s.buffers.slot = .running e) (owner : e.request.identity = s.owner) :
    Program.Buffered.entryEffects p capacity s pc sampled =
      applyResult p capacity s e (result instruction e sampled) := by
  rcases s with ⟨core, ⟨epoch, sequence, slot⟩, identity, first, second⟩
  cases running
  rcases instruction with ⟨operation, append, preserveLevels, preserveEnabled⟩
  cases operation
  all_goals cases append
  all_goals by_cases available : e.txConsumed < e.request.tx.length
  all_goals by_cases room : e.rx.length < e.request.rxLimit
  all_goals simp [Program.Buffered.entryEffects, healthy, fetch, result, consumes, sample,
    applyResult, Result.execution, Program.Buffered.consumed, Program.Buffered.appended,
    Transfer.step, Transfer.Command.identity, Transfer.Slot.identity, Transfer.admittedStep,
    owner, available, room,
    Transfer.reject, replaceExecution]
  done

theorem result_bounds (instruction : Program.Buffered.Instruction) (e : Transfer.Execution)
    (sampled : Inputs) :
    ((result instruction e sampled).consume = true → e.txConsumed < e.request.tx.length) ∧
      ((result instruction e sampled).receive = true → e.rx.length < e.request.rxLimit) := by
  rcases instruction with ⟨operation, append, preserveLevels, preserveEnabled⟩
  cases operation
  all_goals cases append
  all_goals by_cases available : e.txConsumed < e.request.tx.length
  all_goals by_cases room : e.rx.length < e.request.rxLimit
  all_goals simp [result, consumes, available, room]

theorem result_sample (instruction : Program.Buffered.Instruction) (e : Transfer.Execution)
    (sampled : Inputs) : (result instruction e sampled).sample = sample instruction sampled := by
  rcases instruction with ⟨operation, append, preserveLevels, preserveEnabled⟩
  cases operation
  all_goals cases append
  all_goals by_cases available : e.txConsumed < e.request.tx.length
  all_goals by_cases room : e.rx.length < e.request.rxLimit
  all_goals simp [result, consumes, available, room]

theorem settle_busy (p : Program.Buffered.Program) (capacity : Transfer.Capacity)
    (s : Program.Buffered.State) (active : busy s.core = true) :
    Program.Buffered.settle p capacity s = s := by
  cases control : s.core.control <;> simp_all [busy, Program.Buffered.settle]

theorem settle_terminal_running (p : Program.Buffered.Program) (capacity : Transfer.Capacity)
    (s : Program.Buffered.State) (e : Transfer.Execution) (outcome : Transfer.Outcome)
    (running : s.buffers.slot = .running e) (owner : e.request.identity = s.owner) :
    Program.Buffered.settle p capacity (Program.Buffered.terminal p capacity s outcome) =
      Program.Buffered.terminal p capacity s outcome := by
  rw [SpiInterpreter.terminal_running p capacity s e outcome running owner]
  cases outcome <;> simp [Program.Buffered.settle, Program.Buffered.terminal,
    Program.Buffered.lower, Fetch.stop, Transfer.step, Transfer.Command.identity,
    Transfer.Slot.identity, owner, Transfer.admittedStep, Transfer.reject]
  done

end Pinwheel.Hardware.Buffered.GenericEffects
