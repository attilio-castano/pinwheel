import Pinwheel.Hardware.Buffered.GenericHolding
import Pinwheel.Hardware.Buffered.GenericPhasePredicates

/-! Checked guard failures and wait/qualification timeouts retain the exact
source diagnostic prefix in the actual packed stopped state. -/
namespace Pinwheel.Hardware.Buffered.Refinement
open Pinwheel.Hardware Pinwheel.Program

def heldOutcome (timeout : Bool) : Transfer.Outcome := if timeout then .timeout else .fault

theorem Running.stopTick {p : Program.Buffered.Program} {layout : GenericCertificate.Layout p}
    {payload : BitVec 32} {r : Values Reactive.Register} {s : Program.Buffered.State}
    {e : Transfer.Execution} {instruction : Program.Buffered.Instruction} {pc : Program.Buffered.PC}
    (h : Running p layout payload r s e instruction pc) (raw : BitVec 2) (timeout : Bool) :
    Stopped p layout payload (GenericPhase.stopTick r raw timeout)
      (Program.Buffered.terminal p capacity
        {s with samplerFirst := raw, samplerSecond := s.samplerFirst} (heldOutcome timeout))
      e (heldOutcome timeout) := by
  refine { common := (h.common.samplers raw s.samplerFirst).stopTick raw timeout (heldOutcome timeout)
           slot := ?_
           control := ?_
           phase := ?_
           retained := rfl
           pc := rfl
           virtualPC := rfl
           outer := rfl
           inner := rfl
           currentControl := rfl
           remaining := rfl
           waitLeft := rfl
           cachedDuration := rfl
           cachedBudget := rfl
           cachedCheck := rfl
           cachedWait := rfl
           cachedTerminal := rfl
           cachedBranch := rfl }
  case refine_1 =>
    exact congrArg (fun state : Program.Buffered.State => state.buffers.slot)
      (SpiInterpreter.terminal_running p capacity
        {s with samplerFirst := raw, samplerSecond := s.samplerFirst} e (heldOutcome timeout)
        h.slot h.common.owner)
  all_goals cases timeout
  all_goals rfl
  all_goals done

theorem Running.wait_timeout {p : Program.Buffered.Program} {layout : GenericCertificate.Layout p}
    {payload : BitVec 32} {r : Values Reactive.Register} {s : Program.Buffered.State}
    {e : Transfer.Execution} {instruction : Program.Buffered.Instruction} {pc : Program.Buffered.PC}
    (h : Running p layout payload r s e instruction pc) (wait : Engine.Reactive.Wait)
    (control : s.core.control = .waiting pc 0)
    (operation : instruction.operation = .wait wait)
    (blocked : wait.condition.ready s.samplerSecond = false)
    (i : Values Reactive.Input) (quiet : SpiCircuit.Quiet i) :
    Stopped p layout payload (Reactive.circuit.step i r)
      (Program.Buffered.advance p capacity s (i .rawInputs)) e .timeout := by
  have state : Control r instruction pc (.waiting pc 0) := control ▸ h.control
  have blockedBit : Reactive.waitReady.eval i r = 0 := by
    simpa only [blocked, BitVec.ofBool_false] using h.waitReady i wait operation
  rw [GenericPhase.wait_timeout_step i r quiet state.2.1 blockedBit (by simp [state.2.2.1]),
    GenericInterpreter.wait_timeout p capacity s pc instruction wait h.owned control h.fetch operation blocked]
  exact h.stopTick (i .rawInputs) true
  done

theorem Running.checked_fault {p : Program.Buffered.Program} {layout : GenericCertificate.Layout p}
    {payload : BitVec 32} {r : Values Reactive.Register} {s : Program.Buffered.State}
    {e : Transfer.Execution} {instruction : Program.Buffered.Instruction} {pc : Program.Buffered.PC}
    (h : Running p layout payload r s e instruction pc)
    (remaining : Fin 256) (action : Engine.Reactive.Action 15) (guard : Engine.Reactive.Check)
    (terminal : Option (Engine.Reactive.Capture 15)) (finish : Program.Buffered.Finish)
    (control : s.core.control = .checked pc remaining)
    (operation : instruction.operation = .checked action guard terminal finish)
    (blocked : guard.ready s.samplerSecond = false)
    (i : Values Reactive.Input) (quiet : SpiCircuit.Quiet i) :
    Stopped p layout payload (Reactive.circuit.step i r)
      (Program.Buffered.advance p capacity s (i .rawInputs)) e .fault := by
  have state : Control r instruction pc (.checked pc remaining) := control ▸ h.control
  have blockedBit : Reactive.checkedReady.eval i r = 0 := by
    simpa only [blocked, BitVec.ofBool_false] using h.checkedReady i action guard terminal finish operation
  rw [GenericPhase.checked_fault_step i r quiet state.2.1 blockedBit,
    GenericInterpreter.checked_fault p capacity s pc remaining instruction action guard terminal finish
      h.owned control h.fetch operation blocked]
  exact h.stopTick (i .rawInputs) false
  done

theorem Running.qualify_timeout {p : Program.Buffered.Program} {layout : GenericCertificate.Layout p}
    {payload : BitVec 32} {r : Values Reactive.Register} {s : Program.Buffered.State}
    {e : Transfer.Execution} {instruction : Program.Buffered.Instruction} {pc : Program.Buffered.PC}
    (h : Running p layout payload r s e instruction pc)
    (remaining : Fin 256) (qualify : Engine.Reactive.Qualify)
    (control : s.core.control = .qualifying pc remaining 0)
    (operation : instruction.operation = .qualify qualify)
    (blocked : qualify.condition.ready s.samplerSecond = false)
    (i : Values Reactive.Input) (quiet : SpiCircuit.Quiet i) :
    Stopped p layout payload (Reactive.circuit.step i r)
      (Program.Buffered.advance p capacity s (i .rawInputs)) e .timeout := by
  have state : Control r instruction pc (.qualifying pc remaining 0) := control ▸ h.control
  have blockedBit : Reactive.checkedReady.eval i r = 0 := by
    simpa only [blocked, BitVec.ofBool_false] using h.qualifyReady i qualify operation
  rw [GenericPhase.qualify_timeout_step i r quiet state.2.1 blockedBit (by simp [state.2.2.2.1]),
    GenericInterpreter.qualify_timeout p capacity s pc remaining instruction qualify
      h.owned control h.fetch operation blocked]
  exact h.stopTick (i .rawInputs) true
  done

end Pinwheel.Hardware.Buffered.Refinement
