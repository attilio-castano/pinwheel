import Pinwheel.Hardware.Buffered.GenericCommon
import Pinwheel.Hardware.Buffered.GenericInterpreterChecked
import Pinwheel.Hardware.Buffered.SpiRefinement

/-! Preservation of the complete generic source/circuit relation on clocks
that remain inside a leaf or stop on a held guard/timeout condition. -/
namespace Pinwheel.Hardware.Buffered.Refinement
open Pinwheel.Hardware Pinwheel.Program

theorem Common.samplers {p : Program.Buffered.Program} {layout : GenericCertificate.Layout p}
    {payload : BitVec 32} {r : Values Reactive.Register} {s : Program.Buffered.State}
    {e : Transfer.Execution} (h : Common p layout payload r s e)
    (first second : Engine.Reactive.Inputs) :
    Common p layout payload r {s with samplerFirst := first, samplerSecond := second} e :=
  ⟨h.count, h.span, h.idleLevels, h.idleEnabled, h.image, h.valid,
    h.data, h.owner, h.pins, h.scratch⟩

theorem Running.owned {p : Program.Buffered.Program} {layout : GenericCertificate.Layout p}
    {payload : BitVec 32} {r : Values Reactive.Register} {s : Program.Buffered.State}
    {e : Transfer.Execution} {instruction : Program.Buffered.Instruction} {pc : Program.Buffered.PC}
    (h : Running p layout payload r s e instruction pc) : Program.Buffered.owned s = true := by
  simp [Program.Buffered.owned, h.slot, h.common.owner]

theorem Running.holdTick {p : Program.Buffered.Program} {layout : GenericCertificate.Layout p}
    {payload : BitVec 32} {r : Values Reactive.Register} {s : Program.Buffered.State}
    {e : Transfer.Execution} {instruction : Program.Buffered.Instruction} {pc : Program.Buffered.PC}
    (h : Running p layout payload r s e instruction pc)
    (raw : BitVec 2) (remaining waitLeft : BitVec 8) (control : Engine.Reactive.Control 1023)
    (represented : Control (GenericPhase.holdTick r raw remaining waitLeft) instruction pc control) :
    Running p layout payload (GenericPhase.holdTick r raw remaining waitLeft)
      {s with core := {s.core with control}, samplerFirst := raw, samplerSecond := s.samplerFirst}
      e instruction pc :=
  ⟨h.common.holdTick raw remaining waitLeft control, h.slot, h.within, h.fetch,
    h.coordinates, h.virtualPC, h.currentControl,
    ⟨h.caches.duration, h.caches.budget, h.caches.check, h.caches.wait,
      h.caches.terminal, h.caches.branch⟩, represented, h.retained, rfl, h.first⟩

private theorem nonzero8 (n : Fin 256) (positive : 0 < n.val) :
    BitVec.ofNat 8 n.val ≠ 0#8 := by
  intro zero
  have numeric := congrArg BitVec.toNat zero
  simp at numeric
  omega
  done

theorem Running.wait_countdown {p : Program.Buffered.Program} {layout : GenericCertificate.Layout p}
    {payload : BitVec 32} {r : Values Reactive.Register} {s : Program.Buffered.State}
    {e : Transfer.Execution} {instruction : Program.Buffered.Instruction} {pc : Program.Buffered.PC}
    (h : Running p layout payload r s e instruction pc)
    (remaining : Fin 256) (wait : Engine.Reactive.Wait)
    (control : s.core.control = .waiting pc remaining)
    (operation : instruction.operation = .wait wait)
    (blocked : wait.condition.ready s.samplerSecond = false)
    (positive : 0 < remaining.val)
    (i : Values Reactive.Input) (quiet : SpiCircuit.Quiet i) :
    Running p layout payload (Reactive.circuit.step i r)
      (Program.Buffered.advance p capacity s (i .rawInputs)) e instruction pc := by
  have state := h.control
  rw [control] at state
  rcases state with ⟨_, phase, remaining_eq, kind⟩
  have cache : r .cachedWait = BitVec.ofBool wait.condition.level ++
      BitVec.ofNat 1 wait.condition.input.val := by
    simpa only [GenericEncoding.instruction, operation] using h.caches.wait
  have blocked' : wait.condition.ready (r .stage2) = false := by
    simpa only [h.second] using blocked
  have blockedBit : Reactive.waitReady.eval i r = 0 := by
    simpa only [blocked', BitVec.ofBool_false] using GenericPhase.waitReady_matches i r wait.condition cache
  rw [GenericPhase.wait_blocked_step i r quiet phase blockedBit
      (by simpa only [remaining_eq] using nonzero8 remaining positive),
    GenericInterpreter.wait_countdown p capacity s pc remaining instruction wait
      h.owned control h.fetch operation blocked positive]
  exact h.holdTick (i .rawInputs) (r .remaining - 1) (r .waitLeft) _
    ⟨rfl, phase, (congrArg (fun value : BitVec 8 => value - 1) remaining_eq).trans
      (SpiRefinement.decrement8 remaining positive), kind⟩
  done

theorem Running.qualify_progress {p : Program.Buffered.Program} {layout : GenericCertificate.Layout p}
    {payload : BitVec 32} {r : Values Reactive.Register} {s : Program.Buffered.State}
    {e : Transfer.Execution} {instruction : Program.Buffered.Instruction} {pc : Program.Buffered.PC}
    (h : Running p layout payload r s e instruction pc)
    (remaining waitLeft : Fin 256) (qualify : Engine.Reactive.Qualify)
    (control : s.core.control = .qualifying pc remaining waitLeft)
    (operation : instruction.operation = .qualify qualify)
    (ready : qualify.condition.ready s.samplerSecond = true)
    (positive : 0 < remaining.val)
    (i : Values Reactive.Input) (quiet : SpiCircuit.Quiet i) :
    Running p layout payload (Reactive.circuit.step i r)
      (Program.Buffered.advance p capacity s (i .rawInputs)) e instruction pc := by
  have state : Control r instruction pc (.qualifying pc remaining waitLeft) := control ▸ h.control
  have cache : r .cachedCheck = qualify.condition.value ++ qualify.condition.mask := by
    simpa only [GenericEncoding.instruction, operation] using h.caches.check
  have readyBit : Reactive.checkedReady.eval i r = 1 := by
    simpa only [← h.second, ready, BitVec.ofBool_true] using
      GenericPhase.checkedReady_matches i r qualify.condition cache
  rw [GenericPhase.qualify_ready_step i r quiet state.2.1 readyBit
      (by simpa only [state.2.2.1] using nonzero8 remaining positive),
    GenericInterpreter.qualify_progress p capacity s pc remaining waitLeft instruction qualify
      h.owned control h.fetch operation ready positive]
  exact h.holdTick (i .rawInputs) (r .remaining - 1) (r .cachedBudget) _
    ⟨rfl, state.2.1, (congrArg (fun value : BitVec 8 => value - 1) state.2.2.1).trans
      (SpiRefinement.decrement8 remaining positive),
      by simpa only [GenericPhase.holdTick, GenericEncoding.instruction, operation] using h.caches.budget,
      state.2.2.2.2⟩
  done

theorem Running.qualify_blocked {p : Program.Buffered.Program} {layout : GenericCertificate.Layout p}
    {payload : BitVec 32} {r : Values Reactive.Register} {s : Program.Buffered.State}
    {e : Transfer.Execution} {instruction : Program.Buffered.Instruction} {pc : Program.Buffered.PC}
    (h : Running p layout payload r s e instruction pc)
    (remaining waitLeft : Fin 256) (qualify : Engine.Reactive.Qualify)
    (control : s.core.control = .qualifying pc remaining waitLeft)
    (operation : instruction.operation = .qualify qualify)
    (blocked : qualify.condition.ready s.samplerSecond = false)
    (positive : 0 < waitLeft.val)
    (i : Values Reactive.Input) (quiet : SpiCircuit.Quiet i) :
    Running p layout payload (Reactive.circuit.step i r)
      (Program.Buffered.advance p capacity s (i .rawInputs)) e instruction pc := by
  have state : Control r instruction pc (.qualifying pc remaining waitLeft) := control ▸ h.control
  have cache : r .cachedCheck = qualify.condition.value ++ qualify.condition.mask := by
    simpa only [GenericEncoding.instruction, operation] using h.caches.check
  have blockedBit : Reactive.checkedReady.eval i r = 0 := by
    simpa only [← h.second, blocked, BitVec.ofBool_false] using
      GenericPhase.checkedReady_matches i r qualify.condition cache
  rw [GenericPhase.qualify_blocked_step i r quiet state.2.1 blockedBit
      (by simpa only [state.2.2.2.1] using nonzero8 waitLeft positive),
    GenericInterpreter.qualify_blocked p capacity s pc remaining waitLeft instruction qualify
      h.owned control h.fetch operation blocked positive]
  exact h.holdTick (i .rawInputs) (r .cachedDuration) (r .waitLeft - 1) _
    ⟨rfl, state.2.1,
      by simpa only [GenericPhase.holdTick, GenericEncoding.instruction, operation] using h.caches.duration,
      (congrArg (fun value : BitVec 8 => value - 1) state.2.2.2.1).trans
        (SpiRefinement.decrement8 waitLeft positive), state.2.2.2.2⟩
  done

theorem Running.checked_countdown {p : Program.Buffered.Program} {layout : GenericCertificate.Layout p}
    {payload : BitVec 32} {r : Values Reactive.Register} {s : Program.Buffered.State}
    {e : Transfer.Execution} {instruction : Program.Buffered.Instruction} {pc : Program.Buffered.PC}
    (h : Running p layout payload r s e instruction pc)
    (remaining : Fin 256) (action : Engine.Reactive.Action 15) (guard : Engine.Reactive.Check)
    (terminal : Option (Engine.Reactive.Capture 15)) (finish : Program.Buffered.Finish)
    (normalized : Engine.Reactive.Finish 1023 15)
    (control : s.core.control = .checked pc remaining)
    (operation : instruction.operation = .checked action guard terminal finish)
    (normalization : finish.eval pc = some normalized)
    (ready : guard.ready s.samplerSecond = true) (positive : 0 < remaining.val)
    (i : Values Reactive.Input) (quiet : SpiCircuit.Quiet i) :
    Running p layout payload (Reactive.circuit.step i r)
      (Program.Buffered.advance p capacity s (i .rawInputs)) e instruction pc := by
  have state : Control r instruction pc (.checked pc remaining) := control ▸ h.control
  have cache : r .cachedCheck = guard.value ++ guard.mask := by
    simpa only [GenericEncoding.instruction, operation] using h.caches.check
  have readyBit : Reactive.checkedReady.eval i r = 1 := by
    simpa only [← h.second, ready, BitVec.ofBool_true] using
      GenericPhase.checkedReady_matches i r guard cache
  rw [GenericPhase.checked_ready_step i r quiet state.2.1 readyBit
      (by simpa only [state.2.2.1] using nonzero8 remaining positive),
    GenericInterpreter.checked_countdown p capacity s pc remaining instruction action guard
      terminal finish normalized h.owned control h.fetch operation normalization ready positive]
  exact h.holdTick (i .rawInputs) (r .remaining - 1) (r .waitLeft) _
    ⟨rfl, state.2.1, (congrArg (fun value : BitVec 8 => value - 1) state.2.2.1).trans
      (SpiRefinement.decrement8 remaining positive), state.2.2.2⟩
  done

theorem Running.active_countdown {p : Program.Buffered.Program} {layout : GenericCertificate.Layout p}
    {payload : BitVec 32} {r : Values Reactive.Register} {s : Program.Buffered.State}
    {e : Transfer.Execution} {instruction : Program.Buffered.Instruction} {pc : Program.Buffered.PC}
    (h : Running p layout payload r s e instruction pc) (remaining : Fin 256)
    (control : s.core.control = .active pc remaining) (positive : 0 < remaining.val)
    (i : Values Reactive.Input) (quiet : SpiCircuit.Quiet i) :
    Running p layout payload (Reactive.circuit.step i r)
      (Program.Buffered.advance p capacity s (i .rawInputs)) e instruction pc := by
  have state : Control r instruction pc (.active pc remaining) := control ▸ h.control
  have flags := SpiCircuit.countdown_controls i r quiet state.2.1
    (by simpa [state.2.2.1] using nonzero8 remaining positive)
  have actual : @Circuit.step Reactive.Input Reactive.Register Reactive.Output Reactive.circuit i r =
      @GenericPhase.holdTick r (i .rawInputs) (r .remaining - 1) (r .waitLeft) := by
    simpa [state.2.1] using GenericPhase.holding_step i r quiet flags.1 flags.2.1
      flags.2.2.1 flags.2.2.2.2.2
  rw [actual, SpiInterpreter.advance_countdown p capacity s pc remaining h.owned control positive]
  exact h.holdTick (i .rawInputs) (r .remaining - 1) (r .waitLeft) _
    ⟨rfl, state.2.1, (congrArg (fun value : BitVec 8 => value - 1) state.2.2.1).trans
      (SpiRefinement.decrement8 remaining positive), state.2.2.2⟩
  done

end Pinwheel.Hardware.Buffered.Refinement
