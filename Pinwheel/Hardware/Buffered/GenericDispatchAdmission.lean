import Pinwheel.Hardware.Buffered.GenericDispatchTargets
import Pinwheel.Hardware.Buffered.GenericPhaseDispatch
import Pinwheel.Hardware.Buffered.GenericEntryAt

namespace Pinwheel.Hardware.Buffered.Refinement
open Pinwheel.Hardware Pinwheel.Program

theorem Running.active_dispatching {p : Program.Buffered.Program} {layout : GenericCertificate.Layout p}
    {payload : BitVec 32} {r : Values Reactive.Register} {s : Program.Buffered.State}
    {e : Transfer.Execution} {instruction : Program.Buffered.Instruction} {pc : Program.Buffered.PC}
    (h : Running p layout payload r s e instruction pc) (i : Values Reactive.Input)
    (quiet : SpiCircuit.Quiet i) (control : s.core.control = .active pc 0) :
    GenericPhase.Dispatching i r false := by
  have state : Control r instruction pc (.active pc 0) := control ▸ h.control
  exact GenericPhase.active_dispatching i r quiet state.2.1 (by simp [state.2.2.1])
  done

theorem Running.wait_dispatching {p : Program.Buffered.Program} {layout : GenericCertificate.Layout p}
    {payload : BitVec 32} {r : Values Reactive.Register} {s : Program.Buffered.State}
    {e : Transfer.Execution} {instruction : Program.Buffered.Instruction} {pc : Program.Buffered.PC}
    (h : Running p layout payload r s e instruction pc) (i : Values Reactive.Input)
    (quiet : SpiCircuit.Quiet i) (remaining : Fin 256) (wait : Engine.Reactive.Wait)
    (control : s.core.control = .waiting pc remaining)
    (operation : instruction.operation = .wait wait)
    (ready : wait.condition.ready s.samplerSecond = true) :
    GenericPhase.Dispatching i r false := by
  have state : Control r instruction pc (.waiting pc remaining) := control ▸ h.control
  exact GenericPhase.wait_dispatching i r quiet state.2.1
    (by simpa only [ready, BitVec.ofBool_true] using h.waitReady i wait operation)
  done

theorem Running.checked_dispatching {p : Program.Buffered.Program} {layout : GenericCertificate.Layout p}
    {payload : BitVec 32} {r : Values Reactive.Register} {s : Program.Buffered.State}
    {e : Transfer.Execution} {instruction : Program.Buffered.Instruction} {pc : Program.Buffered.PC}
    (h : Running p layout payload r s e instruction pc) (i : Values Reactive.Input)
    (quiet : SpiCircuit.Quiet i) (action : Engine.Reactive.Action 15) (guard : Engine.Reactive.Check)
    (terminal : Option (Engine.Reactive.Capture 15)) (finish : Program.Buffered.Finish)
    (control : s.core.control = .checked pc 0)
    (operation : instruction.operation = .checked action guard terminal finish)
    (ready : guard.ready s.samplerSecond = true) : GenericPhase.Dispatching i r true := by
  have state : Control r instruction pc (.checked pc 0) := control ▸ h.control
  exact GenericPhase.checked_dispatching i r quiet state.2.1
    (by simpa only [ready, BitVec.ofBool_true] using h.checkedReady i action guard terminal finish operation)
    (by simp [state.2.2.1])
  done

theorem Running.qualify_dispatching {p : Program.Buffered.Program} {layout : GenericCertificate.Layout p}
    {payload : BitVec 32} {r : Values Reactive.Register} {s : Program.Buffered.State}
    {e : Transfer.Execution} {instruction : Program.Buffered.Instruction} {pc : Program.Buffered.PC}
    (h : Running p layout payload r s e instruction pc) (i : Values Reactive.Input)
    (quiet : SpiCircuit.Quiet i) (waitLeft : Fin 256) (qualify : Engine.Reactive.Qualify)
    (control : s.core.control = .qualifying pc 0 waitLeft)
    (operation : instruction.operation = .qualify qualify)
    (ready : qualify.condition.ready s.samplerSecond = true) : GenericPhase.Dispatching i r false := by
  have state : Control r instruction pc (.qualifying pc 0 waitLeft) := control ▸ h.control
  exact GenericPhase.qualify_dispatching i r quiet state.2.1
    (by simpa only [ready, BitVec.ofBool_true] using h.qualifyReady i qualify operation)
    (by simp [state.2.2.1])
  done

theorem Common.exitScratch {p : Program.Buffered.Program} {layout : GenericCertificate.Layout p}
    {payload : BitVec 32} {r : Values Reactive.Register} {s : Program.Buffered.State}
    {e : Transfer.Execution} (h : Common p layout payload r s e) (i : Values Reactive.Input)
    (terminal : Reactive.terminalEdge.eval i r = 0) :
    GenericPhase.Scratch (Reactive.exitScratch.eval i r) s.core.samples := by
  simpa [Reactive.exitScratch, Expr.eval, terminal] using h.scratch

theorem Running.checked_exitScratch {p : Program.Buffered.Program} {layout : GenericCertificate.Layout p}
    {payload : BitVec 32} {r : Values Reactive.Register} {s : Program.Buffered.State}
    {e : Transfer.Execution} {instruction : Program.Buffered.Instruction} {pc : Program.Buffered.PC}
    (h : Running p layout payload r s e instruction pc) (i : Values Reactive.Input)
    (action : Engine.Reactive.Action 15) (guard : Engine.Reactive.Check)
    (terminal : Option (Engine.Reactive.Capture 15)) (finish : Program.Buffered.Finish)
    (operation : instruction.operation = .checked action guard terminal finish)
    (terminalEdge : Reactive.terminalEdge.eval i r = 1) :
    GenericPhase.Scratch (Reactive.exitScratch.eval i r)
      (Engine.Reactive.capture s.core.samples terminal s.samplerSecond) := by
  have cache : r .cachedTerminal = GenericEncoding.capture terminal := by
    simpa only [GenericEncoding.instruction, operation] using h.caches.terminal
  simpa only [← h.second] using GenericPhase.exitScratch_matches i r s.core.samples terminal
    (cache ▸ GenericPhase.capture_fields terminal) h.common.scratch terminalEdge
  done

theorem entryAt_of_fields (map : Program.Buffered.PC → GenericLayout.Coordinates)
    (i : Values Reactive.Input) (r : Values Reactive.Register) (pc : Program.Buffered.PC)
    (entering : Reactive.entering.eval i r = 1)
    (fields : Reactive.entryPC.eval i r = (map pc).row ∧
      Reactive.entryVirtual.eval i r = BitVec.ofNat 11 pc.val ∧
      Reactive.entryOuter.eval i r = (map pc).outer ∧
      Reactive.entryInner.eval i r = (map pc).inner) : EntryAt map i r pc := by
  refine ⟨entering, ?_, fields.2.1⟩
  rw [fields.1, fields.2.2.1, fields.2.2.2]
  done

theorem Running.sequential_entryAt {p : Program.Buffered.Program} {layout : GenericCertificate.Layout p}
    {payload : BitVec 32} {r : Values Reactive.Register} {s : Program.Buffered.State}
    {e : Transfer.Execution} {instruction : Program.Buffered.Instruction} {pc : Program.Buffered.PC}
    (h : Running p layout payload r s e instruction pc) (i : Values Reactive.Input)
    (quiet : SpiCircuit.Quiet i) {capture : Bool} (dispatch : GenericPhase.Dispatching i r capture)
    (sequential : GenericLayout.instructionFinish layout.map instruction = 0)
    (within : pc.val + 1 < p.code.span) :
    EntryAt layout.map i r ⟨pc.val + 1, by have := p.fits; omega⟩ := by
  have next := h.sequential_coordinates i quiet (h.sequential_notAbsolute i sequential) within
  exact ⟨dispatch.entering, next.1, next.2⟩
  done

end Pinwheel.Hardware.Buffered.Refinement
