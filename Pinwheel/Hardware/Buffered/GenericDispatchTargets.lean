import Pinwheel.Hardware.Buffered.GenericDispatchCoordinates

/-! Public source-selected jump and branch coordinate consequences. -/
namespace Pinwheel.Hardware.Buffered.Refinement
open Pinwheel.Hardware Pinwheel.Program

theorem Running.jump_coordinates {p : Program.Buffered.Program} {layout : GenericCertificate.Layout p}
    {payload : BitVec 32} {r : Values Reactive.Register} {s : Program.Buffered.State}
    {e : Transfer.Execution} {instruction : Program.Buffered.Instruction} {pc : Program.Buffered.PC}
    (h : Running p layout payload r s e instruction pc) (i : Values Reactive.Input)
    (quiet : SpiCircuit.Quiet i) (action : Engine.Reactive.Action 15) (guard : Engine.Reactive.Check)
    (terminal : Option (Engine.Reactive.Capture 15)) (target : Program.Buffered.PC)
    (operation : instruction.operation = .checked action guard terminal (.jump target))
    (terminalEdge : Reactive.terminalEdge.eval i r = 1) :
    Reactive.absoluteDispatch.eval i r = 1 ∧
    Reactive.entryPC.eval i r = (layout.map target).row ∧
    Reactive.entryVirtual.eval i r = BitVec.ofNat 11 target.val ∧
    Reactive.entryOuter.eval i r = (layout.map target).outer ∧
    Reactive.entryInner.eval i r = (layout.map target).inner := by
  have endpoint := h.jump_endpoint i action guard terminal target operation
  have absolute := absolute_from_endpoint i r target (layout.map target) terminalEdge
    (by simp [(h.jump_fields i action guard terminal target operation).1]) endpoint
  exact ⟨absolute, absolute_coordinates i r target (layout.map target)
    (SpiCircuit.quiet_controls i r quiet).2.2.1 absolute endpoint⟩
  done

theorem Running.branch_absolute_coordinates {p : Program.Buffered.Program}
    {layout : GenericCertificate.Layout p} {payload : BitVec 32}
    {r : Values Reactive.Register} {s : Program.Buffered.State} {e : Transfer.Execution}
    {instruction : Program.Buffered.Instruction} {pc : Program.Buffered.PC}
    (h : Running p layout payload r s e instruction pc) (i : Values Reactive.Input)
    (quiet : SpiCircuit.Quiet i) (action : Engine.Reactive.Action 15) (guard : Engine.Reactive.Check)
    (terminal : Option (Engine.Reactive.Capture 15)) (sample : Fin 16)
    (yes no : Program.Buffered.Target) (target : Program.Buffered.PC)
    (operation : instruction.operation = .checked action guard terminal (.branch sample yes no))
    (terminalEdge : Reactive.terminalEdge.eval i r = 1)
    (selected : (if (Engine.Reactive.capture s.core.samples terminal s.samplerSecond)[sample.val]
      then yes else no) = .absolute target) :
    Reactive.absoluteDispatch.eval i r = 1 ∧
    Reactive.entryPC.eval i r = (layout.map target).row ∧
    Reactive.entryVirtual.eval i r = BitVec.ofNat 11 target.val ∧
    Reactive.entryOuter.eval i r = (layout.map target).outer ∧
    Reactive.entryInner.eval i r = (layout.map target).inner := by
  have endpoint : Reactive.endpoint.eval i r = GenericLayout.endpoint target (layout.map target) := by
    simpa only [selected, GenericLayout.target] using
      h.branch_endpoint i action guard terminal sample yes no operation terminalEdge
  have absolute := absolute_from_endpoint i r target (layout.map target) terminalEdge
    (by simp [(h.branch_fields i action guard terminal sample yes no operation).1]) endpoint
  exact ⟨absolute, absolute_coordinates i r target (layout.map target)
    (SpiCircuit.quiet_controls i r quiet).2.2.1 absolute endpoint⟩
  done

theorem Running.branch_next_virtual {p : Program.Buffered.Program}
    {layout : GenericCertificate.Layout p} {payload : BitVec 32}
    {r : Values Reactive.Register} {s : Program.Buffered.State} {e : Transfer.Execution}
    {instruction : Program.Buffered.Instruction} {pc : Program.Buffered.PC}
    (h : Running p layout payload r s e instruction pc) (i : Values Reactive.Input)
    (quiet : SpiCircuit.Quiet i) (action : Engine.Reactive.Action 15) (guard : Engine.Reactive.Check)
    (terminal : Option (Engine.Reactive.Capture 15)) (sample : Fin 16)
    (yes no : Program.Buffered.Target)
    (operation : instruction.operation = .checked action guard terminal (.branch sample yes no))
    (terminalEdge : Reactive.terminalEdge.eval i r = 1)
    (selected : (if (Engine.Reactive.capture s.core.samples terminal s.samplerSecond)[sample.val]
      then yes else no) = .next) :
    Reactive.absoluteDispatch.eval i r = 0 ∧
    Reactive.entryVirtual.eval i r = BitVec.ofNat 11 (pc.val + 1) := by
  have endpoint : Reactive.endpoint.eval i r = 1 := by
    simpa only [selected, GenericLayout.target] using
      h.branch_endpoint i action guard terminal sample yes no operation terminalEdge
  have notAbsolute := next_notAbsolute i r endpoint
  exact ⟨notAbsolute, sequential_virtual i r pc (SpiCircuit.quiet_controls i r quiet).2.2.1
    notAbsolute h.virtualPC⟩
  done

end Pinwheel.Hardware.Buffered.Refinement
