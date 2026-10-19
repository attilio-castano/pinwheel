import Pinwheel.Hardware.Buffered.GenericDispatchAdmission

/-! Checked source dispatches establish the actual entry location and admission
flags before the selected image word is fetched. -/
namespace Pinwheel.Hardware.Buffered.Refinement
open Pinwheel.Hardware Pinwheel.Program

theorem Running.jump_entryAt {p : Program.Buffered.Program} {layout : GenericCertificate.Layout p}
    {payload : BitVec 32} {r : Values Reactive.Register} {s : Program.Buffered.State}
    {e : Transfer.Execution} {instruction : Program.Buffered.Instruction} {pc : Program.Buffered.PC}
    (h : Running p layout payload r s e instruction pc) (i : Values Reactive.Input)
    (quiet : SpiCircuit.Quiet i) (action : Engine.Reactive.Action 15) (guard : Engine.Reactive.Check)
    (terminal : Option (Engine.Reactive.Capture 15)) (target : Program.Buffered.PC)
    (control : s.core.control = .checked pc 0)
    (operation : instruction.operation = .checked action guard terminal (.jump target))
    (ready : guard.ready s.samplerSecond = true) :
    GenericPhase.Dispatching i r true ∧ EntryAt layout.map i r target := by
  have flags := h.checked_dispatching i quiet action guard terminal (.jump target) control operation ready
  have coordinates := h.jump_coordinates i quiet action guard terminal target operation
    (by simpa only [BitVec.ofBool_true] using flags.terminal)
  exact ⟨flags, entryAt_of_fields layout.map i r target flags.entering coordinates.2⟩
  done

theorem Running.branch_absolute_entryAt {p : Program.Buffered.Program}
    {layout : GenericCertificate.Layout p} {payload : BitVec 32}
    {r : Values Reactive.Register} {s : Program.Buffered.State} {e : Transfer.Execution}
    {instruction : Program.Buffered.Instruction} {pc : Program.Buffered.PC}
    (h : Running p layout payload r s e instruction pc) (i : Values Reactive.Input)
    (quiet : SpiCircuit.Quiet i) (action : Engine.Reactive.Action 15) (guard : Engine.Reactive.Check)
    (terminal : Option (Engine.Reactive.Capture 15)) (sample : Fin 16)
    (yes no : Program.Buffered.Target) (target : Program.Buffered.PC)
    (control : s.core.control = .checked pc 0)
    (operation : instruction.operation = .checked action guard terminal (.branch sample yes no))
    (ready : guard.ready s.samplerSecond = true)
    (selected : (if (Engine.Reactive.capture s.core.samples terminal s.samplerSecond)[sample.val]
      then yes else no) = .absolute target) :
    GenericPhase.Dispatching i r true ∧ EntryAt layout.map i r target := by
  have flags := h.checked_dispatching i quiet action guard terminal (.branch sample yes no) control operation ready
  have coordinates := h.branch_absolute_coordinates i quiet action guard terminal sample yes no target operation
    (by simpa only [BitVec.ofBool_true] using flags.terminal) selected
  exact ⟨flags, entryAt_of_fields layout.map i r target flags.entering coordinates.2⟩
  done

theorem Running.branch_next_entryAt {p : Program.Buffered.Program}
    {layout : GenericCertificate.Layout p} {payload : BitVec 32}
    {r : Values Reactive.Register} {s : Program.Buffered.State} {e : Transfer.Execution}
    {instruction : Program.Buffered.Instruction} {pc : Program.Buffered.PC}
    (h : Running p layout payload r s e instruction pc) (i : Values Reactive.Input)
    (quiet : SpiCircuit.Quiet i) (action : Engine.Reactive.Action 15) (guard : Engine.Reactive.Check)
    (terminal : Option (Engine.Reactive.Capture 15)) (sample : Fin 16)
    (yes no : Program.Buffered.Target)
    (control : s.core.control = .checked pc 0)
    (operation : instruction.operation = .checked action guard terminal (.branch sample yes no))
    (ready : guard.ready s.samplerSecond = true)
    (selected : (if (Engine.Reactive.capture s.core.samples terminal s.samplerSecond)[sample.val]
      then yes else no) = .next) (within : pc.val + 1 < p.code.span) :
    GenericPhase.Dispatching i r true ∧
      EntryAt layout.map i r ⟨pc.val + 1, by have := p.fits; omega⟩ := by
  have flags := h.checked_dispatching i quiet action guard terminal (.branch sample yes no) control operation ready
  have next := h.branch_next_virtual i quiet action guard terminal sample yes no operation
    (by simpa only [BitVec.ofBool_true] using flags.terminal) selected
  have coordinates := h.sequential_coordinates i quiet next.1 within
  exact ⟨flags, ⟨flags.entering, coordinates.1, coordinates.2⟩⟩
  done

end Pinwheel.Hardware.Buffered.Refinement
