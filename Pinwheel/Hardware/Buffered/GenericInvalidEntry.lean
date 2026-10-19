import Pinwheel.Hardware.Buffered.GenericEntryTransfer

/-! A dispatch outside the certified virtual image faults without entry data
effects. The terminal capture, if any, is still retained in scratch. -/
namespace Pinwheel.Hardware.Buffered.Refinement
open Pinwheel.Hardware Pinwheel.Program

theorem illegal_virtual (i : Values Reactive.Input) (r : Values Reactive.Register)
    (outside : (r .virtualSpan).toNat ≤ (Reactive.entryVirtual.eval i r).toNat) :
    Reactive.legalEntry.eval i r = 0 := by
  simp [Reactive.legalEntry, Reactive.inBounds, Reactive.both, Expr.eval,
    show ¬ (Reactive.entryVirtual.eval i r).toNat < (r .virtualSpan).toNat by omega]

theorem invalid_entry {p : Program.Buffered.Program} {layout : GenericCertificate.Layout p}
    {payload : BitVec 32} {r : Values Reactive.Register} {s : Program.Buffered.State}
    {e : Transfer.Execution} (h : Common p layout payload r s e)
    (i : Values Reactive.Input) (quiet : SpiCircuit.Quiet i)
    (slot : s.buffers.slot = .running e) (slots : Vector Bool 16)
    (scratch : GenericPhase.Scratch (Reactive.exitScratch.eval i r) slots)
    (entering : Reactive.entering.eval i r = 1)
    (illegal : Reactive.legalEntry.eval i r = 0)
    (heldTimeout : Reactive.heldTimeout.eval i r = 0) :
    Stopped p layout payload (Reactive.circuit.step i r)
      (Program.Buffered.terminal p capacity {s with core := {s.core with samples := slots}} .fault)
      e .fault := by
  have controls := SpiCircuit.quiet_controls i r quiet
  have running : Reactive.runEntry.eval i r = 0 := by
    simp [Reactive.runEntry, Reactive.both, Expr.eval, illegal]
  have consuming : Reactive.consuming.eval i r = 0 := by
    simp [Reactive.consuming, Reactive.both, Expr.eval, running]
  have appending : Reactive.appending.eval i r = 0 := by
    simp [Reactive.appending, Reactive.both, Expr.eval, running]
  have complete : Reactive.entryComplete.eval i r = 0 := by
    simp [Reactive.entryComplete, Reactive.both, Expr.eval, illegal]
  have timeout : Reactive.entryTimeout.eval i r = 0 := by
    simp [Reactive.entryTimeout, Reactive.both, Expr.eval, illegal]
  have stopping : Reactive.stopping.eval i r = 1 := by
    simp [Reactive.stopping, Reactive.entryFailed, Reactive.both, Reactive.either,
      Expr.eval, controls.1, entering, illegal]
  have executing : SramExecution.ExecutingInput i := by
    simp [SramExecution.ExecutingInput, SharedBranches.Runtime, quiet.1, quiet.2]
  have actual := GenericPhase.entry_stop_step i r executing
    controls.2.2.2.2.2 entering stopping heldTimeout
  rw [actual]
  have data := h.data.entryStopTick i quiet false false consuming appending
    (by simp) (by simp)
  have terminal := SpiInterpreter.terminal_running p capacity
    {s with core := {s.core with samples := slots}} e .fault slot h.owner
  refine ⟨?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · refine ⟨h.count, h.span, h.idleLevels, h.idleEnabled, h.image, h.valid, data,
      h.owner, ?_, ?_⟩
    · change p.idle = ⟨r .idleLevels, r .idleEnabled⟩
      rw [h.idleLevels, h.idleEnabled]
    · change GenericPhase.Scratch ((GenericPhase.entryStopTick i r) .scratch) slots
      simpa only [GenericPhase.entryStopTick, GenericPhase.runEntryTick,
        Reactive.entryScratch, Expr.eval, running, controls.2.2.1,
        show (0 : BitVec 1) ≠ 1 from by decide, ↓reduceIte] using scratch
  · rw [terminal]
  · rw [terminal]
    rfl
  · simp [GenericPhase.entryStopTick, timeout, complete, stopPhase]

end Pinwheel.Hardware.Buffered.Refinement
