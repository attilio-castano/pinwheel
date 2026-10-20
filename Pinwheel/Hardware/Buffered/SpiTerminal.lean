import Pinwheel.Hardware.Buffered.SpiDispatch

/-! Release and HALT dispatch preserve the source/packed-circuit relation. -/
namespace Pinwheel.Hardware.Buffered.SpiRefinement
open Pinwheel.Hardware Pinwheel.Program

theorem Running.release_step {c : SpiSource.Config} {payload : BitVec 32}
    {r : Values Reactive.Register} {s : Program.Buffered.State}
    {e : Transfer.Execution} {pc : Program.Buffered.PC}
    (h : Running c payload r s e pc 0) (i : Values Reactive.Input) (quiet : SpiCircuit.Quiet i)
    (physical : SpiCoordinates.physicalPC c h.nextPC.val = 2) :
    Running c payload (Reactive.circuit.step i r)
      (Program.Buffered.advance (BufferedSPI.program c) capacity s (i .rawInputs))
      e h.nextPC c.halfCyclesMinusOne := by
  have word : Reactive.entryWord.eval i r = SpiSource.word c 2 :=
    h.wordLeaf i quiet 2 physical
  rcases SpiWord.fields c 2 i r word with ⟨kind, capture, terminal, duration, enabled, append⟩
  have kind0 : Reactive.kind.eval i r = 0#3 := by
    simpa [SpiWord.expectedKind] using kind
  have wants : Reactive.wantsRx.eval i r = 0 := by
    simp [Reactive.wantsRx, Expr.eval, append]
  have pre := h.preEntry i quiet
  have flags := SpiEntryControls.release i r pre kind0 wants
  have executing : SramExecution.ExecutingInput i := by
    simp [SramExecution.ExecutingInput, SharedBranches.Runtime, quiet.1, quiet.2]
  have releasing := (SpiCircuit.quiet_controls i r quiet).2.2.2.2.2
  have actual := SpiCircuit.run_entry_step i r executing releasing pre.entering
    flags.stopping flags.running (Or.inl kind0)
  have fetch : (BufferedSPI.program c).fetch h.nextPC =
      some (BufferedSPI.release c.halfCyclesMinusOne) :=
    h.fetchLeaf 2 physical
  rw [actual, SpiInterpreter.advance_release _ _ s pc h.nextPC c.halfCyclesMinusOne
    (i .rawInputs) h.owned h.control h.before_last rfl fetch]
  have terminalEdge : Reactive.terminalEdge.eval i r = 0 := by
    simp [Reactive.terminalEdge, Reactive.isPhase, Reactive.both, Expr.eval, h.coordinates.phase]
  have scratch := SpiScratch.entryScratch_zero i r capture terminalEdge h.common.scratch
  have within : h.nextPC.val ≤ SpiCoordinates.bitSpan c := by
    by_cases inside : h.nextPC.val < SpiCoordinates.bitSpan c
    · omega
    · have outside : h.nextPC.val - SpiCoordinates.bitSpan c + 2 = 2 := by
        simpa [SpiCoordinates.physicalPC, inside] using physical
      omega
  refine ⟨h.common.runEntryTick i e (.active h.nextPC c.halfCyclesMinusOne) ⟨0, 7⟩ s.buffers
    (h.common.data.runEntryTick_unchanged i quiet flags.consuming flags.appending)
    h.common.owner (SpiPins.release_entry_pins c i r word).symm scratch,
    h.slot, rfl, within, h.nextFrame i quiet, ?_, h.retained, rfl, h.first⟩
  simpa [SpiCircuit.runEntryTick] using duration
  done

theorem Running.halt_step {c : SpiSource.Config} {payload : BitVec 32}
    {r : Values Reactive.Register} {s : Program.Buffered.State}
    {e : Transfer.Execution} {pc : Program.Buffered.PC}
    (h : Running c payload r s e pc 0) (i : Values Reactive.Input) (quiet : SpiCircuit.Quiet i)
    (physical : SpiCoordinates.physicalPC c h.nextPC.val = 3) :
    Stopped c payload (Reactive.circuit.step i r)
      (Program.Buffered.advance (BufferedSPI.program c) capacity s (i .rawInputs)) e true := by
  have word : Reactive.entryWord.eval i r = SpiSource.word c 3 :=
    h.wordLeaf i quiet 3 physical
  have fields := SpiWord.fields c 3 i r word
  have kind3 : Reactive.kind.eval i r = 3#3 := by
    simpa [SpiWord.expectedKind] using fields.1
  have pre := h.preEntry i quiet
  have flags := SpiEntryControls.halt i r pre kind3
  have executing : SramExecution.ExecutingInput i := by
    simp [SramExecution.ExecutingInput, SharedBranches.Runtime, quiet.1, quiet.2]
  have releasing := (SpiCircuit.quiet_controls i r quiet).2.2.2.2.2
  have actual := SpiCircuit.stop_entry_step i r executing releasing pre.entering
    flags.stopping flags.noTimeout
  have fetch : (BufferedSPI.program c).fetch h.nextPC = some BufferedSPI.halt :=
    h.fetchLeaf 3 physical
  rw [actual, SpiInterpreter.advance_halt _ _ s e pc h.nextPC (i .rawInputs)
    h.control h.before_last rfl fetch h.slot h.common.owner]
  have terminalEdge : Reactive.terminalEdge.eval i r = 0 := by
    simp [Reactive.terminalEdge, Reactive.isPhase, Reactive.both, Expr.eval, h.coordinates.phase]
  have scratch := SpiScratch.entryScratch_zero i r fields.2.1 terminalEdge h.common.scratch
  refine ⟨h.common.stopEntryTick i e true
    {s.buffers with slot := .completed ⟨e, .complete⟩}
    (h.common.data.stopEntryTick_unchanged i quiet flags.consuming flags.appending)
    h.common.owner scratch, rfl, rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  simp [SpiCircuit.stopEntryTick, flags.complete]
  done

end Pinwheel.Hardware.Buffered.SpiRefinement
