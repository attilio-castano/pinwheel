import Pinwheel.Hardware.Buffered.SpiDispatch

/-! RX append and RX-full fault preservation at actual SPI KEEP dispatches. -/
namespace Pinwheel.Hardware.Buffered.SpiRefinement
open Pinwheel.Hardware Pinwheel.Program

theorem Running.high_full_step {c : SpiSource.Config} {payload : BitVec 32}
    {r : Values Reactive.Register} {s : Program.Buffered.State}
    {e : Transfer.Execution} {pc : Program.Buffered.PC}
    (h : Running c payload r s e pc 0) (i : Values Reactive.Input) (quiet : SpiCircuit.Quiet i)
    (physical : SpiCoordinates.physicalPC c h.nextPC.val = 1)
    (full : ¬ e.rx.length < e.request.rxLimit) :
    Stopped c payload (Reactive.circuit.step i r)
      (Program.Buffered.advance (BufferedSPI.program c) capacity s (i .rawInputs)) e false := by
  have word : Reactive.entryWord.eval i r = SpiSource.word c 1 := h.wordLeaf i quiet 1 physical
  rcases SpiWord.fields c 1 i r word with ⟨kind, capture, terminal, duration, enabled, append⟩
  have kind2 : Reactive.kind.eval i r = 2#3 := by simpa [SpiWord.expectedKind] using kind
  have wants : Reactive.wantsRx.eval i r = 1 := by simp [Reactive.wantsRx, Expr.eval, append]
  have starting := (SpiCircuit.quiet_controls i r quiet).2.2.1
  have noRoom : ¬(Reactive.entryRxLength.eval i r).toNat < (Reactive.entryCapacity.eval i r).toNat := by
    simpa [Reactive.entryRxLength, Reactive.entryCapacity, Expr.eval, starting,
      h.common.data.rxLength, h.common.data.rxCapacity] using full
  have pre := h.preEntry i quiet
  have flags := SpiEntryControls.high_full i r pre kind2 wants noRoom
  have executing : SramExecution.ExecutingInput i := by
    simp [SramExecution.ExecutingInput, SharedBranches.Runtime, quiet.1, quiet.2]
  have releasing := (SpiCircuit.quiet_controls i r quiet).2.2.2.2.2
  have actual := SpiCircuit.stop_entry_step i r executing releasing pre.entering
    flags.stopping flags.noTimeout
  have fetch : (BufferedSPI.program c).fetch h.nextPC = some (BufferedSPI.high c.halfCyclesMinusOne) :=
    h.fetchLeaf 1 physical
  rw [actual, SpiInterpreter.advance_high_full _ _ s e pc h.nextPC c.halfCyclesMinusOne
    (i .rawInputs) h.control h.before_last rfl fetch h.slot h.common.owner full]
  have noTerminal : Reactive.terminalEdge.eval i r = 0 := by
    simp [Reactive.terminalEdge, Reactive.isPhase, Reactive.both, Expr.eval, h.coordinates.phase]
  have scratch := SpiScratch.entryScratch_zero i r capture noTerminal h.common.scratch
  have data := h.common.data.stopEntryTick_unchanged i quiet flags.consuming flags.appending
  refine ⟨h.common.stopEntryTick i e false _ data h.common.owner scratch,
    rfl, rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  simp [SpiCircuit.stopEntryTick, flags.complete]
  done

theorem Running.high_room_step {c : SpiSource.Config} {payload : BitVec 32}
    {r : Values Reactive.Register} {s : Program.Buffered.State}
    {e : Transfer.Execution} {pc : Program.Buffered.PC}
    (h : Running c payload r s e pc 0) (i : Values Reactive.Input) (quiet : SpiCircuit.Quiet i)
    (physical : SpiCoordinates.physicalPC c h.nextPC.val = 1)
    (room : e.rx.length < e.request.rxLimit) :
    Running c payload (Reactive.circuit.step i r)
      (Program.Buffered.advance (BufferedSPI.program c) capacity s (i .rawInputs))
      {e with rx := e.rx ++ [(r .stage2).getLsbD 0]} h.nextPC c.halfCyclesMinusOne := by
  have word : Reactive.entryWord.eval i r = SpiSource.word c 1 := h.wordLeaf i quiet 1 physical
  rcases SpiWord.fields c 1 i r word with ⟨kind, capture, terminal, duration, enabled, append⟩
  have kind2 : Reactive.kind.eval i r = 2#3 := by simpa [SpiWord.expectedKind] using kind
  have wants : Reactive.wantsRx.eval i r = 1 := by simp [Reactive.wantsRx, Expr.eval, append]
  have starting := (SpiCircuit.quiet_controls i r quiet).2.2.1
  have hasRoom : (Reactive.entryRxLength.eval i r).toNat < (Reactive.entryCapacity.eval i r).toNat := by
    simpa [Reactive.entryRxLength, Reactive.entryCapacity, Expr.eval, starting,
      h.common.data.rxLength, h.common.data.rxCapacity] using room
  have pre := h.preEntry i quiet
  have flags := SpiEntryControls.high_room i r pre kind2 wants hasRoom
  have executing : SramExecution.ExecutingInput i := by
    simp [SramExecution.ExecutingInput, SharedBranches.Runtime, quiet.1, quiet.2]
  have releasing := (SpiCircuit.quiet_controls i r quiet).2.2.2.2.2
  have actual := SpiCircuit.run_entry_step i r executing releasing pre.entering
    flags.stopping flags.running (Or.inr (Or.inr kind2))
  have fetch : (BufferedSPI.program c).fetch h.nextPC = some (BufferedSPI.high c.halfCyclesMinusOne) :=
    h.fetchLeaf 1 physical
  have sampled : s.samplerSecond[0] = (r .stage2).getLsbD 0 := by simp [h.second]
  rw [actual, SpiInterpreter.advance_high_room _ _ s e pc h.nextPC c.halfCyclesMinusOne
    (i .rawInputs) h.control h.before_last rfl fetch h.slot h.common.owner room, sampled]
  have inside : h.nextPC.val < SpiCoordinates.bitSpan c := by
    simp only [SpiCoordinates.physicalPC] at physical
    split at physical <;> omega
    done
  have pins : Program.Buffered.keepPins ⟨2, 7⟩ s.core.pins 1 0 =
      ⟨Reactive.entryLevels.eval i r, Reactive.entryEnabled.eval i r⟩ := by
    rw [h.common.pins]
    exact (SpiPins.high_entry_pins c i r word).symm
    done
  have noTerminal : Reactive.terminalEdge.eval i r = 0 := by
    simp [Reactive.terminalEdge, Reactive.isPhase, Reactive.both, Expr.eval, h.coordinates.phase]
  have scratch := SpiScratch.entryScratch_zero i r capture noTerminal h.common.scratch
  have data := h.common.data.runEntryTick_high i quiet word flags.consuming flags.appending room
  refine ⟨h.common.runEntryTick i _ (.active h.nextPC c.halfCyclesMinusOne)
      (Program.Buffered.keepPins ⟨2, 7⟩ s.core.pins 1 0) _ data h.common.owner pins scratch,
    rfl, rfl, Nat.le_of_lt inside, h.nextFrame i quiet, ?_, h.retained, rfl, h.first⟩
  simpa [SpiCircuit.runEntryTick] using duration
  done

theorem Running.high_step {c : SpiSource.Config} {payload : BitVec 32}
    {r : Values Reactive.Register} {s : Program.Buffered.State}
    {e : Transfer.Execution} {pc : Program.Buffered.PC}
    (h : Running c payload r s e pc 0) (i : Values Reactive.Input) (quiet : SpiCircuit.Quiet i)
    (physical : SpiCoordinates.physicalPC c h.nextPC.val = 1) :
    Related c payload (Reactive.circuit.step i r)
      (Program.Buffered.advance (BufferedSPI.program c) capacity s (i .rawInputs)) := by
  by_cases room : e.rx.length < e.request.rxLimit
  · exact Or.inl ⟨_, _, _, h.high_room_step i quiet physical room⟩
  · exact Or.inr ⟨e, false, h.high_full_step i quiet physical room⟩

end Pinwheel.Hardware.Buffered.SpiRefinement
