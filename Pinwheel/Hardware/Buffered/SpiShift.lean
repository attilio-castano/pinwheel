import Pinwheel.Hardware.Buffered.SpiDispatch

/-! SHIFT dispatch preserves the explicit SPI relation, including TX underflow.
-/
namespace Pinwheel.Hardware.Buffered.SpiRefinement
open Pinwheel.Hardware Pinwheel.Program

theorem Running.low_step {c : SpiSource.Config} {payload : BitVec 32}
    {r : Values Reactive.Register} {s : Program.Buffered.State}
    {e : Transfer.Execution} {pc : Program.Buffered.PC}
    (h : Running c payload r s e pc 0) (i : Values Reactive.Input) (quiet : SpiCircuit.Quiet i)
    (physical : SpiCoordinates.physicalPC c h.nextPC.val = 0) :
    Related c payload (Reactive.circuit.step i r)
      (Program.Buffered.advance (BufferedSPI.program c) capacity s (i .rawInputs)) := by
  have word : Reactive.entryWord.eval i r = SpiSource.word c 0 :=
    h.wordLeaf i quiet 0 physical
  rcases SpiWord.fields c 0 i r word with ⟨kind, capture, terminal, duration, enabled, append⟩
  have kind1 : Reactive.kind.eval i r = 1#3 := by
    simpa [SpiWord.expectedKind] using kind
  have wants : Reactive.wantsRx.eval i r = 0 := by
    simp [Reactive.wantsRx, Expr.eval, append]
  have pre := h.preEntry i quiet
  have controls := SpiCircuit.quiet_controls i r quiet
  have starting := controls.2.2.1
  have executing : SramExecution.ExecutingInput i := by
    simp [SramExecution.ExecutingInput, SharedBranches.Runtime, quiet.1, quiet.2]
  have releasing := controls.2.2.2.2.2
  have terminalEdge : Reactive.terminalEdge.eval i r = 0 := by
    simp [Reactive.terminalEdge, Reactive.isPhase, Reactive.both, Expr.eval, h.coordinates.phase]
  have scratch := SpiScratch.entryScratch_zero i r capture terminalEdge h.common.scratch
  have fetch : (BufferedSPI.program c).fetch h.nextPC =
      some (BufferedSPI.low c.halfCyclesMinusOne) :=
    h.fetchLeaf 0 physical
  have counts : (Reactive.entryConsumed.eval i r).toNat = e.txConsumed ∧
      (Reactive.entryTxLength.eval i r).toNat = e.request.tx.length := by
    simp [Reactive.entryConsumed, Reactive.entryTxLength, Expr.eval, starting,
      h.common.data.consumed, h.common.data.txLength]
  have tx : Reactive.entryTx.eval i r = payload >>> e.txConsumed := by
    simpa [Reactive.entryTx, Expr.eval, starting] using h.common.data.shifted
  by_cases available : e.txConsumed < e.request.tx.length
  · have flags := SpiEntryControls.low_available i r pre kind1 wants
      (by rw [counts.1, counts.2]; exact available)
    have actual := SpiCircuit.run_entry_step i r executing releasing pre.entering
      flags.stopping flags.running (Or.inr (Or.inl kind1))
    have lookup : e.request.tx[e.txConsumed]? =
        some ((Reactive.entryTx.eval i r).getLsbD 0) := by
      calc
        e.request.tx[e.txConsumed]? =
            (SpiPacking.txBits payload e.request.tx.length)[e.txConsumed]? :=
          congrArg (fun bits : List Bool => bits[e.txConsumed]?) h.common.data.tx
        _ = some (payload.getLsbD e.txConsumed) := by
          rw [SpiPacking.txBits_getElem?, if_pos available]
        _ = some ((Reactive.entryTx.eval i r).getLsbD 0) := by
          rw [tx]
          simp
    rw [actual, SpiInterpreter.advance_low_available _ _ s e pc h.nextPC
      c.halfCyclesMinusOne (i .rawInputs) ((Reactive.entryTx.eval i r).getLsbD 0)
      h.control h.before_last rfl fetch h.slot h.common.owner lookup]
    have within : h.nextPC.val ≤ SpiCoordinates.bitSpan c := by
      by_cases inside : h.nextPC.val < SpiCoordinates.bitSpan c
      · omega
      · simp [SpiCoordinates.physicalPC, inside] at physical
    refine Or.inl ⟨{e with txConsumed := e.txConsumed + 1}, h.nextPC, c.halfCyclesMinusOne, ?_⟩
    refine ⟨h.common.runEntryTick i {e with txConsumed := e.txConsumed + 1}
      (.active h.nextPC c.halfCyclesMinusOne)
      (Program.Buffered.shiftPins ⟨0, 7⟩ 0 false false ((Reactive.entryTx.eval i r).getLsbD 0))
      {s.buffers with slot := .running {e with txConsumed := e.txConsumed + 1}}
      (h.common.data.runEntryTick_low i quiet flags.consuming flags.appending available)
      h.common.owner (SpiPins.low_entry_pins c i r word).symm scratch,
      rfl, rfl, within, h.nextFrame i quiet, ?_, h.retained, rfl, h.first⟩
    simpa [SpiCircuit.runEntryTick] using duration
    done
  · have flags := SpiEntryControls.low_exhausted i r pre kind1 wants
      (by rw [counts.1, counts.2]; exact available)
    have actual := SpiCircuit.stop_entry_step i r executing releasing pre.entering
      flags.stopping flags.noTimeout
    have lookup : e.request.tx[e.txConsumed]? = none := by
      calc
        e.request.tx[e.txConsumed]? =
            (SpiPacking.txBits payload e.request.tx.length)[e.txConsumed]? :=
          congrArg (fun bits : List Bool => bits[e.txConsumed]?) h.common.data.tx
        _ = none := by rw [SpiPacking.txBits_getElem?, if_neg available]
    rw [actual, SpiInterpreter.advance_low_exhausted _ _ s e pc h.nextPC
      c.halfCyclesMinusOne (i .rawInputs) h.control h.before_last rfl fetch
      h.slot h.common.owner lookup]
    refine Or.inr ⟨e, false, ?_⟩
    refine ⟨h.common.stopEntryTick i e false
      {s.buffers with slot := .completed ⟨e, .fault⟩}
      (h.common.data.stopEntryTick_unchanged i quiet flags.consuming flags.appending)
      h.common.owner scratch, rfl, rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    simp [SpiCircuit.stopEntryTick, flags.complete]
    done
  done

end Pinwheel.Hardware.Buffered.SpiRefinement
