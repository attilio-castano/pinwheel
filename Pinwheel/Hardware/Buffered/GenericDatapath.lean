import Pinwheel.Hardware.Buffered.GenericRelation
import Pinwheel.Hardware.Buffered.GenericPhaseEntryStop
import Pinwheel.Hardware.Buffered.SpiDatapath

/-! The packed entry data update, including simultaneous consume and append.
No instruction kind or protocol configuration is fixed by this lemma. -/
namespace Pinwheel.Hardware.Buffered.Refinement
open Pinwheel.Hardware Pinwheel.Program

def entryExecution (e : Transfer.Execution) (consume receive : Bool) (sample : Bool) :
    Transfer.Execution :=
  {e with
    txConsumed := if consume then e.txConsumed + 1 else e.txConsumed
    rx := if receive then e.rx ++ [sample] else e.rx}

theorem Datapath.runEntryTick {payload : BitVec 32} {r : Values Reactive.Register}
    {e : Transfer.Execution} (h : Datapath payload r e) (i : Values Reactive.Input)
    (quiet : SpiCircuit.Quiet i) (consume receive : Bool)
    (consuming : Reactive.consuming.eval i r = BitVec.ofBool consume)
    (appending : Reactive.appending.eval i r = BitVec.ofBool receive)
    (available : consume = true → e.txConsumed < e.request.tx.length)
    (room : receive = true → e.rx.length < e.request.rxLimit) :
    Datapath payload (GenericPhase.runEntryTick i r)
      (entryExecution e consume receive ((Reactive.sampled.eval i r).getLsbD 0)) := by
  have starting := (SpiCircuit.quiet_controls i r quiet).2.2.1
  refine ⟨?_, h.tx, ?_, ?_, ?_, ?_, ?_, ?_, h.generation, ?_⟩
  · refine ⟨h.bounded.1, ?_, ?_⟩
    · cases consume <;> simp_all only [entryExecution, Bool.false_eq_true, ↓reduceIte]
      · exact h.bounded.2.1
      · have bound := available True.intro
        omega
    · cases receive <;> simp only [entryExecution, Bool.false_eq_true, ↓reduceIte,
        List.length_append, List.length_singleton]
      · exact h.bounded.2.2
      · have bound := room rfl
        omega
  · simpa [GenericPhase.runEntryTick, entryExecution, Reactive.entryTxLength,
      Expr.eval, starting] using h.txLength
  · simpa [GenericPhase.runEntryTick, entryExecution, Reactive.entryCapacity,
      Expr.eval, starting] using h.rxCapacity
  · cases consume <;> simp only [GenericPhase.runEntryTick, entryExecution,
      Reactive.entryConsumed, Expr.eval, starting, consuming, BitVec.ofBool_false,
      BitVec.ofBool_true, Bool.false_eq_true, ↓reduceIte,
      show (0 : BitVec 1) ≠ 1 from by decide]
    · exact h.consumed
    · have bound := available rfl
      have cap : e.request.tx.length ≤ 32 := h.bounded.1.1
      rw [SpiDatapath.increment6 _ (by rw [h.consumed]; omega), h.consumed]
  · cases consume <;> simp only [GenericPhase.runEntryTick, entryExecution,
      Reactive.entryTx, Expr.eval, starting, consuming, BitVec.ofBool_false,
      BitVec.ofBool_true, Bool.false_eq_true, ↓reduceIte,
      show (0 : BitVec 1) ≠ 1 from by decide]
    · exact h.shifted
    · rw [SpiDatapath.shift_one, h.shifted, SpiDatapath.shift_succ]
  · cases receive <;> simp only [GenericPhase.runEntryTick, entryExecution,
      Reactive.entryRxLength, Expr.eval, starting, appending, BitVec.ofBool_false,
      BitVec.ofBool_true, Bool.false_eq_true, ↓reduceIte,
      show (0 : BitVec 1) ≠ 1 from by decide, List.length_append, List.length_singleton]
    · exact h.rxLength
    · have bound := room rfl
      have cap : e.request.rxLimit ≤ 32 := h.bounded.1.2
      rw [SpiDatapath.increment6 _ (by rw [h.rxLength]; omega), h.rxLength]
  · cases receive <;> simp only [GenericPhase.runEntryTick, entryExecution,
      starting, appending, BitVec.ofBool_false, BitVec.ofBool_true,
      Bool.false_eq_true, ↓reduceIte, show (0 : BitVec 1) ≠ 1 from by decide]
    · exact h.received
    · apply SpiDatapath.appended_prefix i r e.rx starting
      · simpa [Reactive.entryRxLength, Expr.eval, starting] using h.rxLength
      · exact h.received
  · simpa [GenericPhase.runEntryTick, entryExecution, starting] using h.transfer
  done

theorem Datapath.entryStopTick {payload : BitVec 32} {r : Values Reactive.Register}
    {e : Transfer.Execution} (h : Datapath payload r e) (i : Values Reactive.Input)
    (quiet : SpiCircuit.Quiet i) (consume receive : Bool)
    (consuming : Reactive.consuming.eval i r = BitVec.ofBool consume)
    (appending : Reactive.appending.eval i r = BitVec.ofBool receive)
    (available : consume = true → e.txConsumed < e.request.tx.length)
    (room : receive = true → e.rx.length < e.request.rxLimit) :
    Datapath payload (GenericPhase.entryStopTick i r)
      (entryExecution e consume receive ((Reactive.sampled.eval i r).getLsbD 0)) := by
  have updated := h.runEntryTick i quiet consume receive consuming appending available room
  exact ⟨updated.bounded, updated.tx, updated.txLength, updated.rxCapacity,
    updated.consumed, updated.shifted, updated.rxLength, updated.received,
    updated.generation, updated.transfer⟩

end Pinwheel.Hardware.Buffered.Refinement
