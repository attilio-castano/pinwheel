import Pinwheel.Hardware.Buffered.SpiRelation
import Pinwheel.Hardware.Buffered.SpiEntryControls

/-! Packed TX/RX updates of the actual SPI entry equations. -/
namespace Pinwheel.Hardware.Buffered.SpiDatapath
open Pinwheel.Hardware Pinwheel.Program

theorem shift_one (word : BitVec 32) : 0#1 ++ word.extractLsb' 1 31 = word >>> 1 := by
  apply (BitVec.eq_of_getLsbD_eq_iff).2
  intro index bound
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb',
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_zero]
  by_cases low : index < 31
  · simp [low, Nat.add_comm]
  · have hi : index = 31 := by omega
    simp [hi]
  done

theorem increment6 (value : BitVec 6) (bound : value.toNat < 32) :
    (value + 1).toNat = value.toNat + 1 := by
  simp [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega : value.toNat + 1 < 64)]

theorem appended_bit (i : Values Reactive.Input) (s : Values Reactive.Register)
    (index : Fin 32) :
    (Reactive.appended.eval i s).getLsbD index.val =
      if Reactive.entryRxLength.eval i s = BitVec.ofNat 6 index.val
      then (Reactive.sampled.eval i s).getLsbD 0
      else (if Reactive.starting.eval i s = 1 then 0 else s .rxData).getLsbD index.val := by
  unfold Reactive.appended
  rw [Reactive.pack_selected_bit 32 _ i s index]
  by_cases eq : Reactive.entryRxLength.eval i s = BitVec.ofNat 6 index.val
  all_goals simp [Expr.eval, eq]

theorem appended_prefix (i : Values Reactive.Input) (s : Values Reactive.Register)
    (bits : List Bool) (notStarting : Reactive.starting.eval i s = 0)
    (length : (Reactive.entryRxLength.eval i s).toNat = bits.length)
    (received : s .rxData = SpiPacking.rxWord bits) :
    Reactive.appended.eval i s =
      SpiPacking.rxWord (bits ++ [(Reactive.sampled.eval i s).getLsbD 0]) := by
  apply (BitVec.eq_of_getLsbD_eq_iff).2
  intro index bound
  rw [appended_bit i s ⟨index, bound⟩,
    SpiPacking.rxWord_append_getLsbD _ _ index bound]
  have condition : Reactive.entryRxLength.eval i s = BitVec.ofNat 6 index ↔
      index = bits.length := by
    constructor
    · intro eq
      have actual := congrArg BitVec.toNat eq
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : index < 2^6)] at actual
      omega
    · intro eq
      apply BitVec.eq_of_toNat_eq
      simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : index < 2^6)] using
        length.trans eq.symm
  simp [condition, notStarting, received]
  done

theorem shift_succ (payload : BitVec 32) (consumed : Nat) :
    (payload >>> consumed) >>> 1 = payload >>> (consumed + 1) := by
  apply (BitVec.eq_of_getLsbD_eq_iff).2
  intro index _
  simp only [BitVec.getLsbD_ushiftRight]
  congr 1 <;> omega

end Pinwheel.Hardware.Buffered.SpiDatapath

namespace Pinwheel.Hardware.Buffered.SpiRefinement
open Pinwheel.Hardware Pinwheel.Program

theorem Datapath.runEntryTick_unchanged {payload : BitVec 32} {r : Values Reactive.Register}
    {e : Transfer.Execution} (h : Datapath payload r e) (i : Values Reactive.Input)
    (quiet : SpiCircuit.Quiet i) (consuming : Reactive.consuming.eval i r = 0)
    (appending : Reactive.appending.eval i r = 0) :
    Datapath payload (SpiCircuit.runEntryTick i r) e := by
  have starting := (SpiCircuit.quiet_controls i r quiet).2.2.1
  refine ⟨h.bounded, h.tx, ?_, ?_, ?_, ?_, ?_, ?_, h.generation, ?_⟩
  · simpa [SpiCircuit.runEntryTick, Reactive.entryTxLength, Expr.eval, starting] using h.txLength
  · simpa [SpiCircuit.runEntryTick, Reactive.entryCapacity, Expr.eval, starting] using h.rxCapacity
  · simpa [SpiCircuit.runEntryTick, Reactive.entryConsumed, Expr.eval, starting, consuming] using h.consumed
  · simpa [SpiCircuit.runEntryTick, Reactive.entryTx, Expr.eval, starting, consuming] using h.shifted
  · simpa [SpiCircuit.runEntryTick, Reactive.entryRxLength, Expr.eval, starting, appending] using h.rxLength
  · simpa [SpiCircuit.runEntryTick, Expr.eval, starting, appending] using h.received
  · simpa [SpiCircuit.runEntryTick, starting] using h.transfer

theorem Datapath.stopEntryTick_unchanged {payload : BitVec 32} {r : Values Reactive.Register}
    {e : Transfer.Execution} (h : Datapath payload r e) (i : Values Reactive.Input)
    (quiet : SpiCircuit.Quiet i) (consuming : Reactive.consuming.eval i r = 0)
    (appending : Reactive.appending.eval i r = 0) :
    Datapath payload (SpiCircuit.stopEntryTick i r) e := by
  have updated := h.runEntryTick_unchanged i quiet consuming appending
  exact ⟨updated.bounded, updated.tx, updated.txLength, updated.rxCapacity,
    updated.consumed, updated.shifted, updated.rxLength, updated.received,
    updated.generation, updated.transfer⟩

theorem Datapath.runEntryTick_low {payload : BitVec 32} {r : Values Reactive.Register}
    {e : Transfer.Execution} (h : Datapath payload r e) (i : Values Reactive.Input)
    (quiet : SpiCircuit.Quiet i) (consuming : Reactive.consuming.eval i r = 1)
    (appending : Reactive.appending.eval i r = 0)
    (available : e.txConsumed < e.request.tx.length) :
    Datapath payload (SpiCircuit.runEntryTick i r) {e with txConsumed := e.txConsumed + 1} := by
  have starting := (SpiCircuit.quiet_controls i r quiet).2.2.1
  have txBound : e.request.tx.length ≤ 32 := h.bounded.1.1
  have consumedBound : (r .txConsumed).toNat < 32 := by rw [h.consumed]; omega
  refine ⟨⟨h.bounded.1, by change e.txConsumed + 1 ≤ e.request.tx.length; omega,
    h.bounded.2.2⟩, h.tx, ?_, ?_, ?_, ?_, ?_, ?_,
    h.generation, ?_⟩
  · simpa [SpiCircuit.runEntryTick, Reactive.entryTxLength, Expr.eval, starting] using h.txLength
  · simpa [SpiCircuit.runEntryTick, Reactive.entryCapacity, Expr.eval, starting] using h.rxCapacity
  · simp [SpiCircuit.runEntryTick, Reactive.entryConsumed, Expr.eval, starting, consuming,
      h.consumed]
    omega
  · simp only [SpiCircuit.runEntryTick, consuming, if_true, Reactive.entryTx, Expr.eval,
      starting, show (0 : BitVec 1) ≠ 1 from by decide, if_false]
    rw [SpiDatapath.shift_one, h.shifted, SpiDatapath.shift_succ]
  · simpa [SpiCircuit.runEntryTick, Reactive.entryRxLength, Expr.eval, starting, appending] using h.rxLength
  · simpa [SpiCircuit.runEntryTick, Expr.eval, starting, appending] using h.received
  · simpa [SpiCircuit.runEntryTick, starting] using h.transfer

theorem Datapath.runEntryTick_high {c : SpiSource.Config} {payload : BitVec 32}
    {r : Values Reactive.Register} {e : Transfer.Execution} (h : Datapath payload r e)
    (i : Values Reactive.Input) (quiet : SpiCircuit.Quiet i)
    (word : Reactive.entryWord.eval i r = SpiSource.word c 1)
    (consuming : Reactive.consuming.eval i r = 0)
    (appending : Reactive.appending.eval i r = 1) (room : e.rx.length < e.request.rxLimit) :
    Datapath payload (SpiCircuit.runEntryTick i r)
      {e with rx := e.rx ++ [(r .stage2).getLsbD 0]} := by
  have starting := (SpiCircuit.quiet_controls i r quiet).2.2.1
  have rxBound : e.request.rxLimit ≤ 32 := h.bounded.1.2
  have sampled : (Reactive.sampled.eval i r).getLsbD 0 = (r .stage2).getLsbD 0 := by
    rw [SpiExecution.high_sampled c i r word]
    simp
  have length : (Reactive.entryRxLength.eval i r).toNat = e.rx.length := by
    simpa [Reactive.entryRxLength, Expr.eval, starting] using h.rxLength
  have received := SpiDatapath.appended_prefix i r e.rx starting length h.received
  rw [sampled] at received
  refine ⟨⟨h.bounded.1, h.bounded.2.1, ?_⟩, h.tx, ?_, ?_, ?_, ?_, ?_, ?_,
    h.generation, ?_⟩
  · change (e.rx ++ [(r .stage2).getLsbD 0]).length ≤ e.request.rxLimit
    simp only [List.length_append, List.length_singleton]
    omega
  · simpa [SpiCircuit.runEntryTick, Reactive.entryTxLength, Expr.eval, starting] using h.txLength
  · simpa [SpiCircuit.runEntryTick, Reactive.entryCapacity, Expr.eval, starting] using h.rxCapacity
  · simpa [SpiCircuit.runEntryTick, Reactive.entryConsumed, Expr.eval, starting, consuming] using h.consumed
  · simpa [SpiCircuit.runEntryTick, Reactive.entryTx, Expr.eval, starting, consuming] using h.shifted
  · simp [SpiCircuit.runEntryTick, Reactive.entryRxLength, Expr.eval, starting, appending,
      h.rxLength]
    omega
  · simpa [SpiCircuit.runEntryTick, appending] using received
  · simpa [SpiCircuit.runEntryTick, starting] using h.transfer

end Pinwheel.Hardware.Buffered.SpiRefinement
