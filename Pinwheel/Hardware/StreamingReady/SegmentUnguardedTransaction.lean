import Pinwheel.Hardware.StreamingReady.SegmentUnguardedReceive

/-! Unguarded STREAM service witnesses for the checked transaction path. -/
namespace Pinwheel.Hardware.StreamingReady.SegmentUnguardedTransaction

open Pinwheel.Hardware SegmentCore SegmentTransaction SegmentUnguardedReceive
open Pinwheel.Program.StreamingReady (Cell)
open Pinwheel.Program.StreamingReadySegments

private theorem successor_stream (row : rows[cursor.pc]? = some (.cell (.stream cell none)))
    (armed : cursor.slots = some slots) (checked : successors rows budget cursor = some (.next following)) :
    following.pc = cursor.pc + 1 ∧ following.slots = none ∧ following.capture = cell.receive ∧
      following.tx = cursor.tx + (if cell.transmit then slots else 0) ∧
      following.rx = cursor.rx + (if cell.receive then slots else 0) ∧
      0 < slots ∧ following.tx ≤ budget ∧ following.rx < 65536 ∧
      following.coreClocks = cursor.coreClocks + (1 + slots * (3 + cell.lowDuration.val + cell.highDuration.val)) := by
  simp [successors, row, armed] at checked
  obtain ⟨_, advance⟩ := checked
  change (if (0 < slots ∧ cursor.tx + (if cell.transmit then slots else 0) ≤ budget) ∧
      cursor.rx + (if cell.receive then slots else 0) < 65536 then
    some (Successors.next {
      pc := cursor.pc + 1
      slots := none
      capture := cell.receive
      tx := cursor.tx + if cell.transmit then slots else 0
      rx := cursor.rx + if cell.receive then slots else 0
      coreClocks := cursor.coreClocks + (1 + slots *
        (1 + (cell.lowDuration.val + 1) + (cell.highDuration.val + 1) + 0))
    }) else none) = some (.next following) at advance
  simp at advance
  obtain ⟨⟨⟨positive, txFits⟩, rxFits⟩, rfl⟩ := advance
  refine ⟨rfl, rfl, rfl, rfl, rfl, positive, txFits, rxFits, ?_⟩
  have durations : 1 + (cell.lowDuration.val + 1) + (cell.highDuration.val + 1) =
    3 + cell.lowDuration.val + cell.highDuration.val := by omega
  rw [durations]

private theorem count_without_wrap (before : BitVec 16) (enabled : Bool) (slots : Nat)
    (bound : before.toNat + (if enabled then slots else 0) < 65536) :
    (before + (if enabled then BitVec.ofNat 16 slots else 0#16)).toNat =
      before.toNat + (if enabled then slots else 0) := by
  cases enabled
  · simp
  · have slotsFit : slots < 65536 := by simp at bound; omega
    simp only [if_true, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt slotsFit]
    exact Nat.mod_eq_of_lt bound

/-- A served unguarded row realizes its compiled successor. Credit and sample
    timing are stated on the concrete slot plans, with exact non-wrapping
    TX/RX accounting and a qualified last input for the next checked branch. -/
theorem service_stream (registered : Bool) (cell : Cell) (s : Values (Register a))
    (fetch : Values Core.Input) (slots : List SlotPlan) (cut : Cut registered rows cursor previous s)
    (row : rows[cursor.pc]? = some (.cell (.stream cell none)))
    (checked : successors rows budget cursor = some (.next following)) (budgetFits : budget < 65536)
    (armed : cursor.slots = some slots.length) (ordinary : SegmentPathControl.NoReset fetch)
    (served : Served registered cell ((circuit a registered).step fetch s) slots) :
    ServiceSpan registered rows following
      (captured registered cell ((circuit a registered).step fetch s) previous slots) s
      (@fetch :: slots.flatMap SlotPlan.inputs) := by
  obtain ⟨nextPC, nextSlots, nextCapture, nextTX, nextRX, positive, txFits, rxFits, _⟩ :=
    successor_stream row armed checked
  obtain ⟨completed, active⟩ := run_stream_row registered cell s fetch slots cut.boundary ordinary row
    positive (cut.slots _ armed) served
  refine ⟨by simp, active, ⟨nextPC ▸ completed.boundary, ?_, by simp [nextSlots], ?_, ?_⟩⟩
  · intro qualified
    exact captured_qualifies registered cell _ previous slots (nextCapture ▸ qualified) (by
      intro empty
      simp [empty] at positive)
  · have bound : (s (.base .txConsumed)).toNat + (if cell.transmit then slots.length else 0) < 65536 := by
      rw [cut.tx, ← nextTX]
      exact Nat.lt_of_le_of_lt txFits budgetFits
    rw [completed.consumed, count_without_wrap _ _ _ bound, cut.tx, nextTX]
  · have bound : (s (.base .rxProduced)).toNat + (if cell.receive then slots.length else 0) < 65536 := by
      rw [cut.rx, ← nextRX]
      exact rxFits
    rw [completed.produced, count_without_wrap _ _ _ bound, cut.rx, nextRX]

/-- The static stream cost is the programmed clock count. The delivered
    clocks also include the actual no-credit parks. -/
theorem stream_clocks (registered : Bool) (cell : Cell) (s : Values (Register a))
    (fetch : Values Core.Input) (slots : List SlotPlan)
    (row : rows[cursor.pc]? = some (.cell (.stream cell none)))
    (checked : successors rows budget cursor = some (.next following))
    (armed : cursor.slots = some slots.length)
    (served : Served registered cell ((circuit a registered).step fetch s) slots) :
    cursor.coreClocks + (List.cons (α := Values Core.Input) fetch (slots.flatMap SlotPlan.inputs)).length =
      following.coreClocks + (slots.map (fun slot => slot.parks.length)).sum := by
  obtain ⟨_, _, _, _, _, _, _, _, nominal⟩ := successor_stream row armed checked
  rw [nominal]
  simp only [List.length_cons, served_length registered cell ((circuit a registered).step fetch s) slots served]
  omega

end Pinwheel.Hardware.StreamingReady.SegmentUnguardedTransaction
