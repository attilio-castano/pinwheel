import Pinwheel.Hardware.StreamingReady.SegmentTransaction

/-! A pulse consumes the two setup edges, both encoded dwells, and the
    two pad-transition edges from the supplied clock trace. -/
namespace Pinwheel.Hardware.StreamingReady.SegmentTimedPulse

open Pinwheel.Hardware SegmentCore SegmentPathControl SegmentTransaction
open Pinwheel.Program.StreamingReady (Cell)
open Pinwheel.Program.StreamingReadySegments

private theorem split_at (dwell : Nat) (inputs : List (Values Core.Input)) (room : dwell < inputs.length) :
    ∃ (edge : Values Core.Input) (rest : List (Values Core.Input)),
      inputs = inputs.take dwell ++ @edge :: rest := by
  cases after : inputs.drop dwell with
  | nil =>
    have length : (inputs.drop dwell).length = inputs.length - dwell := List.length_drop
    simp only [after, List.length_nil] at length
    omega
  | cons edge rest =>
    refine ⟨edge, rest, ?_⟩
    rw [← after, List.take_append_drop]

def duration (cell : Cell) : Nat := 4 + cell.lowDuration.val + cell.highDuration.val

/-- A long enough flat clock list with ordinary inputs delivers the complete
    pulse. The exact duration determines the cut and leaves all later clocks
    for the next row. TX offers may occur outside the LOW dwell. -/
theorem from_clocks (registered : Bool) (s : Values (Register a)) (cell : Cell)
    (inputs : List (Values Core.Input)) (cut : Cut registered rows cursor capture s)
    (row : rows[cursor.pc]? = some (.cell (.pulse cell)))
    (checked : successors rows budget cursor = some (.next following))
    (room : duration cell ≤ inputs.length)
    (ordinary : ∀ i ∈ inputs.take (duration cell), NoReset i)
    (lowOrdinary : ∀ i ∈ (inputs.drop 2).take cell.lowDuration.val, ProtocolOwnership.DrainInput i) :
    ∃ (used rest : List (Values Core.Input)), inputs = used ++ rest ∧ used.length = duration cell ∧
      ServiceSpan registered rows following capture s used := by
  cases inputs with
  | nil => simp [duration] at room
  | cons fetch remaining =>
    cases remaining with
    | nil => simp [duration] at room; omega
    | cons arm dwell =>
      simp only [List.length_cons, duration] at room
      have firstRoom : cell.lowDuration.val < dwell.length := by omega
      obtain ⟨rise, high, partitionLow⟩ := split_at cell.lowDuration.val dwell firstRoom
      let low := dwell.take cell.lowDuration.val
      have lowTicks : low.length = cell.lowDuration.val := by
        simp [low, Nat.min_eq_left (Nat.le_of_lt firstRoom)]
      have lowSplit : dwell = low ++ @rise :: high := partitionLow
      rw [lowSplit, List.length_append, lowTicks, List.length_cons] at room
      have secondRoom : cell.highDuration.val < high.length := by omega
      obtain ⟨fall, rest, partitionHigh⟩ := split_at cell.highDuration.val high secondRoom
      let highHolds := high.take cell.highDuration.val
      have highTicks : highHolds.length = cell.highDuration.val := by
        simp [highHolds, Nat.min_eq_left (Nat.le_of_lt secondRoom)]
      let used : List (Values Core.Input) :=
        @fetch :: @arm :: (low ++ @rise :: (highHolds ++ [@fall]))
      have partition : (@fetch :: @arm :: dwell : List (Values Core.Input)) = used ++ rest := by
        change high = highHolds ++ @fall :: rest at partitionHigh
        rw [lowSplit, partitionHigh]
        simp [used, List.append_assoc]
      have length : used.length = duration cell := by
        simp only [used, List.length_cons, List.length_append, List.length_nil, lowTicks, highTicks, duration]
        omega
      have safe : ∀ i ∈ used, NoReset i := by
        intro i member
        apply ordinary i
        rw [partition, ← length, List.take_left' rfl]
        exact member
      have lowSafe : ∀ i ∈ low, ProtocolOwnership.DrainInput i := by
        intro i member
        apply lowOrdinary i
        exact member
      have highSafe : ∀ i ∈ highHolds, NoReset i := by
        intro i member
        exact safe i (by simp [used, member])
      exact ⟨used, rest, partition, length, service_pulse registered s cell cut row checked
        fetch arm rise fall low highHolds (safe _ (by simp [used])) (safe _ (by simp [used]))
        (safe _ (by simp [used])) (safe _ (by simp [used])) lowSafe highSafe lowTicks highTicks⟩

end Pinwheel.Hardware.StreamingReady.SegmentTimedPulse
