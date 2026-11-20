import Pinwheel.Program.StreamingReadySegmentExecution

/-! A stream whose final cell has no special pin modifiers can be split
between any two cells without changing its cell events or guard outcomes. -/
namespace Pinwheel.Program.StreamingReadySegments.Execution

open StreamingReady (Cell Guard)

def FinalPinsNeutral (cell : Cell) : Prop :=
  cell.lastLowLevels = 0 ∧ cell.lastHighLevels = 0 ∧
    cell.lastLowEnabled = 0 ∧ cell.lastHighEnabled = 0

private theorem basePins_neutral (neutral : FinalPinsNeutral cell) (high last : Bool) :
    cell.basePins high last = cell.basePins high false := by
  cases high <;> cases last <;>
    simp [Streaming.Cell.basePins, neutral.1, neutral.2.1, neutral.2.2.1, neutral.2.2.2]

private theorem dataPins_neutral (neutral : FinalPinsNeutral cell) (high last bit : Bool) :
    cell.dataPins high last bit = cell.dataPins high false bit := by
  simp only [Streaming.Cell.dataPins, basePins_neutral neutral high last]

/-- Cell execution factors at the split. The second group starts with the
first group's unconsumed bits and samples. A timeout interrupts the same
logical slot when slots are numbered across both groups. -/
theorem runCells_split (cell : Cell) (guard : Option Guard) (neutral : FinalPinsNeutral cell)
    (slot first second : Nat) (before : Machine) :
    runCells cell guard slot (first + second) before =
      (runCells cell guard slot first before).bind fun
        | .advance midway => runCells cell guard (slot + first) second midway
        | .expired atSlot after => some (.expired atSlot after) := by
  induction first generalizing slot before with
  | zero => simp [runCells]
  | succ first ih =>
    rw [Nat.succ_add]
    simp only [runCells, basePins_neutral neutral, dataPins_neutral neutral]
    rw [show slot + (first + 1) = slot + 1 + first by omega]
    simp only [ih]
    cases before.observations with
    | nil => rfl
    | cons observation rest =>
      cases observation with
      | wait samples => rfl
      | cell parked samples =>
        dsimp only []
        let entered : Machine := {before with observations := rest}
        generalize reserve (if parked == 0 then entered else entered.emit (.park parked))
          cell = reserved
        cases reserved with
        | none => rfl
        | some selected =>
          cases guard with
          | none =>
            rcases samples with _ | ⟨sample, tail⟩
            · rfl
            · cases tail <;> rfl
          | some g =>
            dsimp only []
            cases pollWindow g samples with
            | none => rfl
            | some matched => cases matched <;> rfl
        done

theorem i2cCell_final_pins (profile : StreamingReady.I2cProfile) :
    FinalPinsNeutral (StreamingReady.i2cCell profile) := ⟨rfl, rfl, rfl, rfl⟩

end Pinwheel.Program.StreamingReadySegments.Execution
