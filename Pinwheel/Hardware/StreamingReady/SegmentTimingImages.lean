import Pinwheel.Program.StreamingReadyRegisterReadVariants
import Pinwheel.Program.StreamingSWDBranching

/-! Row capabilities of the flat timing providers and the images that use them. -/
namespace Pinwheel.Hardware.StreamingReady.SegmentTimingImages

open Pinwheel.Program.StreamingReady (Cell Guard Instruction Pins WaitLimit)
open Pinwheel.Program.StreamingReadySegments

private def bounded : WaitLimit → Bool
  | .unbounded => false
  | .misses _ => true

/-- The timed providers handle pulses, bounded waits, and unguarded streams.
    The guarded stream provider currently requires reception and a bounded
    guard. Terminal instructions are handled by the admission walk itself. -/
def supported : Instruction → Bool
  | .halt | .fault | .pulse _ | .stream _ none => true
  | .driveWait _ guard => bounded guard.limit
  | .stream cell (some guard) => cell.receive && bounded guard.limit

abbrev Supported (instruction : Instruction) : Prop := supported instruction = true

theorem wait_limit {pins : Pins} {guard : Guard} (valid : Supported (.driveWait pins guard)) :
    ∃ limit : Fin 255, guard.limit = .misses limit := by
  cases limit : guard.limit with
  | unbounded => simp [Supported, supported, bounded, limit] at valid
  | misses n => exact ⟨n, rfl⟩

theorem guarded_stream {cell : Cell} {guard : Guard} (valid : Supported (.stream cell (some guard))) :
    cell.receive = true ∧ ∃ limit : Fin 255, guard.limit = .misses limit := by
  cases limit : guard.limit with
  | unbounded => simp [Supported, supported, bounded, limit] at valid
  | misses n =>
    have receives : cell.receive = true := by simpa [Supported, supported, bounded, limit] using valid
    exact ⟨receives, n, rfl⟩

private def supportedRow : Row → Bool
  | .cell instruction => supported instruction
  | _ => true

abbrev SupportedRows (rows : List Row) : Prop := rows.all supportedRow = true

theorem SupportedRows.instruction {rows : List Row} {pc : Nat} {i : Instruction} (valid : SupportedRows rows)
    (row : rows[pc]? = some (Row.cell i)) : Supported i := by
  exact List.all_eq_true.mp valid _ (List.mem_of_getElem? row)

theorem standard_i2c : SupportedRows (registerReadRows .standard) := by decide +kernel

theorem split_i2c : SupportedRows (Pinwheel.Program.StreamingReadyRegisterReadVariants.splitRows .standard) := by
  decide +kernel

theorem standard_swd : SupportedRows (Pinwheel.Program.StreamingSWDBranching.rows 3 .standard) := by
  decide +kernel

end Pinwheel.Hardware.StreamingReady.SegmentTimingImages
