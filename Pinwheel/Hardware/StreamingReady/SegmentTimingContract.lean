import Pinwheel.Hardware.StreamingReady.SegmentTimedGuarded
import Pinwheel.Hardware.StreamingReady.SegmentTimedPulse
import Pinwheel.Hardware.StreamingReady.SegmentTimedUnguarded
import Pinwheel.Hardware.StreamingReady.SegmentTimedWait
import Pinwheel.Hardware.StreamingReady.SegmentTimingImages

/-! Sufficient timing conditions for the checked Ready program. The conditions
    concern available clocks and host service at the reached port cuts. The
    same tape supplies the peer samples for the first qualified poll, branch
    and timeout. -/
namespace Pinwheel.Hardware.StreamingReady.SegmentTimingContract

open Pinwheel.Hardware SegmentCore SegmentPathControl SegmentTransaction
open SegmentTiming (run)
open ProtocolOwnership (DrainInput)
open SegmentTimingImages (SupportedRows)
open Pinwheel.Program.StreamingReady (Instruction Cell Guard)
open Pinwheel.Program.StreamingReadySegments

def RowTiming (registered : Bool) (s : Values (Register a)) (clocks : List (Values Core.Input))
    (parkBound : Nat) : Instruction → Prop
  | .halt | .fault => True
  | .pulse cell =>
      SegmentTimedPulse.duration cell ≤ clocks.length ∧
      ∀ i ∈ (clocks.drop 2).take cell.lowDuration.val, DrainInput i
  | .driveWait _ guard => ∀ n : Fin 255, guard.limit = .misses n →
      n.val + 2 ≤ clocks.length ∧ ∀ i ∈ clocks.take (n.val + 2), DrainInput i
  | .stream cell none =>
      1 + (s (.base .remaining)).toNat * SegmentTimedUnguarded.slotBudget cell parkBound ≤ clocks.length ∧
      (∀ i ∈ clocks, DrainInput i) ∧ SegmentTimedUnguarded.CreditFrom registered s clocks parkBound
  | .stream cell (some guard) => ∀ n : Fin 255, guard.limit = .misses n →
      1 + (s (.base .remaining)).toNat * SegmentTimedGuarded.slotBudget cell n parkBound ≤ clocks.length ∧
      SegmentTimedGuarded.SupplyFrom registered s clocks cell n parkBound

/-- At FETCH, the port trace supplies an ordinary head clock and enough
    service for the instruction at the current PC. Runtime guard success,
    branch direction, and terminal status are determined by the engine. -/
structure Timing (registered : Bool) (rows : List Row) (started : Values (Register a))
    (trace : List (Values Core.Input)) (parkBound : Nat) : Prop where
  ordinary : ∀ i ∈ trace, NoReset i
  fetch : ∀ (elapsed remaining : List (Values Core.Input)), trace = elapsed ++ remaining →
    (run registered started elapsed) (.base .phase) = 1#3 →
    ∃ (i : Values Core.Input) (rest : List (Values Core.Input)),
      remaining = @i :: rest ∧ DrainInput i
  row : ∀ (elapsed remaining : List (Values Core.Input)) (pc : Nat) (instruction : Instruction),
    trace = elapsed ++ remaining → (run registered started elapsed) (.base .phase) = 1#3 →
    ((run registered started elapsed) (.base .pc)).toNat = pc →
    rows[pc]? = some (.cell instruction) →
    RowTiming registered (run registered started elapsed) remaining parkBound instruction

private theorem armed_stream {g : Option Guard} (row : rows[cursor.pc]? = some (.cell (.stream cell g)))
    (checked : successors rows budget cursor = some (.next following)) : ∃ slots, cursor.slots = some slots := by
  cases count : cursor.slots with
  | none => simp [successors, row, count] at checked
  | some slots => exact ⟨slots, rfl⟩

theorem Timing.supply {started : Values (Register a)} (timing : Timing registered rows started trace parkBound)
    (supported : SupportedRows rows) (budgetFits : budget < 65536) :
    SegmentAdmission.Supply registered rows budget started trace := by
  constructor
  · intro elapsed remaining cursor capture split cut
    obtain ⟨i, rest, shape, drain⟩ := timing.fetch elapsed remaining split cut.boundary.phase
    exact ⟨i, rest, shape, ⟨drain.1, by simp [drain.2.1]⟩, fun _ _ => drain⟩
  · intro elapsed remaining cursor capture split cut instruction following kind row checked
    let s : Values (Register a) := run registered started elapsed
    have timingAtRow := timing.row elapsed remaining cursor.pc instruction split cut.boundary.phase cut.boundary.position row
    have ordinary : ∀ i ∈ remaining, NoReset i := by
      intro i h
      apply timing.ordinary i
      rw [split]
      exact List.mem_append_right _ h
    have valid := supported.instruction row
    cases kind with
    | @pulse cell =>
      obtain ⟨used, rest, shape, _, service⟩ := SegmentTimedPulse.from_clocks registered s cell remaining cut row checked
        timingAtRow.1 (fun i hi => ordinary i (List.mem_of_mem_take hi)) timingAtRow.2
      exact .advance shape service
    | @wait pins guard =>
      obtain ⟨n, limit⟩ := SegmentTimingImages.wait_limit valid
      have bounds := timingAtRow n limit
      cases SegmentTimedWait.from_bounded_prefix registered s pins guard n limit cut row checked remaining bounds.1 bounds.2 with
      | inl yes =>
        obtain ⟨used, rest, shape, service⟩ := yes
        exact .advance shape service
      | inr no =>
        obtain ⟨used, last, rest, shape, service⟩ := no
        exact .timeout shape service
    | @stream cell guard =>
      obtain ⟨slots, armed⟩ := armed_stream row checked
      have count : (s (.base .remaining)).toNat = slots := cut.slots slots armed
      cases guard with
      | none =>
        obtain ⟨room, drains, credit⟩ := timingAtRow
        obtain ⟨used, rest, bit, shape, _, service⟩ := SegmentTimedUnguarded.from_clocks registered cell s cut row checked
          budgetFits slots armed remaining parkBound (count ▸ room) drains credit
        exact .advance shape service
      | some guard =>
        obtain ⟨receives, n, limit⟩ := SegmentTimingImages.guarded_stream valid
        have bounds := timingAtRow n limit
        exact SegmentTimedGuarded.from_clocks registered s cell guard n limit receives cut row checked
          budgetFits slots armed remaining parkBound (count ▸ bounds.1) ordinary bounds.2

private theorem image_budget (image : Image rows budget) : budget < 65536 := by
  have checked := image.checked
  unfold Pinwheel.Program.StreamingReadySegments.check at checked
  split at checked
  · rename_i fits
    simp only [Bool.and_eq_true, decide_eq_true_eq] at fits
    exact fits.2
  · contradiction

/-- A supported checked image reaches its first terminal edge from these
    timing conditions. No intermediate row service or chosen outcome is
    required from the caller. -/
theorem from_start (image : Image rows budget) (supported : SupportedRows rows)
    (registered : Bool) (s : Values (Register a)) (start : Values Core.Input)
    (trace : List (Values Core.Input)) (parkBound : Nat)
    (installed : Installed rows s) (admitted : Core.starting.eval start (project s) = 1#1)
    (timing : Timing registered rows ((circuit a registered).step start s) trace parkBound) :
    ∃ (active : List (Values Core.Input)) (last : Values Core.Input) (rest : List (Values Core.Input))
      (ending : Execution.Terminal), trace = active ++ @last :: rest ∧
      SegmentAdmission.Admitted image registered s start active last ending :=
  SegmentAdmission.from_start image registered s start trace installed admitted
    (timing.supply supported (image_budget image))

end Pinwheel.Hardware.StreamingReady.SegmentTimingContract
