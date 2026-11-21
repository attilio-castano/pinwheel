import Pinwheel.Hardware.StreamingReady.SegmentTimedGuarded
import Pinwheel.Hardware.StreamingReady.SegmentTimedPulse
import Pinwheel.Hardware.StreamingReady.SegmentTimedUnguarded
import Pinwheel.Hardware.StreamingReady.SegmentTimedWait
import Pinwheel.Hardware.StreamingReady.SegmentTimingImages
import Pinwheel.Hardware.StreamingReady.SegmentEventWaitAdmission
import Pinwheel.Hardware.StreamingReady.SegmentEventStream

/-! Sufficient timing conditions for the checked Ready program. The conditions
    concern available clocks and host service at the reached port cuts. The
    same tape supplies the peer samples for the first qualified poll, branch
    and timeout. -/
namespace Pinwheel.Hardware.StreamingReady.SegmentTimingContract

open Pinwheel.Hardware SegmentCore SegmentPathControl SegmentTransaction
open SegmentTiming (run)
open ProtocolOwnership (DrainInput)
open SegmentTimingImages (SupportedRows)
open Pinwheel.Program.StreamingReady (Instruction Cell Guard Pins)
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
      SegmentTimedUnguarded.CreditFrom registered s clocks parkBound
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

/-- Environmental progress for event rows. These conditions concern only
    reached clock cuts, ordinary host inputs, and samples supplied by the
    peer. The encoded wait remains unbounded if the peer never responds. -/
structure Events (registered : Bool) (rows : List Row) (started : Values (Register a))
    (trace : List (Values Core.Input)) (parkBound : Nat) : Prop where
  wait : ∀ (elapsed remaining : List (Values Core.Input)) (pc : Nat) (pins : Pins) (g : Guard),
    trace = elapsed ++ remaining →
    (run registered started elapsed) (.base .phase) = 1#3 →
    ((run registered started elapsed) (.base .pc)).toNat = pc →
    rows[pc]? = some (.cell (.driveWait pins g)) → g.limit = .unbounded →
    ∃ (entry : Values Core.Input) (clocks : List (Values Core.Input)), remaining = @entry :: clocks ∧
      (∀ i ∈ clocks, DrainInput i) ∧
      let after : Values (Register a) := (circuit a registered).step entry (run registered started elapsed)
      (SegmentRawAperture.samples (after (.base .stage2)) (after (.base .stage1)) clocks).any g.matches = true
  stream : ∀ (elapsed remaining : List (Values Core.Input)) (pc : Nat) (cell : Cell) (g : Guard),
    trace = elapsed ++ remaining →
    (run registered started elapsed) (.base .phase) = 1#3 →
    ((run registered started elapsed) (.base .pc)).toNat = pc →
    rows[pc]? = some (.cell (.stream cell (some g))) → g.limit = .unbounded →
    ∃ peerBound, 1 + ((run registered started elapsed) (.base .remaining)).toNat *
      SegmentEventStream.slotBudget cell peerBound parkBound ≤ remaining.length ∧
      SegmentEventStream.SupplyFrom registered (run registered started elapsed) remaining cell g peerBound parkBound

theorem Timing.supply_with_events {started : Values (Register a)} (timing : Timing registered rows started trace parkBound)
    (events : Events registered rows started trace parkBound)
    (receiving : ∀ (pc : Nat) (cell : Cell) (g : Guard), rows[pc]? = some (Row.cell (.stream cell (some g))) → cell.receive = true)
    (budgetFits : budget < 65536) :
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
    cases kind with
    | @pulse cell =>
      obtain ⟨used, rest, shape, _, service⟩ := SegmentTimedPulse.from_clocks registered s cell remaining cut row checked
        timingAtRow.1 (fun i hi => ordinary i (List.mem_of_mem_take hi)) timingAtRow.2
      exact .advance shape service
    | @wait pins guard =>
      cases limit : guard.limit with
      | unbounded =>
        obtain ⟨entry, clocks, splitClocks, drain, event⟩ := events.wait elapsed remaining cursor.pc pins guard
          split cut.boundary.phase cut.boundary.position row limit
        obtain ⟨used, rest, shape, service⟩ := SegmentEventWaitAdmission.wait_from_clocks registered s pins guard
          limit cut row checked entry clocks (ordinary entry (by rw [splitClocks]; simp)) drain event
        exact .advance (splitClocks.trans shape) service
      | misses n =>
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
        obtain ⟨room, credit⟩ := timingAtRow
        obtain ⟨used, rest, bit, shape, _, service⟩ := SegmentTimedUnguarded.from_clocks registered cell s cut row checked
          budgetFits slots armed remaining parkBound (count ▸ room) ordinary credit
        exact .advance shape service
      | some guard =>
        have receives := receiving cursor.pc cell guard row
        cases limit : guard.limit with
        | unbounded =>
          obtain ⟨_, room, service⟩ := events.stream elapsed remaining cursor.pc cell guard split
            cut.boundary.phase cut.boundary.position row limit
          obtain ⟨used, rest, bit, shape, span⟩ := SegmentEventStream.from_clocks registered s cell guard limit
            receives cut row checked budgetFits slots armed remaining (count ▸ room) service
          exact .advance shape span
        | misses n =>
          have bounds := timingAtRow n limit
          exact SegmentTimedGuarded.from_clocks registered s cell guard n limit receives cut row checked
            budgetFits slots armed remaining parkBound (count ▸ bounds.1) ordinary bounds.2

theorem Timing.supply {started : Values (Register a)} (timing : Timing registered rows started trace parkBound)
    (supported : SupportedRows rows) (budgetFits : budget < 65536) :
    SegmentAdmission.Supply registered rows budget started trace := by
  refine timing.supply_with_events ⟨?_, ?_⟩ (fun _ _ _ row =>
    (SegmentTimingImages.guarded_stream (supported.instruction row)).1) budgetFits
  · intro elapsed remaining pc pins guard split phase position row event
    obtain ⟨_, bounded⟩ := SegmentTimingImages.wait_limit (supported.instruction row)
    rw [event] at bounded
    contradiction
  · intro elapsed remaining pc cell guard split phase position row event
    obtain ⟨_, _, bounded⟩ := SegmentTimingImages.guarded_stream (supported.instruction row)
    rw [event] at bounded
    contradiction

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

/-- Compose bounded rows and event rows on one physical trace. -/
theorem from_start_with_events (image : Image rows budget)
    (registered : Bool) (s : Values (Register a)) (start : Values Core.Input)
    (trace : List (Values Core.Input)) (parkBound : Nat)
    (installed : Installed rows s) (admitted : Core.starting.eval start (project s) = 1#1)
    (timing : Timing registered rows ((circuit a registered).step start s) trace parkBound)
    (events : Events registered rows ((circuit a registered).step start s) trace parkBound)
    (receiving : ∀ (pc : Nat) (cell : Cell) (g : Guard), rows[pc]? = some (Row.cell (.stream cell (some g))) → cell.receive = true) :
    ∃ (active : List (Values Core.Input)) (last : Values Core.Input) (rest : List (Values Core.Input))
      (ending : Execution.Terminal), trace = active ++ @last :: rest ∧
      SegmentAdmission.Admitted image registered s start active last ending :=
  SegmentAdmission.from_start image registered s start trace installed admitted
    (timing.supply_with_events events receiving (image_budget image))

end Pinwheel.Hardware.StreamingReady.SegmentTimingContract
