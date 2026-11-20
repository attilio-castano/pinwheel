import Pinwheel.Hardware.StreamingReady.SegmentEventWait

/-! Select the clock span of a peer-driven standalone wait on the same
    physical trace that drives admission. -/
namespace Pinwheel.Hardware.StreamingReady.SegmentEventWaitAdmission

open Pinwheel.Hardware SegmentCore SegmentPathControl SegmentTransaction
open Pinwheel.Program.StreamingReady (Guard Pins)
open Pinwheel.Program.StreamingReadySegments
open SegmentRawAperture (LoadedGuard samples)
open ProtocolOwnership (DrainInput)

/-- A qualifying sample somewhere on the offered tape suffices. The
    engine advances on the first match, after any number of missed polls. -/
theorem wait_from_clocks (registered : Bool) (s : Values (Register a)) (pins : Pins) (g : Guard)
    (limit : g.limit = .unbounded) (cut : Cut registered rows cursor capture s)
    (row : rows[cursor.pc]? = some (.cell (.driveWait pins g)))
    (checked : successors rows budget cursor = some (.next following))
    (entry : Values Core.Input) (clocks : List (Values Core.Input)) (entryOrdinary : NoReset entry)
    (ordinary : ∀ i ∈ clocks, DrainInput i)
    (arrives : let entered : Values (Register a) := (circuit a registered).step entry s
      (samples (entered (.base .stage2)) (entered (.base .stage1)) clocks).any g.matches = true) :
    ∃ (used rest : List (Values Core.Input)), @entry :: clocks = used ++ rest ∧
      ServiceSpan registered rows following capture s used := by
  let entered : Values (Register a) := (circuit a registered).step entry s
  let old := entered (.base .stage2)
  let recent := entered (.base .stage1)
  have fetch : SegmentControl.AtFetch entry s :=
    ⟨entryOrdinary.1, entryOrdinary.2, cut.boundary.phase, by
      rw [cut.boundary.position, cut.boundary.installed.count]
      exact (List.getElem?_eq_some_iff.mp row).1⟩
  have loaded := SegmentWaitRefinement.load_wait registered entry s fetch pins g
    (successor_wait_fields row checked).2.2.2.2.2 (selected_row cut.boundary entry row)
  have guard : LoadedGuard g entered := LoadedGuard.wait pins g loaded.current
  rcases SegmentEventWait.select_first g old recent clocks with absent | ⟨prior, last, rest, split, missed, matched⟩
  · change (samples old recent clocks).any g.matches = true at arrives
    simp [absent] at arrives
  · have ordinaryPrior : ∀ i ∈ prior, DrainInput i := fun i hi => ordinary i
      (split.symm ▸ List.mem_append_left _ hi)
    have finalOrdinary : DrainInput last := ordinary last (split.symm ▸ List.mem_append_right _ (by simp))
    have window := SegmentEventWait.first_qualified registered entered g old recent prior last rfl rfl
      ordinaryPrior loaded.phase guard limit missed matched
    have active := (SegmentEventWait.hold_misses registered entered prior loaded.phase
      (SegmentEventWait.zero_budget guard limit) window.misses).2
    refine ⟨@entry :: (prior ++ [@last]), rest, ?_, ?_⟩
    · simp [split, List.append_assoc]
    · exact service_wait_window registered s pins g cut row checked entry last prior entryOrdinary finalOrdinary
        loaded active window.held.phase window.held.reserved (window.resume finalOrdinary pins loaded.current)

end Pinwheel.Hardware.StreamingReady.SegmentEventWaitAdmission
