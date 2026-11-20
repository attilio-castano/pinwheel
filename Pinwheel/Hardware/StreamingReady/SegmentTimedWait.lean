import Pinwheel.Hardware.StreamingReady.SegmentRawAperture
import Pinwheel.Hardware.StreamingReady.SegmentTransactionTimeout

/-! Bounded standalone waits select their first qualified aperture directly
    from a flat clock list. The caller supplies ordinary clocks and room for
    the encoded worst-case window. -/
namespace Pinwheel.Hardware.StreamingReady.SegmentTimedWait

open Pinwheel.Hardware SegmentCore SegmentPathControl SegmentTransaction SegmentTiming
open SegmentTransactionTimeout (TimeoutSpan)
open SegmentRawAperture (LoadedGuard select_poll poll_from_raw)
open ProtocolOwnership (DrainInput)
open Pinwheel.Program.StreamingReady (encode Guard Pins WaitLimit)
open Pinwheel.Program.StreamingReadySegments

private theorem noReset {i : Values Core.Input} (ordinary : DrainInput i) :
    NoReset i := ⟨ordinary.1, by simp [ordinary.2.1]⟩

/-- An ordinary clock list long enough for FETCH and a full guard budget
    supplies either a checked successor or the final missed poll. Any input
    clocks after the selected verdict remain available to the next row. -/
theorem from_clocks (registered : Bool) (s : Values (Register a)) (pins : Pins) (g : Guard)
    (n : Fin 255) (limit : g.limit = .misses n)
    (cut : Cut registered rows cursor capture s)
    (row : rows[cursor.pc]? = some (.cell (.driveWait pins g)))
    (checked : successors rows budget cursor = some (.next following))
    (inputs : List (Values Core.Input)) (room : n.val + 2 ≤ inputs.length)
    (ordinary : ∀ i ∈ inputs, DrainInput i) :
    (∃ (used rest : List (Values Core.Input)), inputs = used ++ rest ∧
      ServiceSpan registered rows following capture s used) ∨
    (∃ (used : List (Values Core.Input)) (last : Values Core.Input) (rest : List (Values Core.Input)),
      inputs = used ++ @last :: rest ∧
      TimeoutSpan registered rows budget cursor 0 cursor.tx cursor.rx s used last) := by
  cases inputs with
  | nil => simp at room
  | cons fetch clocks =>
    have fetchInput : DrainInput fetch := ordinary fetch (by simp)
    have fetchOrdinary := noReset fetchInput
    have atFetch : SegmentControl.AtFetch fetch s := by
      refine ⟨fetchOrdinary.1, fetchOrdinary.2, cut.boundary.phase, ?_⟩
      rw [cut.boundary.position, cut.boundary.installed.count]
      exact (List.getElem?_eq_some_iff.mp row).1
    obtain ⟨_, _, _, _, _, _, canonical⟩ := successor_wait row checked limit
    let entered : Values (Register a) := (circuit a registered).step fetch s
    let older := entered (.base .stage2)
    let newer := entered (.base .stage1)
    have load := SegmentWaitRefinement.load_wait registered fetch s atFetch pins g canonical
      (selected_row cut.boundary fetch row)
    have loaded : LoadedGuard g entered := LoadedGuard.wait pins g load.current
    have bounded : guardBudget entered ≠ 0#8 := by
      rw [loaded.budget, limit]
      exact SourceRefinement.budget_nonzero n
    have count : (entered (.base .countdown)).toNat = n.val := by
      rw [show entered (.base .countdown) = g.limit.initialCountdown from load.countdown, limit]
      simp [WaitLimit.initialCountdown, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show n.val < 256 by omega)]
    have enough : n.val + 1 ≤ clocks.length := by simp only [List.length_cons] at room; omega
    obtain ⟨prior, last, rest, split, within, misses, verdict⟩ := select_poll g older newer clocks n.val enough
    have drainClocks : ∀ i ∈ clocks, DrainInput i := fun i member =>
      ordinary i (List.mem_cons_of_mem (α := Values Core.Input) fetch member)
    have drainPrior : ∀ i ∈ prior, DrainInput i := by
      intro i member
      apply drainClocks i
      rw [split]
      exact List.mem_append_left _ member
    have lastOrdinary : DrainInput last := drainClocks last (by rw [split]; simp)
    have withinCount : prior.length ≤ (entered (.base .countdown)).toNat := count ▸ within
    have aperture := poll_from_raw registered entered g older newer prior last rfl rfl drainPrior
      load.phase loaded bounded withinCount misses
    let poll : Values (Register a) := run registered entered prior
    cases readyBit : g.matches (poll (.base .stage2)) with
    | true =>
      refine .inl ⟨@fetch :: (prior ++ [@last]), rest, ?_, ?_⟩
      · simpa only [List.cons_append, List.append_assoc, List.singleton_append, List.nil_append] using
          congrArg (List.cons (α := Values Core.Input) fetch) split
      · exact service_wait registered s pins g n cut row checked fetch last prior fetchOrdinary lastOrdinary
          limit within aperture.history readyBit
    | false =>
      have expired : prior.length = n.val := by
        rw [← aperture.sample, readyBit] at verdict
        exact verdict.resolve_left (by decide)
      have elapsed : poll (.base .countdown) = 0#8 := by
        apply BitVec.eq_of_toNat_eq
        change (poll (.base .countdown)).toNat = 0
        rw [aperture.cut.countdown, count, expired, Nat.sub_self]
      have current : poll (.base .currentWord) = encode (.driveWait pins g) :=
        aperture.cut.pose.current.trans load.current
      have final : ProtocolOwnership.AtDeadline last poll := by
        refine ⟨lastOrdinary, aperture.cut.phase, ?_, ?_, elapsed⟩
        · have atPoll : LoadedGuard g poll := loaded.same_word aperture.cut.pose.current
          change ready last poll = 0#1
          rw [atPoll.qualifies, readyBit]
          rfl
        · have same : poll (.base .currentWord) = entered (.base .currentWord) := aperture.cut.pose.current
          change (poll (.base .currentWord)).extractLsb' 54 8 ≠ 0#8
          rw [same]
          exact bounded
      have window := SegmentWaitRefinement.wait_window registered entered prior last load.phase pins g load.current
        bounded aperture.history withinCount lastOrdinary
      obtain ⟨active, reserved⟩ := wait_prefix registered entered prior load.phase bounded aperture.history withinCount
      have counts := fetch_counts cut.boundary fetch fetchOrdinary
      refine .inr ⟨@fetch :: prior, last, rest, ?_, ?_⟩
      · simpa only [List.cons_append] using congrArg (List.cons (α := Values Core.Input) fetch) split
      · refine ⟨.cons fetchOrdinary (by simp [cut.boundary.phase]) (by simp [cut.boundary.phase])
          (by simp [cut.boundary.phase]) active, ⟨.driveWait pins g, row, .wait, current⟩, ⟨following, checked⟩,
          ?_, ?_, ?_, final⟩
        · exact (congrArg BitVec.toNat (window.position.trans load.pc)).trans cut.boundary.position
        · exact (congrArg BitVec.toNat (reserved.trans counts.1)).trans cut.tx
        · exact (congrArg BitVec.toNat (aperture.cut.captured.trans counts.2)).trans cut.rx

/-- Only the FETCH and worst-case guard window require ordinary drain clocks.
    Later clocks can carry host offers for the following stream. -/
theorem from_bounded_prefix (registered : Bool) (s : Values (Register a)) (pins : Pins) (g : Guard)
    (n : Fin 255) (limit : g.limit = .misses n) (cut : Cut registered rows cursor capture s)
    (row : rows[cursor.pc]? = some (.cell (.driveWait pins g)))
    (checked : successors rows budget cursor = some (.next following))
    (inputs : List (Values Core.Input)) (room : n.val + 2 ≤ inputs.length)
    (ordinary : ∀ i ∈ inputs.take (n.val + 2), DrainInput i) :
    (∃ (used rest : List (Values Core.Input)), inputs = used ++ rest ∧
      ServiceSpan registered rows following capture s used) ∨
    (∃ (used : List (Values Core.Input)) (last : Values Core.Input) (rest : List (Values Core.Input)),
      inputs = used ++ @last :: rest ∧
      TimeoutSpan registered rows budget cursor 0 cursor.tx cursor.rx s used last) := by
  have ahead : (inputs.take (n.val + 2)).length = n.val + 2 := by rw [List.length_take, Nat.min_eq_left room]
  have all := List.take_append_drop (n.val + 2) inputs
  cases from_clocks registered s pins g n limit cut row checked (inputs.take (n.val + 2))
      (Nat.le_of_eq ahead.symm) ordinary with
  | inl yes =>
    obtain ⟨used, rest, split, span⟩ := yes
    exact .inl ⟨used, rest ++ inputs.drop (n.val + 2),
      all.symm.trans (by rw [split, List.append_assoc]), span⟩
  | inr no =>
    obtain ⟨used, last, rest, split, span⟩ := no
    exact .inr ⟨used, last, rest ++ inputs.drop (n.val + 2),
      all.symm.trans (by rw [split, List.append_assoc, List.cons_append]), span⟩

end Pinwheel.Hardware.StreamingReady.SegmentTimedWait
