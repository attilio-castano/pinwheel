import Pinwheel.Hardware.StreamingReady.SegmentTrace

/-! Select a bounded poll aperture using only the physical raw-input history.
    Each step tests the older of the two samples already in flight. -/
namespace Pinwheel.Hardware.StreamingReady.SegmentRawAperture

open Pinwheel.Hardware SegmentCore SegmentPathControl
open Pinwheel.Program.StreamingReady (Cell Guard Pins encode encode_fields)
open ProtocolOwnership (DrainInput)
open SegmentTiming (run ready MissHistory MissCut guardBudget)

/-- The pre-edge observations for a clock list, seeded by the two raw samples
    immediately preceding the list. -/
def samples (older newer : BitVec 2) : List (Values Core.Input) → List (BitVec 2)
  | [] => []
  | i :: rest => older :: samples newer (i .rawInputs) rest

/-- The pre-edge observation on the following clock. -/
def sampleAfter (older newer : BitVec 2) : List (Values Core.Input) → BitVec 2
  | [] => older
  | i :: rest => sampleAfter newer (i .rawInputs) rest

/-- A complete finite budget contains either the earliest qualified poll or a
    miss at its last eligible edge. No raw samples after that poll are used. -/
theorem select_poll (g : Guard) (older newer : BitVec 2) (clocks : List (Values Core.Input))
    (n : Nat) (enough : n + 1 ≤ clocks.length) :
    ∃ (prior : List (Values Core.Input)) (last : Values Core.Input) (rest : List (Values Core.Input)),
      clocks = prior ++ @last :: rest ∧ prior.length ≤ n ∧
      (samples older newer prior).any g.matches = false ∧
      (g.matches (sampleAfter older newer prior) = true ∨ prior.length = n) := by
  induction n generalizing older newer clocks with
  | zero =>
    cases clocks with
    | nil => simp at enough
    | cons i rest => exact ⟨[], i, rest, rfl, by decide, rfl, Or.inr rfl⟩
  | succ n ih =>
    cases clocks with
    | nil => simp at enough
    | cons i rest =>
      cases ready : g.matches older with
      | true => exact ⟨[], i, rest, rfl, Nat.zero_le _, rfl, Or.inl ready⟩
      | false =>
        have tailEnough : n + 1 ≤ rest.length := by simp only [List.length_cons] at enough; omega
        obtain ⟨prior, last, suffix, shape, within, misses, outcome⟩ :=
          ih newer (i .rawInputs) rest tailEnough
        refine ⟨@i :: prior, last, suffix, ?_, by simpa using Nat.succ_le_succ within, ?_, ?_⟩
        · simp only [List.cons_append, shape]
        · simp [samples, ready, misses]
        · simpa [sampleAfter, List.length_cons] using outcome

/-- The portion of the fetched word that determines poll timing and
    qualification. It is shared by waited stream cells and standalone waits. -/
structure LoadedGuard (g : Guard) (s : Values (Register a)) : Prop where
  mask : (s (.base .currentWord)).extractLsb' 50 2 = g.mask
  expected : (s (.base .currentWord)).extractLsb' 52 2 = g.expected
  budget : guardBudget s = g.limit.budget

theorem LoadedGuard.stream {s : Values (Register a)} (cell : Cell) (g : Guard)
    (loaded : s (.base .currentWord) = encode (.stream cell (some g))) : LoadedGuard g s :=
  let fields := encode_fields (.stream cell (some g))
  ⟨loaded ▸ fields.guardMask, loaded ▸ fields.guardExpected,
    by rw [guardBudget, loaded]; exact fields.guardBudget⟩

theorem LoadedGuard.wait {s : Values (Register a)} (pins : Pins) (g : Guard)
    (loaded : s (.base .currentWord) = encode (.driveWait pins g)) : LoadedGuard g s :=
  let fields := encode_fields (.driveWait pins g)
  ⟨loaded ▸ fields.guardMask, loaded ▸ fields.guardExpected,
    by rw [guardBudget, loaded]; exact fields.guardBudget⟩

theorem LoadedGuard.same_word {s after : Values (Register a)} (loaded : LoadedGuard g s)
    (same : after (.base .currentWord) = s (.base .currentWord)) : LoadedGuard g after :=
  ⟨same ▸ loaded.mask, same ▸ loaded.expected,
    by simpa only [guardBudget, same] using loaded.budget⟩

theorem LoadedGuard.qualifies {s : Values (Register a)} (loaded : LoadedGuard g s) (i : Values Core.Input) :
    ready i s = BitVec.ofBool (g.matches (s (.base .stage2))) := by
  simp only [ready, Core.waitReady, Core.guardMask, Core.guardExpected, Core.field, Expr.eval, project,
    loaded.mask, loaded.expected, Guard.matches, Bool.beq_eq_decide_eq]

private theorem noReset {i : Values Core.Input} (ordinary : DrainInput i) : NoReset i :=
  ⟨ordinary.1, by simp [ordinary.2.1]⟩

/-- Under ordinary clocks the final comparison consumes exactly the
    externally seeded, delayed raw sample. -/
theorem sampler_sampleAfter (registered : Bool) (s : Values (Register a))
    (older newer : BitVec 2) (clocks : List (Values Core.Input))
    (old : s (.base .stage2) = older) (recent : s (.base .stage1) = newer)
    (ordinary : ∀ i ∈ clocks, NoReset i) :
    run registered s clocks (.base .stage2) = sampleAfter older newer clocks := by
  induction clocks generalizing s older newer with
  | nil => exact old
  | cons i rest ih =>
    have sampled := SegmentTrace.sampler_step registered i s (ordinary i (by simp))
    exact ih ((circuit a registered).step i s) newer (i .rawInputs) (sampled.2.trans recent) sampled.1
      (fun j hj => ordinary j (List.mem_cons_of_mem (α := Values Core.Input) i hj))

/-- An entirely unqualified physical sample prefix consumes miss budget
    clock by clock. Every runtime guard comparison and timer step is derived
    from the raw trace, the initial loaded word and the available count. -/
theorem miss_history (registered : Bool) (s : Values (Register a)) (g : Guard)
    (older newer : BitVec 2) (clocks : List (Values Core.Input))
    (old : s (.base .stage2) = older) (recent : s (.base .stage1) = newer)
    (ordinary : ∀ i ∈ clocks, DrainInput i) (waiting : s (.base .phase) = 7#3)
    (loaded : LoadedGuard g s) (bounded : guardBudget s ≠ 0#8)
    (within : clocks.length ≤ (s (.base .countdown)).toNat)
    (missed : (samples older newer clocks).any g.matches = false) : MissHistory registered s clocks := by
  induction clocks generalizing s older newer with
  | nil => trivial
  | cons i rest ih =>
    simp only [samples, List.any_cons, Bool.or_eq_false_iff] at missed
    have input := ordinary i (by simp)
    have unqualified : ready i s = 0#1 := by rw [loaded.qualifies, old, missed.1]; rfl
    have one : MissHistory registered s [@i] := ⟨input, unqualified, trivial⟩
    have firstWithin : [@i].length ≤ (s (.base .countdown)).toNat := by
      simp only [List.length_cons, List.length_nil] at within ⊢
      omega
    let after : Values (Register a) := (circuit a registered).step i s
    have step : MissCut s after 1 := SegmentTiming.miss_prefix registered s [@i] waiting bounded one firstWithin
    have sampled := SegmentTrace.sampler_step registered i s (noReset input)
    have nextBound : guardBudget after ≠ 0#8 := by simpa only [guardBudget, step.pose.current] using bounded
    have nextWithin : rest.length ≤ (after (.base .countdown)).toNat := by
      rw [step.countdown]
      simp only [List.length_cons] at within
      omega
    exact ⟨input, unqualified, ih after newer (i .rawInputs) (sampled.2.trans recent) sampled.1
      (fun j hj => ordinary j (List.mem_cons_of_mem (α := Values Core.Input) i hj))
      step.phase (loaded.same_word step.pose.current) nextBound nextWithin missed.2⟩

/-- An admitted raw window provides both the runtime guard history and the
    final-edge verdict for capture, a wait successor, or timeout. -/
structure Admitted (g : Guard) (registered : Bool) (s : Values (Register a))
    (older newer : BitVec 2) (prior : List (Values Core.Input)) (last : Values Core.Input) : Prop where
  history : MissHistory registered s prior
  cut : MissCut s (run registered s prior) prior.length
  sample : run registered s prior (.base .stage2) = sampleAfter older newer prior
  comparator : ready last (run registered s prior) = BitVec.ofBool (g.matches (sampleAfter older newer prior))

theorem poll_from_raw (registered : Bool) (s : Values (Register a)) (g : Guard)
    (older newer : BitVec 2) (prior : List (Values Core.Input)) (last : Values Core.Input)
    (old : s (.base .stage2) = older) (recent : s (.base .stage1) = newer)
    (ordinary : ∀ i ∈ prior, DrainInput i) (waiting : s (.base .phase) = 7#3)
    (loaded : LoadedGuard g s) (bounded : guardBudget s ≠ 0#8)
    (within : prior.length ≤ (s (.base .countdown)).toNat)
    (missed : (samples older newer prior).any g.matches = false) :
    Admitted g registered s older newer prior last := by
  have history := miss_history registered s g older newer prior old recent ordinary waiting loaded bounded within missed
  have cut := SegmentTiming.miss_prefix registered s prior waiting bounded history within
  have sample := sampler_sampleAfter registered s older newer prior old recent (fun i hi => noReset (ordinary i hi))
  exact ⟨history, cut, sample, by rw [(loaded.same_word cut.pose.current).qualifies, sample]⟩

end Pinwheel.Hardware.StreamingReady.SegmentRawAperture
