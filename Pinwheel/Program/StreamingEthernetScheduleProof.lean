import Pinwheel.Program.StreamingEthernetSchedule

namespace Pinwheel.Program.StreamingEthernetSchedule
open StreamingReady StreamingEthernetCore StreamingEthernetFrame

private theorem runtimeOK_sound (s : Session.State 1) (pin : Session.Pins)
    (ok : runtimeOK s pin = true) : Session.RuntimeInput s pin := by
  simpa [runtimeOK, Session.RuntimeInput, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, and_assoc] using ok

theorem scan_state (observe : Session.State 1 → Nat → Session.Pins → Bool)
    (s : Session.State 1) (cut : Nat) (pins : List Session.Pins) :
    (scan observe s cut pins).1 = s.run program false pins := by
  induction pins generalizing s cut with
  | nil => rfl
  | cons pin rest ih => exact ih _ _

theorem scan_runtime (observe : Session.State 1 → Nat → Session.Pins → Bool)
    (s : Session.State 1) (cut : Nat) (pins : List Session.Pins)
    (ok : (scan observe s cut pins).2 = true) : Session.RuntimeTrace program false s pins := by
  induction pins generalizing s cut with
  | nil => trivial
  | cons pin rest ih =>
    simp only [scan, Bool.and_eq_true] at ok
    exact ⟨runtimeOK_sound _ _ ok.1.1, ih _ _ ok.2⟩

theorem scan_cut (observe : Session.State 1 → Nat → Session.Pins → Bool)
    (s : Session.State 1) (cut : Nat) (pins : List Session.Pins)
    (ok : (scan observe s cut pins).2 = true) (k : Nat) (inside : k < pins.length) :
    observe (s.run program false (pins.take k)) (cut + k) pins[k] = true := by
  induction pins generalizing s cut k with
  | nil => simp at inside
  | cons pin rest ih =>
    simp only [scan, Bool.and_eq_true] at ok
    cases k with
    | zero => exact ok.1.2
    | succ k =>
      have tail := ih _ _ ok.2 k (by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using inside)
      have plus : cut + (k + 1) = cut + 1 + k := by omega
      simpa only [plus, List.take_succ_cons, Session.State.run, List.foldl_cons,
        List.getElem_cons_succ] using tail

private abbrev quietObserve (_ : Session.State 1) (_ : Nat) (_ : Session.Pins) : Bool := true

private theorem preloaded_run : preloaded = started.run program false afterStart := rfl

structure StartedAndPreloaded : Prop where
  before : Session.RuntimeTrace program false seed beforeStart
  startRuntime : Session.RuntimeInput ready startPin
  command : (ready.command startPin).runtime.command = 3
  count : (ready.command startPin).runtime.startCount = 576
  admitted : ready.core.canStart (ready.command startPin).runtime = true
  after : Session.RuntimeTrace program false started afterStart
  waiting : preloaded.core.phase = .waiting
  accepted : preloaded.core.txAccepted = 64
  queued : preloaded.core.tx.count.val = 2
  unconsumed : preloaded.core.txConsumed = 0

theorem started_and_preloaded : StartedAndPreloaded := by
  have h := prelude_checked
  unfold checkPrelude at h
  simp only [scan_state, ← preloaded_run, Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨b,r⟩,a⟩,cmd⟩,cnt⟩,start⟩,waiting⟩,accepted⟩,queued⟩,unconsumed⟩,_⟩
  exact ⟨scan_runtime quietObserve seed 0 beforeStart b, runtimeOK_sound ready startPin r,
    cmd, cnt, start, scan_runtime quietObserve started (startCut+1) afterStart a,
    waiting, accepted, queued, unconsumed⟩

structure Executed (highWidth : Nat) : Prop where
  bodyOK : (scan checkCut preloaded 0 (bodyPins highWidth)).2 = true
  releaseOK : (scan checkCut (wireComplete highWidth) wireLength (releaseClocked highWidth)).2 = true
  completed : (wireComplete highWidth).core.phase = .completed
  drained : (wireComplete highWidth).core.drained = true
  accepted : (wireComplete highWidth).core.txAccepted = 576
  consumed : (wireComplete highWidth).core.txConsumed = 576
  free : (released highWidth).core.phase = .free
  transfer : (released highWidth).core.transfer = 1
  releasedCode : (released highWidth).host.code = 0

private theorem body_sound (initial : Session.State 1) (wire closing : List Session.Pins) (endCut : Nat)
    (h :
      let (final, good) := scan checkCut initial 0 wire
      let (after, releaseGood) := scan checkCut final endCut closing
      (good && releaseGood && final.core.phase == .completed && final.core.drained &&
        final.core.txAccepted == 576 && final.core.txConsumed == 576 &&
        final.host.phase == 0 && !final.host.ready && !final.host.active &&
        after.core.phase == .free && after.core.transfer == 1 &&
        after.host.code == 0 && !after.host.ready && !after.host.active) = true) :
    let final := initial.run program false wire
    let after := final.run program false closing
    (scan checkCut initial 0 wire).2 = true ∧ (scan checkCut final endCut closing).2 = true ∧
    final.core.phase = .completed ∧ final.core.drained = true ∧
    final.core.txAccepted = 576 ∧ final.core.txConsumed = 576 ∧
    after.core.phase = .free ∧ after.core.transfer = 1 ∧ after.host.code = 0 := by
  simp only [scan_state, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨basis,free⟩, transfer⟩, code⟩, _⟩, _⟩ := h
  obtain ⟨⟨⟨earlier, _⟩, _⟩, _⟩ := basis
  obtain ⟨⟨⟨⟨⟨body, ending⟩, complete⟩, drained⟩, accepted⟩, consumed⟩ := earlier
  exact ⟨body, ending, complete, drained, accepted, consumed, free, transfer, code⟩

theorem executed (width : highWidth = 1 ∨ highWidth = 2) : Executed highWidth := by
  have checks := body_checked width
  unfold checkBody at checks
  obtain ⟨body, ending, complete, drained, accepted, consumed, free, transfer, code⟩ :=
    body_sound preloaded (bodyPins highWidth) (releaseClocked highWidth) wireLength checks
  refine ⟨body, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [wireComplete] using ending
  · simpa only [wireComplete] using complete
  · simpa only [wireComplete] using drained
  · simpa only [wireComplete] using accepted
  · simpa only [wireComplete] using consumed
  · simpa only [released, wireComplete] using free
  · simpa only [released, wireComplete] using transfer
  · simpa only [released, wireComplete] using code

theorem Executed.body_runtime (e : Executed highWidth) :
    Session.RuntimeTrace program false preloaded (bodyPins highWidth) :=
  scan_runtime _ _ _ _ e.bodyOK

theorem Executed.release_runtime (e : Executed highWidth) :
    Session.RuntimeTrace program false (wireComplete highWidth) (releaseClocked highWidth) :=
  scan_runtime _ _ _ _ e.releaseOK

theorem body_length (highWidth : Nat) : (bodyPins highWidth).length = wireLength := by
  simp only [bodyPins, withClock, List.length_map, List.length_zipIdx]
  decide +kernel

private theorem checked_sample (k : Nat) (inside : k < 576) (core : State 1)
    (sample : sampleMatches (firstSample + 6 * k) core = true) :
    core.pins.enabled = 3 ∧ core.pins.levels[1] = true ∧ core.pins.levels[0] = frameBits[k]?.getD false := by
  let cut := firstSample + 6 * k
  have position : cut - firstSample = 6 * k := by unfold cut; omega
  have afterStart : firstSample ≤ cut := by unfold cut; omega
  have divides : (6 * k) % 6 = 0 := by omega
  have index : (6 * k) / 6 = k := by omega
  change sampleMatches cut core = true at sample
  simpa [sampleMatches, position, afterStart, divides, index, inside, and_assoc] using sample

/-- The actual sampled source session presents each host-supplied frame bit at
the corresponding PHY sampling cut, with both SNI outputs driven. -/
theorem Executed.phy_sample (e : Executed highWidth) (k : Nat) (inside : k < 576) :
    let cut := firstSample + 6 * k
    let data := (wireAt highWidth cut).core.pins
    data.enabled = 3 ∧ data.levels[1] = true ∧ data.levels[0] = frameBits[k]?.getD false := by
  intro cut data
  have inTrace : cut < (bodyPins highWidth).length := by
    rw [body_length]
    unfold cut firstSample wireLength
    omega
  have observation := scan_cut checkCut preloaded 0 (bodyPins highWidth) e.bodyOK cut inTrace
  simp only [Nat.zero_add, checkCut, Bool.and_eq_true] at observation
  exact checked_sample k inside (wireAt highWidth cut).core observation.1.1.1

/-- The same bit is already present immediately after the preceding launch
edge, one pre-edge observation before the PHY sample. -/
theorem Executed.setup_sample (e : Executed highWidth) (k : Nat) (inside : k < 576) :
    let cut := firstSample + 6 * k - 1
    let data := (wireAt highWidth cut).core.pins
    data.enabled = 3 ∧ data.levels[1] = true ∧ data.levels[0] = frameBits[k]?.getD false := by
  intro cut data
  have inTrace : cut < (bodyPins highWidth).length := by
    rw [body_length]
    unfold cut firstSample wireLength
    omega
  have observation := scan_cut checkCut preloaded 0 (bodyPins highWidth) e.bodyOK cut inTrace
  simp only [Nat.zero_add, checkCut, Bool.and_eq_true] at observation
  have sample : cut + 1 = firstSample + 6 * k := by unfold cut firstSample; omega
  have checked := observation.2
  rw [sample] at checked
  exact checked_sample k inside (wireAt highWidth cut).core checked

theorem Executed.enable_at (e : Executed highWidth) (cut : Nat) (inside : cut < wireLength) :
    let pins := (wireAt highWidth cut).core.pins
    pins.enabled = 3 ∧ pins.levels[1] = decide (firstSample - 2 ≤ cut ∧ cut < wireLength) := by
  have observation := scan_cut checkCut preloaded 0 (bodyPins highWidth) e.bodyOK cut
    (by rwa [body_length])
  simp only [Nat.zero_add, checkCut, Bool.and_eq_true] at observation
  have enabled : enableMatches cut (wireAt highWidth cut).core = true := observation.1.2
  simpa only [enableMatches, Bool.and_eq_true, beq_iff_eq] using enabled

theorem release_length (highWidth : Nat) : (releaseClocked highWidth).length = 245 := by
  simp only [releaseClocked, withClock, List.length_map, List.length_zipIdx, releasePins,
    Streaming.BootPins.transaction_length]

theorem Executed.next_phy_idle (e : Executed highWidth) :
    let pins := ((wireComplete highWidth).run program false ((releaseClocked highWidth).take 1)).core.pins
    pins.enabled = 3 ∧ pins.levels[1] = false := by
  have observation := scan_cut checkCut (wireComplete highWidth) wireLength
    (releaseClocked highWidth) e.releaseOK 1 (by rw [release_length]; decide)
  simp only [checkCut, Bool.and_eq_true] at observation
  simpa [enableMatches, wireLength, firstSample, Bool.and_eq_true, beq_iff_eq] using observation.1.2

theorem Executed.refill_admitted (e : Executed highWidth) (round : Nat) (inside : round < 8) :
    let cut := refillStart round + 90
    let s := wireAt highWidth cut
    let pin := (bodyPins highWidth)[cut]?.getD {}
    s.host.phase = 1 ∧ s.host.request = exchangeRequest (round + 1) ∧
      s.core.tx.count.val = 0 ∧ s.core.txValid ≠ 0 ∧
      s.host.bulkAdmitted (s.hostInput false pin).status = true := by
  intro cut s pin
  have inTrace : cut < (bodyPins highWidth).length := by
    rw [body_length]
    unfold cut refillStart firstSample wireLength
    omega
  have observation := scan_cut checkCut preloaded 0 (bodyPins highWidth) e.bodyOK cut inTrace
  simp only [Nat.zero_add, checkCut, Bool.and_eq_true] at observation
  have refill : refillMatches cut s pin = true := by
    change refillMatches cut (wireAt highWidth cut) ((bodyPins highWidth)[cut]?.getD {}) = true
    rw [List.getElem?_eq_getElem inTrace, Option.getD_some]
    exact observation.1.1.2.1
  have position : cut - refillStart 0 - 90 = 384 * round := by unfold cut refillStart; omega
  have afterStart : refillStart 0 + 90 ≤ cut := by unfold cut refillStart; omega
  have divides : (384 * round) % 384 = 0 := by omega
  have index : (384 * round) / 384 = round := by omega
  simpa [refillMatches, position, afterStart, divides, index, inside, and_assoc] using refill

end Pinwheel.Program.StreamingEthernetSchedule
