import Pinwheel.Program.StreamingEthernetScheduleProof
import Pinwheel.Program.StreamingEthernetCredit

/-! Host refill policies for the existing depth-two sampled-ready Ethernet image. -/
namespace Pinwheel.Program.StreamingEthernetRefill
open StreamingReady StreamingEthernetCore StreamingEthernetFrame
open StreamingEthernetSchedule hiding bodyPins

/-- Delay each of the eight refills from its uniform launch cut. -/
abbrev Policy := Fin 8 → Nat

def uniform : Policy := fun _ => 0
def staggered : Policy := fun round => if round.val % 2 = 0 then 0 else 24

def launch (policy : Policy) (round : Fin 8) : Nat := refillStart round.val + policy round

private def padding (policy : Policy) (round : Fin 8) : Nat :=
  let next := if further : round.val + 1 < 8 then policy ⟨round.val + 1, further⟩ else 0
  136 + next - policy round

def bodyPins (policy : Policy) (highWidth : Nat) : List Session.Pins :=
  withClock highWidth 0
    (idlePinsFor (launch policy 0) ++ (List.finRange 8).flatMap (fun round =>
      exchangePins (round.val + 1) ++ idlePinsFor (padding policy round)) ++ idlePinsFor 267)

def alignmentPins (policy : Policy) (highWidth : Nat) : List Session.Pins :=
  (bodyPins policy highWidth).take (firstSample - 2)

def aligned (policy : Policy) (highWidth : Nat) : Session.State 1 :=
  preloaded.run program false (alignmentPins policy highWidth)

def activePins (policy : Policy) (highWidth : Nat) : List Session.Pins :=
  (bodyPins policy highWidth).drop (firstSample - 2)

def checkCredit (policy : Policy) (highWidth : Nat) : Bool :=
  StreamingEthernetCredit.check (aligned policy highWidth) (activePins policy highWidth) frameBits

theorem uniform_body (highWidth : Nat) :
    bodyPins uniform highWidth = StreamingEthernetSchedule.bodyPins highWidth := by
  have rounds : List.range 8 = (List.finRange 8).map Fin.val := by decide +kernel
  unfold bodyPins StreamingEthernetSchedule.bodyPins
  rw [rounds, List.flatMap_map]
  simp [launch, padding, uniform, refillBlock]

private def admission (round : Fin 8) (s : Session.State 1) (pin : Session.Pins) : Bool :=
  s.host.phase == 1 && s.host.request == exchangeRequest (round.val + 1) &&
    s.core.tx.count.val == 0 && s.core.txValid != 0 &&
    s.host.bulkAdmitted (s.hostInput false pin).status

private def admitsAtCut (policy : Policy) (s : Session.State 1) (cut : Nat) (pin : Session.Pins) : Bool :=
  (List.finRange 8).all fun round => cut != launch policy round + 90 || admission round s pin

def complete (policy : Policy) (highWidth : Nat) : Session.State 1 :=
  preloaded.run program false (bodyPins policy highWidth)

def released (policy : Policy) (highWidth : Nat) : Session.State 1 :=
  (complete policy highWidth).run program false (releaseClocked highWidth)

private def check (policy : Policy) (highWidth : Nat) : Bool :=
  let pins := bodyPins policy highWidth
  let (final, good) := scan (admitsAtCut policy) preloaded 0 pins
  let (after, releaseGood) := scan (fun _ _ _ => true) final wireLength (releaseClocked highWidth)
  (pins.length == wireLength && (List.finRange 8).all (fun r => launch policy r + 90 < pins.length)) &&
    (good && releaseGood) &&
    (final.core.phase == .completed && final.core.drained &&
      final.core.txAccepted == 576 && final.core.txConsumed == 576) &&
    (after.core.phase == .free && after.core.transfer == 1 && after.host.code == 0)

structure Executed (policy : Policy) (highWidth : Nat) : Prop where
  length : (bodyPins policy highWidth).length = wireLength
  cuts : ∀ round : Fin 8, launch policy round + 90 < (bodyPins policy highWidth).length
  bodyOK : (scan (admitsAtCut policy) preloaded 0 (bodyPins policy highWidth)).2 = true
  releaseOK : (scan (fun _ _ _ => true) (complete policy highWidth) wireLength (releaseClocked highWidth)).2 = true
  completed : (complete policy highWidth).core.phase = .completed
  drained : (complete policy highWidth).core.drained = true
  accepted : (complete policy highWidth).core.txAccepted = 576
  consumed : (complete policy highWidth).core.txConsumed = 576
  free : (released policy highWidth).core.phase = .free
  transfer : (released policy highWidth).core.transfer = 1
  releasedCode : (released policy highWidth).host.code = 0

private theorem check_sound (ok : check policy highWidth = true) : Executed policy highWidth := by
  unfold check at ok
  simp only [scan_state, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true] at ok
  obtain ⟨⟨⟨⟨length, cuts⟩, body, ending⟩, ⟨⟨⟨completed, drained⟩, accepted⟩, consumed⟩⟩,
    ⟨⟨free, transfer⟩, code⟩⟩ := ok
  exact ⟨length, fun r => cuts r (by simp), body, ending, completed, drained, accepted,
    consumed, free, transfer, code⟩

theorem Executed.body_runtime (e : Executed policy highWidth) :
    Session.RuntimeTrace program false preloaded (bodyPins policy highWidth) :=
  scan_runtime _ _ _ _ e.bodyOK

theorem Executed.release_runtime (e : Executed policy highWidth) :
    Session.RuntimeTrace program false (complete policy highWidth) (releaseClocked highWidth) :=
  scan_runtime _ _ _ _ e.releaseOK

theorem Executed.refill_admitted (e : Executed policy highWidth) (round : Fin 8) :
    let cut := launch policy round + 90
    let pins := bodyPins policy highWidth
    let s := preloaded.run program false (pins.take cut)
    let pin := pins[cut]'(e.cuts round)
    s.host.phase = 1 ∧ s.host.request = exchangeRequest (round.val + 1) ∧
      s.core.tx.count.val = 0 ∧ s.core.txValid ≠ 0 ∧
      s.host.bulkAdmitted (s.hostInput false pin).status = true := by
  have observed := scan_cut _ _ _ _ e.bodyOK _ (e.cuts round)
  simp only [Nat.zero_add, admitsAtCut, List.all_eq_true] at observed
  have admitted := observed round (by simp)
  simpa [admission, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, and_assoc] using admitted

set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
private theorem uniform_one : check uniform 1 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
private theorem uniform_two : check uniform 2 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
private theorem staggered_one : check staggered 1 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
private theorem staggered_two : check staggered 2 = true := by decide +kernel

theorem uniform_executed (legal : highWidth = 1 ∨ highWidth = 2) : Executed uniform highWidth :=
  check_sound (legal.elim (fun h => h.symm ▸ uniform_one) (fun h => h.symm ▸ uniform_two))

theorem staggered_executed (legal : highWidth = 1 ∨ highWidth = 2) : Executed staggered highWidth :=
  check_sound (legal.elim (fun h => h.symm ▸ staggered_one) (fun h => h.symm ▸ staggered_two))

set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
private theorem uniform_credit_one : checkCredit uniform 1 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
private theorem uniform_credit_two : checkCredit uniform 2 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
private theorem staggered_credit_one : checkCredit staggered 1 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
private theorem staggered_credit_two : checkCredit staggered 2 = true := by decide +kernel

theorem uniform_credit (legal : highWidth = 1 ∨ highWidth = 2) : checkCredit uniform highWidth = true :=
  legal.elim (fun h => h.symm ▸ uniform_credit_one) (fun h => h.symm ▸ uniform_credit_two)

theorem staggered_credit (legal : highWidth = 1 ∨ highWidth = 2) : checkCredit staggered highWidth = true :=
  legal.elim (fun h => h.symm ▸ staggered_credit_one) (fun h => h.symm ▸ staggered_credit_two)

end Pinwheel.Program.StreamingEthernetRefill
