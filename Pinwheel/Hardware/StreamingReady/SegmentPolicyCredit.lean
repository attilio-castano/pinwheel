import Pinwheel.Hardware.StreamingReady.SegmentCadencedHost
import Pinwheel.Hardware.StreamingReady.SegmentTransmitPolicy

/-! Quantitative credit recovery for the causal host. A sustained wait
    reaches the next packet offer. The same edge can drain a full RX queue. -/
namespace Pinwheel.Hardware.StreamingReady.SegmentPolicyCredit

open Pinwheel.Hardware SegmentCore SegmentPathControl SegmentCausal
open SegmentCadencedHost (Policy Chunk host offer)
open SegmentHostService (Available BoundedCredit available_iff_credit)
open SegmentTransmitPolicy (Offer)

theorem tags (policy : Policy) (registered : Bool) (peer : Peer P) (s : State a Nat P) :
    (input registered (host policy) peer s) .expectedGeneration = s.core (.base .generation) ∧
      (input registered (host policy) peer s) .expectedTransfer = s.core (.base .transfer) ∧
      (input registered (host policy) peer s) .rxPop = 1#1 := ⟨rfl, rfl, rfl⟩

private theorem observed_wait (registered : Bool) (i : Values Core.Input) (s : State a Nat P) :
    (circuit a registered).observe i s.core .waitingTX = status registered s .waitingTX :=
  SegmentTransmitPolicy.waiting_input_independent registered i quiet s.core

private theorem blocked_by_wait (registered : Bool) (i : Values Core.Input) (s : State a Nat P)
    (phase : s.core (.base .phase) = 2#3) (waiting : status registered s .waitingTX = 1#1) :
    Core.credit.eval i (project s.core) = 0#1 := by
  rcases BitVec.eq_zero_or_eq_one (Core.credit.eval i (project s.core)) with zero | one
  · exact zero
  · have openNow := ((available_iff_credit registered i s.core phase).mpr one).1
    rw [observed_wait, waiting] at openNow
    contradiction

/-- At the offer edge the independent packet plan supplies a chunk that
    fits the publicly reported remaining START budget. -/
def PacketReady (policy : Policy) (registered : Bool) (s : State a Nat P) : Prop :=
  ∃ chunk, policy.chunkAt (status registered s .txAccepted).toNat = some chunk ∧
    (status registered s .txAccepted).toNat + chunk.sizeMinusOne.val + 1 ≤ (status registered s .total).toNat

theorem ready_offer (policy : Policy) (registered : Bool) (peer : Peer P) (s : State a Nat P)
    (waiting : status registered s .waitingTX = 1#1) (age : policy.cooldown ≤ s.host)
    (openTX : s.core .txClosed = 0#1) (packet : PacketReady policy registered s) :
    Offer (input registered (host policy) peer s) s.core := by
  obtain ⟨chunk, offered, fits⟩ := packet
  have choice : offer policy s.host (status registered s) = some chunk := by simp [offer, waiting, age, offered]
  have count : (input registered (host policy) peer s .txBits).toNat = chunk.sizeMinusOne.val + 1 := by
    change ((offer policy s.host (status registered s)).map Chunk.size |>.getD 0).toNat = _
    simp [choice, Chunk.size, Nat.mod_eq_of_lt (show chunk.sizeMinusOne.val + 1 < 64 by omega)]
  obtain ⟨generation, transfer, _⟩ := tags policy registered peer s
  refine ⟨input_ordinary registered (host policy) peer s (SegmentCadencedHost.runtime policy),
    generation, transfer, openTX, ?_, ?_, ?_, ?_⟩
  · change BitVec.ofBool (offer policy s.host (status registered s)).isSome = 1#1
    rw [choice]
    rfl
  · intro empty
    rw [empty, BitVec.toNat_zero] at count
    omega
  · rw [count]
    omega
  · rw [count]
    change (s.core (.base .txAccepted)).toNat + (chunk.sizeMinusOne.val + 1) ≤ (s.core (.base .total)).toNat
    change (s.core (.base .txAccepted)).toNat + chunk.sizeMinusOne.val + 1 ≤ (s.core (.base .total)).toNat at fits
    omega

private theorem wait_until_offer (policy : Policy) (registered : Bool) (peer : Peer P) (s : State a Nat P)
    (n : Nat) (distance : policy.cooldown - s.host = n)
    (boundary : s.core (.base .phase) = 2#3) (waiting : status registered s .waitingTX = 1#1) :
    let later := run registered (host policy) peer s n
    policy.cooldown ≤ later.host ∧ later.core (.base .phase) = 2#3 ∧ status registered later .waitingTX = 1#1 := by
  induction n generalizing s with
  | zero => exact ⟨by change policy.cooldown ≤ s.host; omega, boundary, waiting⟩
  | succ n ih =>
    let i : Values Core.Input := input registered (host policy) peer s
    let advanced := step registered (host policy) peer s
    have below : ¬ policy.cooldown ≤ s.host := by omega
    have ordinary : NoReset i := input_ordinary registered (host policy) peer s (SegmentCadencedHost.runtime policy)
    have noOffer : i .txPush = 0#1 := by
      exact (SegmentCadencedHost.causal_input_drains policy registered peer s (by simp [offer, below])).2.2
    have blocked := blocked_by_wait registered i s boundary waiting
    have advances : advanced.host = s.host + 1 := by
      simp [advanced, step, host, SegmentCadencedHost.nextAge, waiting]
    have waitingAgain : status registered advanced .waitingTX = 1#1 := by
      exact (SegmentTransmitPolicy.wait_held_at_park registered i quiet s.core ordinary boundary noOffer blocked).trans
        ((observed_wait registered i s).trans waiting)
    have phaseAgain : advanced.core (.base .phase) = 2#3 :=
      (SegmentStreamStep.park_runtime registered i s.core ordinary boundary blocked).phase
    exact ih advanced (by rw [advances]; omega) phaseAgain waitingAgain

/-- The host's sustained-wait timer and valid packet availability give a
    credit-bearing edge by cooldown plus one. Packet availability is only
    required at a reached offer cut, and depends on the public accepted
    count and total. -/
theorem bounded_credit (policy : Policy) (registered : Bool) (peer : Peer P) (s : State a Nat P)
    (count : Nat) (enough : policy.cooldown + 2 ≤ count) (depth : a ≤ 3)
    (boundary : s.core (.base .phase) = 2#3)
    (rxBound : ∀ k ≤ policy.cooldown,
      ((run registered (host policy) peer s k).core (.base .rxCount)).toNat ≤ 2 ^ a)
    (packet : ∀ k ≤ policy.cooldown, let atOffer := run registered (host policy) peer s k
      atOffer.core (.base .phase) = 2#3 → status registered atOffer .waitingTX = 1#1 →
      policy.cooldown ≤ atOffer.host → atOffer.core .txClosed = 0#1 ∧ PacketReady policy registered atOffer) :
    BoundedCredit registered s.core (clocks registered (host policy) peer s count) (policy.cooldown + 1) := by
  let driver := host policy
  have service (k : Nat) (inside : k ≤ policy.cooldown)
      (live : (run registered driver peer s k).core (.base .phase) = 2#3)
      (canOffer : status registered (run registered driver peer s k) .waitingTX = 1#1 →
        policy.cooldown ≤ (run registered driver peer s k).host) :
      BoundedCredit registered s.core (clocks registered driver peer s count) (policy.cooldown + 1) := by
    let atEdge := run registered driver peer s k
    let i : Values Core.Input := input registered driver peer atEdge
    let after := step registered driver peer atEdge
    let j : Values Core.Input := input registered driver peer after
    have ordinary : NoReset i := input_ordinary registered driver peer atEdge (SegmentCadencedHost.runtime policy)
    rcases BitVec.eq_zero_or_eq_one (Core.credit.eval i (project atEdge.core)) with blocked | ready
    · have offered (waiting : (circuit a registered).observe i atEdge.core .waitingTX = 1#1) : Offer i atEdge.core := by
        have publicWait : status registered atEdge .waitingTX = 1#1 := (observed_wait registered i atEdge).symm.trans waiting
        obtain ⟨openTX, chunk⟩ := packet k inside live publicWait (canOffer publicWait)
        exact ready_offer policy registered peer atEdge publicWait (canOffer publicWait) openTX chunk
      have quietAfter (ready : (circuit a registered).observe i atEdge.core .waitingTX = 0#1) :
          i .txPush = 0#1 := by
        have clear : status registered atEdge .waitingTX = 0#1 := (observed_wait registered i atEdge).symm.trans ready
        exact (SegmentCadencedHost.cleardown policy registered peer atEdge clear).1.2.2
      obtain ⟨generation, transfer, pop⟩ := tags policy registered peer atEdge
      have result := SegmentTransmitPolicy.credit_after_service registered i j atEdge.core depth ordinary live blocked
        offered quietAfter generation transfer (rxBound k inside) (fun _ => pop)
      have nextEq : run registered driver peer s (k + 1) = after := by rw [run_add]; rfl
      have nextClock : (clocks registered driver peer s count)[k + 1]? = some (@j) := by
        rw [clocks_at _ _ _ _ _ _ (by omega), nextEq]
      refine ⟨k + 1, by omega, j, nextClock, ?_⟩
      rw [clocks_take _ _ _ _ _ _ (by omega), ← run_core, nextEq]
      exact (available_iff_credit registered j after.core result.1.phase).mpr result.2
    · refine ⟨k, by omega, i, clocks_at _ _ _ _ _ _ (by omega), ?_⟩
      rw [clocks_take _ _ _ _ _ _ (by omega), ← run_core]
      exact (available_iff_credit registered i atEdge.core live).mpr ready
  rcases BitVec.eq_zero_or_eq_one (status registered s .waitingTX) with clear | waiting
  · exact service 0 (Nat.zero_le _) boundary (by intro h; change status registered s .waitingTX = 1#1 at h; rw [clear] at h; contradiction)
  · let k := policy.cooldown - s.host
    have met := wait_until_offer policy registered peer s k rfl boundary waiting
    exact service k (Nat.sub_le ..) met.2.1 (fun _ => met.1)

end Pinwheel.Hardware.StreamingReady.SegmentPolicyCredit
