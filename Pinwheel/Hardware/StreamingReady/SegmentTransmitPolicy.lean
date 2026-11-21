import Pinwheel.Hardware.StreamingReady.SegmentReceivePolicy

/-! Host provisioning at a Ready reservation boundary. The host offers a
    nonempty packet using the current owner and the outstanding START
    budget. Storage and next-edge credit follow from the circuit. -/
namespace Pinwheel.Hardware.StreamingReady.SegmentTransmitPolicy

open Pinwheel.Hardware SegmentCore SegmentPathControl

/-- A tagged TX offer uses only ordinary port inputs and the current
    transaction budget. A simultaneous RX pop is allowed. -/
structure Offer (i : Values Core.Input) (s : Values (Register a)) : Prop where
  ordinary : NoReset i
  generation : i .expectedGeneration = s (.base .generation)
  transfer : i .expectedTransfer = s (.base .transfer)
  openTX : s .txClosed = 0#1
  push : i .txPush = 1#1
  nonempty : i .txBits ≠ 0#6
  packet : (i .txBits).toNat ≤ 32
  fits : (s (.base .txAccepted)).toNat + (i .txBits).toNat ≤ (s (.base .total)).toNat

private def selected (registered : Bool) (i : Values Core.Input) (s : Values (Register a)) :
    Values (Register a) := withFetch s ((word registered).eval i s)

private theorem step_base (registered : Bool) (i : Values Core.Input) (s : Values (Register a))
    (r : Core.Register a w) :
    (circuit a registered).step i s (.base r) = (nextBase r).eval i (selected registered i s) :=
  bindWord_eval _ _ _ _

private theorem waiting (registered : Bool) (i : Values Core.Input) (s : Values (Register a)) :
    (circuit a registered).observe i s .waitingTX = (Core.output .waitingTX).eval i (project s) := by
  change (bindWord (word registered) (output .waitingTX)).eval i s = _
  rw [bindWord_eval]
  rfl

private theorem wait_bits (sending valid count : BitVec 1) :
    (1#1 &&& (sending &&& (valid &&& count)) = 1#1) ↔
      sending = 1#1 ∧ valid = 1#1 ∧ count = 1#1 := by
  decide +revert +kernel

private theorem flag {p : Prop} [Decidable p] : (BitVec.ofBool (decide p) = 1#1) → p := by
  by_cases h : p <;> simp [h]

private theorem and_one (b : BitVec 1) : 1#1 &&& b = b := by decide +revert +kernel

private theorem runtime_inputs_eq (registered : Bool) (i : Values Core.Input) (s : Values (Register a))
    (push : (runtimeInput Streaming.Core.Input.txPush).eval i (selected registered i s) = i .txPush) :
    (fun {w} (port : Core.Input w) => (runtimeInput port).eval i (selected registered i s)) = (@i) := by
  funext w port
  cases port <;> first | exact push | rfl

theorem empty_on_wait (registered : Bool) (i : Values Core.Input) (s : Values (Register a))
    (boundary : s (.base .phase) = 2#3)
    (blocked : (circuit a registered).observe i s .waitingTX = 1#1) :
    Core.transmit.eval i (project s) = 1#1 ∧
      s (.base .txValid) = 0#6 ∧ s (.base .txCount) = 0#4 := by
  rw [waiting] at blocked
  simp only [Core.output, Core.both, Core.either, Core.txAvailable, Core.isPhase,
    Expr.eval, project, boundary, BitVec.not_not] at blocked
  have facts := (wait_bits _ _ _).mp blocked
  exact ⟨facts.1, flag facts.2.1, flag facts.2.2⟩

private theorem blocked_credit (i : Values Core.Input) (s : Values (Register a))
    (sending : Core.transmit.eval i (project s) = 1#1)
    (emptyShifter : s (.base .txValid) = 0#6) (emptyQueue : s (.base .txCount) = 0#4) :
    Core.credit.eval i (project s) = 0#1 := by
  simp [Core.credit, Core.txAvailable, Core.both, Core.either, Expr.eval, project, sending,
    emptyShifter, emptyQueue]

/-- A successful refill takes place at the old TX tail. It does not reserve
    the just-inserted word on the same edge. -/
structure Refilled (i : Values Core.Input) (s after : Values (Register a)) : Prop where
  park : SegmentStreamStep.CreditPark s after
  owner : OwnerFrame s after
  accepted : (after (.base .txAccepted)).toNat =
    (s (.base .txAccepted)).toNat + (i .txBits).toNat
  queued : after (.base .txCount) = 1#4
  shifter : after (.base .txValid) = 0#6
  word : after (.base (.txWord (s (.base .txTail)))) = i .txData
  bits : after (.base (.txBits (s (.base .txTail)))) = i .txBits

theorem Refilled.available {s after : Values (Register a)} {i : Values Core.Input}
    (done : Refilled i s after) (nextInput : Values Core.Input) :
    Core.txAvailable.eval nextInput (project after) = 1#1 := by
  simp [Core.txAvailable, Core.either, Expr.eval, project, done.queued]

set_option linter.unusedSimpArgs false in
theorem refill (registered : Bool) (i : Values Core.Input) (s : Values (Register a))
    (capacity : 0 < 2 ^ a % 16) (boundary : s (.base .phase) = 2#3)
    (blocked : (circuit a registered).observe i s .waitingTX = 1#1) (offer : Offer i s) :
    Refilled i s ((circuit a registered).step i s) := by
  obtain ⟨sending, shifter, queue⟩ := empty_on_wait registered i s boundary blocked
  have park := SegmentStreamStep.park_runtime registered i s offer.ordinary boundary
    (blocked_credit i s sending shifter queue)
  have owner := active_owner_frame registered i s offer.ordinary
    (by simp [boundary]) (by simp [boundary]) (by simp [boundary])
  have packetNat : ((0#10) ++ i .txBits).toNat = (i .txBits).toNat := by rw [BitVec.toNat_append]; simp
  have ordered : s (.base .txAccepted) ≤ s (.base .total) := by
    change (s (.base .txAccepted)).toNat ≤ (s (.base .total)).toNat
    have := offer.fits
    omega
  have fits : ¬((s (.base .total) - s (.base .txAccepted)).toNat < ((0#10) ++ i .txBits).toNat) := by
    rw [BitVec.toNat_sub_of_le ordered, packetNat]
    have := offer.fits
    omega
  have packet : ¬32 < (i .txBits).toNat := Nat.not_lt_of_ge offer.packet
  have narrow (x y : BitVec 16) : (x - (0#16 - y)).toNat = (x.toNat + y.toNat) % 65536 := by
    rw [BitVec.sub_eq_add_neg, BitVec.zero_sub, BitVec.neg_neg, BitVec.toNat_add]
  have noWrap : ((s (.base .txAccepted)).toNat + (i .txBits).toNat) % 65536 =
      (s (.base .txAccepted)).toNat + (i .txBits).toNat :=
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt offer.fits (s (.base .total)).isLt)
  have taking : Core.takingTX.eval i (project s) = 0#1 := by
    simp [Core.takingTX, Core.reserving, Expr.eval, Core.both,
      blocked_credit i s sending shifter queue]
  have stop : Core.takingTX.eval i (fun r => s (.base r)) = 0#1 := taking
  have push : Core.pushing.eval i (fun r => s (.base r)) = 1#1 := by
    have numericFit := fits
    simp only [BitVec.toNat_sub, packetNat] at numericFit
    simp [Core.pushing, Core.hostOwner, Core.identity, Core.owned, Core.busy, Core.retained, Core.txRoom,
      Core.depth, Core.txBits16, Core.resetting, Core.cold, Core.warm, Core.cmd, Core.isPhase, Core.both,
      Core.either, Expr.eval, boundary, capacity, queue, packet,
      numericFit, packetNat, offer.generation, offer.transfer, offer.push, offer.nonempty,
      offer.ordinary.1, offer.ordinary.2]
  have unmasked := runtime_inputs_eq registered i s (by
    simp [runtimeInput, denyTX, SegmentCore.discard, fetching, SegmentCore.both, SegmentCore.either, selected,
      lift, withFetch, Core.fetching, Core.resetting, Core.cold, Core.warm, Core.cmd, Core.isPhase,
      Core.both, Core.either, Expr.eval_bind, Expr.eval, offer.ordinary.1, offer.ordinary.2,
      boundary, offer.openTX, and_one])
  refine ⟨park, owner, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp only [step_base, nextBase, originalNext, Expr.eval, Expr.eval_bind, usesEntryWord, if_false, unmasked]
  all_goals simp [selected, Expr.eval_bind,
    withFetch, lift, Expr.eval, Core.next, Core.nextRaw, SegmentCore.discard, fetching, SegmentCore.both,
    SegmentCore.either, denyTX, Core.fetching, Core.cold, Core.warm, Core.resetting, Core.cmd, Core.isPhase,
    Core.both, Core.either, Core.free, Core.owned, Core.busy, Core.retained, Core.starting, Core.releasing,
    Core.identity, Core.hostOwner, Core.clearedRuntime, Core.txBits16,
    Core.queueCount, Core.loadingTX, Core.inc, Core.add, boundary, shifter, queue,
    offer.ordinary.1, offer.ordinary.2, narrow, packetNat, noWrap, stop, push, and_one]
  done

set_option linter.unusedSimpArgs false in
/-- An RX-only service clock during a credit park does not consume an
    available TX bit or modify TX custody. -/
theorem tx_held_at_park (registered : Bool) (i : Values Core.Input) (s : Values (Register a))
    (ordinary : NoReset i) (boundary : s (.base .phase) = 2#3) (noOffer : i .txPush = 0#1)
    (blocked : Core.credit.eval i (project s) = 0#1) :
    let after : Values (Register a) := (circuit a registered).step i s
    after (.base .txCount) = s (.base .txCount) ∧ after (.base .txValid) = s (.base .txValid) ∧
      after (.base .txAccepted) = s (.base .txAccepted) := by
  have taking : Core.takingTX.eval i (fun r => s (.base r)) = 0#1 := by
    have credit : Core.credit.eval i (fun r => s (.base r)) = 0#1 := blocked
    simp [Core.takingTX, Core.reserving, Expr.eval, Core.both, credit]
  have noPush : Core.pushing.eval i (fun r => s (.base r)) = 0#1 := by
    simp [Core.pushing, Core.both, Expr.eval, noOffer]
  have unmasked := runtime_inputs_eq registered i s (by simp [runtimeInput, SegmentCore.both, Expr.eval, noOffer])
  refine ⟨?_, ?_, ?_⟩
  all_goals simp only [step_base, nextBase, originalNext, Expr.eval, Expr.eval_bind, usesEntryWord, if_false, unmasked]
  all_goals simp [selected, Expr.eval_bind, withFetch, lift, Expr.eval, Core.next, Core.nextRaw,
    SegmentCore.discard, fetching, SegmentCore.both, SegmentCore.either, Core.fetching, Core.cold, Core.warm,
    Core.resetting, Core.cmd, Core.isPhase, Core.both, Core.either, Core.free, Core.owned, Core.busy,
    Core.retained, Core.starting, Core.releasing, Core.identity, Core.hostOwner, Core.clearedRuntime,
    Core.queueCount, Core.loadingTX, Core.add, boundary, ordinary.1, ordinary.2, taking, noPush]
  done

private def waitFlag (phase : BitVec 3) (row : BitVec 64) (valid : BitVec 6) (count : BitVec 4) : BitVec 1 :=
  BitVec.ofBool (decide (phase = 2#3)) &&&
    ((BitVec.ofBool (decide (row.extractLsb' 0 3 = 1#3)) &&& row.extractLsb' 34 1) &&&
      (BitVec.ofBool (decide (valid = 0#6)) &&& BitVec.ofBool (decide (count = 0#4))))

private theorem waiting_flag (registered : Bool) (i : Values Core.Input) (s : Values (Register a)) :
    (circuit a registered).observe i s .waitingTX =
      waitFlag (s (.base .phase)) (s (.base .currentWord)) (s (.base .txValid)) (s (.base .txCount)) := by
  rw [waiting]
  simp [waitFlag, Core.output, Core.isPhase, Core.transmit, Core.stream, Core.field, Core.txAvailable,
    Core.both, Core.either, Expr.eval, project]
  rfl

/-- The public TX demand can be observed before selecting this edge's host
    actions or resolving its raw peer pins. -/
theorem waiting_input_independent (registered : Bool) (i j : Values Core.Input) (s : Values (Register a)) :
    (circuit a registered).observe i s .waitingTX = (circuit a registered).observe j s .waitingTX := by
  rw [waiting_flag, waiting_flag]

/-- Before a TX offer, a credit park presents exactly the same TX demand
    to the host. The raw peer pins and any RX pop do not affect this flag. -/
theorem wait_held_at_park (registered : Bool) (i nextInput : Values Core.Input) (s : Values (Register a))
    (ordinary : NoReset i) (boundary : s (.base .phase) = 2#3) (noOffer : i .txPush = 0#1)
    (blocked : Core.credit.eval i (project s) = 0#1) :
    (circuit a registered).observe nextInput ((circuit a registered).step i s) .waitingTX =
      (circuit a registered).observe i s .waitingTX := by
  let after : Values (Register a) := (circuit a registered).step i s
  have held := tx_held_at_park registered i s ordinary boundary noOffer blocked
  have park := SegmentStreamStep.park_runtime registered i s ordinary boundary blocked
  have current : after (.base .currentWord) = s (.base .currentWord) := park.pose.current
  have phase : after (.base .phase) = 2#3 := park.phase
  have queue : after (.base .txCount) = s (.base .txCount) := held.1
  have shifter : after (.base .txValid) = s (.base .txValid) := held.2.1
  change (circuit a registered).observe nextInput after .waitingTX = _
  rw [waiting_flag, waiting_flag, phase, current, shifter, queue, boundary]

theorem tx_ready_or_refill (registered : Bool) (i nextInput : Values Core.Input) (s : Values (Register a))
    (capacity : 0 < 2 ^ a % 16) (ordinary : NoReset i) (boundary : s (.base .phase) = 2#3)
    (blocked : Core.credit.eval i (project s) = 0#1)
    (whenWaiting : (circuit a registered).observe i s .waitingTX = 1#1 → Offer i s)
    (whenReady : (circuit a registered).observe i s .waitingTX = 0#1 → i .txPush = 0#1) :
    (circuit a registered).observe nextInput ((circuit a registered).step i s) .waitingTX = 0#1 := by
  rcases BitVec.eq_zero_or_eq_one ((circuit a registered).observe i s .waitingTX) with okay | needs
  · exact (wait_held_at_park registered i nextInput s ordinary boundary (whenReady okay) blocked).trans okay
  · have reached := refill registered i s capacity boundary needs (whenWaiting needs)
    rw [waiting]
    have ready := reached.available nextInput
    simp [Core.output, Core.both, Expr.eval, ready]
  done

/-- Refill and drain service can occur on the same parked clock. The next
    clock sees both queue resources ready, using no added credit premise. -/
theorem credit_after_service (registered : Bool) (i nextInput : Values Core.Input)
    (s : Values (Register a)) (depth : a ≤ 3)
    (ordinary : NoReset i) (boundary : s (.base .phase) = 2#3)
    (blocked : Core.credit.eval i (project s) = 0#1)
    (whenWaiting : (circuit a registered).observe i s .waitingTX = 1#1 → Offer i s)
    (whenReady : (circuit a registered).observe i s .waitingTX = 0#1 → i .txPush = 0#1)
    (generation : i .expectedGeneration = s (.base .generation))
    (transfer : i .expectedTransfer = s (.base .transfer))
    (rxBound : (s (.base .rxCount)).toNat ≤ 2 ^ a)
    (whenFull : (s (.base .rxCount)).toNat = 2 ^ a → i .rxPop = 1#1) :
    let after : Values (Register a) := (circuit a registered).step i s
    SegmentStreamStep.CreditPark s after ∧ Core.credit.eval nextInput (project after) = 1#1 := by
  let after : Values (Register a) := (circuit a registered).step i s
  have capacity : 0 < 2 ^ a % 16 := by
    have fits := SourceRefinement.depth_toNat depth
    change 2 ^ a % 16 = 2 ^ a at fits
    rw [fits]
    exact Nat.two_pow_pos _
  have parked := SegmentStreamStep.park_runtime registered i s ordinary boundary blocked
  have txClear := tx_ready_or_refill registered i nextInput s capacity ordinary boundary blocked whenWaiting whenReady
  have room := SegmentReceivePolicy.rx_room_or_drain registered i s ordinary boundary blocked
    generation transfer rxBound whenFull
  have roomEval : Core.rxRoom.eval nextInput (project after) = 1#1 := by
    rw [SegmentReceivePolicy.room_eval depth, decide_eq_true room]
    rfl
  have rxClear : (circuit a registered).observe nextInput after .waitingRX = 0#1 := by
    change (bindWord (word registered) (output .waitingRX)).eval nextInput after = _
    rw [bindWord_eval]
    change (Core.output .waitingRX).eval nextInput (project after) = _
    simp [Core.output, Core.both, Expr.eval, roomEval]
  exact ⟨parked, (SegmentHostService.available_iff_credit registered nextInput after parked.phase).mp
    ⟨txClear, rxClear⟩⟩

/-- Discard closes TX only on an edge that enters retained completion.
    Reached active states inherit the open offer gate. -/
theorem open_until_completion (registered : Bool) (i : Values Core.Input) (s : Values (Register a))
    (openTX : s .txClosed = 0#1)
    (live : (circuit a registered).step i s (.base .phase) ≠ 5#3) :
    (circuit a registered).step i s .txClosed = 0#1 := by
  have noDiscard : SegmentCore.discard.eval i (selected registered i s) = 0#1 := by
    rcases BitVec.eq_zero_or_eq_one (SegmentCore.discard.eval i (selected registered i s)) with no | yes
    · exact no
    · exact (live (by
        rw [step_base]
        simp [nextBase, Expr.eval, yes])).elim
  change (bindWord (word registered) (next .txClosed)).eval i s = _
  rw [bindWord_eval]
  change (next .txClosed).eval i (selected registered i s) = 0#1
  have kept : selected registered i s .txClosed = 0#1 := openTX
  simp [next, Expr.eval, SegmentCore.either, noDiscard, kept]

private theorem start_opens (registered : Bool) (i : Values Core.Input) (s : Values (Register a))
    (admitted : Core.starting.eval i (project s) = 1#1) :
    (circuit a registered).step i s .txClosed = 0#1 := by
  change (bindWord (word registered) (next .txClosed)).eval i s = _
  rw [bindWord_eval]
  change (next .txClosed).eval i (selected registered i s) = 0#1
  have cleared : (lift Core.clearedRuntime).eval i (selected registered i s) = 1#1 := by
    change Core.clearedRuntime.eval i (project s) = 1#1
    simp [Core.clearedRuntime, Core.either, Expr.eval, admitted]
  simp [next, Expr.eval, cleared]

set_option linter.unusedSimpArgs false in
private theorem settled_phase (registered : Bool) (i : Values Core.Input) (s : Values (Register a))
    (init : i .initialize = 0#1) (quiet : i .command = 0#4)
    (completed : s (.base .phase) = 5#3) :
    (circuit a registered).step i s (.base .phase) = 5#3 := by
  simp [step_base, selected, nextBase, originalNext, Expr.eval_bind, usesEntryWord, decodedRegister,
    runtimeInput, lift, withFetch, Expr.eval, SegmentCore.discard, SegmentCore.control, setCount,
    branch, fetching, SegmentCore.both, SegmentCore.either, Core.next, Core.nextRaw, Core.fetching,
    Core.isPhase, Core.cold, Core.warm, Core.resetting, Core.cmd, Core.both, Core.either, Core.owned,
    Core.busy, Core.retained, Core.identity, Core.hostOwner, Core.starting, Core.free, Core.releasing,
    Core.enteringCell, Core.reserving, Core.lowEnd, Core.highEnd, Core.capture, Core.guardedLowEnd,
    Core.waitSuccess, Core.waitFault, Core.standaloneSuccess, Core.waitDecrement, Core.advancing,
    init, quiet, completed]

private theorem open_or_retained (registered : Bool) (s : Values (Register a))
    (inputs : List (Values Core.Input)) (before : s .txClosed = 0#1 ∨ s (.base .phase) = 5#3)
    (clocks : ∀ i ∈ inputs, i .initialize = 0#1 ∧ i .command = 0#4) :
    let after : Values (Register a) := SegmentTiming.run registered s inputs
    after .txClosed = 0#1 ∨ after (.base .phase) = 5#3 := by
  induction inputs generalizing s with
  | nil => exact before
  | cons i rest ih =>
    let after : Values (Register a) := (circuit a registered).step i s
    have next : after .txClosed = 0#1 ∨ after (.base .phase) = 5#3 := by
      rcases before with opened | completed
      · by_cases finish : after (.base .phase) = 5#3
        · exact .inr finish
        · exact .inl (open_until_completion registered i s opened finish)
      · have ⟨init, quiet⟩ := clocks i (by simp)
        exact .inr (settled_phase registered i s init quiet completed)
    exact ih after next (fun j hj => clocks j (List.mem_cons_of_mem (α := Values Core.Input) i hj))

/-- With admitted START and command-zero runtime inputs, a reached
    reservation always has an open TX gate. The host need not inspect
    the private discard latch. -/
theorem open_at_reservation (registered : Bool) (start : Values Core.Input) (s : Values (Register a))
    (admitted : Core.starting.eval start (project s) = 1#1) (inputs : List (Values Core.Input))
    (clocks : ∀ i ∈ inputs, i .initialize = 0#1 ∧ i .command = 0#4)
    (boundary : SegmentTiming.run registered ((circuit a registered).step start s) inputs (.base .phase) = 2#3) :
    SegmentTiming.run registered ((circuit a registered).step start s) inputs .txClosed = 0#1 := by
  have invariant := open_or_retained registered ((circuit a registered).step start s) inputs
    (.inl (start_opens registered start s admitted)) clocks
  exact invariant.resolve_right (by simp [boundary])

end Pinwheel.Hardware.StreamingReady.SegmentTransmitPolicy
