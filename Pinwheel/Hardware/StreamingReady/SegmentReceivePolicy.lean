import Pinwheel.Hardware.StreamingReady.SegmentHostService

/-! A host can create RX credit in one ordinary clock by requesting a
    correctly tagged pop at a full receive queue. Reservation still uses
    pre-edge credit, so the clock that drains the queue parks the stream. -/
namespace Pinwheel.Hardware.StreamingReady.SegmentReceivePolicy

open Pinwheel.Hardware SegmentCore SegmentPathControl SegmentHostService
open SegmentTiming (run)

/-- Ideal host input for receive-only operation. The host copies the public
    owner tag and asks to pop on each ordinary clock. -/
def drainInput (generation transfer : BitVec 16) (raw : BitVec 2) : Values Core.Input
  | _, .rxPop => 1#1
  | _, .expectedGeneration => generation
  | _, .expectedTransfer => transfer
  | _, .rawInputs => raw
  | _, _ => 0

private theorem step_base (registered : Bool) (i : Values Core.Input) (s : Values (Register a))
    (r : Core.Register a w) :
    (circuit a registered).step i s (.base r) = (nextBase r).eval i (withFetch s ((word registered).eval i s)) :=
  bindWord_eval _ _ _ _

private theorem inv_one_inv (x : BitVec 1) : ~~~(1#1 &&& ~~~x) = x := by decide +revert +kernel

theorem popping_at_boundary (i : Values Core.Input) (s : Values (Register a))
    (ordinary : NoReset i) (boundary : s (.base .phase) = 2#3)
    (generation : i .expectedGeneration = s (.base .generation))
    (transfer : i .expectedTransfer = s (.base .transfer)) (pop : i .rxPop = 1#1)
    (nonempty : s (.base .rxCount) ≠ 0#4) : Core.popping.eval i (project s) = 1#1 := by
  simp [Core.popping, Core.hostOwner, Core.owned, Core.identity, Core.resetting,
    Core.busy, Core.retained, Core.isPhase, Core.cold, Core.warm, Core.cmd, Core.both, Core.either,
    Expr.eval, project, ordinary.1, ordinary.2, boundary, generation, transfer, pop, nonempty]

set_option linter.unusedSimpArgs false in
private theorem count_at_boundary (registered : Bool) (i : Values Core.Input) (s : Values (Register a))
    (ordinary : NoReset i) (phase : s (.base .phase) = 2#3)
    (generation : i .expectedGeneration = s (.base .generation))
    (transfer : i .expectedTransfer = s (.base .transfer)) :
    (circuit a registered).step i s (.base .rxCount) =
      if i .rxPop = 1#1 ∧ s (.base .rxCount) ≠ 0#4 then s (.base .rxCount) - 1#4 else s (.base .rxCount) := by
  rcases BitVec.eq_zero_or_eq_one (i .rxPop) with pop | pop <;>
    by_cases empty : s (.base .rxCount) = 0#4 <;>
    simp [step_base, nextBase, originalNext, Expr.eval_bind, usesEntryWord, runtimeInput,
    withFetch, Expr.eval, Core.next, Core.nextRaw, Core.queueCount, Core.emittingRX, Core.normalEmit,
    Core.timeoutFlush, Core.capturingRX, Core.capture, Core.lowEnd, Core.waitSuccess, Core.waitFault,
    Core.resetting, Core.releasing, Core.starting, Core.hostOwner, Core.free, Core.owned, Core.identity,
    Core.popping, Core.busy, Core.retained, Core.isPhase, Core.cold, Core.warm, Core.cmd,
    Core.both, Core.either, ordinary.1, ordinary.2, phase, generation, transfer, pop, empty, inv_one_inv]

structure Popped (s after : Values (Register a)) : Prop where
  room : (after (.base .rxCount)).toNat < 2 ^ a
  count : after (.base .rxCount) = s (.base .rxCount) - 1#4
  phase : after (.base .phase) = 2#3
  captured : after (.base .rxProduced) = s (.base .rxProduced)
  owner : OwnerFrame s after

/-- A correctly tagged pop frees room at the next edge. The commit of this
    pop does not retroactively supply credit to the current parked slot. -/
theorem pop_at_park (registered : Bool) (i : Values Core.Input) (s : Values (Register a))
    (ordinary : NoReset i) (phase : s (.base .phase) = 2#3)
    (blocked : Core.credit.eval i (project s) = 0#1)
    (generation : i .expectedGeneration = s (.base .generation))
    (transfer : i .expectedTransfer = s (.base .transfer)) (pop : i .rxPop = 1#1)
    (nonempty : s (.base .rxCount) ≠ 0#4)
    (bound : (s (.base .rxCount)).toNat ≤ 2 ^ a) :
    Popped s ((circuit a registered).step i s) := by
  have count : (circuit a registered).step i s (.base .rxCount) = s (.base .rxCount) - 1#4 := by
    rw [count_at_boundary registered i s ordinary phase generation transfer, if_pos ⟨pop, nonempty⟩]
  have parked := SegmentStreamStep.park_runtime registered i s ordinary phase blocked
  have owned := active_owner_frame registered i s ordinary (by simp [phase]) (by simp [phase]) (by simp [phase])
  have positive : 0 < (s (.base .rxCount)).toNat := by
    by_cases zero : (s (.base .rxCount)).toNat = 0
    · exact (nonempty (BitVec.eq_of_toNat_eq zero)).elim
    · omega
  have oneLe : (1#4) ≤ s (.base .rxCount) := Nat.succ_le_of_lt positive
  refine ⟨?_, count, parked.phase, parked.produced, owned⟩
  rw [count, BitVec.toNat_sub_of_le oneLe]
  change (s (.base .rxCount)).toNat - 1 < 2 ^ a
  omega

theorem room_eval (depth : a ≤ 3) (i : Values Core.Input) (s : Values (Register a)) :
    Core.rxRoom.eval i (project s) = BitVec.ofBool (decide ((s (.base .rxCount)).toNat < 2 ^ a)) := by
  simp [Core.rxRoom, Core.depth, Expr.eval, project, SourceRefinement.depth_toNat depth]

/-- Asking for a pop only on a full queue suffices to restore RX room. On
    the parked clock a smaller queue either holds its count or loses one. -/
theorem rx_room_or_drain (registered : Bool) (i : Values Core.Input) (s : Values (Register a))
    (ordinary : NoReset i) (phase : s (.base .phase) = 2#3)
    (blocked : Core.credit.eval i (project s) = 0#1)
    (generation : i .expectedGeneration = s (.base .generation))
    (transfer : i .expectedTransfer = s (.base .transfer))
    (bound : (s (.base .rxCount)).toNat ≤ 2 ^ a)
    (whenFull : (s (.base .rxCount)).toNat = 2 ^ a → i .rxPop = 1#1) :
    (((circuit a registered).step i s) (.base .rxCount)).toNat < 2 ^ a := by
  by_cases room : (s (.base .rxCount)).toNat < 2 ^ a
  · rw [count_at_boundary registered i s ordinary phase generation transfer]
    split
    · rename_i didPop
      have positive : 0 < (s (.base .rxCount)).toNat := by
        by_cases zero : (s (.base .rxCount)).toNat = 0
        · exact (didPop.2 (BitVec.eq_of_toNat_eq zero)).elim
        · omega
      rw [BitVec.toNat_sub_of_le (show (1#4) ≤ s (.base .rxCount) from Nat.succ_le_of_lt positive)]
      change (s (.base .rxCount)).toNat - 1 < 2 ^ a
      omega
    · exact room
  · have full : (s (.base .rxCount)).toNat = 2 ^ a := by omega
    have nonempty : s (.base .rxCount) ≠ 0#4 := by
      intro empty
      rw [empty] at full
      exact Nat.ne_of_gt (Nat.two_pow_pos a) full.symm
    exact (pop_at_park registered i s ordinary phase blocked generation transfer (whenFull full) nonempty bound).room

private theorem credit_from_room (i : Values Core.Input) (s : Values (Register a))
    (transmit : Core.transmit.eval i (project s) = 0#1)
    (room : Core.rxRoom.eval i (project s) = 1#1) :
    Core.credit.eval i (project s) = 1#1 := by
  have identity (tx receive : BitVec 1) :
      ~~~(0#1 &&& ~~~tx) &&& ~~~(receive &&& ~~~1#1) = 1#1 := by decide +revert +kernel
  simp only [Core.credit, Core.both, Core.either, Expr.eval, transmit, room, BitVec.not_not]
  exact identity _ _

/-- On a receive-only boundary, a host that asks to drain with the active
    tag can reserve on the first clock or immediately after a full-queue pop. -/
theorem credit_within_one (registered : Bool) (s : Values (Register a))
    (first next : Values Core.Input) (rest : List (Values Core.Input))
    (ordinary : NoReset first) (phase : s (.base .phase) = 2#3)
    (generation : first .expectedGeneration = s (.base .generation))
    (transfer : first .expectedTransfer = s (.base .transfer)) (pop : first .rxPop = 1#1)
    (depth : a ≤ 3) (bound : (s (.base .rxCount)).toNat ≤ 2 ^ a)
    (receiveOnly : Core.transmit.eval first (project s) = 0#1) :
    BoundedCredit registered s (@first :: @next :: rest) 1 := by
  rcases BitVec.eq_zero_or_eq_one (Core.credit.eval first (project s)) with blocked | credit
  · have noRoom : ¬ (s (.base .rxCount)).toNat < 2 ^ a := by
      intro room
      have actual : Core.rxRoom.eval first (project s) = 1#1 := by
        rw [room_eval depth, decide_eq_true room]
        rfl
      rw [credit_from_room first s receiveOnly actual] at blocked
      contradiction
    have nonempty : s (.base .rxCount) ≠ 0#4 := by
      intro empty
      rw [empty] at noRoom
      exact noRoom (Nat.two_pow_pos a)
    let after : Values (Register a) := (circuit a registered).step first s
    have popped := pop_at_park registered first s ordinary phase blocked generation transfer pop nonempty bound
    have parked := SegmentStreamStep.park_runtime registered first s ordinary phase blocked
    have transmitAfter : Core.transmit.eval next (project after) = 0#1 := by
      have same : after (.base .currentWord) = s (.base .currentWord) := parked.pose.current
      simp only [Core.transmit, Core.stream, Core.field, Core.both, Expr.eval, project, same] at receiveOnly ⊢
      exact receiveOnly
    have roomAfter : Core.rxRoom.eval next (project after) = 1#1 := by
      rw [room_eval depth, decide_eq_true popped.room]
      rfl
    have available := (available_iff_credit registered next after popped.phase).mpr
      (credit_from_room next after transmitAfter roomAfter)
    exact ⟨1, Nat.le_refl 1, next, rfl, available⟩
  · exact ⟨0, Nat.zero_le 1, first, rfl, (available_iff_credit registered first s phase).mpr credit⟩

private theorem rx_count_eval (registered : Bool) (i : Values Core.Input) (s : Values (Register a)) :
    (circuit a registered).step i s (.base .rxCount) = (Core.next .rxCount).eval i (project s) := by
  rw [step_base]
  rfl

private theorem reset_off (i : Values Core.Input) (s : Values (Register a)) (ordinary : NoReset i) :
    Core.resetting.eval i (project s) = 0#1 := by
  simp [Core.resetting, Core.cold, Core.warm, Core.cmd, Core.both, Core.either, Expr.eval,
    ordinary.1, ordinary.2]

private theorem owned_nonzero (i : Values Core.Input) (s : Values (Register a))
    (notFree : s (.base .phase) ≠ 0#3) : Core.owned.eval i (project s) = 1#1 := by
  have range (p : BitVec 3) : p = 0#3 ∨ p = 1#3 ∨ p = 2#3 ∨ p = 3#3 ∨
      p = 4#3 ∨ p = 5#3 ∨ p = 6#3 ∨ p = 7#3 := by decide +revert +kernel
  rcases range (s (.base .phase)) with zero | phase | phase | phase | phase | phase | phase | phase
  · exact (notFree zero).elim
  all_goals simp [Core.owned, Core.busy, Core.retained, Core.isPhase, Core.both, Core.either, Expr.eval, project, phase]

theorem popping_owned (i : Values Core.Input) (s : Values (Register a))
    (ordinary : NoReset i) (notFree : s (.base .phase) ≠ 0#3)
    (generation : i .expectedGeneration = s (.base .generation))
    (transfer : i .expectedTransfer = s (.base .transfer)) :
    Core.popping.eval i (project s) =
      BitVec.ofBool (decide (i .rxPop = 1#1 ∧ s (.base .rxCount) ≠ 0#4)) := by
  have owned := owned_nonzero i s notFree
  have reset := reset_off i s ordinary
  rcases BitVec.eq_zero_or_eq_one (i .rxPop) with pop | pop <;>
    by_cases empty : s (.base .rxCount) = 0#4 <;>
    simp [Core.popping, Core.hostOwner, Core.identity, Core.both, Expr.eval, project,
      reset, owned, generation, transfer, pop, empty]

private theorem count_update (registered : Bool) (i : Values Core.Input) (s : Values (Register a))
    (reset : Core.resetting.eval i (project s) = 0#1)
    (release : Core.releasing.eval i (project s) = 0#1)
    (start : Core.starting.eval i (project s) = 0#1) :
    (circuit a registered).step i s (.base .rxCount) =
      if Core.emittingRX.eval i (project s) = (1 : BitVec 1) then
        if Core.popping.eval i (project s) = (1 : BitVec 1) then s (.base .rxCount) else s (.base .rxCount) + 1#4
      else if Core.popping.eval i (project s) = (1 : BitVec 1) then s (.base .rxCount) - (1 : BitVec 4)
        else s (.base .rxCount) := by
  have incr (q : BitVec 4) : q - 15#4 = q + 1#4 := by decide +revert +kernel
  have step : BitVec.ofNat 4 (2^4 - 1) = 15#4 := rfl
  have keep : ~~~(~~~0#1 &&& ~~~0#1) ≠ (1 : BitVec 1) := by decide
  rw [rx_count_eval]
  simp only [Core.next, Core.nextRaw, Core.queueCount, Core.either, Core.inc, Expr.eval,
    reset, release, start, project, if_neg keep, if_neg (show 0#1 ≠ (1 : BitVec 1) by decide), step, incr]

private theorem count_bound (registered : Bool) (i : Values Core.Input) (s : Values (Register a))
    (ordinary : NoReset i) (notFree : s (.base .phase) ≠ 0#3)
    (release : Core.releasing.eval i (project s) = 0#1)
    (start : Core.starting.eval i (project s) = 0#1)
    (generation : i .expectedGeneration = s (.base .generation))
    (transfer : i .expectedTransfer = s (.base .transfer))
    (limit : Nat) (positiveLimit : 0 < limit) (fits : limit < 16)
    (bound : (s (.base .rxCount)).toNat ≤ limit)
    (whenFull : (s (.base .rxCount)).toNat = limit → i .rxPop = 1#1) :
    (((circuit a registered).step i s) (.base .rxCount)).toNat ≤ limit := by
  rw [count_update registered i s (reset_off i s ordinary) release start,
    popping_owned i s ordinary notFree generation transfer]
  have ofBool (flag : Bool) : (BitVec.ofBool flag = (1 : BitVec 1)) = (flag = true) := by cases flag <;> decide
  simp only [ofBool, decide_eq_true_eq]
  by_cases pop : i .rxPop = 1#1 ∧ s (.base .rxCount) ≠ 0#4
  · have positive : 0 < (s (.base .rxCount)).toNat := by
      by_cases zero : (s (.base .rxCount)).toNat = 0
      · exact (pop.2 (BitVec.eq_of_toNat_eq zero)).elim
      · omega
    simp only [if_pos pop]
    split
    · exact bound
    · rw [BitVec.toNat_sub_of_le (show (1 : BitVec 4) ≤ s (.base .rxCount) from Nat.succ_le_of_lt positive)]
      exact Nat.le_trans (Nat.sub_le ..) bound
  · have room : (s (.base .rxCount)).toNat < limit := by
      apply Nat.lt_of_le_of_ne bound
      intro full
      apply pop
      refine ⟨whenFull full, fun empty => ?_⟩
      rw [empty] at full
      exact Nat.ne_of_gt positiveLimit full.symm
    simp only [if_neg pop]
    split
    · rw [BitVec.toNat_add]
      change ((s (.base .rxCount)).toNat + 1) % 16 ≤ limit
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    · exact bound

/-- A correctly tagged pop on a full queue preserves the RX capacity
    bound on all active clocks, including captures and timeout flushes. -/
theorem rx_count_bound (registered : Bool) (i : Values Core.Input) (s : Values (Register a))
    (ordinary : NoReset i) (notFree : s (.base .phase) ≠ 0#3)
    (notComplete : s (.base .phase) ≠ 5#3) (notFault : s (.base .phase) ≠ 6#3)
    (generation : i .expectedGeneration = s (.base .generation))
    (transfer : i .expectedTransfer = s (.base .transfer))
    (depth : a ≤ 3) (bound : (s (.base .rxCount)).toNat ≤ 2 ^ a)
    (whenFull : (s (.base .rxCount)).toNat = 2 ^ a → i .rxPop = 1#1) :
    (((circuit a registered).step i s) (.base .rxCount)).toNat ≤ 2 ^ a := by
  have release : Core.releasing.eval i (project s) = 0#1 := by
    simp [Core.releasing, Core.retained, Core.isPhase, Core.either, Core.both, Expr.eval, project,
      notComplete, notFault]
  have start : Core.starting.eval i (project s) = 0#1 := by
    simp [Core.starting, Core.free, Core.both, Expr.eval, project, notFree]
  exact count_bound registered i s ordinary notFree release start generation transfer (2 ^ a) (Nat.two_pow_pos a)
    (Nat.lt_of_le_of_lt (Nat.pow_le_pow_right (by decide) depth) (show 8 < 16 by decide)) bound whenFull

private theorem count_bound_ordinary (registered : Bool) (i : Values Core.Input) (s : Values (Register a))
    (init : i .initialize = 0#1) (command : i .command = 0#4)
    (generation : i .expectedGeneration = s (.base .generation))
    (transfer : i .expectedTransfer = s (.base .transfer))
    (limit : Nat) (positiveLimit : 0 < limit) (fits : limit < 16)
    (bound : (s (.base .rxCount)).toNat ≤ limit)
    (whenFull : (s (.base .rxCount)).toNat = limit → i .rxPop = 1#1) :
    (((circuit a registered).step i s) (.base .rxCount)).toNat ≤ limit := by
  have ordinary : NoReset i := ⟨init, by simp [command]⟩
  have release : Core.releasing.eval i (project s) = 0#1 := by
    simp [Core.releasing, Core.cmd, Core.both, Expr.eval, command]
  have start : Core.starting.eval i (project s) = 0#1 := by
    simp [Core.starting, Core.cmd, Core.both, Expr.eval, command]
  by_cases free : s (.base .phase) = 0#3
  · have noEmit : Core.emittingRX.eval i (project s) = 0#1 := by
      simp [Core.emittingRX, Core.normalEmit, Core.timeoutFlush, Core.capturingRX, Core.capture,
        Core.lowEnd, Core.waitSuccess, Core.waitFault, Core.isPhase, Core.both, Core.either, Expr.eval,
        project, free]
    have noPop : Core.popping.eval i (project s) = 0#1 := by
      simp [Core.popping, Core.hostOwner, Core.owned, Core.busy, Core.retained, Core.isPhase, Core.both,
        Core.either, Expr.eval, project, free]
    rw [count_update registered i s (reset_off i s ordinary) release start]
    simpa [noEmit, noPop] using bound
  · exact count_bound registered i s ordinary free release start generation transfer limit positiveLimit fits bound whenFull

/-- The RX capacity bound survives command-zero clocks before or after
    the active exchange, allowing induction across a whole causal tape. -/
theorem rx_count_bound_ordinary (registered : Bool) (i : Values Core.Input) (s : Values (Register a))
    (init : i .initialize = 0#1) (command : i .command = 0#4)
    (generation : i .expectedGeneration = s (.base .generation))
    (transfer : i .expectedTransfer = s (.base .transfer))
    (depth : a ≤ 3) (bound : (s (.base .rxCount)).toNat ≤ 2 ^ a)
    (whenFull : (s (.base .rxCount)).toNat = 2 ^ a → i .rxPop = 1#1) :
    (((circuit a registered).step i s) (.base .rxCount)).toNat ≤ 2 ^ a :=
  count_bound_ordinary registered i s init command generation transfer (2 ^ a) (Nat.two_pow_pos a)
    (Nat.lt_of_le_of_lt (Nat.pow_le_pow_right (by decide) depth) (show 8 < 16 by decide)) bound whenFull

/-- Immediate draining keeps at most one complete RX word in the queue
    when starting from an empty queue. In particular, a depth of two or
    more never stalls a receive-only stream under this host policy. -/
theorem rx_count_one_ordinary (registered : Bool) (i : Values Core.Input) (s : Values (Register a))
    (init : i .initialize = 0#1) (command : i .command = 0#4)
    (generation : i .expectedGeneration = s (.base .generation))
    (transfer : i .expectedTransfer = s (.base .transfer))
    (bound : (s (.base .rxCount)).toNat ≤ 1)
    (whenPending : s (.base .rxCount) ≠ 0#4 → i .rxPop = 1#1) :
    (((circuit a registered).step i s) (.base .rxCount)).toNat ≤ 1 :=
  count_bound_ordinary registered i s init command generation transfer 1 (by decide) (by decide) bound
    fun full => whenPending (fun empty => by simp [empty] at full)

theorem rx_count_at_start (registered : Bool) (i : Values Core.Input) (s : Values (Register a))
    (admitted : Core.starting.eval i (project s) = 1#1) :
    (circuit a registered).step i s (.base .rxCount) = 0#4 := by
  rw [rx_count_eval]
  simp [Core.next, Core.nextRaw, Expr.eval, admitted]

end Pinwheel.Hardware.StreamingReady.SegmentReceivePolicy
