import Pinwheel.Program.StreamingReadyCustody
import Pinwheel.Program.StreamingReadyControl
import Pinwheel.Program.StreamingReservation

namespace Pinwheel.Program.StreamingReady
open Pinwheel.Program.Streaming
set_option linter.unusedSimpArgs false

theorem status_txFree_nat (s : State a) (pending : Bool) (i : Input) (ha : a ≤ 3) :
    (s.status pending i).txFree.toNat = queueDepth a - s.tx.count.val := by
  have depth : 2^a ≤ 2^3 := Nat.pow_le_pow_right (by decide) ha
  have count := s.tx.count.isLt
  have bound : s.tx.count.val ≤ queueDepth a := by omega
  have smallDepth : queueDepth a < 16 := by unfold queueDepth; omega
  have smallCount : s.tx.count.val < 16 := by omega
  change (BitVec.ofNat 4 (queueDepth a) - BitVec.ofNat 4 s.tx.count.val).toNat = _
  rw [BitVec.toNat_sub_of_le]
  · simp only [BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt smallDepth,Nat.mod_eq_of_lt smallCount]
  · simp only [BitVec.le_def,BitVec.toNat_ofNat]
    rwa [Nat.mod_eq_of_lt smallCount,Nat.mod_eq_of_lt smallDepth]

theorem engine_reservation_fields (p : Program) (s : State a) :
    (engine p s).generation = s.generation ∧ (engine p s).transfer = s.transfer ∧
    (engine p s).total = s.total := by
  have fields := engine_frame p s
  exact ⟨fields.2.2.2.2.1, fields.2.2.2.2.2.1, engine_total p s⟩

theorem engine_reservation_owned (p : Program) (s : State a)
    (owned : (s.phase.busy || s.phase.retained) = true) :
    ((engine p s).phase.busy || (engine p s).phase.retained) = true := by
  by_cases busy : s.phase.busy = true
  · rcases engine_live p s busy with running | retained
    · simp [running]
    · simp [retained]
  · cases phase : s.phase <;> simp [phase,Phase.busy,Phase.retained] at owned busy
    all_goals simp [engine,phase,Phase.busy,Phase.retained]

theorem Session.State.work_command (s : Session.State a) (i : Session.Pins)
    (phase : s.host.phase = 1#3) (bulk : s.host.bulk = true) :
    (s.command i).runtime.command = 0#4 ∧ (s.command i).runtime.txPush = false ∧
    (s.command i).runtime.rxPop = false := by
  simp [Session.State.command,Host.State.command,Host.State.delivering,
    Host.State.stagedTX,Host.State.stagedRX,phase,bulk]

theorem Session.State.stage_clock (s : Session.State a) (p : Program) (pending : Bool)
    (i : Session.Pins) (cold : i.initialize = false) (command : (s.command i).runtime.command = 0#4) :
    (s.step p pending i).core = clock p (s.command i).runtime s.core := by
  change StreamingReady.step p (s.command i).runtime s.core = _
  have coldInput : (s.command i).runtime.initialize = false := cold
  simp [StreamingReady.step,coldInput,command,BitVec.ofNat_eq_ofNat]

theorem Session.State.admission_reservation (s : Session.State a) (pending : Bool)
    (i : Session.Pins) (ha : a ≤ 3) (structural : s.core.Structural)
    (admitted : s.host.admittingBulk (s.hostInput pending i).status = true) :
    (s.core.phase.busy || s.core.phase.retained) = true ∧
    s.host.payload 112 16 = s.core.generation ∧ s.host.payload 96 16 = s.core.transfer ∧
    (s.host.wanted (s.hostInput pending i).status).toNat ≤ 64 ∧
    s.core.tx.count.val + neededWords (s.host.wanted (s.hostInput pending i).status).toNat ≤ queueDepth a ∧
    s.core.txAccepted.toNat + (s.host.wanted (s.hostInput pending i).status).toNat ≤ s.core.total.toNat := by
  have facts := admitted
  simp only [Host.State.admittingBulk,Bool.and_eq_true,beq_iff_eq] at facts
  have bulk := facts.2
  simp only [Host.State.bulkAdmitted,Bool.and_eq_true] at bulk
  have owner := bulk.1.1.1.1
  simp only [Host.State.bulkOwner,Bool.and_eq_true,beq_iff_eq] at owner
  have tag := s.host.tag_fields s.core.generation s.core.transfer owner.2
  have wanted := s.host.wanted_bound (s.hostInput pending i).status structural.accepted
  have free := bulk.2
  simp only [Bool.not_eq_true',decide_eq_false_iff_not] at free
  have capacity : neededWords (s.host.wanted (s.hostInput pending i).status).toNat ≤
      queueDepth a - s.core.tx.count.val := by
    change Streaming.neededWords (s.host.wanted (s.hostInput pending i).status).toNat ≤ _
    rw [← s.host.beatsNeeded_nat (s.hostInput pending i).status]
    have hfree := status_txFree_nat s.core pending (s.command i).runtime ha
    change ¬ (s.core.status pending (s.command i).runtime).txFree.toNat < _ at free
    rw [hfree] at free
    omega
  have count := s.core.tx.count.isLt
  exact ⟨owner.1,tag.1,tag.2,wanted.1,by omega,wanted.2⟩

theorem Session.State.StageGrant.admit (s : Session.State a) (p : Program) (pending : Bool)
    (i : Session.Pins) (ha : a ≤ 3) (cold : i.initialize = false)
    (safe : s.host.FrameSafe) (structural : s.core.Structural)
    (admitted : s.host.admittingBulk (s.hostInput pending i).status = true) :
    (s.step p pending i).StageGrant := by
  have facts := admitted
  simp only [Host.State.admittingBulk,Bool.and_eq_true,beq_iff_eq] at facts
  have phase : s.host.phase = 1#3 := facts.1.1
  have controls := s.work_command i phase facts.1.2
  have core := s.stage_clock p pending i cold controls.1
  have noPush : s.core.hostPush (s.command i).runtime = none := by
    simp [State.hostPush,controls.2.1]
  have noPop : s.core.hostPop (s.command i).runtime = false := by
    simp [State.hostPop,controls.2.2]
  have request : (s.step p pending i).host.request = s.host.request :=
    s.host.request_work (s.hostInput pending i) safe (by rw [phase]; decide) cold
  have host := s.host.admit_stage_fields (s.hostInput pending i) cold admitted
  have reservation := s.admission_reservation pending i ha structural admitted
  have fields := engine_reservation_fields p s.core
  constructor
  · rw [core]
    exact engine_reservation_owned p s.core reservation.1
  · change (s.step p pending i).host.request.extractLsb' 128 16 = _
    rw [request,core]
    exact reservation.2.1.trans fields.1.symm
  · change (s.step p pending i).host.request.extractLsb' 112 16 = _
    rw [request,core]
    exact reservation.2.2.1.trans fields.2.1.symm
  · change (Host.step (s.hostInput pending i) s.host).txLeft.toNat ≤ 64
    rw [host.1]
    exact reservation.2.2.2.1
  · rw [core]
    change (s.core.tx.tick (s.core.hostPush (s.command i).runtime) s.core.enginePop).count.val +
      neededWords (Host.step (s.hostInput pending i) s.host).txLeft.toNat ≤ _
    rw [noPush,host.1]
    have count := Queue.tick_no_push_le s.core.tx s.core.enginePop
    have space := reservation.2.2.2.2.1
    omega
  · rw [core]
    change (s.core.txAccepted + (if s.core.tx.willPush (s.core.hostPush (s.command i).runtime) then
      BitVec.ofNat 16 ((s.core.hostPush (s.command i).runtime).getD {}).validBits else 0)).toNat +
      (Host.step (s.hostInput pending i) s.host).txLeft.toNat ≤ (engine p s.core).total.toNat
    simp only [noPush,Queue.willPush,Option.isSome_none,Bool.false_and,Bool.false_eq_true,
      if_false,BitVec.ofNat_eq_ofNat,BitVec.add_zero,host.1,fields.2.2]
    exact reservation.2.2.2.2.2
  · intro receiving
    have queued : (s.core.status pending (s.command i).runtime).rxQueued ≠ 0#4 := by
      change (Host.step (s.hostInput pending i) s.host).rxPending = true at receiving
      rw [host.2] at receiving
      change ((s.core.status pending (s.command i).runtime).rxQueued != 0#4) = true at receiving
      simpa only [bne_iff_ne] using receiving
    have nonzero : s.core.rx.count.val ≠ 0 := by
      intro zero
      simp [State.status,zero] at queued
    have readable : s.core.rx.readable = true := by simpa [Queue.readable] using nonzero
    rw [core]
    change (s.core.rx.tick s.core.enginePush (s.core.hostPop (s.command i).runtime)).readable = true
    rw [noPop]
    exact Queue.tick_readable_no_pop _ _ readable

theorem neededWords_stage (n : Nat) (bound : n ≤ 64) :
    neededWords (n - min 32 n) + (if n = 0 then 0 else 1) = neededWords n := by
  by_cases zero : n = 0
  · simp [zero,neededWords,Streaming.neededWords]
  · by_cases large : 32 < n
    · have positive : 0 < n-32 := by omega
      have small : n-32 ≤ 32 := by omega
      simp [neededWords,Streaming.neededWords,zero,large,Nat.min_eq_left (show 32 ≤ n by omega),
        Nat.ne_of_gt positive,Nat.not_lt_of_ge small]
    · simp [neededWords,Streaming.neededWords,zero,large,Nat.min_eq_right (show n ≤ 32 by omega)]

theorem State.hostPush_bits_nat (s : State a) (i : Input)
    (pushed : (s.hostPush i).isSome = true) :
    ((s.hostPush i).getD {}).validBits = i.txBits.toNat := by
  unfold State.hostPush at pushed ⊢
  split
  · simp only [Option.getD_some,Chunk.validBits]
    omega
  · rename_i guard
    simp only [dif_neg guard,Option.isSome_none,Bool.false_eq_true] at pushed

theorem Session.State.StageGrant.accepted_step (s : Session.State a) (p : Program) (pending : Bool)
    (i : Session.Pins) (cold : i.initialize = false) (phase : s.host.phase = 2#3)
    (grant : s.StageGrant) :
    (s.step p pending i).core.txAccepted.toNat = s.core.txAccepted.toNat + min 32 s.host.txLeft.toNat := by
  rw [s.stage_clock p pending i cold (s.stage_command i phase).1]
  change (s.core.txAccepted + (if s.core.tx.willPush (s.core.hostPush (s.command i).runtime) then
    BitVec.ofNat 16 ((s.core.hostPush (s.command i).runtime).getD {}).validBits else 0)).toNat = _
  by_cases zero : s.host.txLeft = 0#7
  · have noPush : s.core.hostPush (s.command i).runtime = none := by
      simp [State.hostPush,(s.stage_command i phase).2.1,zero]
    simp [noPush,Queue.willPush,zero]
  · have accepted := s.stage_push i phase grant zero
    have offered : (s.core.hostPush (s.command i).runtime).isSome = true := by
      simp only [Queue.willPush,Bool.and_eq_true] at accepted
      exact accepted.1
    have chunk := s.core.hostPush_bits_nat (s.command i).runtime offered
    change ((s.core.hostPush (s.command i).runtime).getD {}).validBits = s.host.stagedBits.toNat at chunk
    rw [accepted,if_pos rfl,chunk,stagedBits_nat s.host grant.bounded]
    have budget := grant.budget
    have total := s.core.total.isLt
    simp only [BitVec.toNat_add,BitVec.toNat_ofNat]
    omega

theorem Session.State.StageGrant.queue_count_step (s : Session.State a) (p : Program) (pending : Bool)
    (i : Session.Pins) (cold : i.initialize = false) (phase : s.host.phase = 2#3)
    (grant : s.StageGrant) :
    (s.step p pending i).core.tx.count.val ≤ s.core.tx.count.val +
      (if s.host.txLeft.toNat = 0 then 0 else 1) := by
  rw [s.stage_clock p pending i cold (s.stage_command i phase).1]
  change (s.core.tx.tick (s.core.hostPush (s.command i).runtime) s.core.enginePop).count.val ≤ _
  rw [Queue.tick_count]
  by_cases zero : s.host.txLeft = 0#7
  · have noPush : s.core.hostPush (s.command i).runtime = none := by
      simp [State.hostPush,(s.stage_command i phase).2.1,zero]
    simp [noPush,Queue.willPush,zero]
  · have accepted := s.stage_push i phase grant zero
    have nonzero : s.host.txLeft.toNat ≠ 0 := by
      intro h
      exact zero (BitVec.eq_of_toNat_eq h)
    rw [accepted]
    simp only [↓reduceIte,nonzero]
    omega

theorem Session.State.StageGrant.stage (s : Session.State a) (p : Program) (pending : Bool)
    (i : Session.Pins) (cold : i.initialize = false) (safe : s.host.FrameSafe)
    (phase : s.host.phase = 2#3) (grant : s.StageGrant) :
    (s.step p pending i).StageGrant := by
  have core := s.stage_clock p pending i cold (s.stage_command i phase).1
  have fields := engine_reservation_fields p s.core
  have request : (s.step p pending i).host.request = s.host.request :=
    s.host.request_work (s.hostInput pending i) safe (by rw [phase]; decide) cold
  have remaining := s.host.stage_remaining (s.hostInput pending i) cold phase grant.bounded
  have left : (s.step p pending i).host.txLeft.toNat =
      s.host.txLeft.toNat - min 32 s.host.txLeft.toNat := remaining.1
  have accepted := grant.accepted_step s p pending i cold phase
  have count := grant.queue_count_step s p pending i cold phase
  constructor
  · rw [core]
    exact engine_reservation_owned p s.core grant.owned
  · change (s.step p pending i).host.request.extractLsb' 128 16 = _
    rw [request,core]
    exact grant.generation.trans fields.1.symm
  · change (s.step p pending i).host.request.extractLsb' 112 16 = _
    rw [request,core]
    exact grant.transfer.trans fields.2.1.symm
  · rw [left]
    have bound := grant.bounded
    omega
  · rw [left]
    have words := neededWords_stage s.host.txLeft.toNat grant.bounded
    have space := grant.space
    omega
  · rw [accepted,left]
    have total : (s.step p pending i).core.total = s.core.total := by
      rw [core]
      exact fields.2.2
    rw [total]
    have budget := grant.budget
    omega
  · intro receiving
    change (Host.step (s.hostInput pending i) s.host).rxPending = true at receiving
    rw [remaining.2] at receiving
    contradiction

end Pinwheel.Program.StreamingReady
