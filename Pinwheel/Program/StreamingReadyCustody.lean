import Pinwheel.Program.StreamingCustody
import Pinwheel.Program.StreamingReadySession
import Pinwheel.Program.StreamingReadyCounting

namespace Pinwheel.Program.StreamingReady
open Pinwheel.Program.Streaming
set_option linter.unusedSimpArgs false

abbrev neededWords := Streaming.neededWords

structure Session.State.StageGrant (s : Session.State a) : Prop where
  owned : (s.core.phase.busy || s.core.phase.retained) = true
  generation : s.host.payload 112 16 = s.core.generation
  transfer : s.host.payload 96 16 = s.core.transfer
  bounded : s.host.txLeft.toNat ≤ 64
  space : s.core.tx.count.val + neededWords s.host.txLeft.toNat ≤ queueDepth a
  budget : s.core.txAccepted.toNat + s.host.txLeft.toNat ≤ s.core.total.toNat
  receive : s.host.rxPending = true → s.core.rx.readable = true

theorem Session.State.stage_command (s : Session.State a) (i : Session.Pins) (phase : s.host.phase = 2#3) :
    (s.command i).runtime.command = 0#4 ∧
    (s.command i).runtime.txPush = (s.host.txLeft != 0) ∧
    (s.command i).runtime.rxPop = s.host.rxPending := by
  simp [Session.State.command, Host.State.command, Host.State.delivering,
    Host.State.stagedTX, Host.State.stagedRX, phase]

theorem Session.State.stage_owned (s : Session.State a) (i : Session.Pins)
    (grant : s.StageGrant) : s.core.owned (s.command i).runtime = true := by
  simp [State.owned, Session.State.command, Host.State.command, grant.owned,
    grant.generation, grant.transfer]

theorem Session.State.stage_push (s : Session.State a) (i : Session.Pins)
    (phase : s.host.phase = 2#3) (grant : s.StageGrant) (sending : s.host.txLeft ≠ 0#7) :
    s.core.tx.willPush (s.core.hostPush (s.command i).runtime) = true := by
  have count := stagedBits_nat s.host grant.bounded
  have positive : 0 < s.host.txLeft.toNat := by
    have := BitVec.toNat_ne_iff_ne.mpr sending
    simp only [BitVec.toNat_ofNat] at this
    omega
  have room : s.core.tx.count.val < queueDepth a := by
    have space := grant.space
    simp [neededWords,Streaming.neededWords, Nat.ne_of_gt positive] at space
    split at space <;> omega
  have bits : 0 < s.host.stagedBits.toNat ∧ s.host.stagedBits.toNat ≤ 32 ∧
      s.core.txAccepted.toNat + s.host.stagedBits.toNat ≤ s.core.total.toNat := by
    have budget := grant.budget
    rw [count]
    omega
  have txPush : (s.command i).runtime.txPush = true := by
    rw [(s.stage_command i phase).2.1]
    simp [sending]
  have guard : s.core.owned (s.command i).runtime = true ∧ (s.command i).runtime.txPush = true ∧
      0 < (s.command i).runtime.txBits.toNat ∧ (s.command i).runtime.txBits.toNat ≤ 32 ∧
      s.core.txAccepted.toNat + (s.command i).runtime.txBits.toNat ≤ s.core.total.toNat :=
    ⟨s.stage_owned i grant, txPush, bits⟩
  have offered : (s.core.hostPush (s.command i).runtime).isSome = true := by
    simp only [State.hostPush, dif_pos guard, Option.isSome_some]
  simp [Queue.willPush, offered, Queue.writable, room]

theorem Session.State.stage_pop (s : Session.State a) (i : Session.Pins)
    (phase : s.host.phase = 2#3) (grant : s.StageGrant) (receiving : s.host.rxPending = true) :
    s.core.rx.willPop (s.core.hostPop (s.command i).runtime) = true := by
  simp [Queue.willPop, State.hostPop, s.stage_owned i grant,
    (s.stage_command i phase).2.2, receiving, grant.receive receiving]

/-- Reserved staging remains admissible even if the engine becomes retained. -/
theorem Session.State.stage_not_rejected (s : Session.State a) (i : Session.Pins) (pending : Bool)
    (phase : s.host.phase = 2#3) (grant : s.StageGrant) :
    (s.hostInput pending i).status.rejected = false := by
  have pushGood : (s.command i).runtime.txPush = true →
      s.core.tx.willPush (s.core.hostPush (s.command i).runtime) = true := by
    intro sending
    have nonzero : s.host.txLeft ≠ 0#7 := by
      simpa only [(s.stage_command i phase).2.1, bne_iff_ne, BitVec.ofNat_eq_ofNat] using sending
    exact s.stage_push i phase grant nonzero
  have popGood : (s.command i).runtime.rxPop = true →
      s.core.rx.willPop (s.core.hostPop (s.command i).runtime) = true := by
    intro receiving
    exact s.stage_pop i phase grant ((s.stage_command i phase).2.2 ▸ receiving)
  change (s.core.status pending (s.command i).runtime).rejected = false
  simp only [State.status, (s.stage_command i phase).1]
  cases tx : (s.command i).runtime.txPush <;> cases rx : (s.command i).runtime.rxPop <;> simp_all

end Pinwheel.Program.StreamingReady
