import Pinwheel.Hardware.StreamingReady.SegmentRawAperture
import Pinwheel.Hardware.StreamingReady.SegmentWaitRefinement

/-! A zero guard budget keeps a reached WAIT active on every missed poll.
The first physically qualifying sample is selected from the same raw
clocks that advance the circuit and its two-stage sampler. -/
namespace Pinwheel.Hardware.StreamingReady.SegmentEventWait

open Pinwheel.Hardware SegmentCore SegmentPathControl SegmentTiming
open SegmentRawAperture (LoadedGuard samples sampleAfter sampler_sampleAfter)
open ProtocolOwnership (DrainInput)
open Pinwheel.Program.StreamingReady (Cell Guard Pins encode encode_fields)

structure HoldCut (s after : Values (Register a)) : Prop where
  phase : after (.base .phase) = 7#3
  pc : after (.base .pc) = s (.base .pc)
  countdown : after (.base .countdown) = s (.base .countdown)
  pose : WaitPose s after
  owner : OwnerFrame s after
  accepted : after (.base .txAccepted) = s (.base .txAccepted)
  reserved : after (.base .txConsumed) = s (.base .txConsumed)
  captured : after (.base .rxProduced) = s (.base .rxProduced)
  latched : after .lastCapture = s .lastCapture
  valid : after .captureValid = s .captureValid

private theorem HoldCut.refl (s : Values (Register a)) (waiting : s (.base .phase) = 7#3) : HoldCut s s :=
  ⟨waiting, rfl, rfl, ⟨rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl⟩

private theorem HoldCut.trans {s mid after : Values (Register a)} (before : HoldCut s mid)
    (later : HoldCut mid after) : HoldCut s after :=
  ⟨later.phase, later.pc.trans before.pc, later.countdown.trans before.countdown,
    ⟨later.pose.current.trans before.pose.current, later.pose.remaining.trans before.pose.remaining,
      later.pose.levels.trans before.pose.levels, later.pose.enabled.trans before.pose.enabled⟩,
    ⟨later.owner.generation.trans before.owner.generation, later.owner.transfer.trans before.owner.transfer,
      later.owner.total.trans before.owner.total⟩,
    later.accepted.trans before.accepted, later.reserved.trans before.reserved,
    later.captured.trans before.captured, later.latched.trans before.latched, later.valid.trans before.valid⟩

private theorem noReset {i : Values Core.Input} (ordinary : DrainInput i) : NoReset i :=
  ⟨ordinary.1, by simp [ordinary.2.1]⟩

private theorem inv_one_inv (x : BitVec 1) : ~~~(1#1 &&& ~~~x) = x := by decide +revert +kernel

set_option linter.unusedSimpArgs false in
/-- One unqualified event wait holds its current row and capture history.
    Tagged RX drain remains legal while the peer is silent. -/
theorem hold_edge (registered : Bool) (i : Values Core.Input) (s : Values (Register a))
    (ordinary : DrainInput i) (waiting : s (.base .phase) = 7#3) (miss : ready i s = 0#1)
    (unbounded : guardBudget s = 0#8) : HoldCut s ((circuit a registered).step i s) := by
  have owner := active_owner_frame registered i s (noReset ordinary)
    (by simp [waiting]) (by simp [waiting]) (by simp [waiting])
  obtain ⟨init, command, noPush⟩ := ordinary
  have mismatch :
      (s (.base .stage2) &&& (s (.base .currentWord)).extractLsb' 50 2) ≠
        (s (.base .currentWord)).extractLsb' 52 2 := by
    simp [ready, Core.waitReady, Core.guardMask, Core.guardExpected, Core.field, Expr.eval, project] at miss
    exact of_decide_eq_false miss
  simp only [guardBudget] at unbounded
  refine ⟨?_, ?_, ?_, ⟨?_, ?_, ?_, ?_⟩, owner, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [Circuit.step, circuit, bindWord_eval, next, nextBase, originalNext, Expr.eval_bind,
      SegmentCore.discard, SegmentCore.control, setCount, branch, fetching, both, either,
      Expr.eval, usesEntryWord, runtimeInput, decodedRegister, lift, withFetch,
      Core.next, Core.nextRaw, Core.isPhase, Core.fetching, Core.clearedRuntime,
      Core.cold, Core.warm, Core.cmd, Core.resetting, Core.either, Core.both, Core.releasing,
      Core.starting, Core.free, Core.hostOwner, Core.owned, Core.busy, Core.identity, Core.retained,
      Core.enteringCell, Core.reserving, Core.lowEnd, Core.highEnd, Core.capturingRX, Core.capture,
      Core.advancing, Core.guardedLowEnd, Core.waitSuccess, Core.standaloneSuccess, Core.waitFault,
      Core.waitDecrement, Core.waitReady, Core.guardBudget, Core.guardMask, Core.guardExpected,
      Core.field, Core.nextPins, Core.pushing, Core.takingTX, SegmentCore.denyTX,
      init, command, noPush, waiting, mismatch, unbounded, inv_one_inv] <;> done

/-- The next qualifying edge, when present, depends only on the incoming
    raw tape and the two sampler values already in flight. -/
theorem select_first (g : Guard) (older newer : BitVec 2) (clocks : List (Values Core.Input)) :
    (samples older newer clocks).any g.matches = false ∨
    ∃ (prior : List (Values Core.Input)) (last : Values Core.Input) (rest : List (Values Core.Input)),
      clocks = prior ++ @last :: rest ∧
      (samples older newer prior).any g.matches = false ∧
      g.matches (sampleAfter older newer prior) = true := by
  induction clocks generalizing older newer with
  | nil => exact .inl rfl
  | cons i rest ih =>
    cases hit : g.matches older with
    | true => exact .inr ⟨[], i, rest, rfl, rfl, hit⟩
    | false =>
      rcases ih newer (i .rawInputs) with misses | ⟨before, last, tail, split, misses, hit'⟩
      · exact .inl (by simp [samples, hit, misses])
      · exact .inr ⟨@i :: before, last, tail, by simp only [List.cons_append, split],
          by simp [samples, hit, misses], hit'⟩

theorem zero_budget {s : Values (Register a)} (loaded : LoadedGuard g s) (limit : g.limit = .unbounded) :
    guardBudget s = 0#8 := by
  rw [loaded.budget, limit]
  rfl

/-- Each clock of an unbounded miss history is active, with the same row
    and transaction counters when the history ends. -/
theorem hold_misses (registered : Bool) (s : Values (Register a)) (clocks : List (Values Core.Input))
    (waiting : s (.base .phase) = 7#3) (unbounded : guardBudget s = 0#8)
    (history : MissHistory registered s clocks) :
    HoldCut s (run registered s clocks) ∧ SegmentTransaction.ActiveClocks registered s clocks := by
  induction clocks generalizing s with
  | nil => exact ⟨HoldCut.refl s waiting, .nil⟩
  | cons i rest ih =>
    obtain ⟨ordinary, miss, later⟩ := history
    let after : Values (Register a) := (circuit a registered).step i s
    have cut : HoldCut s after := hold_edge registered i s ordinary waiting miss unbounded
    have stillUnbounded : guardBudget after = 0#8 := by
      simpa only [guardBudget, cut.pose.current] using unbounded
    obtain ⟨held, active⟩ := ih after cut.phase stillUnbounded later
    exact ⟨cut.trans held, .cons (noReset ordinary) (by simp [waiting]) (by simp [waiting])
      (by simp [waiting]) active⟩

/-- A missed event prefix can be arbitrarily long. These invariants hold
    without any bound on time to arrival of the peer signal. -/
theorem hold_from_raw (registered : Bool) (s : Values (Register a)) (g : Guard)
    (older newer : BitVec 2) (clocks : List (Values Core.Input))
    (old : s (.base .stage2) = older) (recent : s (.base .stage1) = newer)
    (ordinary : ∀ i ∈ clocks, DrainInput i) (waiting : s (.base .phase) = 7#3)
    (loaded : LoadedGuard g s) (limit : g.limit = .unbounded)
    (missed : (samples older newer clocks).any g.matches = false) :
    HoldCut s (run registered s clocks) ∧ MissHistory registered s clocks := by
  induction clocks generalizing s older newer with
  | nil => exact ⟨HoldCut.refl s waiting, trivial⟩
  | cons i rest ih =>
    simp only [samples, List.any_cons, Bool.or_eq_false_iff] at missed
    have input := ordinary i (by simp)
    have unqualified : ready i s = 0#1 := by rw [loaded.qualifies, old, missed.1]; rfl
    let after : Values (Register a) := (circuit a registered).step i s
    have cut : HoldCut s after := hold_edge registered i s input waiting unqualified (zero_budget loaded limit)
    have sampled := SegmentTrace.sampler_step registered i s (noReset input)
    obtain ⟨held, history⟩ := ih after newer (i .rawInputs) (sampled.2.trans recent) sampled.1
      (fun j hj => ordinary j (List.mem_cons_of_mem (α := Values Core.Input) i hj))
      cut.phase (loaded.same_word cut.pose.current) missed.2
    exact ⟨cut.trans held, ⟨input, unqualified, history⟩⟩

structure FirstQualified (g : Guard) (registered : Bool) (s : Values (Register a))
    (older newer : BitVec 2) (prior : List (Values Core.Input)) (last : Values Core.Input) : Prop where
  held : HoldCut s (run registered s prior)
  misses : MissHistory registered s prior
  sample : run registered s prior (.base .stage2) = sampleAfter older newer prior
  ready : SegmentTiming.ready last (run registered s prior) = 1#1

/-- A split selected from the raw tape gives the first runtime qualifier,
    together with the held active owner at that edge. -/
theorem first_qualified (registered : Bool) (s : Values (Register a)) (g : Guard)
    (older newer : BitVec 2) (prior : List (Values Core.Input)) (last : Values Core.Input)
    (old : s (.base .stage2) = older) (recent : s (.base .stage1) = newer)
    (ordinary : ∀ i ∈ prior, DrainInput i) (waiting : s (.base .phase) = 7#3)
    (loaded : LoadedGuard g s) (limit : g.limit = .unbounded)
    (missed : (samples older newer prior).any g.matches = false)
    (matched : g.matches (sampleAfter older newer prior) = true) :
    FirstQualified g registered s older newer prior last := by
  obtain ⟨held, history⟩ := hold_from_raw registered s g older newer prior old recent
    ordinary waiting loaded limit missed
  have sampled := sampler_sampleAfter registered s older newer prior old recent (fun i hi => noReset (ordinary i hi))
  exact ⟨held, history, sampled, by rw [(loaded.same_word held.pose.current).qualifies, sampled, matched]; rfl⟩

/-- A standalone wait resumes FETCH immediately after the first match. -/
theorem FirstQualified.resume {s : Values (Register a)}
    (window : FirstQualified g registered s older newer prior last)
    (ordinary : DrainInput last) (pins : Pins)
    (loaded : s (.base .currentWord) = encode (.driveWait pins g)) :
    SegmentWaitRefinement.WaitSuccess s (run registered s (prior ++ [@last])) := by
  let poll : Values (Register a) := run registered s prior
  have wordAtPoll := window.held.pose.current.trans loaded
  have matchAtPoll : g.matches (poll (.base .stage2)) = true := by
    have hit := window.ready
    rw [SegmentWaitRefinement.ready_from_wait last poll pins g wordAtPoll] at hit
    cases matchBit : g.matches (poll (.base .stage2)) <;> simp_all
  rw [run_append]
  have step := SegmentWaitRefinement.success_step registered last poll ordinary window.held.phase pins g
    wordAtPoll matchAtPoll
  exact ⟨step.phase, step.pc.trans (congrArg (· + 1#7) window.held.pc), step.countdown,
    ⟨step.pose.current.trans window.held.pose.current, step.pose.remaining.trans window.held.pose.remaining,
      step.pose.levels.trans window.held.pose.levels, step.pose.enabled.trans window.held.pose.enabled⟩,
    step.captured.trans window.held.captured, step.latched.trans window.held.latched,
    step.valid.trans window.held.valid⟩

/-- A guarded stream captures exactly the sample at its first match. -/
theorem FirstQualified.receive {s : Values (Register a)}
    (window : FirstQualified g registered s older newer prior last)
    (ordinary : DrainInput last) (cell : Cell) (receives : cell.receive = true)
    (loaded : s (.base .currentWord) = encode (.stream cell (some g))) :
    ReceiveCut s (run registered s prior) (run registered s (prior ++ [@last])) := by
  let poll : Values (Register a) := run registered s prior
  have wordAtPoll : poll (.base .currentWord) = encode (.stream cell (some g)) :=
    window.held.pose.current.trans loaded
  have fields := encode_fields (.stream cell (some g))
  have stream : (poll (.base .currentWord)).extractLsb' 0 3 = 1#3 := wordAtPoll ▸ fields.operation
  have receiveBit : (poll (.base .currentWord)).extractLsb' 35 1 = 1#1 := by
    rw [wordAtPoll, fields.receive]
    change BitVec.ofBool cell.receive = 1#1
    rw [receives]
    rfl
  rw [run_append]
  have step := receive_edge registered last poll ordinary window.held.phase window.ready stream receiveBit
  exact ⟨step.phase,
    ⟨step.pose.current.trans window.held.pose.current, step.pose.remaining.trans window.held.pose.remaining,
      step.pose.levels.trans window.held.pose.levels, step.pose.enabled.trans window.held.pose.enabled⟩,
    step.produced.trans (congrArg (· + 1#16) window.held.captured), step.valid, step.sample⟩

end Pinwheel.Hardware.StreamingReady.SegmentEventWait
