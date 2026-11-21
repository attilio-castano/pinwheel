import Pinwheel.Hardware.StreamingReady.SegmentPathControl
import Pinwheel.Hardware.StreamingReady.SegmentTiming
import Pinwheel.Program.StreamingReadySegmentExecution

/-! Interpret source guard observations from actual reached samples of the
    segmented circuit. Each observation belongs to the state before its edge. -/
namespace Pinwheel.Hardware.StreamingReady.SegmentPollRefinement

open Pinwheel.Hardware SegmentCore
open Pinwheel.Program.StreamingReady (Cell Guard WaitLimit encode encode_fields)
open Pinwheel.Program.StreamingReadySegments (Row)
open Pinwheel.Program.StreamingReadySegments.Execution (pollWindow pollWindow_after_misses)
open ProtocolOwnership (DrainInput)
open SegmentTiming
open SegmentPathControl

def stage2Samples (registered : Bool) (s : Values (Register a)) :
    List (Values Core.Input) → List (BitVec 2)
  | [] => []
  | i :: rest => s (.base .stage2) ::
      stage2Samples registered ((circuit a registered).step i s) rest

@[simp] theorem stage2Samples_length (registered : Bool) (s : Values (Register a))
    (inputs : List (Values Core.Input)) :
    (stage2Samples registered s inputs).length = inputs.length := by
  induction inputs generalizing s with
  | nil => rfl
  | cons i rest ih => simp [stage2Samples, ih]

private theorem stage2Samples_miss (registered : Bool) (s : Values (Register a))
    (cell : Cell) (g : Guard) (waiting : s (.base .phase) = 7#3)
    (loaded : s (.base .currentWord) = encode (.stream cell (some g)))
    (bounded : guardBudget s ≠ 0#8) (inputs : List (Values Core.Input))
    (history : MissHistory registered s inputs) (within : inputs.length ≤ (s (.base .countdown)).toNat) :
    (stage2Samples registered s inputs).any g.matches = false := by
  induction inputs generalizing s with
  | nil => rfl
  | cons i rest ih =>
    obtain ⟨ordinary, notReady, later⟩ := history
    have before := ready_from_row i s cell g loaded
    rw [notReady] at before
    have miss : g.matches (s (.base .stage2)) = false := by
      cases hit : g.matches (s (.base .stage2)) <;> simp [hit] at before ⊢
    have single : MissHistory registered s [@i] := ⟨ordinary, notReady, trivial⟩
    have one : [@i].length ≤ (s (.base .countdown)).toNat := by
      simp only [List.length_cons, List.length_nil]
      simp only [List.length_cons] at within
      omega
    have first : MissCut s ((circuit a registered).step i s) 1 :=
      miss_prefix registered s [@i] waiting bounded single one
    have nextBounded : guardBudget ((circuit a registered).step i s) ≠ 0#8 := by
      simpa only [guardBudget, first.pose.current] using bounded
    have nextWithin : rest.length ≤ (((circuit a registered).step i s) (.base .countdown)).toNat := by
      rw [first.countdown]
      simp only [List.length_cons] at within
      omega
    have tail := ih _ first.phase (first.pose.current.trans loaded) nextBounded later nextWithin
    simp [stage2Samples, miss, tail]

theorem rxBit_from_row (s : Values (Register a)) (cell : Cell) (g : Guard)
    (loaded : s (.base .currentWord) = encode (.stream cell (some g))) :
    rxBit s = BitVec.ofBool ((s (.base .stage2))[cell.rxInput.val]) := by
  rw [rxBit, loaded, (encode_fields (.stream cell (some g))).rxInput]
  rw [← BitVec.getLsbD_eq_getElem]
  have slice (x : BitVec 2) (idx : Nat) :
      x.extractLsb' idx 1 = BitVec.ofBool (x.getLsbD idx) := by
    rw [BitVec.getLsbD_eq_extractLsb']
    rcases BitVec.eq_zero_or_eq_one (x.extractLsb' idx 1) with h | h <;> simp [h]
  have bound := cell.rxInput.isLt
  have selector : cell.rxInput.val = 0 ∨ cell.rxInput.val = 1 := by omega
  rcases selector with selector | selector <;>
    simp [Program.StreamingReady.Instruction.cell, selector, slice]
  done

/-- The guarded stream converges on the same source observation and latch
    as the circuit. A final miss has the source timeout verdict and the
    hardware retains the owner with its previous receive prefix. -/
theorem guarded_stream_poll (registered : Bool) (s : Values (Register a)) (cell : Cell) (g : Guard)
    (n : Fin 255) (limit : g.limit = .misses n) (receive : cell.receive = true)
    (arm last : Values Core.Input) (misses : List (Values Core.Input))
    (armOrdinary : DrainInput arm) (lastOrdinary : DrainInput last)
    (low : s (.base .phase) = 3#3) (elapsed : s (.base .countdown) = 0#8)
    (loaded : s (.base .currentWord) = encode (.stream cell (some g)))
    (history : MissHistory registered ((circuit a registered).step arm s) misses)
    (within : misses.length ≤ n.val) :
    let entered : Values (Register a) := (circuit a registered).step arm s
    let poll : Values (Register a) := run registered entered misses
    let after : Values (Register a) := run registered s ((@arm) :: misses ++ [@last])
    let heldSample := poll (.base .stage2)
    let verdict := pollWindow g (stage2Samples registered entered misses ++ [heldSample])
    (verdict =
      if g.matches heldSample then some (some heldSample)
      else if misses.length == n.val then some none else none) ∧
    (∀ sample, verdict = some (some sample) →
      ReceiveCut entered poll after ∧ after .lastCapture = BitVec.ofBool sample[cell.rxInput.val]) ∧
    (verdict = some none → TimeoutCut poll after) := by
  let entered : Values (Register a) := (circuit a registered).step arm s
  let poll : Values (Register a) := run registered entered misses
  have hardware := guarded_stream_window registered s cell g n limit arm last misses
    armOrdinary lastOrdinary low elapsed loaded history within
  have word : entered (.base .currentWord) = encode (.stream cell (some g)) :=
    hardware.1.current.trans loaded
  have bounded : guardBudget entered ≠ 0#8 := by
    rw [guardBudget, word, (encode_fields (.stream cell (some g))).guardBudget]
    change g.limit.budget ≠ 0#8
    rw [limit]
    exact SourceRefinement.budget_nonzero n
  have count : (entered (.base .countdown)).toNat = n.val := by
    have countdown : entered (.base .countdown) = g.limit.initialCountdown := hardware.1.countdown
    rw [countdown, limit]
    simpa [WaitLimit.initialCountdown, BitVec.toNat_ofNat] using
      (Nat.mod_eq_of_lt (show n.val < 256 by omega))
  have prior := stage2Samples_miss registered entered cell g hardware.1.phase word
    bounded misses history (count ▸ within)
  have verdict := pollWindow_after_misses g n limit (stage2Samples registered entered misses)
    (poll (.base .stage2)) prior (by simpa using within)
  rw [stage2Samples_length] at verdict
  refine ⟨verdict, ?_, ?_⟩
  · intro sample qualified
    change pollWindow g (stage2Samples registered entered misses ++ [poll (.base .stage2)]) =
      some (some sample) at qualified
    rw [verdict] at qualified
    cases hit : g.matches (poll (.base .stage2)) with
    | false =>
      by_cases final : misses.length = n.val <;> simp [hit, final] at qualified
    | true =>
      have same : poll (.base .stage2) = sample := by simpa [hit] using qualified
      have captured := hardware.2.2.1 hit receive
      have pollWord : poll (.base .currentWord) = encode (.stream cell (some g)) :=
        hardware.2.1.pose.current.trans word
      refine ⟨captured, captured.sample.trans ?_⟩
      rw [rxBit_from_row poll cell g pollWord]
      simp only [same]
  · intro expired
    change pollWindow g (stage2Samples registered entered misses ++ [poll (.base .stage2)]) =
      some none at expired
    rw [verdict] at expired
    cases hit : g.matches (poll (.base .stage2)) with
    | true => simp [hit] at expired
    | false =>
      have final : misses.length = n.val := by
        by_cases same : misses.length = n.val
        · exact same
        · simp [hit, same] at expired
      exact hardware.2.2.2 hit final
  done

private structure RowFrame (s after : Values (Register a)) : Prop where
  image : ImageFrame s after
  owner : OwnerFrame s after
  pc : after (.base .pc) = s (.base .pc)

private theorem RowFrame.refl (s : Values (Register a)) : RowFrame s s :=
  ⟨⟨rfl, rfl, fun _ => rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, rfl⟩

private theorem join_owner {s mid after : Values (Register a)}
    (before : OwnerFrame s mid) (afterwards : OwnerFrame mid after) : OwnerFrame s after :=
  ⟨afterwards.generation.trans before.generation, afterwards.transfer.trans before.transfer,
    afterwards.total.trans before.total⟩

private theorem RowFrame.trans {s mid after : Values (Register a)}
    (first : RowFrame s mid) (second : RowFrame mid after) : RowFrame s after :=
  ⟨⟨second.image.count.trans first.image.count, second.image.valid.trans first.image.valid,
    fun address => (second.image.word address).trans (first.image.word address),
    second.image.generation.trans first.image.generation⟩,
  join_owner first.owner second.owner, second.pc.trans first.pc⟩

private theorem ordinary_of_drain (i : Values Core.Input) (drain : DrainInput i) : NoReset i :=
  ⟨drain.1, by simp [drain.2.1]⟩

set_option linter.unusedSimpArgs false in
private theorem frame_edge (registered : Bool) (i : Values Core.Input) (s : Values (Register a))
    (drain : DrainInput i) (active : s (.base .phase) = 3#3 ∨ s (.base .phase) = 7#3)
    (stream : IsStream s) : RowFrame s ((circuit a registered).step i s) := by
  have ordinary := ordinary_of_drain i drain
  have image := image_frame registered i s ordinary (Or.inl (by rcases active with h | h <;> simp [h]))
  have owner := active_owner_frame registered i s ordinary
    (by rcases active with h | h <;> simp [h])
    (by rcases active with h | h <;> simp [h])
    (by rcases active with h | h <;> simp [h])
  refine ⟨image, owner, ?_⟩
  change (bindWord (word registered) (nextBase .pc)).eval i s = _
  rw [bindWord_eval]
  have operation : (s (.base .currentWord)).extractLsb' 0 3 = 1#3 := stream
  rcases active with phase | phase <;>
    simp [nextBase, originalNext, Expr.eval_bind, usesEntryWord, runtimeInput,
      withFetch, Expr.eval, Core.next, Core.nextRaw, Core.cold, Core.warm, Core.resetting,
      Core.cmd, Core.both, Core.either, Core.free, Core.starting, Core.releasing, Core.hostOwner,
      Core.owned, Core.retained, Core.isPhase, Core.fetching, Core.advancing, Core.highEnd,
      Core.standaloneSuccess, Core.waitSuccess, Core.stream, Core.field, lift, decodedRegister,
      SegmentCore.discard, branch, setCount, fetching, both, either, drain.1, drain.2.1, phase, operation] <;> done

private theorem miss_frames (registered : Bool) (s : Values (Register a)) (inputs : List (Values Core.Input))
    (waiting : s (.base .phase) = 7#3) (stream : IsStream s) (bounded : guardBudget s ≠ 0#8)
    (history : MissHistory registered s inputs) (within : inputs.length ≤ (s (.base .countdown)).toNat) :
    RowFrame s (run registered s inputs) := by
  induction inputs generalizing s with
  | nil => exact RowFrame.refl s
  | cons i rest ih =>
    obtain ⟨ordinary, miss, later⟩ := history
    have one : [@i].length ≤ (s (.base .countdown)).toNat := by
      simp only [List.length_cons, List.length_nil]
      simp only [List.length_cons] at within
      omega
    let after : Values (Register a) := (circuit a registered).step i s
    have step : MissCut s after 1 :=
      miss_prefix registered s [@i] waiting bounded ⟨ordinary, miss, trivial⟩ one
    have nextBounded : guardBudget after ≠ 0#8 := by
      simpa only [guardBudget, step.pose.current] using bounded
    have nextWithin : rest.length ≤ (after (.base .countdown)).toNat := by
      rw [step.countdown]
      simp only [List.length_cons] at within
      omega
    have nextStream : IsStream after := by simpa only [IsStream, step.pose.current] using stream
    exact (frame_edge registered i s ordinary (.inr waiting) stream).trans
      (ih after step.phase nextStream nextBounded later nextWithin)

set_option linter.unusedSimpArgs false in
theorem high_countdown (registered : Bool) (i : Values Core.Input) (s : Values (Register a))
    (cell : Cell) (g : Guard) (drain : DrainInput i)
    (waiting : s (.base .phase) = 7#3) (hit : g.matches (s (.base .stage2)) = true)
    (loaded : s (.base .currentWord) = encode (.stream cell (some g))) :
    ((circuit a registered).step i s) (.base .countdown) = BitVec.ofNat 8 cell.highDuration.val := by
  change (bindWord (word registered) (nextBase .countdown)).eval i s = _
  rw [bindWord_eval]
  have fields := encode_fields (.stream cell (some g))
  have operation : (s (.base .currentWord)).extractLsb' 0 3 = 1#3 := loaded ▸ fields.operation
  have period : (s (.base .currentWord)).extractLsb' 11 8 = BitVec.ofNat 8 cell.highDuration.val :=
    loaded ▸ fields.highDuration
  have ready : ready i s = 1#1 := by rw [ready_from_row i s cell g loaded, hit]; rfl
  simp only [SegmentTiming.ready, Core.waitReady, Core.guardMask, Core.guardExpected, Core.field,
    Expr.eval, project] at ready
  have matchSample := of_decide_eq_true (BitVec.ofBool_eq_iff_eq.mp (show BitVec.ofBool _ = BitVec.ofBool true
    from ready))
  simp [nextBase, originalNext, Expr.eval_bind, usesEntryWord, runtimeInput, withFetch, Expr.eval,
    Core.next, Core.nextRaw, Core.cold, Core.warm, Core.resetting, Core.cmd, Core.both, Core.either,
    Core.free, Core.starting, Core.releasing, Core.hostOwner, Core.owned, Core.retained, Core.isPhase,
    Core.fetching, Core.enteringCell, Core.entryWait, Core.reserving, Core.lowEnd, Core.guardedLowEnd,
    Core.capture, Core.standaloneSuccess, Core.waitSuccess, Core.waitReady, Core.guardMask,
    Core.guardExpected, Core.field, Core.stream, Core.waitDecrement, Core.clearedRuntime, Core.guardBudget,
    lift, decodedRegister,
    SegmentCore.discard, branch, setCount, fetching, both, either, drain.1, drain.2.1, waiting,
    operation, period, matchSample] <;> done

/-- A qualified last-slot poll and the following encoded branch are one
    circuit run. The successor is chosen by the source poll's sampled bit,
    even when the input changes during the HIGH dwell or the branch edge. -/
theorem qualified_last_slot_to_branch (registered : Bool) (s : Values (Register a))
    (rows : List Row) (pc : Nat) (cell : Cell) (g : Guard) (n : Fin 255)
    (limit : g.limit = .misses n) (receive : cell.receive = true)
    (arm pollLast highLast branchInput : Values Core.Input)
    (misses highHolds : List (Values Core.Input))
    (armOrdinary : DrainInput arm) (lastOrdinary : DrainInput pollLast)
    (highOrdinary : ∀ i ∈ highHolds, NoReset i) (endOrdinary : NoReset highLast)
    (branchOrdinary : NoReset branchInput)
    (low : s (.base .phase) = 3#3) (elapsed : s (.base .countdown) = 0#8)
    (loaded : s (.base .currentWord) = encode (.stream cell (some g)))
    (installed : Installed rows s) (position : (s (.base .pc)).toNat = pc)
    (finalSlot : s (.base .remaining) = 1#16)
    (history : MissHistory registered ((circuit a registered).step arm s) misses)
    (within : misses.length ≤ n.val) (holdDuration : highHolds.length = cell.highDuration.val)
    (qualified : g.matches (run registered ((circuit a registered).step arm s) misses (.base .stage2)) = true)
    (destination : BitVec 6) (onBit : Bool) (next : rows[pc + 1]? = some (.branch destination onBit))
    (forward : pc + 1 < destination.toNat) (inBounds : destination.toNat < rows.length) :
    let entered : Values (Register a) := (circuit a registered).step arm s
    let atPoll : Values (Register a) := run registered entered misses
    let sample := atPoll (.base .stage2)
    let acquired : Values (Register a) := run registered s ((@arm) :: misses ++ [@pollLast])
    let fetched : Values (Register a) := run registered acquired (highHolds ++ [@highLast])
    let after : Values (Register a) := (circuit a registered).step branchInput fetched
    let capture := sample[cell.rxInput.val]
    pollWindow g (stage2Samples registered entered misses ++ [sample]) = some (some sample) ∧
      AtBoundary registered rows (if capture = onBit then destination.toNat else pc + 2) none after ∧
      OwnerFrame s after := by
  let entered : Values (Register a) := (circuit a registered).step arm s
  let atPoll : Values (Register a) := run registered entered misses
  let sample := atPoll (.base .stage2)
  let acquired : Values (Register a) := run registered s ((@arm) :: misses ++ [@pollLast])
  let fetched : Values (Register a) := run registered acquired (highHolds ++ [@highLast])
  let capture := sample[cell.rxInput.val]
  have hardware := guarded_stream_window registered s cell g n limit arm pollLast misses
    armOrdinary lastOrdinary low elapsed loaded history within
  have source := guarded_stream_poll registered s cell g n limit receive arm pollLast misses
    armOrdinary lastOrdinary low elapsed loaded history within
  have hit : g.matches sample = true := qualified
  have verdict : pollWindow g (stage2Samples registered entered misses ++ [sample]) = some (some sample) := by
    have value := source.1
    change pollWindow g (stage2Samples registered entered misses ++ [sample]) =
      (if g.matches sample then some (some sample)
        else if misses.length == n.val then some none else none) at value
    simpa only [hit, if_true] using value
  obtain ⟨received, latch⟩ := source.2.1 sample verdict
  have entryWord : entered (.base .currentWord) = encode (.stream cell (some g)) :=
    hardware.1.current.trans loaded
  have pollWord : atPoll (.base .currentWord) = encode (.stream cell (some g)) :=
    hardware.2.1.pose.current.trans entryWord
  have fields := encode_fields (.stream cell (some g))
  have bounded : guardBudget entered ≠ 0#8 := by
    rw [guardBudget, entryWord, fields.guardBudget]
    change g.limit.budget ≠ 0#8
    rw [limit]
    exact SourceRefinement.budget_nonzero n
  have entryCount : (entered (.base .countdown)).toNat = n.val := by
    have countdown : entered (.base .countdown) = g.limit.initialCountdown := hardware.1.countdown
    rw [countdown, limit]
    simpa [WaitLimit.initialCountdown, BitVec.toNat_ofNat] using
      (Nat.mod_eq_of_lt (show n.val < 256 by omega))
  have receiveEq : @acquired = @Circuit.step _ _ _ (circuit a registered) pollLast atPoll := by
    change @run a registered entered (misses ++ [@pollLast]) = _
    rw [run_append]
    rfl
  have frames : RowFrame s acquired := by
    rw [receiveEq]
    have stream (state : Values (Register a))
        (current : state (.base .currentWord) = encode (.stream cell (some g))) : IsStream state := by
      change (state (.base .currentWord)).extractLsb' 0 3 = 1#3
      rw [current]
      exact fields.operation
    have initial := frame_edge registered arm s armOrdinary (.inl low) (stream s loaded)
    have wait := miss_frames registered entered misses hardware.1.phase (stream entered entryWord)
      bounded history (entryCount ▸ within)
    have last := frame_edge registered pollLast atPoll lastOrdinary (.inr hardware.2.1.phase)
      (stream atPoll pollWord)
    exact initial.trans (wait.trans last)
  have duration : highHolds.length = (acquired (.base .countdown)).toNat := by
    rw [receiveEq, high_countdown registered pollLast atPoll cell g lastOrdinary hardware.2.1.phase hit pollWord,
      holdDuration, BitVec.toNat_ofNat]
    exact (Nat.mod_eq_of_lt (show cell.highDuration.val < 256 from cell.highDuration.isLt)).symm
  have remain : acquired (.base .remaining) = 1#16 :=
    received.pose.remaining.trans (hardware.1.remaining.trans finalSlot)
  have slot : ¬(IsStream acquired ∧ 1 < (acquired (.base .remaining)).toNat) := by simp [remain]
  have rowBound : pc < rows.length := by
    have found := List.getElem?_eq_some_iff.mp next |>.1
    omega
  have latched : HasCapture acquired (some capture) := ⟨received.valid, latch⟩
  have boundary : AtBoundary registered rows (pc + 1) (some capture) fetched :=
    high_to_boundary registered acquired highHolds highLast highOrdinary endOrdinary received.phase duration
      slot (frames.image.installed installed) ((congrArg BitVec.toNat frames.pc).trans position) rowBound latched
  refine ⟨verdict, branch_step boundary branchInput branchOrdinary next forward inBounds, ?_⟩
  let held : Values (Register a) := run registered acquired highHolds
  have high := high_prefix registered acquired highHolds highOrdinary received.phase
    (Nat.le_of_eq duration) latched
  have highPhase : held (.base .phase) = 4#3 := high.phase
  have finished : OwnerFrame held fetched := by
    unfold fetched
    rw [run_append]
    exact active_owner_frame registered highLast held endOrdinary
      (by simp [highPhase]) (by simp [highPhase]) (by simp [highPhase])
  have branch := active_owner_frame registered branchInput fetched branchOrdinary
    (by simp [boundary.phase]) (by simp [boundary.phase]) (by simp [boundary.phase])
  exact join_owner frames.owner (join_owner high.owner (join_owner finished branch))
  done

end Pinwheel.Hardware.StreamingReady.SegmentPollRefinement
