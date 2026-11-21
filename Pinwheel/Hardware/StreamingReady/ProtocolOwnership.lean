import Pinwheel.Hardware.StreamingReady.SessionProof
import Pinwheel.Hardware.StreamingReady.SegmentCustody

/-! An ownership settlement describes the drained cut immediately before
release, continued retention, or explicit warm cancellation. A reservation
can precede physical transmission of its bit, particularly at a missed
guard. The accounting therefore uses reservations, not wire edges. -/
namespace Pinwheel.Hardware.StreamingReady.ProtocolOwnership

open Pinwheel.Hardware Pinwheel.Program.StreamingReady

inductive Exit where
  | completed | earlyExit | timeout
  deriving DecidableEq, Repr

inductive Closure where
  | released | retained | cancelled
  deriving DecidableEq, Repr

structure Report where
  exit : Exit
  closure : Closure
  tag : Nat
  endingTag : Nat
  txAccepted : Nat
  txReserved : Nat
  txCancelled : Nat
  txOwned : Nat
  rxCaptured : Nat
  rxAcknowledged : Nat
  deriving DecidableEq, Repr

/-- In-program cancellation belongs to an early exit. A timeout still owns
its unused suffix at the drained cut, even if warm cancellation follows. -/
def Report.Valid (r : Report) : Prop :=
  r.txAccepted = r.txReserved + r.txCancelled + r.txOwned ∧
    r.rxCaptured = r.rxAcknowledged ∧ r.tag = r.endingTag ∧
    match r.exit with
    | .completed => r.closure = .released ∧ r.txCancelled = 0 ∧ r.txOwned = 0
    | .earlyExit => r.closure = .released ∧ r.txOwned = 0
    | .timeout => (r.closure = .retained ∨ r.closure = .cancelled) ∧ r.txCancelled = 0

instance (r : Report) : Decidable r.Valid := by
  cases r with
  | mk exit closure tag ending accepted reserved cancelled owned captured acknowledged =>
    cases exit <;> unfold Report.Valid <;> infer_instance

/-- The numeric settlement represents an ordered split of the actual accepted
bits. In particular, cancellation can only account for a suffix. -/
theorem Report.split_tx (r : Report) (valid : r.Valid) (accepted reserved : List Bool)
    (ordered : reserved <+: accepted) (acceptedCount : accepted.length = r.txAccepted)
    (reservedCount : reserved.length = r.txReserved) :
    ∃ cancelled owned : List Bool, accepted = reserved ++ cancelled ++ owned ∧
      cancelled.length = r.txCancelled ∧ owned.length = r.txOwned := by
  obtain ⟨tail, ht⟩ := ordered
  have len : tail.length = r.txCancelled + r.txOwned := by
    have total := valid.1
    rw [← acceptedCount, ← reservedCount, ← ht, List.length_append] at total
    omega
  refine ⟨tail.take r.txCancelled, tail.drop r.txCancelled, ?_, ?_, ?_⟩
  · rw [List.append_assoc, List.take_append_drop, ht]
  · simp [len]
  · rw [List.length_drop, len]
    omega

def ownerTag (generation transfer : BitVec 16) : Nat := (generation ++ transfer).toNat

def fixedReport (s after : Session.State a) : Report :=
  { exit := if s.core.phase = .completed then .completed else .timeout
    closure := .released
    tag := ownerTag s.core.generation s.core.transfer
    endingTag := ownerTag after.core.generation after.core.transfer
    txAccepted := s.core.txAccepted.toNat
    txReserved := s.core.txConsumed.toNat
    txCancelled := 0
    txOwned := 0
    rxCaptured := s.core.rxProduced.toNat
    rxAcknowledged := s.host.ackOffset.toNat }

/-- SPI's existing concrete START-to-RELEASE proof gives the same ledger with
empty cancelled and retained suffixes. -/
theorem fixed_release {rows : List Instruction} {idle : Pins} {image : Compiled rows idle}
    {rep : SourceRefinement.Image image.program} {actual : Package.State a}
    {s : Session.State a} {trace : BitTrace}
    (reached : InitializedCustody.Reached image actual s trace rep) (pin : Session.Pins)
    (ha : a ≤ 3) (runtime : Session.RuntimeInput s pin)
    (admitted : InitializedCustody.ActualRelease actual pin) (completed : s.core.phase = .completed) :
    let after := s.step image.program false pin
    (fixedReport s after).Valid ∧ after.core.phase = .free := by
  let cut := SessionProof.release_to_free reached pin ha runtime admitted
  have accepted := reached.custody.counts.accepted
  have reserved := reached.custody.counts.consumed
  have captured := reached.custody.counts.captured
  have tx : s.core.txAccepted.toNat = s.core.txConsumed.toNat := by
    rw [← accepted, ← reserved, cut.accounted.accepted]
  have rx : s.core.rxProduced.toNat = s.host.ackOffset.toNat := by
    rw [← captured, cut.accounted.exported, cut.accounted.ackOffset]
  exact ⟨by simp [fixedReport, Report.Valid, completed, tx, rx, cut.generation, cut.transfer], cut.free⟩

open SegmentCore

/-- RX drain may change the FIFO and frontend handoff, while the terminal
decision, counters and TX disposition remain fixed. -/
structure TerminalCut where
  phase : BitVec 3
  txClosed : BitVec 1
  generation : BitVec 16
  transfer : BitVec 16
  accepted : BitVec 16
  reserved : BitVec 16
  captured : BitVec 16
  deriving DecidableEq, Repr

def TerminalCut.of (s : Values (Register a)) : TerminalCut :=
  ⟨s (.base .phase), s .txClosed, s (.base .generation), s (.base .transfer),
    s (.base .txAccepted), s (.base .txConsumed), s (.base .rxProduced)⟩

def TerminalCut.Retained (cut : TerminalCut) : Prop := cut.phase = 5#3 ∨ cut.phase = 6#3

def DrainInput (i : Values Core.Input) : Prop :=
  i .initialize = 0#1 ∧ i .command = 0#4 ∧ i .txPush = 0#1

private theorem selected_step (registered : Bool) (i : Values Core.Input) (s : Values (Register a))
    (r : Core.Register a w) :
    (circuit a registered).step i s (.base r) = (nextBase r).eval i (withFetch s ((word registered).eval i s)) :=
  bindWord_eval _ _ _ _

private theorem selected_close (registered : Bool) (i : Values Core.Input) (s : Values (Register a)) :
    (circuit a registered).step i s .txClosed = (next .txClosed).eval i (withFetch s ((word registered).eval i s)) :=
  bindWord_eval _ _ _ _

private theorem inv_one_inv (value : BitVec 1) : ~~~(1#1 &&& ~~~value) = value := by decide +revert +kernel

set_option linter.unusedSimpArgs false in
theorem drain_step_preserves (registered : Bool) (i : Values Core.Input) (s : Values (Register a))
    (retained : (TerminalCut.of s).Retained) (drain : DrainInput i) :
    TerminalCut.of ((circuit a registered).step i s) = TerminalCut.of s := by
  obtain ⟨init, command, noPush⟩ := drain
  rcases retained with phase | phase <;>
    change s (.base .phase) = _ at phase <;>
    simp [TerminalCut.of, selected_step, selected_close, nextBase, next, originalNext, Expr.eval_bind,
      SegmentCore.discard, SegmentCore.control, setCount, branch, fetching, SegmentCore.either, SegmentCore.both,
      Expr.eval, usesEntryWord, runtimeInput, decodedRegister, lift, withFetch,
      Core.next, Core.nextRaw, Core.isPhase, Core.fetching, Core.clearedRuntime,
      Core.cold, Core.warm, Core.cmd, Core.resetting, Core.either, Core.both, Core.releasing,
      Core.starting, Core.free, Core.hostOwner, Core.owned, Core.busy, Core.identity, Core.retained,
      Core.committing, Core.pushing, Core.takingTX, Core.reserving, Core.lowEnd, Core.highEnd,
      Core.capturingRX, Core.capture, Core.guardedLowEnd, Core.waitSuccess, Core.standaloneSuccess,
      Core.waitFault, init, command, noPush, phase, inv_one_inv]

theorem drain_run_preserves (registered : Bool) (s : Values (Register a)) (inputs : List (Values Core.Input))
    (retained : (TerminalCut.of s).Retained) (drain : ∀ i ∈ inputs, DrainInput i) :
    TerminalCut.of (inputs.foldl (α := Values (Register a))
      (fun state i => (circuit a registered).step i state) s) = TerminalCut.of s := by
  induction inputs generalizing s with
  | nil => rfl
  | cons i inputs ih =>
    have preserved := drain_step_preserves registered i s retained (drain i List.mem_cons_self)
    have survives : (TerminalCut.of ((circuit a registered).step i s)).Retained := preserved ▸ retained
    exact (ih _ survives (fun j member => drain j
      (List.mem_cons_of_mem (α := Values Core.Input) i member))).trans preserved

/-- The same two receive cuts as in the fixed-length proof: the core has
handed over every captured bit, and the frontend's export interval is empty
at its exact acknowledged end. -/
structure AcknowledgedReceive (s : Values (Register a))
    (front : Values Streaming.Frontend.Register) : Prop where
  popped : s (.base .rxPopped) = s (.base .rxProduced)
  cleared : front .exportBits = 0#7
  start : front .ackOffset = front .exportStart
  endOffset : (front .exportStart).toNat + (front .exportBits).toNat = (s (.base .rxPopped)).toNat

theorem AcknowledgedReceive.exact {s : Values (Register a)} {front : Values Streaming.Frontend.Register}
    (drain : AcknowledgedReceive s front) : (s (.base .rxProduced)).toNat = (front .ackOffset).toNat := by
  have ending := drain.endOffset
  rw [drain.cleared, drain.popped, ← drain.start] at ending
  simpa using ending.symm

def segmentedReport (exit : Exit) (closure : Closure) (cancelled owned : Nat)
    (s after : Values (Register a)) (front : Values Streaming.Frontend.Register) : Report :=
  { exit := exit
    closure := closure
    tag := ownerTag (s (.base .generation)) (s (.base .transfer))
    endingTag := ownerTag (after (.base .generation)) (after (.base .transfer))
    txAccepted := (s (.base .txAccepted)).toNat
    txReserved := (s (.base .txConsumed)).toNat
    txCancelled := cancelled
    txOwned := owned
    rxCaptured := (s (.base .rxProduced)).toNat
    rxAcknowledged := (front .ackOffset).toNat }

inductive ReleasedTx (s : Values (Register a)) : Exit → Nat → Prop where
  | complete (used : s (.base .txAccepted) = s (.base .txConsumed)) : ReleasedTx s .completed 0
  | discard (closed : s .txClosed = 1#1)
      (ordered : (s (.base .txConsumed)).toNat ≤ (s (.base .txAccepted)).toNat) :
      ReleasedTx s .earlyExit ((s (.base .txAccepted)).toNat - (s (.base .txConsumed)).toNat)

/-- Completion and an early discard both settle the exact receive interval
and use the same owner-checked RELEASE proof on either instruction store. -/
theorem segmented_release (registered : Bool) (s : Values (Register a))
    (front : Values Streaming.Frontend.Register) (release : Values Core.Input)
    (atRelease : SegmentCustody.AtRelease release s) (drained : AcknowledgedReceive s front)
    (tx : ReleasedTx s exit cancelled) :
    let after : Values (Register a) := (circuit a registered).step release s
    (segmentedReport exit .released cancelled 0 s after front).Valid ∧ after (.base .phase) = 0#3 := by
  obtain ⟨phase, _, _, _, generation, transfer⟩ := SegmentCustody.release_after_drain registered release s atRelease
  refine ⟨⟨?_, drained.exact, ?_, ?_⟩, phase⟩
  · cases tx with
    | complete used => simp [segmentedReport, used]
    | discard _ ordered => exact (Nat.add_sub_of_le ordered).symm
  · simp [segmentedReport, generation, transfer]
  · cases tx <;> simp [segmentedReport]

/-- Early halt moves the accepted-but-unreserved suffix out of TX custody,
while arbitrary ordinary RX-drain edges preserve the terminal counters.
The resulting ownership ledger has the same release rule as completion. -/
theorem early_exit_release (registered : Bool) (before : Values (Register a)) (discardInput : Values Core.Input)
    (atDiscard : SegmentCustody.AtDiscard registered discardInput before)
    (ordered : (before (.base .txConsumed)).toNat ≤ (before (.base .txAccepted)).toNat)
    (inputs : List (Values Core.Input)) (ordinary : ∀ i ∈ inputs, DrainInput i)
    (front : Values Streaming.Frontend.Register) (release : Values Core.Input) :
    let halted : Values (Register a) := (circuit a registered).step discardInput before
    let drained : Values (Register a) := inputs.foldl (α := Values (Register a))
      (fun state i => (circuit a registered).step i state) halted
    SegmentCustody.AtRelease release drained → AcknowledgedReceive drained front →
      let after : Values (Register a) := (circuit a registered).step release drained
      let cancelled := (before (.base .txAccepted)).toNat - (before (.base .txConsumed)).toNat
      (segmentedReport .earlyExit .released cancelled 0 drained after front).Valid ∧
      drained (.base .generation) = before (.base .generation) ∧
      drained (.base .transfer) = before (.base .transfer) ∧
      drained (.base .rxProduced) = before (.base .rxProduced) ∧
      after (.base .phase) = 0#3 := by
  intro halted drained atRelease received after cancelled
  have discard := SegmentCustody.discard_preserves_custody registered discardInput before atDiscard
  have preserved : TerminalCut.of drained = TerminalCut.of halted :=
    drain_run_preserves registered halted inputs (Or.inl discard.completed) ordinary
  have accepted := congrArg TerminalCut.accepted preserved
  have reserved := congrArg TerminalCut.reserved preserved
  have captured := congrArg TerminalCut.captured preserved
  have ownerGeneration := congrArg TerminalCut.generation preserved
  have ownerTransfer := congrArg TerminalCut.transfer preserved
  have closed := congrArg TerminalCut.txClosed preserved
  simp only [TerminalCut.of] at accepted reserved closed
  have acceptedBefore := accepted.trans discard.accepted
  have reservedBefore := reserved.trans discard.sent
  have txOrder : (drained (.base .txConsumed)).toNat ≤ (drained (.base .txAccepted)).toNat := by
    rwa [acceptedBefore, reservedBefore]
  have tx : ReleasedTx drained .earlyExit cancelled := by
    have amount : cancelled = (drained (.base .txAccepted)).toNat - (drained (.base .txConsumed)).toNat := by
      rw [acceptedBefore, reservedBefore]
    rw [amount]
    exact .discard (closed.trans discard.closed) txOrder
  obtain ⟨valid, phase⟩ := segmented_release registered drained front release atRelease received tx
  exact ⟨valid, ownerGeneration.trans discard.owner.1, ownerTransfer.trans discard.owner.2,
    captured.trans discard.captured, phase⟩

/-- The ordinary sampled deadline cut. `ready` reads the second sampler, so
an electrical transition later than this evaluation does not advance RX. -/
structure AtDeadline (i : Values Core.Input) (s : Values (Register a)) : Prop where
  ordinary : DrainInput i
  waiting : s (.base .phase) = 7#3
  ready : Core.waitReady.eval i (project s) = 0#1
  bounded : Core.guardBudget.eval i (project s) ≠ 0#8
  expired : s (.base .countdown) = 0#8

set_option linter.unusedSimpArgs false in
/-- Timeout retains accepted TX and the captured prefix, and flushes the
partial RX register. It does not manufacture a capture for the failed cell. -/
theorem deadline_step (registered : Bool) (i : Values Core.Input) (s : Values (Register a))
    (cut : AtDeadline i s) :
    let next : Values (Register a) := (circuit a registered).step i s
    TerminalCut.of next = { TerminalCut.of s with phase := 6#3 } ∧
      next (.base .txCount) = s (.base .txCount) ∧
      next (.base .txValid) = s (.base .txValid) ∧ next (.base .rxUsed) = 0#6 := by
  dsimp only
  obtain ⟨init, command, noPush⟩ := cut.ordinary
  have notReady := cut.ready
  have bounded := cut.bounded
  simp [Core.waitReady, Core.guardMask, Core.guardExpected, Core.field, project, Expr.eval] at notReady
  have notMatching : (s (.base .stage2) &&& ((s (.base .currentWord)).extractLsb' 50 2)) ≠
      (s (.base .currentWord)).extractLsb' 52 2 := by
    exact of_decide_eq_false notReady
  simp [Core.guardBudget, Core.field, project, Expr.eval] at bounded
  simp [TerminalCut.of, selected_step, selected_close, nextBase, next, originalNext, Expr.eval_bind,
    SegmentCore.discard, SegmentCore.control, setCount, branch, fetching, SegmentCore.either, SegmentCore.both,
    Expr.eval, usesEntryWord, runtimeInput, decodedRegister, lift, withFetch,
    Core.next, Core.nextRaw, Core.isPhase, Core.fetching, Core.clearedRuntime,
    Core.cold, Core.warm, Core.cmd, Core.resetting, Core.either, Core.both, Core.releasing,
    Core.starting, Core.free, Core.hostOwner, Core.owned, Core.busy, Core.identity, Core.retained,
    Core.committing, Core.pushing, Core.takingTX, Core.reserving, Core.lowEnd, Core.highEnd,
    Core.capturingRX, Core.capture, Core.guardedLowEnd, Core.waitSuccess, Core.standaloneSuccess,
    Core.waitFault, Core.waitReady, Core.guardBudget, Core.guardMask, Core.guardExpected, Core.field,
    Core.queueCount, Core.loadingTX, init, command, noPush, cut.waiting, cut.expired, notMatching, bounded, inv_one_inv]

set_option linter.unusedSimpArgs false in
/-- Explicit warm cancellation frees a retained owner and clears its queues
and validity. The previous generation and transfer counters survive. -/
theorem cancel_step (registered : Bool) (i : Values Core.Input) (s : Values (Register a))
    (init : i .initialize = 0#1) (command : i .command = 15#4) :
    let after : Values (Register a) := (circuit a registered).step i s
    after (.base .phase) = 0#3 ∧ after .txClosed = 0#1 ∧
      after (.base .valid) = 0#1 ∧ after (.base .txCount) = 0#4 ∧
      after (.base .txValid) = 0#6 ∧ after (.base .rxCount) = 0#4 ∧ after (.base .rxUsed) = 0#6 ∧
      after (.base .generation) = s (.base .generation) ∧ after (.base .transfer) = s (.base .transfer) := by
  dsimp only
  simp [selected_step, selected_close, nextBase, next, originalNext, Expr.eval_bind,
    SegmentCore.discard, SegmentCore.control, setCount, branch, fetching, SegmentCore.either, SegmentCore.both,
    Expr.eval, usesEntryWord, runtimeInput, decodedRegister, lift, withFetch,
    Core.next, Core.nextRaw, Core.isPhase, Core.fetching, Core.clearedRuntime,
    Core.cold, Core.warm, Core.cmd, Core.resetting, Core.either, Core.both, Core.releasing,
    Core.starting, Core.free, Core.hostOwner, Core.owned, Core.busy, Core.identity, Core.retained,
    Core.writing, Core.committing, init, command]

set_option linter.unusedSimpArgs false in
/-- Ordinary RELEASE keeps a timed-out transfer retained while there is
still accepted TX in the queue or shifter, including after RX has drained. -/
theorem timeout_rejects_release (registered : Bool) (i : Values Core.Input) (s : Values (Register a))
    (init : i .initialize = 0#1) (command : i .command = 4#4) (fault : s (.base .phase) = 6#3)
    (owned : s (.base .txCount) ≠ 0#4 ∨ s (.base .txValid) ≠ 0#6) :
    (circuit a registered).observe i s .rejected = 1#1 ∧
      (circuit a registered).step i s (.base .phase) = 6#3 := by
  have rejected : (circuit a registered).observe i s .rejected =
      (output .rejected).eval i (withFetch s ((word registered).eval i s)) := bindWord_eval _ _ _ _
  rw [rejected, selected_step]
  rcases owned with pending | pending <;>
    simp [output, Core.output, Core.rejected, nextBase, originalNext, Expr.eval_bind,
      SegmentCore.discard, SegmentCore.control, setCount, branch, fetching, SegmentCore.either, SegmentCore.both,
      Expr.eval, usesEntryWord, runtimeInput, decodedRegister, lift, withFetch,
      Core.next, Core.nextRaw, Core.isPhase, Core.fetching, Core.clearedRuntime,
      Core.cold, Core.warm, Core.cmd, Core.resetting, Core.either, Core.both, Core.releasing, Core.drained,
      Core.starting, Core.free, Core.hostOwner, Core.owned, Core.busy, Core.identity, Core.retained,
      Core.writing, Core.committing, Core.reserving, Core.guardedLowEnd, Core.lowEnd, Core.highEnd,
      Core.capture, Core.waitSuccess, Core.standaloneSuccess, Core.waitFault, init, command, fault, pending]

private theorem timeout_report (s after : Values (Register a)) (front : Values Streaming.Frontend.Register)
    (closure : Closure) (wasFault : closure = .retained ∨ closure = .cancelled)
    (received : AcknowledgedReceive s front)
    (ordered : (s (.base .txConsumed)).toNat ≤ (s (.base .txAccepted)).toNat)
    (generation : after (.base .generation) = s (.base .generation))
    (transfer : after (.base .transfer) = s (.base .transfer)) :
    (segmentedReport .timeout closure 0
      ((s (.base .txAccepted)).toNat - (s (.base .txConsumed)).toNat) s after front).Valid := by
  refine ⟨?_, received.exact, ?_, wasFault, rfl⟩
  · exact (Nat.add_sub_of_le ordered).symm
  · simp [segmentedReport, generation, transfer]

/-- A sampled timeout and the following drain leave the original captured
prefix with the same owner. An explicit warm cancellation returns it to a
free uninstalled state without retrospectively calling unsent TX reserved. -/
theorem timeout_after_drain (registered : Bool) (i : Values Core.Input) (before : Values (Register a))
    (deadline : AtDeadline i before)
    (ordered : (before (.base .txConsumed)).toNat ≤ (before (.base .txAccepted)).toNat)
    (inputs : List (Values Core.Input)) (ordinary : ∀ j ∈ inputs, DrainInput j)
    (front : Values Streaming.Frontend.Register) :
    let fault : Values (Register a) := (circuit a registered).step i before
    let drained : Values (Register a) := inputs.foldl (α := Values (Register a))
      (fun state j => (circuit a registered).step j state) fault
    let owned := (before (.base .txAccepted)).toNat - (before (.base .txConsumed)).toNat
    AcknowledgedReceive drained front →
      (segmentedReport .timeout .retained 0 owned drained drained front).Valid ∧
      drained (.base .phase) = 6#3 ∧
      drained (.base .rxProduced) = before (.base .rxProduced) ∧
      drained (.base .generation) = before (.base .generation) ∧
      drained (.base .transfer) = before (.base .transfer) ∧
      ∀ cancel : Values Core.Input, cancel .initialize = 0#1 → cancel .command = 15#4 →
        let after : Values (Register a) := (circuit a registered).step cancel drained
        (segmentedReport .timeout .cancelled 0 owned drained after front).Valid ∧
          after (.base .phase) = 0#3 ∧ after (.base .valid) = 0#1 := by
  intro fault drained owned received
  have didFault : TerminalCut.of fault = { TerminalCut.of before with phase := 6#3 } :=
    (deadline_step registered i before deadline).1
  have retained : (TerminalCut.of fault).Retained := by rw [didFault]; exact Or.inr rfl
  have joined := (drain_run_preserves registered fault inputs retained ordinary).trans didFault
  have phase : drained (.base .phase) = 6#3 := congrArg TerminalCut.phase joined
  have accepted : drained (.base .txAccepted) = before (.base .txAccepted) := congrArg TerminalCut.accepted joined
  have reserved : drained (.base .txConsumed) = before (.base .txConsumed) := congrArg TerminalCut.reserved joined
  have order : (drained (.base .txConsumed)).toNat ≤ (drained (.base .txAccepted)).toNat := by
    rwa [accepted, reserved]
  have amount : owned = (drained (.base .txAccepted)).toNat - (drained (.base .txConsumed)).toNat := by
    rw [accepted, reserved]
  refine ⟨?_, phase, congrArg TerminalCut.captured joined, congrArg TerminalCut.generation joined,
    congrArg TerminalCut.transfer joined, ?_⟩
  · rw [amount]
    exact timeout_report drained drained front .retained (Or.inl rfl) received order rfl rfl
  · intro cancel init command after
    obtain ⟨free, _, invalid, _, _, _, _, generation, transfer⟩ := cancel_step registered cancel drained init command
    rw [amount]
    exact ⟨timeout_report drained after front .cancelled (Or.inr rfl) received order generation transfer, free, invalid⟩

end Pinwheel.Hardware.StreamingReady.ProtocolOwnership
