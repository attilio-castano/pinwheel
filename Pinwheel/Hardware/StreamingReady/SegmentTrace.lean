import Pinwheel.Hardware.StreamingReady.SegmentTransaction

/-! Whole-trace accounting for an active segmented exchange. The observed bits
    come from the same pre-edge expressions that drive reservation and capture. -/
namespace Pinwheel.Hardware.StreamingReady.SegmentTrace

open Pinwheel.Hardware SegmentCore SegmentPathControl SegmentTransaction
open SegmentTiming (run)
open Pinwheel.Program.StreamingReadySegments (Row)

structure Bits where
  tx : List Bool := []
  rx : List Bool := []
  deriving DecidableEq, Repr

def Bits.append (first rest : Bits) : Bits :=
  ⟨first.tx ++ rest.tx, first.rx ++ rest.rx⟩

/-- Record what this clock reserves and samples in chronological order. -/
def edge (i : Values Core.Input) (s : Values (Register a)) : Bits :=
  let base : Values (Core.Register a) := project s
  ⟨if Core.takingTX.eval i base = 1#1 then [Core.nextBit.eval i base == 1#1] else [],
   if Core.capturingRX.eval i base = 1#1 then [Core.inputBit.eval i base == 1#1] else []⟩

def observe (registered : Bool) (s : Values (Register a)) : List (Values Core.Input) → Bits
  | [] => {}
  | i :: rest => (edge i s).append (observe registered ((circuit a registered).step i s) rest)

/-- The physical trace contains ordinary clocks up to the first terminal edge.
    This check consumes raw inputs, including concurrent host push/pop. -/
def active (registered : Bool) (s : Values (Register a)) : List (Values Core.Input) → Bool
  | [] => true
  | i :: rest =>
    (i .initialize == 0#1 && i .command != 15#4 &&
      s (.base .phase) != 0#3 && s (.base .phase) != 5#3 && s (.base .phase) != 6#3) &&
        active registered ((circuit a registered).step i s) rest

theorem active_clocks {s : Values (Register a)} (accepted : active registered s inputs = true) :
    @ActiveClocks registered a s inputs := by
  induction inputs generalizing s with
  | nil => exact .nil
  | cons i rest ih =>
    have facts := accepted
    simp only [active, Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at facts
    obtain ⟨⟨⟨⟨⟨init, command⟩, running⟩, incomplete⟩, unfaulted⟩, tail⟩ := facts
    exact .cons ⟨init, command⟩ running incomplete unfaulted (ih tail)

private theorem step_base (registered : Bool) (i : Values Core.Input) (s : Values (Register a))
    (r : Core.Register a w) : (circuit a registered).step i s (.base r) =
      (nextBase r).eval i (withFetch s ((word registered).eval i s)) :=
  bindWord_eval _ _ _ _

private theorem inv_one_inv (x : BitVec 1) : ~~~(1#1 &&& ~~~x) = x := by decide +revert +kernel

set_option linter.unusedSimpArgs false in
/-- Ordinary edges shift raw pins through the two sampler registers. -/
theorem sampler_step (registered : Bool) (i : Values Core.Input) (s : Values (Register a))
    (ordinary : NoReset i) :
    let after : Values (Register a) := (circuit a registered).step i s
    after (.base .stage1) = i .rawInputs ∧ after (.base .stage2) = s (.base .stage1) := by
  constructor <;>
    simp [step_base, nextBase, originalNext, usesEntryWord, Expr.eval_bind, withFetch, Expr.eval,
      Core.next, Core.nextRaw, Core.cold, Core.warm, Core.cmd, Core.resetting, Core.both,
      Core.either, runtimeInput, ordinary.1, ordinary.2, inv_one_inv]

/-- An eligible aperture reads the physical input from two clocks before it.
    This holds through host commands, credit stalls and row transitions. -/
theorem sampler_after_two (registered : Bool) (before following : Values Core.Input)
    (s : Values (Register a)) (first : NoReset before) (second : NoReset following) :
    run registered s [@before, @following] (.base .stage2) = before .rawInputs := by
  exact (sampler_step registered following ((circuit a registered).step before s) second).2.trans
    (sampler_step registered before s first).1

set_option linter.unusedSimpArgs false in
private theorem edge_counts (registered : Bool) (i : Values Core.Input) (s : Values (Register a))
    (ordinary : NoReset i) (running : s (.base .phase) ≠ 0#3)
    (incomplete : s (.base .phase) ≠ 5#3) (unfaulted : s (.base .phase) ≠ 6#3) :
    let after : Values (Register a) := (circuit a registered).step i s
    after (.base .txConsumed) = s (.base .txConsumed) + BitVec.ofNat 16 (edge i s).tx.length ∧
      after (.base .rxProduced) = s (.base .rxProduced) + BitVec.ofNat 16 (edge i s).rx.length := by
  have increment (n : BitVec 16) : n - 65535#16 = n + 1 := by decide +revert +kernel
  constructor <;>
    simp [step_base, nextBase, originalNext, usesEntryWord, Expr.eval_bind, withFetch, Expr.eval,
      Core.next, Core.nextRaw, Core.cold, Core.warm, Core.cmd, Core.resetting,
      Core.both, Core.either, Core.isPhase, Core.free, Core.releasing, Core.starting, Core.retained,
      Core.inc, runtimeInput, project, ordinary.1, ordinary.2, running, incomplete, unfaulted,
      inv_one_inv, edge]
  · change (if Core.takingTX.eval i (project s) = 1#1
        then s (.base .txConsumed) - 65535#16 else s (.base .txConsumed)) = _
    by_cases take : Core.takingTX.eval i (project s) = 1#1 <;> simp [take, increment]
  · change (if Core.capturingRX.eval i (project s) = 1#1
        then s (.base .rxProduced) - 65535#16 else s (.base .rxProduced)) = _
    by_cases sample : Core.capturingRX.eval i (project s) = 1#1 <;> simp [sample, increment]
  all_goals done

theorem counts (span : @ActiveClocks registered a s inputs) :
    let after : Values (Register a) := run registered s inputs
    let captured := observe registered s inputs
    after (.base .txConsumed) = s (.base .txConsumed) + BitVec.ofNat 16 captured.tx.length ∧
      after (.base .rxProduced) = s (.base .rxProduced) + BitVec.ofNat 16 captured.rx.length := by
  induction span with
  | nil => simp [observe, run]
  | cons ordinary running incomplete unfaulted _ ih =>
    obtain ⟨txEdge, rxEdge⟩ := edge_counts registered _ _ ordinary running incomplete unfaulted
    obtain ⟨txRest, rxRest⟩ := ih
    simp only [run] at txRest rxRest
    constructor <;> simp only [observe, run, List.foldl_cons, Bits.append, List.length_append, BitVec.ofNat_add]
    · rw [txRest]
      exact (congrArg (· + _) txEdge).trans (BitVec.add_assoc _ _ _)
    · rw [rxRest]
      exact (congrArg (· + _) rxEdge).trans (BitVec.add_assoc _ _ _)

/-- After admitted START a single checked clock trace determines the exact
    reservation and receive counts and preserves START's owner. -/
theorem from_start (registered : Bool) (s : Values (Register a)) (start : Values Core.Input)
    (installed : Installed rows s) (admitted : Core.starting.eval start (project s) = 1#1)
    (accepted : active registered ((circuit a registered).step start s) inputs = true) :
    let started : Values (Register a) := (circuit a registered).step start s
    let after : Values (Register a) := run registered s (start :: inputs)
    let events := observe registered started inputs
    after (.base .txConsumed) = BitVec.ofNat 16 events.tx.length ∧
      after (.base .rxProduced) = BitVec.ofNat 16 events.rx.length ∧
      after (.base .generation) = s (.base .generation) ∧
      after (.base .transfer) = s (.base .transfer) + 1 ∧
      after (.base .total) = start .startCount := by
  obtain ⟨_, generation, transfer, total, _, _, tx, rx⟩ :=
    start_at_boundary registered start s installed admitted
  have served := active_clocks accepted
  have tally := counts served
  have sameOwner := served.owner
  exact ⟨by simpa only [run, List.foldl_cons, tx, BitVec.zero_add] using tally.1,
    by simpa only [run, List.foldl_cons, rx, BitVec.zero_add] using tally.2,
    sameOwner.generation.trans generation, sameOwner.transfer.trans transfer,
    sameOwner.total.trans total⟩

private theorem coherent_run {s : Values (Register a)}
    (inputs : List (Values Core.Input)) (initial : registered = true → SegmentStore.Coherent s) :
    registered = true → SegmentStore.Coherent (run registered s inputs) := by
  intro selected
  subst registered
  induction inputs generalizing s with
  | nil => exact initial rfl
  | cons i rest ih =>
    exact ih (fun _ => SegmentStore.coherent_after_edge i s)

/-- Check the final decoded row before its clock. The installed program
    determines whether the owner completes normally or discards a TX suffix. -/
def closing (rows : List Row) (discard : Bool) (i : Values Core.Input) (s : Values (Register a)) : Bool :=
  i .initialize == 0#1 && i .command == 0#4 && i .txPush == 0#1 &&
    s (.base .phase) == 1#3 &&
    rows[(s (.base .pc)).toNat]? == some (if discard then .discard else .cell .halt)

/-- A clock list and its last ordinary edge suffice to check either runtime
    completion. The contract checks the actual pre-edge row, without requiring
    an intermediate `Cut` or a delivered-path witness from the caller. -/
theorem closes_from_start (registered : Bool) (s : Values (Register a)) (start last : Values Core.Input)
    (inputs : List (Values Core.Input)) (discard : Bool)
    (installed : Installed rows s) (admitted : Core.starting.eval start (project s) = 1#1)
    (accepted : active registered ((circuit a registered).step start s) inputs = true)
    (finish : closing rows discard last (run registered ((circuit a registered).step start s) inputs) = true) :
    let started : Values (Register a) := (circuit a registered).step start s
    let before : Values (Register a) := run registered started inputs
    let after : Values (Register a) := (circuit a registered).step last before
    let bits := observe registered started inputs
    after (.base .phase) = 5#3 ∧
      after (.base .txConsumed) = BitVec.ofNat 16 bits.tx.length ∧
      after (.base .rxProduced) = BitVec.ofNat 16 bits.rx.length ∧
      after (.base .txAccepted) = before (.base .txAccepted) ∧
      after (.base .generation) = s (.base .generation) ∧
      after (.base .transfer) = s (.base .transfer) + 1 ∧
      (discard = true → after .txClosed = 1#1 ∧ after (.base .txCount) = 0#4 ∧ after (.base .txValid) = 0#6) := by
  let started : Values (Register a) := (circuit a registered).step start s
  let before : Values (Register a) := run registered started inputs
  let after : Values (Register a) := (circuit a registered).step last before
  have first := (start_at_boundary registered start s installed admitted).1
  have clockSpan := active_clocks accepted
  have coherent := coherent_run inputs first.coherent
  have stillInstalled := clockSpan.image first.installed
  have counts := from_start registered s start installed admitted accepted
  have facts := finish
  simp only [closing, Bool.and_eq_true, beq_iff_eq] at facts
  obtain ⟨⟨⟨⟨init, command⟩, noTX⟩, phase⟩, row⟩ := facts
  have ordinary : NoReset last := ⟨init, by simp [command]⟩
  have drain : ProtocolOwnership.DrainInput last := ⟨init, command, noTX⟩
  have latch : ∃ bit, HasCapture before bit := by
    rcases BitVec.eq_zero_or_eq_one (before .captureValid) with empty | valid
    · exact ⟨none, empty⟩
    · rcases BitVec.eq_zero_or_eq_one (before .lastCapture) with low | high
      · exact ⟨some false, valid, low⟩
      · exact ⟨some true, valid, high⟩
  obtain ⟨bit, latch⟩ := latch
  have cut : AtBoundary registered rows (before (.base .pc)).toNat bit before :=
    ⟨stillInstalled, phase, rfl, latch, coherent⟩
  have owner := active_owner_frame registered last before ordinary
    (by simp [cut.phase]) (by simp [cut.phase]) (by simp [cut.phase])
  have tx : before (.base .txConsumed) = BitVec.ofNat 16 (observe registered started inputs).tx.length := counts.1
  have rx : before (.base .rxProduced) = BitVec.ofNat 16 (observe registered started inputs).rx.length := counts.2.1
  cases discard
  · have finished := (terminal_step cut last drain false row).1
    exact ⟨congrArg ProtocolOwnership.TerminalCut.phase finished,
      (congrArg ProtocolOwnership.TerminalCut.reserved finished).trans tx,
      (congrArg ProtocolOwnership.TerminalCut.captured finished).trans rx,
      congrArg ProtocolOwnership.TerminalCut.accepted finished,
      owner.generation.trans counts.2.2.1, owner.transfer.trans counts.2.2.2.1, by simp⟩
  · have finished := discard_step cut last ordinary row
    exact ⟨finished.completed, finished.sent.trans tx, finished.captured.trans rx, finished.accepted,
      owner.generation.trans counts.2.2.1, owner.transfer.trans counts.2.2.2.1, fun _ => ⟨finished.closed, finished.txEmpty⟩⟩

end Pinwheel.Hardware.StreamingReady.SegmentTrace
