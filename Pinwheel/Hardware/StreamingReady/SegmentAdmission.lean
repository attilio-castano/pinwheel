import Pinwheel.Hardware.StreamingReady.SegmentTraceTimeout
import Pinwheel.Program.StreamingReadySegmentExecution

/-! Follow the checked program on one supplied clock trace. A service policy
    supplies local clock spans at reached FETCH cuts; the image and the actual
    capture latch determine the path and the final edge. -/
namespace Pinwheel.Hardware.StreamingReady.SegmentAdmission

open Pinwheel.Hardware SegmentCore SegmentPathControl SegmentTransaction
open Pinwheel.Program.StreamingReady (Instruction)
open Pinwheel.Program.StreamingReadySegments
open SegmentTiming (run)
open SegmentTransactionTimeout (GuardedSlot TimeoutSpan)

abbrev Terminal := Execution.Terminal

/-- A timed row uses a prefix of the same remaining clocks in either case. -/
inductive TimedService (registered : Bool) (rows : List Row) (budget : Nat)
    (cursor following : Cursor) (s : Values (Register a))
    (remaining : List (Values Core.Input)) : Prop where
  | advance (split : remaining = clocks ++ rest)
      (service : ServiceSpan registered rows following bit s clocks)
  | timeout (split : remaining = clocks ++ @last :: rest)
      (service : TimeoutSpan registered rows budget cursor slot tx rx s clocks last)

/-- One environment supplies clocks at the reached cuts of a flat trace. The
    terminal row is serviced with an ordinary drain input. Countdown, guard,
    and credit behavior within a timed row use the corresponding service
    witness. No path choice or final outcome is an input to the policy. -/
structure Supply (registered : Bool) (rows : List Row) (budget : Nat)
    (started : Values (Register a)) (trace : List (Values Core.Input)) : Prop where
  clock : ∀ (elapsed remaining : List (Values Core.Input)) (cursor : Cursor) (capture : Option Bool),
    trace = elapsed ++ remaining →
    Cut registered rows cursor capture (run registered started elapsed) →
    ∃ (head : Values Core.Input) (tail : List (Values Core.Input)),
      remaining = @head :: tail ∧ NoReset head ∧
        (∀ endAt, successors rows budget cursor = some (.finish endAt) → ProtocolOwnership.DrainInput head)
  timed : ∀ (elapsed remaining : List (Values Core.Input)) (cursor : Cursor) (capture : Option Bool),
    trace = elapsed ++ remaining →
    Cut registered rows cursor capture (run registered started elapsed) →
    ∀ (instruction : Instruction) (following : Cursor),
      Serviced instruction → rows[cursor.pc]? = some (.cell instruction) →
      successors rows budget cursor = some (.next following) →
      TimedService registered rows budget cursor following (run registered started elapsed) remaining

private inductive Dispatch (rows : List Row) (cursor : Cursor) : Successors → Prop where
  | count (row : rows[cursor.pc]? = some (.count slots)) (nonzero : slots ≠ 0#16) :
      Dispatch rows cursor (.next (countCursor cursor slots))
  | branch (row : rows[cursor.pc]? = some (.branch destination onBit)) (qualified : cursor.capture = true)
      (forward : cursor.pc < destination.toNat) (inBounds : destination.toNat < rows.length) :
      Dispatch rows cursor (.both (branchCursor cursor destination false) (branchCursor cursor destination true))
  | timed (row : rows[cursor.pc]? = some (.cell instruction)) (kind : Serviced instruction) :
      Dispatch rows cursor (.next following)
  | finish (row : rows[cursor.pc]? = some (terminalRow exit)) :
      Dispatch rows cursor (.finish (endOf cursor exit))

private theorem dispatch {next : Successors} (entry : successors rows budget cursor = some next) :
    Dispatch rows cursor next := by
  cases row : rows[cursor.pc]? with
  | none => simp [successors, row] at entry
  | some rowValue =>
    cases rowValue with
    | count slots =>
      simp [successors, row] at entry
      have nextEq : Successors.next (countCursor cursor slots) = next := entry.2
      exact nextEq ▸ .count row entry.1.2
    | branch target onBit =>
      simp [successors, row] at entry
      obtain ⟨⟨⟨⟨_, qualified⟩, _⟩, forward⟩, inBounds⟩ := entry.1
      have nextEq : (Successors.both (branchCursor cursor target false)
          (branchCursor cursor target true)) = next := entry.2
      exact nextEq ▸ .branch row qualified forward inBounds
    | discard =>
      simp [successors, row] at entry
      have nextEq : Successors.finish (endOf cursor .discard) = next := entry.2
      exact nextEq ▸ .finish row
    | cell instruction =>
      cases instruction with
      | halt =>
        simp [successors, row] at entry
        have nextEq : Successors.finish (endOf cursor .complete) = next := entry.2.2
        exact nextEq ▸ .finish row
      | fault =>
        simp [successors, row] at entry
        have nextEq : Successors.finish (endOf cursor .fault) = next := entry.2.2
        exact nextEq ▸ .finish row
      | pulse cell =>
        simp [successors, row] at entry
        cases entry.2.2
        exact .timed row .pulse
      | driveWait pins guard =>
        simp [successors, row] at entry
        obtain ⟨clocks, _, checked⟩ := Option.bind_eq_some_iff.mp entry.2
        simp at checked
        cases checked.2
        exact .timed row .wait
      | stream cell guard =>
        simp [successors, row] at entry
        obtain ⟨slots, _, afterSlots⟩ := Option.bind_eq_some_iff.mp entry.2
        obtain ⟨polls, _, checked⟩ := Option.bind_eq_some_iff.mp afterSlots
        simp at checked
        cases checked.2
        exact .timed row .stream

/-- The end of the consumed trace is a checked terminal instruction or its
    first exhausted guard aperture. In both cases the circuit is at the
    last pre-edge state described by the trace. -/
inductive FinalCut (registered : Bool) (rows : List Row) (s : Values (Register a))
    (last : Values Core.Input) : Terminal → Prop where
  | planned (cut : Cut registered rows cursor capture s)
      (row : rows[cursor.pc]? = some (terminalRow exit)) (drain : ProtocolOwnership.DrainInput last) :
      FinalCut registered rows s last (.planned (endOf cursor exit))
  | timeout (pc : (s (.base .pc)).toNat = cursor.pc)
      (deadline : ProtocolOwnership.AtDeadline last s)
      (row : rows[cursor.pc]? = some (.cell instruction))
      (slotIndex : GuardedSlot cursor instruction slot tx rx)
      (word : s (.base .currentWord) = Pinwheel.Program.StreamingReady.encode instruction)
      (txCount : (s (.base .txConsumed)).toNat = tx)
      (rxCount : (s (.base .rxProduced)).toNat = rx) :
      FinalCut registered rows s last (.timeout cursor.pc slot)

structure Reached (registered : Bool) (rows : List Row) (budget : Nat) (cursor : Cursor)
    (s : Values (Register a)) (clocks : List (Values Core.Input)) (last : Values Core.Input)
    (terminal : Terminal) : Prop where
  active : ActiveClocks registered s clocks
  final : FinalCut registered rows (run registered s clocks) last terminal
  planned : ∀ outcome, terminal = .planned outcome → Reaches rows budget cursor outcome

private theorem reached_append
    (first : @ActiveClocks registered a s before)
    (rest : Reached registered rows budget following (run registered s before) after last terminal)
    (reaches : ∀ outcome, Reaches rows budget following outcome → Reaches rows budget cursor outcome) :
    Reached registered rows budget cursor s (before ++ after) last terminal := by
  refine ⟨first.append rest.active, ?_, fun outcome eq => reaches outcome (rest.planned outcome eq)⟩
  rw [SegmentTiming.run_append]
  exact rest.final

private theorem walk {started : Values (Register a)} {trace : List (Values Core.Input)}
    (policy : Supply registered rows budget started trace)
    (fuel : Nat) (cursor : Cursor) (capture : Option Bool)
    (elapsed remaining : List (Values Core.Input))
    (split : trace = elapsed ++ remaining)
    (cut : Cut registered rows cursor capture (run registered started elapsed))
    (checked : ∃ outcomes, paths rows budget fuel cursor = some outcomes) :
    ∃ (active : List (Values Core.Input)) (last : Values Core.Input) (rest : List (Values Core.Input))
      (terminal : Terminal), remaining = active ++ @last :: rest ∧
      Reached registered rows budget cursor (run registered started elapsed) active last terminal := by
  induction fuel generalizing cursor capture elapsed remaining with
  | zero =>
    obtain ⟨_, ruledOut⟩ := checked
    simp [paths] at ruledOut
  | succ fuel ih =>
    let s : Values (Register a) := run registered started elapsed
    obtain ⟨outcomes, verified⟩ := checked
    have continueAt {following : Cursor} {bit : Option Bool} {head tail : List (Values Core.Input)}
        (partition : remaining = head ++ tail)
        (advance : Advance registered rows budget cursor capture s head following bit)
        (path : ∃ outcomes, paths rows budget fuel following = some outcomes)
        (back : ∀ ending, Reaches rows budget following ending → Reaches rows budget cursor ending) :
        ∃ (active : List (Values Core.Input)) (last : Values Core.Input) (rest : List (Values Core.Input))
          (terminal : Terminal), remaining = active ++ @last :: rest ∧
          Reached registered rows budget cursor s active last terminal := by
      obtain ⟨newCut, headActive⟩ := advance.refines cut
      have atNext : Cut registered rows following bit (run registered started (elapsed ++ head)) := by
        rw [SegmentTiming.run_append]
        exact newCut
      have stillSame : trace = (elapsed ++ head) ++ tail := by rw [split, partition, List.append_assoc]
      obtain ⟨active, last, rest, ending, tailSplit, reached⟩ := ih following bit
        (elapsed ++ head) tail stillSame atNext path
      have afterHead : Reached registered rows budget following (run registered s head) active last ending := by
        rw [SegmentTiming.run_append] at reached
        exact reached
      refine ⟨head ++ active, last, rest, ending, ?_, reached_append headActive afterHead back⟩
      rw [partition, tailSplit, List.append_assoc]
    cases entry : successors rows budget cursor with
    | none => simp [paths, entry] at verified
    | some next =>
      have actual := dispatch entry
      cases actual with
      | @count slots row nonzero =>
        obtain ⟨head, tail, partition, ordinary, _⟩ := policy.clock elapsed remaining cursor capture split cut
        have path : paths rows budget fuel (countCursor cursor slots) = some outcomes := by
          simpa [paths, entry] using verified
        exact continueAt (by simpa using partition) (.count row nonzero ordinary entry)
          ⟨outcomes, path⟩ (fun _ => .next entry)
      | @branch destination onBit row qualified forward inBounds =>
        cases capture with
        | none =>
          have missing : (none : Option Bool).isSome = true := cut.qualified qualified
          simp at missing
        | some value =>
          obtain ⟨head, tail, partition, ordinary, _⟩ := policy.clock elapsed remaining cursor _ split cut
          have branches :
              (paths rows budget fuel (branchCursor cursor destination false)).bind (fun no =>
                (paths rows budget fuel (branchCursor cursor destination true)).bind fun yes => some (no ++ yes)) =
                  some outcomes := by
            simpa [paths, entry] using verified
          obtain ⟨no, noPath, remainingPath⟩ := Option.bind_eq_some_iff.mp branches
          obtain ⟨yes, yesPath, _⟩ := Option.bind_eq_some_iff.mp remainingPath
          have path : ∃ ends, paths rows budget fuel (branchCursor cursor destination (decide (value = onBit))) =
              some ends := by
            by_cases taken : value = onBit
            · exact ⟨yes, by simpa [taken] using yesPath⟩
            · exact ⟨no, by simpa [taken] using noPath⟩
          apply continueAt (head := [@head]) (tail := tail) (by simpa using partition)
            (.branch row ordinary forward inBounds entry) path
          intro ending reached
          apply Reaches.branch entry (decide (value = onBit))
          by_cases taken : value = onBit <;> simpa [taken] using reached
      | @timed instruction following row kind =>
        have served := policy.timed elapsed remaining cursor capture split cut instruction following kind row entry
        cases served with
        | advance partition service =>
          have path : paths rows budget fuel following = some outcomes := by
            simpa [paths, entry] using verified
          exact continueAt partition (.cell kind row entry (fun _ => service))
            ⟨outcomes, path⟩ (fun _ => .next entry)
        | @timeout clocks last rest slot tx rx partition service =>
          obtain ⟨_, row, indexed, loaded⟩ := service.row
          exact ⟨clocks, last, rest, .timeout cursor.pc slot, partition, service.active,
            .timeout service.pc service.deadline row indexed loaded service.txCount service.rxCount, by simp⟩
      | @finish exit row =>
        obtain ⟨head, tail, partition, _, drain⟩ := policy.clock elapsed remaining cursor capture split cut
        refine ⟨[], head, tail, .planned (endOf cursor exit), by simpa using partition, .nil,
          .planned cut row (drain _ entry), ?_⟩
        intro ending eq
        cases eq
        exact .finish entry

theorem active_of_clocks (clocks : @ActiveClocks registered a s active) :
    SegmentTrace.active registered s active = true := by
  induction clocks with
  | nil => rfl
  | cons ordinary busy complete fault _ ih =>
    simp [SegmentTrace.active, ordinary.1, ordinary.2, busy, complete, fault, ih]

def phaseOf : Terminal → BitVec 3
  | .planned outcome => terminalPhase outcome.exit
  | .timeout .. => 6#3

theorem FinalCut.phase {s : Values (Register a)} (terminal : FinalCut registered rows s last ending) :
    ((circuit a registered).step last s) (.base .phase) = phaseOf ending := by
  cases terminal with
  | planned cut row drain => exact (terminal_end cut last drain row).phase
  | timeout _ deadline _ _ _ _ _ =>
    exact congrArg ProtocolOwnership.TerminalCut.phase (SegmentTiming.timeout_edge registered last s deadline).retained

theorem FinalCut.owner {s : Values (Register a)} (terminal : FinalCut registered rows s last ending) :
    OwnerFrame s ((circuit a registered).step last s) := by
  cases terminal with
  | planned cut _ drain =>
    exact active_owner_frame registered last s ⟨drain.1, by simp [drain.2.1]⟩
      (by simp [cut.boundary.phase]) (by simp [cut.boundary.phase]) (by simp [cut.boundary.phase])
  | timeout _ deadline _ _ _ _ _ =>
    exact active_owner_frame registered last s ⟨deadline.ordinary.1, by simp [deadline.ordinary.2.1]⟩
      (by simp [deadline.waiting]) (by simp [deadline.waiting]) (by simp [deadline.waiting])

theorem FinalCut.closed
    (terminal : FinalCut registered rows s last (.planned outcome)) (conclude : outcome.exit ≠ .fault) :
    SegmentTrace.closing rows (outcome.exit == .discard) last s = true := by
  cases terminal with
  | @planned cursor capture exit cut row drain =>
    cases exit with
    | complete =>
      simpa [SegmentTrace.closing, endOf, drain.1, drain.2.1, drain.2.2, cut.boundary.phase,
        cut.boundary.position, terminalRow] using row
    | discard =>
      simpa [SegmentTrace.closing, endOf, drain.1, drain.2.1, drain.2.2, cut.boundary.phase,
        cut.boundary.position, terminalRow] using row
    | fault => exact (conclude rfl).elim

theorem FinalCut.expired (terminal : FinalCut registered rows s last (.timeout pc slot)) :
    SegmentTraceTimeout.deadline last s = true := by
  cases terminal with
  | timeout _ expiry _ _ _ _ _ =>
    simp [SegmentTraceTimeout.deadline, expiry.ordinary.1, expiry.ordinary.2.1, expiry.ordinary.2.2,
      expiry.waiting, expiry.ready, expiry.bounded, expiry.expired]

/-- Admission is an actual active prefix, a last edge, and core ownership
    through that edge. Checked planned exits and runtime expiry use their
    respective flat trace checkers. -/
structure Admitted {rows : List Row} {budget : Nat} (image : Image rows budget)
    (registered : Bool) (s : Values (Register a)) (start : Values Core.Input)
    (active : List (Values Core.Input)) (last : Values Core.Input) (ending : Terminal) : Prop where
  reached : Reached registered rows budget {} ((circuit a registered).step start s) active last ending
  runs : SegmentTrace.active registered ((circuit a registered).step start s) active = true
  terminal : let opened : Values (Register a) := (circuit a registered).step start s
    let before : Values (Register a) := run registered opened active
    let after : Values (Register a) := (circuit a registered).step last before
    after (.base .phase) = phaseOf ending ∧
      after (.base .generation) = s (.base .generation) ∧
      after (.base .transfer) = s (.base .transfer) + 1 ∧
      after (.base .total) = start .startCount
  planned : ∀ result, ending = .planned result → result ∈ image.outcomes ∧
    (result.exit ≠ .fault →
      SegmentTrace.closing rows (result.exit == .discard) last
        (run registered ((circuit a registered).step start s) active) = true)
  expired : ∀ pc slot, ending = .timeout pc slot →
    SegmentTraceTimeout.accepts registered ((circuit a registered).step start s) active last = true

/-- Walk a single serviced input trace from START. Fuel comes from the
    image check and each branch follows the circuit's qualified capture.
    The returned clock prefix always ends on its first terminal edge. -/
theorem from_start (image : Image rows budget) (registered : Bool) (s : Values (Register a))
    (start : Values Core.Input) (trace : List (Values Core.Input))
    (installed : Installed rows s) (admitted : Core.starting.eval start (project s) = 1#1)
    (policy : Supply registered rows budget ((circuit a registered).step start s) trace) :
    ∃ (active : List (Values Core.Input)) (last : Values Core.Input) (rest : List (Values Core.Input))
      (ending : Terminal), trace = active ++ @last :: rest ∧
      Admitted image registered s start active last ending := by
  let opened : Values (Register a) := (circuit a registered).step start s
  obtain ⟨boundary, generation, transfer, total, _, _, tx, rx⟩ :=
    start_at_boundary registered start s installed admitted
  have initial : Cut registered rows {} none (run registered opened []) := by
    change Cut registered rows {} none ((circuit a registered).step start s)
    exact ⟨boundary, by simp, by simp, by simp [tx], by simp [rx]⟩
  have checked : paths rows budget rows.length {} = some image.outcomes := by
    have check := image.checked
    unfold Pinwheel.Program.StreamingReadySegments.check at check
    split at check
    · exact check
    · contradiction
  obtain ⟨active, last, rest, ending, split, reached⟩ :=
    walk policy rows.length {} none [] trace rfl initial ⟨_, checked⟩
  have runs := active_of_clocks reached.active
  have headOwner := reached.active.owner
  have lastOwner := reached.final.owner
  refine ⟨active, last, rest, ending, split, reached, runs,
    ⟨reached.final.phase, lastOwner.generation.trans (headOwner.generation.trans generation),
      lastOwner.transfer.trans (headOwner.transfer.trans transfer),
      lastOwner.total.trans (headOwner.total.trans total)⟩, ?_, ?_⟩
  · intro result eq
    have finish := reached.final
    rw [eq] at finish
    exact ⟨image.covers (reached.planned result eq), finish.closed⟩
  · intro pc slot eq
    have finish := reached.final
    rw [eq] at finish
    simp only [SegmentTraceTimeout.accepts, Bool.and_eq_true]
    exact ⟨runs, finish.expired⟩

end Pinwheel.Hardware.StreamingReady.SegmentAdmission
