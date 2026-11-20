import Pinwheel.Hardware.StreamingReady.SegmentAdmission
import Pinwheel.Hardware.StreamingReady.SegmentReload

/-! A run may change its checked Ready image after each retained owner.
    The tape records actual decoded commands and runtime clocks in order. -/
namespace Pinwheel.Hardware.StreamingReady.SegmentSequence

open Pinwheel.Hardware SegmentCore SegmentTiming SegmentReload
open Pinwheel.Program.StreamingReady (Pins)
open Pinwheel.Program.StreamingReadySegments (Image Row)
open ProtocolOwnership (DrainInput TerminalCut)

structure Session where
  rows : List Row
  budget : Nat
  image : Image rows budget
  idle : Pins
  requested : BitVec 16
  handoff : HandoffTrace
  runtime : List (Values Core.Input)

def Session.opened (session : Session) (registered : Bool) (s : Values (Register a)) :
    Values (Register a) :=
  (circuit a registered).step session.handoff.start (session.handoff.atStart registered s)

def Session.retained (session : Session) (registered : Bool) (s : Values (Register a)) :
    Values (Register a) :=
  run registered (session.opened registered s) session.runtime

def Session.clocks (session : Session) : List (Values Core.Input) :=
  let trace := session.handoff
  [@trace.settle] ++ (((trace.writes ++ [@trace.commit]) ++ trace.replyClocks) ++
    ([@trace.stale] ++ (trace.retryClocks ++ ([@trace.start] ++ session.runtime))))

theorem Session.run_clocks (session : Session) (registered : Bool) (s : Values (Register a)) :
    @run a registered s session.clocks = fun {w} r => session.retained registered s (w := w) r := by
  simp only [Session.clocks, Session.retained, Session.opened, HandoffTrace.atStart,
    HandoffTrace.atStale, HandoffTrace.atSettlement, run_append]
  rfl

/-- After a retained result, the host's remaining runtime clocks only drain.
    This property refers to reached public phases, independently of the
    path or index of the first terminal edge. -/
def RetainedDrain (registered : Bool) (opened : Values (Register a))
    (runtime : List (Values Core.Input)) : Prop :=
  ∀ (elapsed later : List (Values Core.Input)) (edge : Values Core.Input),
    runtime = elapsed ++ @edge :: later →
    (TerminalCut.of (run registered opened elapsed)).Retained → DrainInput edge

private theorem RetainedDrain.cut {opened : Values (Register a)}
    (policy : RetainedDrain registered opened runtime) (elapsed rest : List (Values Core.Input))
    (split : runtime = elapsed ++ rest) (atCut : (TerminalCut.of (run registered opened elapsed)).Retained) :
    TerminalCut.of (run registered opened runtime) = TerminalCut.of (run registered opened elapsed) := by
  induction rest generalizing elapsed with
  | nil => simpa using congrArg (fun clocks => TerminalCut.of (run registered opened clocks)) split
  | cons edge later ih =>
    have first := policy elapsed later edge split atCut
    have next : runtime = (elapsed ++ [@edge]) ++ later := by simpa [List.append_assoc] using split
    have stationary : TerminalCut.of (run registered opened (elapsed ++ [@edge])) =
        TerminalCut.of (run registered opened elapsed) := by
      rw [run_append]
      exact ProtocolOwnership.drain_step_preserves registered edge (run registered opened elapsed) atCut first
    exact (ih (elapsed ++ [@edge]) next (stationary ▸ atCut)).trans stationary

structure Session.Delivered (session : Session) (registered : Bool) (s : Values (Register a)) : Prop where
  handoff : HandoffDelivery session.handoff session.rows session.idle session.requested s
  service : SegmentAdmission.Supply registered session.rows session.budget (session.opened registered s) session.runtime
  drain : RetainedDrain registered (session.opened registered s) session.runtime

structure Receipt where
  ending : SegmentAdmission.Terminal
  clocksThroughTerminal : Nat
  wire : SegmentTrace.Bits
  tag : Nat
  cut : TerminalCut

structure Session.Verified (session : Session) (registered : Bool) (s : Values (Register a))
    (receipt : Receipt) : Prop where
  handoff : HandoffResult session.handoff registered session.rows session.idle session.requested s
  firstTerminal : ∃ (active : List (Values Core.Input)) (last : Values Core.Input) (rest : List (Values Core.Input)),
    session.runtime = active ++ @last :: rest ∧
    SegmentAdmission.Admitted session.image registered (session.handoff.atStart registered s)
      session.handoff.start active last receipt.ending ∧
    receipt.clocksThroughTerminal = active.length + 1 ∧
    receipt.wire = SegmentTrace.observe registered (session.opened registered s) (active ++ [@last]) ∧
    receipt.cut = TerminalCut.of (run registered (session.opened registered s) (active ++ [@last])) ∧
    TerminalCut.of (session.retained registered s) =
      TerminalCut.of (run registered (session.opened registered s) (active ++ [@last]))
  generation : (session.retained registered s) (.base .generation) = s (.base .generation) + 1#16
  transfer : (session.retained registered s) (.base .transfer) = s (.base .transfer) + 1#16
  tag : receipt.tag = ProtocolOwnership.ownerTag ((session.retained registered s) (.base .generation))
    ((session.retained registered s) (.base .transfer))

/-- Each leg is checked from the actual predecessor produced by the hardware.
    The row service only constrains reached cuts of the supplied runtime tape.
    Its first exit, received bits, and final owner are derived here. -/
theorem Session.verify (session : Session) (registered : Bool) (s : Values (Register a))
    (delivered : session.Delivered registered s)
    (generationRoom : s (.base .generation) ≠ 65535#16) (transferRoom : s (.base .transfer) ≠ 65535#16) :
    ∃ receipt, session.Verified registered s receipt := by
  let handoff := session.handoff
  let before : Values (Register a) := handoff.atStart registered s
  let opened : Values (Register a) := session.opened registered s
  have loaded := handoff_checked session.image handoff registered s delivered.handoff generationRoom transferRoom
  obtain ⟨_, generation, transfer⟩ := delivered.handoff.settlement.closes registered
  have priorGeneration : before (.base .generation) = s (.base .generation) + 1#16 :=
    loaded.installed.generation.trans (congrArg (· + 1#16) generation)
  have priorTransfer : before (.base .transfer) = s (.base .transfer) := loaded.installed.transfer.trans transfer
  have expected : handoff.start .expectedGeneration = before (.base .generation) :=
    delivered.handoff.start.expected.trans priorGeneration.symm
  have space : before (.base .transfer) ≠ 65535#16 := by rwa [priorTransfer]
  have free : before (.base .phase) = 0#3 := loaded.installed.free.phase
  have valid : before (.base .valid) = 1#1 := loaded.installed.image.valid
  have cold : handoff.start .initialize = 0#1 := delivered.handoff.start.cold
  have command : handoff.start .command = 3#4 := delivered.handoff.start.command
  have accepted : Core.starting.eval handoff.start (project before) = 1#1 := by
    simp [Core.starting, Core.free, Core.space, Core.warm, Core.cold, Core.resetting, Core.cmd,
      Core.both, Core.either, Expr.eval, project, free, valid, cold, command, expected, space]
  obtain ⟨active, last, rest, ending, split, checked⟩ := SegmentAdmission.from_start session.image registered
    before handoff.start session.runtime loaded.installed.image accepted delivered.service
  let terminal : Values (Register a) := run registered opened (active ++ [@last])
  have terminalEdge : @terminal = @Circuit.step _ _ _ (circuit a registered) last (run registered opened active) := by
    unfold terminal
    rw [run_append]
    rfl
  have phase : terminal (.base .phase) = SegmentAdmission.phaseOf ending := by
    rw [terminalEdge]
    exact checked.terminal.1
  have retained : (TerminalCut.of terminal).Retained := by
    change terminal (.base .phase) = 5#3 ∨ terminal (.base .phase) = 6#3
    rw [phase]
    cases ending with
    | planned outcome =>
      have terminalPhase (exit : Pinwheel.Program.StreamingReadySegments.Exit) :
          SegmentTransaction.terminalPhase exit = 5#3 ∨ SegmentTransaction.terminalPhase exit = 6#3 := by
        cases exit <;> decide
      exact terminalPhase outcome.exit
    | timeout => exact .inr rfl
  have preserved : TerminalCut.of (session.retained registered s) = TerminalCut.of terminal :=
    delivered.drain.cut (active ++ [@last]) rest (by simpa [List.append_assoc] using split) retained
  have finalGeneration : (session.retained registered s) (.base .generation) = s (.base .generation) + 1#16 := by
    change (TerminalCut.of (session.retained registered s)).generation = _
    rw [preserved]
    change terminal (.base .generation) = _
    rw [terminalEdge]
    exact checked.terminal.2.1.trans priorGeneration
  have finalTransfer : (session.retained registered s) (.base .transfer) = s (.base .transfer) + 1#16 := by
    change (TerminalCut.of (session.retained registered s)).transfer = _
    rw [preserved]
    change terminal (.base .transfer) = _
    rw [terminalEdge]
    exact checked.terminal.2.2.1.trans (congrArg (· + 1#16) priorTransfer)
  let receipt : Receipt := ⟨ending, active.length + 1, SegmentTrace.observe registered opened (active ++ [@last]),
    ProtocolOwnership.ownerTag ((session.retained registered s) (.base .generation))
      ((session.retained registered s) (.base .transfer)), TerminalCut.of terminal⟩
  exact ⟨receipt, loaded, ⟨active, last, rest, split, checked, rfl, rfl, rfl, preserved⟩,
    finalGeneration, finalTransfer, rfl⟩

def clocks (sessions : List Session) : List (Values Core.Input) := sessions.flatMap Session.clocks

private theorem run_cons (registered : Bool) (s : Values (Register a)) (session : Session)
    (rest : List Session) :
    @run a registered s (clocks (session :: rest)) =
      @run a registered (session.retained registered s) (clocks rest) := by
  change @run a registered s (session.clocks ++ clocks rest) = _
  rw [run_append, session.run_clocks]

/-- A sequence may reuse the same image or change protocols at each handoff.
    Each delivery premise is relative to its actual preceding terminal cut. -/
def Delivered (registered : Bool) (s : Values (Register a)) : List Session → Prop
  | [] => True
  | session :: rest => session.Delivered registered s ∧ Delivered registered (session.retained registered s) rest

def Receipts (registered : Bool) (s : Values (Register a)) : List Session → List Receipt → Prop
  | [], [] => True
  | session :: rest, receipt :: receipts =>
    session.Verified registered s receipt ∧ Receipts registered (session.retained registered s) rest receipts
  | _, _ => False

structure Verified (registered : Bool) (s : Values (Register a))
    (sessions : List Session) (receipts : List Receipt) : Prop where
  each : Receipts registered s sessions receipts
  length : receipts.length = sessions.length
  generation : (run registered s (clocks sessions) (.base .generation)).toNat =
    (s (.base .generation)).toNat + sessions.length
  transfer : (run registered s (clocks sessions) (.base .transfer)).toNat =
    (s (.base .transfer)).toNat + sessions.length

private theorem toNat_inc (x : BitVec 16) (room : x.toNat + 1 < 65536) :
    (x + 1#16).toNat = x.toNat + 1 := by
  rw [BitVec.toNat_add]
  exact Nat.mod_eq_of_lt room

/-- Replay the concatenation of all physical handoff and runtime clocks.
    Every session gets its first-terminal receipt and advances the generation
    and transfer counts once. Tag headroom is checked for the whole sequence. -/
theorem verify (registered : Bool) (s : Values (Register a)) (sessions : List Session)
    (delivered : Delivered registered s sessions)
    (generationRoom : (s (.base .generation)).toNat + sessions.length < 65536)
    (transferRoom : (s (.base .transfer)).toNat + sessions.length < 65536) :
    ∃ receipts, Verified registered s sessions receipts := by
  induction sessions generalizing s with
  | nil => exact ⟨[], trivial, rfl, by simp [clocks, run], by simp [clocks, run]⟩
  | cons session rest ih =>
    obtain ⟨delivered, tail⟩ := delivered
    simp only [List.length_cons] at generationRoom transferRoom
    have generationSpace : s (.base .generation) ≠ 65535#16 := by
      intro full
      simp [full] at generationRoom
      omega
    have transferSpace : s (.base .transfer) ≠ 65535#16 := by
      intro full
      simp [full] at transferRoom
      omega
    obtain ⟨receipt, checked⟩ := session.verify registered s delivered generationSpace transferSpace
    have newGeneration : (session.retained registered s (.base .generation)).toNat =
        (s (.base .generation)).toNat + 1 := by
      rw [checked.generation, toNat_inc _ (by omega)]
    have newTransfer : (session.retained registered s (.base .transfer)).toNat =
        (s (.base .transfer)).toNat + 1 := by
      rw [checked.transfer, toNat_inc _ (by omega)]
    obtain ⟨receipts, verified⟩ := ih (session.retained registered s) tail
      (by rw [newGeneration]; omega) (by rw [newTransfer]; omega)
    refine ⟨receipt :: receipts, ⟨checked, verified.each⟩, by simp [verified.length], ?_, ?_⟩
    · rw [run_cons, verified.generation, newGeneration]
      simp only [List.length_cons]
      omega
    · rw [run_cons, verified.transfer, newTransfer]
      simp only [List.length_cons]
      omega

/-- Explicit settlement of the final result returns the engine to an empty
    free cut while preserving the owner counts proved across the sequence. -/
theorem Verified.close {s : Values (Register a)} (verified : Verified registered s sessions receipts)
    (last : Values Core.Input) (settlement : Settlement last (run registered s (clocks sessions))) :
    let after : Values (Register a) := run registered s (clocks sessions ++ [@last])
    SegmentHandoffFence.FreeCut registered after ∧
      (after (.base .generation)).toNat = (s (.base .generation)).toNat + sessions.length ∧
      (after (.base .transfer)).toNat = (s (.base .transfer)).toNat + sessions.length := by
  rw [run_append]
  obtain ⟨free, generation, transfer⟩ := settlement.closes registered
  exact ⟨free, (congrArg BitVec.toNat generation).trans verified.generation,
    (congrArg BitVec.toNat transfer).trans verified.transfer⟩

end Pinwheel.Hardware.StreamingReady.SegmentSequence
