import Pinwheel.Hardware.StreamingReady.SegmentUnguardedReceive

/-! Bounded host service at the physical stream reservation boundary.
    The external contract uses the TX and RX wait status on an ordinary
    clock list. A first-credit proof locates the edge on that same list. -/
namespace Pinwheel.Hardware.StreamingReady.SegmentHostService

open Pinwheel.Hardware SegmentCore SegmentPathControl SegmentUnguardedReceive
open Pinwheel.Hardware.StreamingReady.SegmentStreamStep (Reservation)
open SegmentTiming (run)
open SegmentTransaction (ActiveClocks)

/-- Use the public per-direction stall status at the current pre-edge cut. -/
def Available (registered : Bool) (i : Values Core.Input) (s : Values (Register a)) : Prop :=
  (circuit a registered).observe i s .waitingTX = 0#1 ∧
    (circuit a registered).observe i s .waitingRX = 0#1

/-- Over at most `bound` parked clocks the host clears both wait flags on
    an eligible clock of the supplied trace. The contract leaves the exact
    first available edge and every prior park to the implementation. -/
def BoundedCredit (registered : Bool) (s : Values (Register a)) (inputs : List (Values Core.Input))
    (bound : Nat) : Prop :=
  ∃ k ≤ bound, ∃ i : Values Core.Input, inputs[k]? = some (@i) ∧
    Available registered i (run registered s (inputs.take k))

private theorem observe_waitingTX (registered : Bool) (i : Values Core.Input) (s : Values (Register a)) :
    (circuit a registered).observe i s .waitingTX = (Core.output .waitingTX).eval i (project s) := by
  change (bindWord (word registered) (output .waitingTX)).eval i s = _
  rw [bindWord_eval]
  rfl

private theorem observe_waitingRX (registered : Bool) (i : Values Core.Input) (s : Values (Register a)) :
    (circuit a registered).observe i s .waitingRX = (Core.output .waitingRX).eval i (project s) := by
  change (bindWord (word registered) (output .waitingRX)).eval i s = _
  rw [bindWord_eval]
  rfl

private theorem wait_flags (transmit receive hasTX hasRXRoom : BitVec 1) :
    (1#1 &&& (transmit &&& ~~~hasTX) = 0#1 ∧ 1#1 &&& (receive &&& ~~~hasRXRoom) = 0#1) ↔
      ~~~(transmit &&& ~~~hasTX) &&& ~~~(receive &&& ~~~hasRXRoom) = 1#1 := by
  decide +revert +kernel

/-- Both status pins can be clear away from a boundary. At the boundary
    their conjunction exactly characterizes pre-edge credit. -/
theorem available_iff_credit (registered : Bool) (i : Values Core.Input) (s : Values (Register a))
    (phase : s (.base .phase) = 2#3) :
    Available registered i s ↔ Core.credit.eval i (project s) = 1#1 := by
  simp only [Available, observe_waitingTX, observe_waitingRX, Core.output, Core.credit, Core.both,
    Core.either, Core.isPhase, Expr.eval, project, phase, BitVec.not_not]
  exact wait_flags _ _ _ _

private theorem first_credit (registered : Bool) (s : Values (Register a)) (inputs : List (Values Core.Input))
    (bound : Nat) (phase : s (.base .phase) = 2#3) (ordinary : ∀ i ∈ inputs, NoReset i)
    (service : BoundedCredit registered s inputs bound) :
    ∃ parks : List (Values Core.Input), ∃ admit : Values Core.Input, ∃ rest : List (Values Core.Input),
      inputs = parks ++ (@admit) :: rest ∧ parks.length ≤ bound ∧ ParkHistory registered s parks ∧
        NoReset admit ∧ Core.credit.eval admit (project (run registered s parks)) = 1#1 := by
  induction inputs generalizing s bound with
  | nil =>
    obtain ⟨_, _, _, clock, _⟩ := service
    simp at clock
  | cons i rest ih =>
    have clean := ordinary i (by simp)
    by_cases now : Available registered i s
    · exact ⟨[], i, rest, rfl, Nat.zero_le _, trivial, clean,
        (available_iff_credit registered i s phase).mp now⟩
    have missing : Core.credit.eval i (project s) = 0#1 := by
      rcases BitVec.eq_zero_or_eq_one (Core.credit.eval i (project s)) with zero | one
      · exact zero
      · exact (now ((available_iff_credit registered i s phase).mpr one)).elim
    let after : Values (Register a) := (circuit a registered).step i s
    have parked : SegmentStreamStep.CreditPark s after :=
      SegmentStreamStep.park_runtime registered i s clean phase missing
    obtain ⟨k, within, clock, atK, free⟩ := service
    cases k with
    | zero =>
      have same : (@i) = (@clock) := Option.some.inj atK
      cases same
      exact (now free).elim
    | succ k =>
      have tail : BoundedCredit registered after rest (bound - 1) :=
        ⟨k, by omega, clock, atK, free⟩
      obtain ⟨parks, admit, suffix, split, length, history, serviceOrdinary, credit⟩ :=
        ih after (bound - 1) parked.phase (fun j h => ordinary j (List.mem_cons_of_mem _ h)) tail
      exact ⟨i :: parks, admit, suffix, congrArg (List.cons (α := Values Core.Input) i) split,
        by simp only [List.length_cons]; omega, ⟨clean, missing, history⟩, serviceOrdinary, credit⟩

/-- Within the common host service bound the circuit takes its first
    reservation edge. The prefix contains only credit parks and leaves
    the pad pose, row, count, latch and accounting unchanged. The next
    clock starts LOW using the actual pre-edge TX value and RX credit. -/
theorem reserve_within (registered : Bool) (s : Values (Register a)) (inputs : List (Values Core.Input))
    {guard : Option Pinwheel.Program.StreamingReady.Guard}
    (bound : Nat) (entry : AtReservation rows pc cell guard previous s)
    (ordinary : ∀ i ∈ inputs, NoReset i) (service : BoundedCredit registered s inputs bound) :
    ∃ parks : List (Values Core.Input), ∃ admit : Values Core.Input, ∃ rest : List (Values Core.Input),
      let ready : Values (Register a) := run registered s parks
      inputs = parks ++ (@admit) :: rest ∧ parks.length ≤ bound ∧ ParkHistory registered s parks ∧
        Parked rows pc cell guard previous s ready ∧ ActiveClocks registered s parks ∧
        NoReset admit ∧ Core.credit.eval admit (project ready) = 1#1 ∧
        Reservation cell admit ready ((circuit a registered).step admit ready) := by
  obtain ⟨parks, admit, rest, split, within, history, clean, credit⟩ :=
    first_credit registered s inputs bound entry.phase ordinary service
  obtain ⟨parked, active⟩ := run_parks registered s parks entry history
  have reserved := SegmentStreamStep.reserve_runtime registered admit _ cell guard clean parked.ready.phase
    parked.ready.current credit
  exact ⟨parks, admit, rest, split, within, history, parked, active, clean, credit, reserved⟩

end Pinwheel.Hardware.StreamingReady.SegmentHostService
