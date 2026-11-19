import Pinwheel.Program.StreamingI2CTrace

/-! TX is removed from the host queue at reservation and remains in the cell
until its sampled SCL guard qualifies the bit. -/
namespace Pinwheel.Program.StreamingI2CTrace
open StreamingReady

set_option linter.unusedSimpArgs false

namespace Profiled

variable (profile : I2cProfile)

def txFlightBits (s : State a) : List Bool :=
  if s.current.isStream && (s.phase == .low || s.phase == .waiting) then [s.cellBit] else []

theorem tx_qualified_step (s : State a) (i : Input) (h : Positioned profile s)
    (ordinary : Unreleased i) (safe : (step (program profile) i s).phase ≠ .fault) :
    txFlightBits s ++ s.txEvent = txQualified s ++ txFlightBits (step (program profile) i s) := by
  rw [step_eq_clock profile s i h ordinary] at safe ⊢
  rcases h.phase with phase | (phase | phase | phase) | phase | phase
  · cases fetched : (program profile).fetch s.pc.toNat with
    | none =>
      simp [txFlightBits,txQualified,State.txEvent,State.consumes,State.captures,
        clock,engine,phase,fetched,State.stop]
    | some instruction =>
      cases instruction <;> by_cases empty : s.remaining = 0#16 <;>
        simp [txFlightBits,txQualified,State.txEvent,State.consumes,State.captures,
          clock,engine,phase,fetched,State.stop,empty,Instruction.isStream]
  · have current := h.current (Or.inl (Or.inl phase))
    rcases h.cycles (Or.inl phase) with pc | pc | pc | pc <;>
      cases credit : s.canReserve <;>
        simp [txFlightBits,txQualified,State.txEvent,State.consumes,State.captures,
          clock,engine,phase,current,pc,row,Instruction.isStream,Instruction.cell,
          i2cCell,i2cHold,i2cStopLow,credit]
  · by_cases zero : s.countdown = 0#8
    · have on : Cyclic s := Or.inr (Or.inl phase)
      have current := h.current (Or.inl on)
      rcases h.cycles on with pc | pc | pc | pc <;>
        simp [txFlightBits,txQualified,State.txEvent,State.consumes,State.captures,
          clock,engine,phase,zero,current,pc,row,Instruction.isStream,Instruction.hasHighGuard,
          State.enterHigh,State.captureData,i2cHold,i2cStopLow]
    · simp [txFlightBits,txQualified,State.txEvent,State.consumes,State.captures,
        clock,engine,phase,zero]
  · by_cases zero : s.countdown = 0#8
    · cases stream : s.current.isStream <;> by_cases more : s.remaining.toNat > 1 <;>
        simp [txFlightBits,txQualified,State.txEvent,State.consumes,State.captures,
          clock,engine,phase,zero,stream,more]
    · simp [txFlightBits,txQualified,State.txEvent,State.consumes,State.captures,
        clock,engine,phase,zero]
  · cases ready : s.waitReady
    · have miss : s.current.guard.limit.expires s.countdown = false := by
        cases expired : s.current.guard.limit.expires s.countdown
        · rfl
        · simp [clock,engine,phase,ready,expired,State.timeoutFault] at safe
      simp [txFlightBits,txQualified,State.txEvent,State.consumes,State.captures,
        clock,engine,phase,ready,miss]
    · have current := h.current (Or.inr phase)
      rcases h.waits phase with pc | pc | pc <;>
        simp [txFlightBits,txQualified,State.txEvent,State.consumes,State.captures,
          clock,engine,phase,ready,current,pc,row,Instruction.isStream,Instruction.cell,
          State.enterHigh,State.captureData,i2cCell]
  · simp [txFlightBits,txQualified,State.txEvent,State.consumes,State.captures,clock,engine,phase]

private theorem trace_step_eq_clock (s : State a) (i : Input) (h : Positioned profile s)
    (ordinary : Unreleased i) (trace : BitTrace) : trace.step s i = trace.clock s i := by
  rcases ordinary with ⟨⟨cold,warm⟩,release⟩
  have notFree : s.phase ≠ .free := by
    rcases h.phase with phase | (phase | phase | phase) | phase | phase <;> simp [phase]
  simp [BitTrace.step,cold,(show i.command ≠ 15#4 from warm),release,State.canStart,notFree]

/-- The consumed TX bits are the qualified bits followed by any one reserved
bit in the current cell. -/
theorem tx_qualified_run (s : State a) (trace : BitTrace) (sent : List Bool)
    (history : trace.consumed = sent ++ txFlightBits s) (inputs : List Input)
    (h : Positioned profile s) (ordinary : ∀ i ∈ inputs, Unreleased i)
    (safe : (run (program profile) s inputs).phase ≠ .fault) :
    (traceRun (program profile) s trace inputs).consumed =
      sent ++ txQualifiedRun profile s inputs ++ txFlightBits (run (program profile) s inputs) := by
  induction inputs generalizing s trace sent with
  | nil => simpa [traceRun,txQualifiedRun,run] using history
  | cons i rest ih =>
    let next := step (program profile) i s
    have first := ordinary i List.mem_cons_self
    have tail : ∀ j ∈ rest, Unreleased j := fun j mem => ordinary j (List.mem_cons_of_mem _ mem)
    have noFault : next.phase ≠ .fault := fun fault => safe (fault_run profile next rest fault tail)
    have advance : (trace.step s i).consumed = (sent ++ txQualified s) ++ txFlightBits next := by
      rw [trace_step_eq_clock profile s i h first]
      change trace.consumed ++ s.txEvent = _
      rw [history,List.append_assoc,tx_qualified_step profile s i h first noFault,← List.append_assoc]
    have positioned := (positioned_step profile s i h first noFault).1
    have later := ih next (trace.step s i) (sent ++ txQualified s) advance positioned tail safe
    change (traceRun (program profile) next (trace.step s i) rest).consumed =
      sent ++ (txQualified s ++ txQualifiedRun profile next rest) ++ txFlightBits (run (program profile) next rest)
    simpa only [List.append_assoc] using later

theorem qualified_completed (s : State a) (inputs : List Input) (h : Positioned profile s)
    (ordinary : ∀ i ∈ inputs, Unreleased i) (complete : (run (program profile) s inputs).phase = .completed)
    (empty : txFlightBits s = []) :
    (traceRun (program profile) s {} inputs).consumed = txQualifiedRun profile s inputs := by
  have flow := tx_qualified_run profile s {} [] (by simp [empty]) inputs h ordinary (by simp [complete])
  simpa [complete,txFlightBits] using flow

/-- At successful completion every reserved controller bit has qualified. -/
theorem started_tx_qualified (before : State a) (start : Input) (inputs : List Input)
    (positive : 0 < start.startCount.toNat) (ordinary : ∀ i ∈ inputs, Unreleased i)
    (complete : (run (program profile) (before.start (program profile) start) inputs).phase = .completed) :
    (traceRun (program profile) (before.start (program profile) start) {} inputs).consumed =
      txQualifiedRun profile (before.start (program profile) start) inputs :=
  qualified_completed profile _ inputs (positioned_start profile before start positive) ordinary complete rfl

end Profiled

export Profiled (txFlightBits)

abbrev tx_qualified_step := @Profiled.tx_qualified_step .standard
abbrev tx_qualified_run := @Profiled.tx_qualified_run .standard
abbrev qualified_completed := @Profiled.qualified_completed .standard
abbrev started_tx_qualified := @Profiled.started_tx_qualified .standard

end Pinwheel.Program.StreamingI2CTrace
