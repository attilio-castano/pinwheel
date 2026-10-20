import Pinwheel.Hardware.Buffered.GenericPhaseScratch

/-! Exact actual-circuit phase transitions. Word entry and host ownership
remain separate from these clock-only holding and terminal equations. -/
namespace Pinwheel.Hardware.Buffered.GenericPhase
open Pinwheel.Hardware
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

def holdTick (r : Values Reactive.Register) (raw : BitVec 2)
    (remaining waitLeft : BitVec 8) : Values Reactive.Register
  | _, .remaining => remaining
  | _, .waitLeft => waitLeft
  | _, .stage1 => raw
  | _, .stage2 => r .stage1
  | _, reg => r reg

structure Holding (i : Values Reactive.Input) (r : Values Reactive.Register) : Prop where
  busy : Reactive.busy.eval i r = 1
  entering : Reactive.entering.eval i r = 0
  stopping : Reactive.stopping.eval i r = 0
  terminal : Reactive.terminalEdge.eval i r = 0

theorem wait_blocked_controls (i : Values Reactive.Input) (r : Values Reactive.Register)
    (quiet : SpiCircuit.Quiet i) (phase : r .phase = 2)
    (blocked : Reactive.waitReady.eval i r = 0) (remaining : r .remaining ≠ 0#8) :
    Holding i r := by
  constructor
  all_goals simp [Reactive.busy, Reactive.entering, Reactive.stopping,
    Reactive.dispatch, Reactive.heldFault, Reactive.heldTimeout, Reactive.terminalEdge,
    Reactive.entryFailed, Reactive.entryComplete, Reactive.isPhase, Reactive.both,
    Reactive.either, Expr.eval, phase, blocked, remaining,
    (SpiCircuit.quiet_controls i r quiet).1, (SpiCircuit.quiet_controls i r quiet).2.2.1]
  done

theorem checked_ready_controls (i : Values Reactive.Input) (r : Values Reactive.Register)
    (quiet : SpiCircuit.Quiet i) (phase : r .phase = 3)
    (ready : Reactive.checkedReady.eval i r = 1) (remaining : r .remaining ≠ 0#8) :
    Holding i r := by
  constructor
  all_goals simp [Reactive.busy, Reactive.entering, Reactive.stopping,
    Reactive.dispatch, Reactive.heldFault, Reactive.heldTimeout, Reactive.terminalEdge,
    Reactive.entryFailed, Reactive.entryComplete, Reactive.isPhase, Reactive.both,
    Reactive.either, Expr.eval, phase, ready, remaining,
    (SpiCircuit.quiet_controls i r quiet).1, (SpiCircuit.quiet_controls i r quiet).2.2.1]
  all_goals done

theorem qualify_ready_controls (i : Values Reactive.Input) (r : Values Reactive.Register)
    (quiet : SpiCircuit.Quiet i) (phase : r .phase = 4)
    (ready : Reactive.checkedReady.eval i r = 1) (remaining : r .remaining ≠ 0#8) :
    Holding i r := by
  constructor
  all_goals simp [Reactive.busy, Reactive.entering, Reactive.stopping,
    Reactive.dispatch, Reactive.heldFault, Reactive.heldTimeout, Reactive.terminalEdge,
    Reactive.entryFailed, Reactive.entryComplete, Reactive.isPhase, Reactive.both,
    Reactive.either, Expr.eval, phase, ready, remaining,
    (SpiCircuit.quiet_controls i r quiet).1, (SpiCircuit.quiet_controls i r quiet).2.2.1]
  all_goals done

theorem qualify_blocked_controls (i : Values Reactive.Input) (r : Values Reactive.Register)
    (quiet : SpiCircuit.Quiet i) (phase : r .phase = 4)
    (blocked : Reactive.checkedReady.eval i r = 0) (waitLeft : r .waitLeft ≠ 0#8) :
    Holding i r := by
  constructor
  all_goals simp [Reactive.busy, Reactive.entering, Reactive.stopping,
    Reactive.dispatch, Reactive.heldFault, Reactive.heldTimeout, Reactive.terminalEdge,
    Reactive.entryFailed, Reactive.entryComplete, Reactive.isPhase, Reactive.both,
    Reactive.either, Expr.eval, phase, blocked, waitLeft,
    (SpiCircuit.quiet_controls i r quiet).1, (SpiCircuit.quiet_controls i r quiet).2.2.1]
  all_goals done

theorem holding_step (i : Values Reactive.Input) (r : Values Reactive.Register)
    (quiet : SpiCircuit.Quiet i) (busy : Reactive.busy.eval i r = 1)
    (entering : Reactive.entering.eval i r = 0)
    (stopping : Reactive.stopping.eval i r = 0)
    (terminal : Reactive.terminalEdge.eval i r = 0) :
    @Circuit.step Reactive.Input Reactive.Register Reactive.Output Reactive.circuit i r =
      @holdTick r (i .rawInputs)
      (if r .phase = 4 ∧ Reactive.checkedReady.eval i r = 0 then
        r .cachedDuration else r .remaining - 1)
      (if r .phase = 4 then
        if Reactive.checkedReady.eval i r = 1 then r .cachedBudget else r .waitLeft - 1
       else r .waitLeft) := by
  rcases SpiCircuit.quiet_controls i r quiet with ⟨reset, clear, start, commit, write, release⟩
  rcases Reactive.effects_only_on_entry i r entering with ⟨consume, append⟩
  funext width reg
  cases reg
  all_goals simp [Circuit.step, Reactive.circuit, Reactive.next, holdTick,
    Reactive.either, Reactive.both, Reactive.cold, Reactive.warm, Reactive.cmd,
    Reactive.runEntry, Reactive.exitScratch, Reactive.isPhase, Expr.eval,
    reset, clear, start, commit, write, busy, entering, stopping, terminal,
    consume, append, quiet.1, quiet.2]
  all_goals rcases BitVec.eq_zero_or_eq_one (Reactive.checkedReady.eval i r) with ready | ready
  all_goals by_cases phase : r .phase = 4#3 <;> simp [phase, ready]
  all_goals done

theorem Holding.step {i : Values Reactive.Input} {r : Values Reactive.Register}
    (h : Holding i r) (quiet : SpiCircuit.Quiet i) :
    @Circuit.step Reactive.Input Reactive.Register Reactive.Output Reactive.circuit i r =
      @holdTick r (i .rawInputs)
      (if r .phase = 4 ∧ Reactive.checkedReady.eval i r = 0 then
        r .cachedDuration else r .remaining - 1)
      (if r .phase = 4 then
        if Reactive.checkedReady.eval i r = 1 then r .cachedBudget else r .waitLeft - 1
       else r .waitLeft) :=
  holding_step i r quiet h.busy h.entering h.stopping h.terminal

theorem wait_blocked_step (i : Values Reactive.Input) (r : Values Reactive.Register)
    (quiet : SpiCircuit.Quiet i) (phase : r .phase = 2)
    (blocked : Reactive.waitReady.eval i r = 0) (remaining : r .remaining ≠ 0#8) :
    @Circuit.step Reactive.Input Reactive.Register Reactive.Output Reactive.circuit i r =
      @holdTick r (i .rawInputs) (r .remaining - 1) (r .waitLeft) := by
  have flags := wait_blocked_controls i r quiet phase blocked remaining
  simpa [phase] using holding_step i r quiet flags.busy flags.entering flags.stopping flags.terminal
  done

theorem checked_ready_step (i : Values Reactive.Input) (r : Values Reactive.Register)
    (quiet : SpiCircuit.Quiet i) (phase : r .phase = 3)
    (ready : Reactive.checkedReady.eval i r = 1) (remaining : r .remaining ≠ 0#8) :
    @Circuit.step Reactive.Input Reactive.Register Reactive.Output Reactive.circuit i r =
      @holdTick r (i .rawInputs) (r .remaining - 1) (r .waitLeft) := by
  simpa [phase] using (checked_ready_controls i r quiet phase ready remaining).step quiet

theorem qualify_ready_step (i : Values Reactive.Input) (r : Values Reactive.Register)
    (quiet : SpiCircuit.Quiet i) (phase : r .phase = 4)
    (ready : Reactive.checkedReady.eval i r = 1) (remaining : r .remaining ≠ 0#8) :
    @Circuit.step Reactive.Input Reactive.Register Reactive.Output Reactive.circuit i r =
      @holdTick r (i .rawInputs) (r .remaining - 1) (r .cachedBudget) := by
  simpa [phase, ready] using (qualify_ready_controls i r quiet phase ready remaining).step quiet

theorem qualify_blocked_step (i : Values Reactive.Input) (r : Values Reactive.Register)
    (quiet : SpiCircuit.Quiet i) (phase : r .phase = 4)
    (blocked : Reactive.checkedReady.eval i r = 0) (waitLeft : r .waitLeft ≠ 0#8) :
    @Circuit.step Reactive.Input Reactive.Register Reactive.Output Reactive.circuit i r =
      @holdTick r (i .rawInputs) (r .cachedDuration) (r .waitLeft - 1) := by
  simpa [phase, blocked] using (qualify_blocked_controls i r quiet phase blocked waitLeft).step quiet

end Pinwheel.Hardware.Buffered.GenericPhase
