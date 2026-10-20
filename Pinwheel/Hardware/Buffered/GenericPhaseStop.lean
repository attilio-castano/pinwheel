import Pinwheel.Hardware.Buffered.GenericPhase

/-! Fault and timeout clocks stop the actual packed controller while retaining
its diagnostic prefix and arbitrary scratch bank. -/
namespace Pinwheel.Hardware.Buffered.GenericPhase
open Pinwheel.Hardware
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

def stopTick (r : Values Reactive.Register) (raw : BitVec 2) (timeout : Bool) :
    Values Reactive.Register
  | _, .phase => if timeout then 6 else 7
  | _, .retained => 1
  | _, .pc => 0
  | _, .virtualPC => 0
  | _, .currentControl => 0
  | _, .outer => 0
  | _, .inner => 0
  | _, .remaining => 0
  | _, .waitLeft => 0
  | _, .cachedDuration => 0
  | _, .cachedBudget => 0
  | _, .cachedCheck => 0
  | _, .cachedWait => 0
  | _, .cachedTerminal => 0
  | _, .cachedBranch => 0
  | _, .levels => r .idleLevels
  | _, .enabled => r .idleEnabled
  | _, reg => SpiCircuit.sampleTick r raw reg

structure HeldStop (i : Values Reactive.Input) (r : Values Reactive.Register)
    (timeout : Bool) : Prop where
  entering : Reactive.entering.eval i r = 0
  stopping : Reactive.stopping.eval i r = 1
  terminal : Reactive.terminalEdge.eval i r = 0
  timedOut : (Reactive.either Reactive.heldTimeout Reactive.entryTimeout).eval i r = BitVec.ofBool timeout

theorem held_stop_step (i : Values Reactive.Input) (r : Values Reactive.Register)
    (quiet : SpiCircuit.Quiet i) (timeout : Bool) (flags : HeldStop i r timeout) :
    @Circuit.step Reactive.Input Reactive.Register Reactive.Output Reactive.circuit i r =
      @stopTick r (i .rawInputs) timeout := by
  rcases SpiCircuit.quiet_controls i r quiet with ⟨reset, clear, start, commit, write, release⟩
  rcases Reactive.effects_only_on_entry i r flags.entering with ⟨consume, append⟩
  have complete : Reactive.entryComplete.eval i r = 0 := by
    simp [Reactive.entryComplete, Reactive.both, Expr.eval, flags.entering]
  have timed : ~~~(~~~Reactive.heldTimeout.eval i r &&& ~~~Reactive.entryTimeout.eval i r) =
      BitVec.ofBool timeout := flags.timedOut
  funext width reg
  cases reg
  all_goals simp [Circuit.step, Reactive.circuit, Reactive.next, stopTick, SpiCircuit.sampleTick,
    Reactive.either, Reactive.both, Reactive.cold, Reactive.warm, Reactive.cmd,
    Reactive.runEntry, Reactive.exitScratch, Expr.eval,
    reset, clear, start, commit, write, flags.entering, flags.stopping, flags.terminal,
    consume, append, complete, timed, quiet.1, quiet.2]
  all_goals done

theorem checked_fault_controls (i : Values Reactive.Input) (r : Values Reactive.Register)
    (quiet : SpiCircuit.Quiet i) (phase : r .phase = 3)
    (blocked : Reactive.checkedReady.eval i r = 0) : HeldStop i r false := by
  constructor
  all_goals simp [Reactive.entering, Reactive.stopping, Reactive.dispatch,
    Reactive.heldFault, Reactive.heldTimeout, Reactive.terminalEdge,
    Reactive.entryFailed, Reactive.entryComplete, Reactive.entryTimeout,
    Reactive.isPhase, Reactive.both, Reactive.either, Expr.eval, phase, blocked,
    (SpiCircuit.quiet_controls i r quiet).1, (SpiCircuit.quiet_controls i r quiet).2.2.1]
  all_goals done

theorem wait_timeout_controls (i : Values Reactive.Input) (r : Values Reactive.Register)
    (quiet : SpiCircuit.Quiet i) (phase : r .phase = 2)
    (blocked : Reactive.waitReady.eval i r = 0) (remaining : r .remaining = 0) :
    HeldStop i r true := by
  constructor
  all_goals simp [Reactive.entering, Reactive.stopping, Reactive.dispatch,
    Reactive.heldFault, Reactive.heldTimeout, Reactive.terminalEdge,
    Reactive.entryFailed, Reactive.entryComplete, Reactive.entryTimeout,
    Reactive.isPhase, Reactive.both, Reactive.either, Expr.eval, phase, blocked, remaining,
    (SpiCircuit.quiet_controls i r quiet).1, (SpiCircuit.quiet_controls i r quiet).2.2.1]
  all_goals done

theorem qualify_timeout_controls (i : Values Reactive.Input) (r : Values Reactive.Register)
    (quiet : SpiCircuit.Quiet i) (phase : r .phase = 4)
    (blocked : Reactive.checkedReady.eval i r = 0) (waitLeft : r .waitLeft = 0) :
    HeldStop i r true := by
  constructor
  all_goals simp [Reactive.entering, Reactive.stopping, Reactive.dispatch,
    Reactive.heldFault, Reactive.heldTimeout, Reactive.terminalEdge,
    Reactive.entryFailed, Reactive.entryComplete, Reactive.entryTimeout,
    Reactive.isPhase, Reactive.both, Reactive.either, Expr.eval, phase, blocked, waitLeft,
    (SpiCircuit.quiet_controls i r quiet).1, (SpiCircuit.quiet_controls i r quiet).2.2.1]
  all_goals done

theorem checked_fault_step (i : Values Reactive.Input) (r : Values Reactive.Register)
    (quiet : SpiCircuit.Quiet i) (phase : r .phase = 3)
    (blocked : Reactive.checkedReady.eval i r = 0) :
    @Circuit.step Reactive.Input Reactive.Register Reactive.Output Reactive.circuit i r =
      @stopTick r (i .rawInputs) false :=
  held_stop_step i r quiet false (checked_fault_controls i r quiet phase blocked)

theorem wait_timeout_step (i : Values Reactive.Input) (r : Values Reactive.Register)
    (quiet : SpiCircuit.Quiet i) (phase : r .phase = 2)
    (blocked : Reactive.waitReady.eval i r = 0) (remaining : r .remaining = 0) :
    @Circuit.step Reactive.Input Reactive.Register Reactive.Output Reactive.circuit i r =
      @stopTick r (i .rawInputs) true :=
  held_stop_step i r quiet true (wait_timeout_controls i r quiet phase blocked remaining)

theorem qualify_timeout_step (i : Values Reactive.Input) (r : Values Reactive.Register)
    (quiet : SpiCircuit.Quiet i) (phase : r .phase = 4)
    (blocked : Reactive.checkedReady.eval i r = 0) (waitLeft : r .waitLeft = 0) :
    @Circuit.step Reactive.Input Reactive.Register Reactive.Output Reactive.circuit i r =
      @stopTick r (i .rawInputs) true :=
  held_stop_step i r quiet true (qualify_timeout_controls i r quiet phase blocked waitLeft)

end Pinwheel.Hardware.Buffered.GenericPhase
