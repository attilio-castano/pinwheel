import Pinwheel.Hardware.Buffered.GenericPhase

namespace Pinwheel.Hardware.Buffered.GenericPhase
open Pinwheel.Hardware
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

structure Dispatching (i : Values Reactive.Input) (r : Values Reactive.Register)
    (capture : Bool) : Prop where
  entering : Reactive.entering.eval i r = 1
  terminal : Reactive.terminalEdge.eval i r = BitVec.ofBool capture
  fault : Reactive.heldFault.eval i r = 0
  timeout : Reactive.heldTimeout.eval i r = 0

theorem active_dispatching (i : Values Reactive.Input) (r : Values Reactive.Register)
    (quiet : SpiCircuit.Quiet i) (phase : r .phase = 1) (remaining : r .remaining = 0) :
    Dispatching i r false := by
  constructor
  all_goals simp [Reactive.entering, Reactive.dispatch, Reactive.terminalEdge,
    Reactive.heldFault, Reactive.heldTimeout, Reactive.isPhase, Reactive.both,
    Reactive.either, Expr.eval, phase, remaining,
    (SpiCircuit.quiet_controls i r quiet).1, (SpiCircuit.quiet_controls i r quiet).2.2.1]
  all_goals done

theorem wait_dispatching (i : Values Reactive.Input) (r : Values Reactive.Register)
    (quiet : SpiCircuit.Quiet i) (phase : r .phase = 2)
    (ready : Reactive.waitReady.eval i r = 1) : Dispatching i r false := by
  constructor
  all_goals simp [Reactive.entering, Reactive.dispatch, Reactive.terminalEdge,
    Reactive.heldFault, Reactive.heldTimeout, Reactive.isPhase, Reactive.both,
    Reactive.either, Expr.eval, phase, ready,
    (SpiCircuit.quiet_controls i r quiet).1, (SpiCircuit.quiet_controls i r quiet).2.2.1]
  all_goals done

theorem checked_dispatching (i : Values Reactive.Input) (r : Values Reactive.Register)
    (quiet : SpiCircuit.Quiet i) (phase : r .phase = 3)
    (ready : Reactive.checkedReady.eval i r = 1) (remaining : r .remaining = 0) :
    Dispatching i r true := by
  constructor
  all_goals simp [Reactive.entering, Reactive.dispatch, Reactive.terminalEdge,
    Reactive.heldFault, Reactive.heldTimeout, Reactive.isPhase, Reactive.both,
    Reactive.either, Expr.eval, phase, ready, remaining,
    (SpiCircuit.quiet_controls i r quiet).1, (SpiCircuit.quiet_controls i r quiet).2.2.1]
  all_goals done

theorem qualify_dispatching (i : Values Reactive.Input) (r : Values Reactive.Register)
    (quiet : SpiCircuit.Quiet i) (phase : r .phase = 4)
    (ready : Reactive.checkedReady.eval i r = 1) (remaining : r .remaining = 0) :
    Dispatching i r false := by
  constructor
  all_goals simp [Reactive.entering, Reactive.dispatch, Reactive.terminalEdge,
    Reactive.heldFault, Reactive.heldTimeout, Reactive.isPhase, Reactive.both,
    Reactive.either, Expr.eval, phase, ready, remaining,
    (SpiCircuit.quiet_controls i r quiet).1, (SpiCircuit.quiet_controls i r quiet).2.2.1]
  all_goals done

end Pinwheel.Hardware.Buffered.GenericPhase
