import Pinwheel.Hardware.Buffered.GenericPhaseEntry

/-! Terminal entry retains the actual entry datapath effects, including a
consumed TX bit before RX overflow, and distinguishes explicit timeout words. -/
namespace Pinwheel.Hardware.Buffered.GenericPhase
open Pinwheel.Hardware
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

def entryStopTick (i : Values Reactive.Input) (r : Values Reactive.Register) :
    Values Reactive.Register
  | _, .phase => if Reactive.entryTimeout.eval i r = 1 then 6
      else if Reactive.entryComplete.eval i r = 1 then 5 else 7
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
  | _, reg => runEntryTick i r reg

theorem entry_stop_step (i : Values Reactive.Input) (r : Values Reactive.Register)
    (executing : SramExecution.ExecutingInput i)
    (release : Reactive.releasing.eval i r = 0)
    (entering : Reactive.entering.eval i r = 1)
    (stopping : Reactive.stopping.eval i r = 1)
    (heldTimeout : Reactive.heldTimeout.eval i r = 0) :
    @Circuit.step Reactive.Input Reactive.Register Reactive.Output Reactive.circuit i r =
      @entryStopTick i r := by
  rcases SpiCircuit.runtime_controls i r executing release with ⟨reset, clear, commit, write, warm⟩
  funext width reg
  cases reg
  all_goals simp [Circuit.step, Reactive.circuit, Reactive.next, entryStopTick, runEntryTick,
    Reactive.either, Reactive.both, Reactive.cold, Reactive.entryTx,
    Reactive.entryTxLength, Reactive.entryConsumed, Reactive.entryRxLength,
    Reactive.entryCapacity, Reactive.increment, BitVec.sub_eq_add_neg, Expr.eval,
    reset, clear, commit, write, warm, executing.2.1, entering, stopping, heldTimeout]
  all_goals simp only [show (1#1) = BitVec.allOnes 1 from rfl,
    BitVec.allOnes_and, BitVec.not_not]
  all_goals done

end Pinwheel.Hardware.Buffered.GenericPhase
