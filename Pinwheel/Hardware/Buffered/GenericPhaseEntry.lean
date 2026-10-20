import Pinwheel.Hardware.Buffered.SpiCircuit

/-! Actual packed entry updates for every reactive instruction kind. These
equations keep entry decoding and its datapath decisions in the circuit graph. -/
namespace Pinwheel.Hardware.Buffered.GenericPhase
open Pinwheel.Hardware
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

def runEntryTick (i : Values Reactive.Input) (r : Values Reactive.Register) :
    Values Reactive.Register
  | _, .transfer => if Reactive.starting.eval i r = 1 then r .transfer + 1 else r .transfer
  | _, .phase => Reactive.entryPhase.eval i r
  | _, .pc => Reactive.entryPC.eval i r
  | _, .virtualPC => (Reactive.entryVirtual.eval i r).extractLsb' 0 10
  | _, .currentControl => (Reactive.entryControl.eval i r).extractLsb' 0 22
  | _, .outer => Reactive.entryOuter.eval i r
  | _, .inner => Reactive.entryInner.eval i r
  | _, .remaining => if (Reactive.isKind 5).eval i r = 1 then
      (Reactive.entryWord.eval i r).extractLsb' 47 8 else (Reactive.entryWord.eval i r).extractLsb' 9 8
  | _, .waitLeft => if (Reactive.isKind 7).eval i r = 1 then
      (Reactive.entryWord.eval i r).extractLsb' 47 8 else 0
  | _, .scratch => Reactive.entryScratch.eval i r
  | _, .cachedDuration => (Reactive.entryWord.eval i r).extractLsb' 9 8
  | _, .cachedBudget => (Reactive.entryWord.eval i r).extractLsb' 47 8
  | _, .cachedCheck => (Reactive.entryWord.eval i r).extractLsb' 41 4
  | _, .cachedWait => (Reactive.entryWord.eval i r).extractLsb' 45 2
  | _, .cachedTerminal => Reactive.terminalCapture.eval i r
  | _, .cachedBranch => (Reactive.entryBranch.eval i r).extractLsb' 0 54
  | _, .levels => Reactive.entryLevels.eval i r
  | _, .enabled => Reactive.entryEnabled.eval i r
  | _, .txData => if Reactive.consuming.eval i r = 1 then
      0#1 ++ (Reactive.entryTx.eval i r).extractLsb' 1 31 else Reactive.entryTx.eval i r
  | _, .txLength => Reactive.entryTxLength.eval i r
  | _, .txConsumed => if Reactive.consuming.eval i r = 1 then
      Reactive.entryConsumed.eval i r + 1 else Reactive.entryConsumed.eval i r
  | _, .rxData => if Reactive.appending.eval i r = 1 then Reactive.appended.eval i r
      else if Reactive.starting.eval i r = 1 then 0 else r .rxData
  | _, .rxLength => if Reactive.appending.eval i r = 1 then
      Reactive.entryRxLength.eval i r + 1 else Reactive.entryRxLength.eval i r
  | _, .rxCapacity => Reactive.entryCapacity.eval i r
  | _, .stage1 => i .rawInputs
  | _, .stage2 => r .stage1
  | _, reg => r reg

theorem run_entry_step (i : Values Reactive.Input) (r : Values Reactive.Register)
    (executing : SramExecution.ExecutingInput i)
    (release : Reactive.releasing.eval i r = 0)
    (entering : Reactive.entering.eval i r = 1)
    (stopping : Reactive.stopping.eval i r = 0)
    (running : Reactive.runEntry.eval i r = 1) :
    @Circuit.step Reactive.Input Reactive.Register Reactive.Output Reactive.circuit i r =
      @runEntryTick i r := by
  rcases SpiCircuit.runtime_controls i r executing release with ⟨reset, clear, commit, write, warm⟩
  funext width reg
  cases reg
  all_goals simp [Circuit.step, Reactive.circuit, Reactive.next, runEntryTick,
    Reactive.either, Reactive.both, Reactive.cold, Reactive.entryTx,
    Reactive.entryTxLength, Reactive.entryConsumed, Reactive.entryRxLength,
    Reactive.entryCapacity, Reactive.increment, BitVec.sub_eq_add_neg, Expr.eval,
    reset, clear, commit, write, warm, executing.2.1, entering, stopping, running]
  all_goals done

end Pinwheel.Hardware.Buffered.GenericPhase
