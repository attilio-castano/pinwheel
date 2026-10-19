import Pinwheel.Hardware.Buffered.GenericStartImage
import Pinwheel.Hardware.Buffered.GenericEntryFacts

/-! Entry flags on an admitted START compare the operands of that START,
independently of stale buffer registers from an earlier transfer. -/
namespace Pinwheel.Hardware.Buffered.GenericStart
open Pinwheel.Hardware Pinwheel.Program GenericEntryFlags
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

def execution (r : Values Reactive.Register) (i : Values Reactive.Input) : Transfer.Execution :=
  ⟨request r i, 0, []⟩

private theorem append_some_nonzero : ∀ input : Fin 2,
    GenericEncoding.append (some input) ≠ 0#2 := by
  decide +kernel

private theorem one_and (x : BitVec 1) : 1#1 &&& x = x := BitVec.allOnes_and
private theorem append_none : GenericEncoding.append none = 0#2 := rfl

theorem flags (instruction : Program.Buffered.Instruction)
    (i : Values Reactive.Input) (r : Values Reactive.Register)
    (starting : Reactive.starting.eval i r = 1)
    (legal : Reactive.legalEntry.eval i r = 1)
    (word : Reactive.entryWord.eval i r = GenericEncoding.encode instruction) :
    GenericEntryFlags.Flags instruction (execution r i) (r .stage2) i r := by
  have h := SpiEntryControls.starting_preEntry i r starting legal
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h.heldFault, h.heldTimeout⟩
  all_goals rcases instruction with ⟨operation, append, preserveLevels, preserveEnabled⟩
  all_goals cases operation
  all_goals cases append
  all_goals by_cases available : 0 < (i .txLength).toNat
  all_goals by_cases room : 0 < (i .rxCapacity).toNat
  all_goals simp [Reactive.runEntry, Reactive.entryTerminal, Reactive.isKind, Reactive.kind,
    Reactive.underflow, Reactive.overflow, Reactive.consuming, Reactive.appending,
    Reactive.entryComplete, Reactive.entryFailed, Reactive.stopping, Reactive.entryTimeout,
    Reactive.entryConsumed, Reactive.entryTxLength, Reactive.entryRxLength, Reactive.entryCapacity,
    Reactive.wantsRx, Reactive.both, Reactive.either, Expr.eval, h.resetting, h.entering,
    h.legal, h.heldFault, h.heldTimeout, starting, word, GenericWord.kind_field,
    GenericWord.append_field, GenericWord.timeout_field, GenericEncoding.instruction,
    GenericEncoding.action, GenericEncoding.empty, append_some_nonzero, append_none, one_and,
    execution, SpiStart.request, available, room, runs, completes, timesOut,
    underflows, overflows, GenericEffects.result, GenericEffects.consumes,
    GenericEffects.finalOutcome, Program.Buffered.Failure.outcome]

end Pinwheel.Hardware.Buffered.GenericStart
