import Pinwheel.Hardware.Buffered.GenericStartFlags

/-! START loads the full original payload and initializes its logical prefix,
then performs this entry's consume and append decisions. Old data registers
play no role, including in retained diagnostic data on an immediate fault. -/
namespace Pinwheel.Hardware.Buffered.GenericStart
open Pinwheel.Hardware Pinwheel.Program

theorem appended_first (i : Values Reactive.Input) (r : Values Reactive.Register)
    (starting : Reactive.starting.eval i r = 1) :
    Reactive.appended.eval i r =
      SpiPacking.rxWord [(Reactive.sampled.eval i r).getLsbD 0] := by
  apply BitVec.eq_of_getLsbD_eq
  intro index bound
  rw [SpiDatapath.appended_bit i r ⟨index, bound⟩,
    show [(Reactive.sampled.eval i r).getLsbD 0] =
      [] ++ [(Reactive.sampled.eval i r).getLsbD 0] from rfl,
    SpiPacking.rxWord_append_getLsbD [] _ index bound]
  have condition : 0#6 = BitVec.ofNat 6 index ↔ index = 0 := by
    simp [← BitVec.toNat_inj, Nat.mod_eq_of_lt (by omega : index < 2^6), eq_comm]
  simp [Reactive.entryRxLength, Expr.eval, starting, condition]
  done

theorem datapath (i : Values Reactive.Input) (r : Values Reactive.Register)
    (starting : Reactive.starting.eval i r = 1) (consume receive : Bool)
    (consuming : Reactive.consuming.eval i r = BitVec.ofBool consume)
    (appending : Reactive.appending.eval i r = BitVec.ofBool receive)
    (available : consume = true → 0 < (i .txLength).toNat)
    (room : receive = true → 0 < (i .rxCapacity).toNat) :
    Refinement.Datapath (i .txData) (GenericPhase.runEntryTick i r)
      (Refinement.entryExecution (execution r i) consume receive
        ((Reactive.sampled.eval i r).getLsbD 0)) := by
  have facts := SpiCircuit.starting_facts i r starting
  cases consume <;> cases receive <;> constructor
  all_goals simp [Transfer.Execution.Bounded, Transfer.Request.Bounded,
    SpiRefinement.capacity, execution, SpiStart.request,
    Refinement.entryExecution, GenericPhase.runEntryTick, Reactive.entryTx,
    Reactive.entryTxLength, Reactive.entryConsumed, Reactive.entryRxLength,
    Reactive.entryCapacity, Expr.eval, starting, consuming, appending,
    facts.txLength, facts.rxCapacity, SpiDatapath.shift_one,
    appended_first i r starting]
  all_goals have transfer := facts.transfer
  all_goals simp_all [Nat.succ_le_iff]
  all_goals omega
  done

theorem datapath_result (instruction : Program.Buffered.Instruction)
    (i : Values Reactive.Input) (r : Values Reactive.Register)
    (starting : Reactive.starting.eval i r = 1)
    (word : Reactive.entryWord.eval i r = GenericEncoding.encode instruction)
    (consuming : Reactive.consuming.eval i r =
      BitVec.ofBool (GenericEffects.result instruction (execution r i) (r .stage2)).consume)
    (appending : Reactive.appending.eval i r =
      BitVec.ofBool (GenericEffects.result instruction (execution r i) (r .stage2)).receive) :
    Refinement.Datapath (i .txData) (GenericPhase.runEntryTick i r)
      ((GenericEffects.result instruction (execution r i) (r .stage2)).execution (execution r i)) := by
  have bounds := GenericEffects.result_bounds instruction (execution r i) (r .stage2)
  have updated := datapath i r starting _ _ consuming appending
    (by simpa [execution, SpiStart.request] using bounds.1)
    (by simpa [execution, SpiStart.request] using bounds.2)
  cases receive : (GenericEffects.result instruction (execution r i) (r .stage2)).receive
  case false =>
    simpa only [Refinement.entryExecution, GenericEffects.Result.execution, receive,
      Bool.false_eq_true, ↓reduceIte] using updated
  case true =>
    simpa only [Refinement.entryExecution, GenericEffects.Result.execution,
      GenericSample.sampled_on_receive instruction (execution r i) i r word receive] using updated

theorem stop_datapath_result (instruction : Program.Buffered.Instruction)
    (i : Values Reactive.Input) (r : Values Reactive.Register)
    (starting : Reactive.starting.eval i r = 1)
    (word : Reactive.entryWord.eval i r = GenericEncoding.encode instruction)
    (consuming : Reactive.consuming.eval i r =
      BitVec.ofBool (GenericEffects.result instruction (execution r i) (r .stage2)).consume)
    (appending : Reactive.appending.eval i r =
      BitVec.ofBool (GenericEffects.result instruction (execution r i) (r .stage2)).receive) :
    Refinement.Datapath (i .txData) (GenericPhase.entryStopTick i r)
      ((GenericEffects.result instruction (execution r i) (r .stage2)).execution (execution r i)) := by
  have h := datapath_result instruction i r starting word consuming appending
  exact ⟨h.bounded, h.tx, h.txLength, h.rxCapacity, h.consumed, h.shifted,
    h.rxLength, h.received, h.generation, h.transfer⟩

end Pinwheel.Hardware.Buffered.GenericStart
