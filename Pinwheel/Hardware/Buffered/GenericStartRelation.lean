import Pinwheel.Hardware.Buffered.GenericStartCommon

/-! One actual admitted START establishes the full generic source relation
for every certified instruction kind, including immediate retained outcomes. -/
namespace Pinwheel.Hardware.Buffered.GenericStart
open Pinwheel.Hardware Pinwheel.Program

theorem running {p : Program.Buffered.Program} {layout : GenericCertificate.Layout p}
    (instruction : Program.Buffered.Instruction) (i : Values Reactive.Input)
    (r : Values Reactive.Register) (installed : Installed p layout r)
    (starting : Reactive.starting.eval i r = 1) (fetch : p.fetch 0 = some instruction)
    (word : Reactive.entryWord.eval i r = GenericEncoding.encode instruction)
    (flags : GenericEntryFlags.Flags instruction (execution r i) (r .stage2) i r)
    (nonterminal : (GenericEncoding.instruction instruction).kind ≠ 3 ∧
      (GenericEncoding.instruction instruction).kind ≠ 4)
    (success : (GenericEffects.result instruction (execution r i) (r .stage2)).outcome = none) :
    Refinement.Running p layout (i .txData) (GenericPhase.runEntryTick i r)
      (updated p instruction i r)
      ((GenericEffects.result instruction (execution r i) (r .stage2)).execution (execution r i))
      instruction 0 := by
  have atEntry := entryAt layout i r starting
  have branch := atEntry.branch (GenericLayout.span_positive p.code) instruction fetch installed.image
  refine ⟨common_running instruction i r installed starting word flags nonterminal success,
    rfl, GenericLayout.span_positive p.code, fetch, atEntry.coordinates, ?_, ?_,
    Refinement.Caches.runEntryTick p layout i r instruction word branch,
    Refinement.entry_control i r instruction 0 word nonterminal,
    (SpiCircuit.starting_facts i r starting).retained, rfl, rfl⟩
  · change (Reactive.entryVirtual.eval i r).extractLsb' 0 10 = BitVec.ofNat 10 0
    rw [atEntry.virtualPC]
    rfl
  · change (Reactive.entryControl.eval i r).extractLsb' 0 22 = _
    simp only [Reactive.entryControl, Expr.eval,
      Refinement.entryRecord layout i r 0 atEntry.entering atEntry.address installed.image]
    apply BitVec.eq_of_getLsbD_eq
    intro k bound
    simp [bound, show k < 24 by omega]

theorem stopped {p : Program.Buffered.Program} {layout : GenericCertificate.Layout p}
    (instruction : Program.Buffered.Instruction) (i : Values Reactive.Input)
    (r : Values Reactive.Register) (installed : Installed p layout r)
    (starting : Reactive.starting.eval i r = 1)
    (word : Reactive.entryWord.eval i r = GenericEncoding.encode instruction)
    (flags : GenericEntryFlags.Flags instruction (execution r i) (r .stage2) i r)
    (outcome : Transfer.Outcome)
    (stops : GenericEffects.finalOutcome instruction (execution r i) (r .stage2) = some outcome) :
    Refinement.Stopped p layout (i .txData) (GenericPhase.entryStopTick i r)
      (Program.Buffered.terminal p Refinement.capacity (updated p instruction i r) outcome)
      ((GenericEffects.result instruction (execution r i) (r .stage2)).execution (execution r i))
      outcome := by
  have terminal := SpiInterpreter.terminal_running p Refinement.capacity (updated p instruction i r)
    ((GenericEffects.result instruction (execution r i) (r .stage2)).execution (execution r i))
    outcome rfl rfl
  refine ⟨common_stopped instruction i r installed starting word flags outcome,
    ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · rw [terminal]
  · rw [terminal]
    cases outcome <;> rfl
  · change (if Reactive.entryTimeout.eval i r = 1 then 6
      else if Reactive.entryComplete.eval i r = 1 then 5 else 7) = _
    rw [flags.timeout, flags.complete]
    exact GenericEntryFlags.final_some_phase instruction (execution r i) (r .stage2) outcome stops

end Pinwheel.Hardware.Buffered.GenericStart
