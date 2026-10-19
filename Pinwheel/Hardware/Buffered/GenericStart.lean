import Pinwheel.Hardware.Buffered.GenericStartRelation

/-! A certified installed image and the actual START admission gate suffice
to establish generic source/circuit execution. No successful transfer outcome
or post-edge observation equality is assumed. -/
namespace Pinwheel.Hardware.Buffered.GenericStart
open Pinwheel.Hardware Pinwheel.Program

theorem start_related {p : Program.Buffered.Program} {layout : GenericCertificate.Layout p}
    (i : Values Reactive.Input) (r : Values Reactive.Register)
    (installed : Installed p layout r) (starting : Reactive.starting.eval i r = 1) :
    Refinement.Related p layout (i .txData) (Reactive.circuit.step i r) (started p r i) := by
  have within := GenericLayout.span_positive p.code
  obtain ⟨instruction, fetch, _⟩ := layout.sourceRecord 0 within
  have controls := SpiAdmission.starting_controls i r starting
  have atEntry := entryAt layout i r starting
  have word := atEntry.word within instruction fetch installed.image
  have flag := flags instruction i r starting (legal installed starting) word
  rw [started_final p layout r i instruction fetch]
  change Refinement.Related p layout (i .txData) (Reactive.circuit.step i r)
    (GenericEntry.finalState p (base p r i) (execution r i) 0 instruction
      (Vector.replicate 16 false) (r .stage2))
  cases stops : GenericEffects.finalOutcome instruction (execution r i) (r .stage2)
  case none =>
    have success := GenericEntryFlags.final_none instruction (execution r i) (r .stage2) stops
    have running : Reactive.runEntry.eval i r = 1 := by rw [flag.running, success.1]; rfl
    have stopping : Reactive.stopping.eval i r = 0 := by
      simpa only [stops, Option.isSome_none, BitVec.ofBool_false] using flag.stopping
    rw [GenericPhase.run_entry_step i r controls.executing controls.releasing
      controls.entering stopping running]
    simp only [GenericEntry.finalState, stops]
    change Refinement.Related p layout (i .txData) (GenericPhase.runEntryTick i r)
      (GenericEffects.replaceExecution
        (GenericEntry.coreState p (base p r i) 0 instruction (Vector.replicate 16 false) (r .stage2))
        ((GenericEffects.result instruction (execution r i) (r .stage2)).execution (execution r i)))
    exact Or.inl ⟨_, instruction, 0,
      GenericStart.running instruction i r installed starting fetch word flag
        ⟨success.2.1, success.2.2.1⟩ success.2.2.2⟩
  case some outcome =>
    have stopping : Reactive.stopping.eval i r = 1 := by
      simpa only [stops, Option.isSome_some, BitVec.ofBool_true] using flag.stopping
    rw [GenericPhase.entry_stop_step i r controls.executing controls.releasing
      controls.entering stopping flag.heldTimeout]
    simp only [GenericEntry.finalState, stops]
    change Refinement.Related p layout (i .txData) (GenericPhase.entryStopTick i r)
      (Program.Buffered.terminal p Refinement.capacity (updated p instruction i r) outcome)
    exact Or.inr ⟨_, outcome, GenericStart.stopped instruction i r installed starting word flag outcome stops⟩

end Pinwheel.Hardware.Buffered.GenericStart
