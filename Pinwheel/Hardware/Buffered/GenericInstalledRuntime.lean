import Pinwheel.Hardware.Buffered.GenericInstalledSram

/-! START, polling, rejected opcode five and RELEASE preserve the certified
resident image and geometry, independently of the engine's transfer phase. -/
namespace Pinwheel.Hardware.Buffered.Refinement
open Pinwheel.Hardware Pinwheel.Program

private inductive ImageField : Nat → Type where
  | count : ImageField 7
  | span : ImageField 11
  | idleLevels : ImageField 3
  | idleEnabled : ImageField 3
  | valid : ImageField 1
  | word (index : BitVec 6) : ImageField 144

private def ImageField.register : ImageField w → Reactive.Register w
  | .count => .count | .span => .virtualSpan | .idleLevels => .idleLevels
  | .idleEnabled => .idleEnabled | .valid => .valid | .word index => .word index

private theorem image_step (field : ImageField w) (i : Values Reactive.Input)
    (r : Values Reactive.Register) (executing : SramExecution.ExecutingInput i) :
    Reactive.circuit.step i r field.register = r field.register := by
  have resetting := SramExecution.resetting_executing i r executing
  have writing : Reactive.writing.eval i r = 0 := by
    simp [Reactive.writing, Reactive.both, Reactive.cmd, Expr.eval, executing.1.1]
  have committing : Reactive.committing.eval i r = 0 := by
    simp [Reactive.committing, Reactive.both, Reactive.cmd, Expr.eval, executing.1.2.1]
  cases field
  all_goals simp [ImageField.register, Circuit.step, Reactive.circuit, Reactive.next,
    Reactive.both, Reactive.either, Reactive.cold, Expr.eval, resetting, writing, committing,
    executing.2.1]

theorem InstalledSram.step {p : Program.Buffered.Program} {layout : GenericCertificate.Layout p}
    {actual : SramState.State} (h : InstalledSram p layout actual)
    (i : Values Reactive.Input) (executing : SramExecution.ExecutingInput i) :
    InstalledSram p layout (actual.step i) := by
  rcases h with ⟨rows, dictionary, resident, ready, installed, valid⟩
  refine ⟨rows, dictionary,
    SramExecution.resident_executing actual i rows dictionary executing resident,
    SramExecution.ready_executing actual i rows dictionary executing resident, ?_, ?_⟩
  · rw [SramExecution.reference_step_eq actual i rows dictionary executing resident ready]
    exact ⟨(image_step .count i _ executing).trans installed.count,
      (image_step .span i _ executing).trans installed.span,
      (image_step .idleLevels i _ executing).trans installed.idleLevels,
      (image_step .idleEnabled i _ executing).trans installed.idleEnabled,
      fun k => (image_step (.word k) i _ executing).trans (installed.image k)⟩
  · change (SramExecution.reference (actual.step i) rows dictionary) .valid = 1
    rw [SramExecution.reference_step_eq actual i rows dictionary executing resident ready]
    exact (image_step .valid i _ executing).trans valid

theorem InstalledSram.run {p : Program.Buffered.Program} {layout : GenericCertificate.Layout p}
    {actual : SramState.State} (h : InstalledSram p layout actual)
    (inputs : List (Values Reactive.Input))
    (executing : ∀ i ∈ inputs, SramExecution.ExecutingInput i) :
    InstalledSram p layout (actual.run inputs) := by
  induction inputs generalizing actual
  case nil => exact h
  case cons i rest ih =>
    exact ih (h.step i (executing i (by simp)))
      (fun j member => executing j (List.mem_cons.mpr (Or.inr member)))

end Pinwheel.Hardware.Buffered.Refinement
