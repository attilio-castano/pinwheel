import Pinwheel.Hardware.Buffered.GenericUploadImage

namespace Pinwheel.Hardware.Buffered.GenericUpload
open Pinwheel.Hardware Pinwheel.Program
variable {p : Program.Buffered.Program} {layout : GenericCertificate.Layout p}
set_option maxRecDepth 4096

structure Geometry (p : Program.Buffered.Program) (layout : GenericCertificate.Layout p)
    (r : Values Reactive.Register) : Prop where
  count : r .count = BitVec.ofNat 7 layout.count.val
  span : r .virtualSpan = BitVec.ofNat 11 p.code.span
  idleLevels : r .idleLevels = p.idle.levels
  idleEnabled : r .idleEnabled = p.idle.enabled

def WhenValid (p : Program.Buffered.Program) (layout : GenericCertificate.Layout p)
    (s : SramState.State) : Prop := s.core .valid = 1 → Geometry p layout (SramExecution.core s.registers)

private theorem valid_post (i : Values Sram.Input) (s : Values Sram.Register)
    (valid : Sram.circuit.step i s (.core .valid) = 1) :
    SramCoverage.resetting.eval i s ≠ 1 ∧ i (.base .initialize) ≠ 1 ∧
      (Sram.committing.eval i s = 1 ∨ s (.core .valid) = 1) := by
  rw [SramCoverage.valid_step] at valid
  split at valid
  · contradiction
  · rename_i notReset
    refine ⟨fun h => notReset (Or.inl h),?_,?_⟩
    · exact fun cold => notReset (Or.inl (SramCoverage.cold_resetting i s cold))
    · split at valid
      · exact Or.inl ‹_›
      · exact Or.inr valid

theorem geometry_step (image : Image p layout) (s : SramState.State) (i : Values Reactive.Input)
    (h : WhenValid p layout s) (source : SourceInput image s i) : WhenValid p layout (s.step i) := by
  intro valid
  have facts := valid_post (s.inputs i) s.registers valid
  by_cases commit : Sram.committing.eval (s.inputs i) s.registers = 1
  · have geometry := source.commit commit
    have cold : i .initialize ≠ 1 := facts.2.1
    constructor
    all_goals simp only [SramExecution.core,SramState.State.step,SramCoverage.count_step,
      SpiGeometry.virtualSpan_step,SpiGeometry.idleLevels_step,SpiGeometry.idleEnabled_step,
      if_neg facts.1,if_pos commit,SramState.State.inputs]
    all_goals simp only [geometry.1,geometry.2.1,geometry.2.2.1,geometry.2.2.2,if_neg cold]
  · have old := h (facts.2.2.resolve_left commit)
    have cold : i .initialize ≠ 1 := facts.2.1
    constructor
    all_goals simp only [SramExecution.core,SramState.State.step,SramCoverage.count_step,
      SpiGeometry.virtualSpan_step,SpiGeometry.idleLevels_step,SpiGeometry.idleEnabled_step,
      if_neg facts.1,if_neg commit,SramState.State.inputs,if_neg cold]
    · exact old.count
    · exact old.span
    · exact old.idleLevels
    · exact old.idleEnabled

theorem geometry_run (image : Image p layout) (s : SramState.State) (t : SramLoading.Ledger)
    (inputs : List (Values Reactive.Input)) (h : WhenValid p layout s)
    (history : SourceHistory image s inputs) : WhenValid p layout (SramLoading.run s t inputs).1 := by
  induction inputs generalizing s t with
  | nil => exact h
  | cons i rest ih => exact ih (s.step i) (t.step s i) (geometry_step image s i h history.1) history.2

theorem loading_run (s : SramState.State) (t : SramLoading.Ledger) (inputs : List (Values Reactive.Input)) :
    (SramLoading.run s t inputs).1 = s.run inputs := by
  induction inputs generalizing s t with
  | nil => rfl
  | cons i rest ih => exact ih (s.step i) (t.step s i)

theorem reset_installed (image : Image p layout) (s : SramState.State)
    (reset : Values Reactive.Input) (resetting : Reactive.resetting.eval reset s.core = 1)
    (inputs : List (Values Reactive.Input)) (history : SourceHistory image (s.step reset) inputs)
    (valid : ((s.step reset).run inputs).core .valid = 1) :
    Refinement.InstalledSram p layout ((s.step reset).run inputs) := by
  let after := SramLoading.run (s.step reset) SramLoading.Ledger.initial inputs
  have oldValid := (Lifecycle.reset_ownership s reset resetting).1
  have initial : WhenValid p layout (s.step reset) := by
    intro asserted
    exact False.elim ((by decide : (0 : BitVec 1) ≠ 1) (oldValid.symm.trans asserted))
  have actualValid : after.1.registers (.core .valid) = 1 := by
    rw [loading_run]
    exact valid
  have established := SramCorrespondence.established_run inputs (s.step reset)
    SramLoading.Ledger.initial (SramResetLoading.established_reset s reset resetting)
  have ready := SramCorrespondence.ready_run inputs (s.step reset) SramLoading.Ledger.initial
    (SramResetLoading.established_reset s reset resetting) (SramResetLoading.ready_reset s reset resetting) actualValid
  have geometry := geometry_run image (s.step reset) SramLoading.Ledger.initial inputs initial history actualValid
  have known := known_run image (s.step reset) SramLoading.Ledger.initial inputs (known_initial image) history
  have count : after.1.registers (.core .count) = BitVec.ofNat 7 layout.count.val := geometry.count
  have reference : @SramExecution.reference after.1 after.2.rows after.2.dictionaryWords =
      @SramExecution.withWords after.1.core layout.words := by
    unfold SramExecution.reference
    rw [count,resident_source_words image after.1 after.2 known established actualValid count]
    rfl
  have installed : Refinement.InstalledSram p layout after.1 := by
    refine ⟨after.2.rows,after.2.dictionaryWords,established.resident actualValid,ready,?_,actualValid⟩
    rw [reference]
    exact ⟨geometry.count,geometry.span,geometry.idleLevels,geometry.idleEnabled,fun _ => rfl⟩
  rw [loading_run] at installed
  exact installed

end Pinwheel.Hardware.Buffered.GenericUpload
