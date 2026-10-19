import Pinwheel.Hardware.Buffered.GenericStart
import Pinwheel.Hardware.Buffered.GenericSramRelation
import Pinwheel.Hardware.Buffered.I2cCertificate
import Pinwheel.Hardware.Buffered.I2cRuntime

/-! Initialized accepted uploads establish the fixed I²C image and its first
source execution edge at the actual digital SRAM boundary. Dictionary slot1,
both resident replicas, and registered candidate readiness are preserved. -/
namespace Pinwheel.Hardware.Buffered.I2cStart
open Pinwheel.Hardware Pinwheel.Program

theorem installed {r : Values Reactive.Register}
    (geometry : I2cGeometry.Geometry r)
    (image : ∀ k, r (.word k) = I2cSource.fullWords k) :
    GenericStart.Installed I2cSource.source I2cCertificate.layout r :=
  ⟨geometry.count, geometry.virtualSpan, geometry.idleLevels, geometry.idleEnabled, image⟩

theorem initialized_start (s : SramState.State)
    (cold : Values Reactive.Input) (coldInit : cold .initialize = 1)
    (loading : List (Values Reactive.Input))
    (source : I2cLoading.SourceHistory (s.step cold) loading)
    (valid : (SramLoading.run (s.step cold) SramLoading.Ledger.initial loading).1.registers
      (.core .valid) = 1)
    (start : Values Reactive.Input)
    (starting : Reactive.starting.eval start
      (SramExecution.core (SramLoading.run (s.step cold) SramLoading.Ledger.initial loading).1.registers) = 1) :
    let after := SramLoading.run (s.step cold) SramLoading.Ledger.initial loading
    Refinement.RelatedSram I2cSource.source I2cCertificate.layout (start .txData)
      (after.1.step start)
      (GenericStart.started I2cSource.source (SramExecution.core after.1.registers) start) := by
  let after := SramLoading.run (s.step cold) SramLoading.Ledger.initial loading
  let base : Values Reactive.Register := SramExecution.core after.1.registers
  let reference : Values Reactive.Register := SramExecution.withWords base I2cSource.fullWords
  have geometry : I2cGeometry.Geometry reference :=
    (I2cGeometry.initialized_source_geometry s cold coldInit loading source valid).withWords
      I2cSource.fullWords
  have referenceEq : @SramExecution.reference after.1 I2cSource.rows I2cSource.dictionary = @reference := by
    unfold SramExecution.reference
    rw [I2cLoading.initialized_source_count s cold coldInit loading source valid, I2cSource.resident_words]
  have accepted : Reactive.starting.eval start reference = 1 :=
    (SramExecution.starting_withWords start base I2cSource.fullWords).trans starting
  have related := GenericStart.start_related start reference (installed geometry (fun _ => rfl)) accepted
  have executing := (SpiAdmission.starting_controls start base starting).executing
  have resident := I2cLoading.initialized_source_resident s cold coldInit loading source valid
  have ready := I2cLoading.initialized_source_ready s cold coldInit loading source valid
  refine ⟨I2cSource.rows, I2cSource.dictionary,
    SramExecution.resident_executing after.1 start _ _ executing resident,
    SramExecution.ready_executing after.1 start _ _ executing resident, ?_⟩
  rw [SramExecution.reference_step_eq after.1 start _ _ executing resident ready, referenceEq]
  exact related

end Pinwheel.Hardware.Buffered.I2cStart
