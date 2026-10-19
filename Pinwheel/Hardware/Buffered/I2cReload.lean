import Pinwheel.Hardware.Buffered.GenericResetLoading
import Pinwheel.Hardware.Buffered.I2cStart

/-! Reupload after either cold or warm reset reconstructs the certified I²C
image from actual accepted writes. Physical SRAM contents need not be cleared.
The finite generation/transfer reset policy is proved separately. -/
namespace Pinwheel.Hardware.Buffered.I2cReload
open Pinwheel.Hardware Pinwheel.Program

theorem reset_installed (s : SramState.State) (resetInput : Values Reactive.Input)
    (reset : Reactive.resetting.eval resetInput s.core = 1)
    (loading : List (Values Reactive.Input))
    (source : I2cLoading.SourceHistory (s.step resetInput) loading)
    (valid : (SramLoading.run (s.step resetInput) SramLoading.Ledger.initial loading).1.registers
      (.core .valid) = 1) :
    Refinement.InstalledSram I2cSource.source I2cCertificate.layout
      (SramLoading.run (s.step resetInput) SramLoading.Ledger.initial loading).1 := by
  let after := SramLoading.run (s.step resetInput) SramLoading.Ledger.initial loading
  have resetValid : (s.step resetInput).registers (.core .valid) = 0 :=
    (Lifecycle.reset_ownership s resetInput reset).1
  have established := SramCorrespondence.established_run loading (s.step resetInput)
    SramLoading.Ledger.initial (SramResetLoading.established_reset s resetInput reset)
  have ready := SramCorrespondence.ready_run loading (s.step resetInput)
    SramLoading.Ledger.initial (SramResetLoading.established_reset s resetInput reset)
    (SramResetLoading.ready_reset s resetInput reset) valid
  have initialGeometry : I2cGeometry.WhenValid (s.step resetInput) := by
    intro asserted
    exact False.elim ((by decide : (0 : BitVec 1) ≠ 1) (resetValid.symm.trans asserted))
  have geometry := I2cGeometry.source_geometry_run (s.step resetInput)
    SramLoading.Ledger.initial loading initialGeometry source valid
  have known := I2cLoading.known_run (s.step resetInput) SramLoading.Ledger.initial
    loading I2cLoading.known_initial source
  have reference := I2cLoading.reference_source after.1 after.2 known established valid geometry.count
  refine ⟨after.2.rows, after.2.dictionaryWords, established.resident valid, ready, ?_, valid⟩
  rw [reference]
  exact I2cStart.installed (geometry.withWords I2cSource.fullWords) (fun _ => rfl)

theorem warm_installed (s : SramState.State) (warmInput : Values Reactive.Input)
    (cold : warmInput .initialize = 0) (warm : warmInput .command = 7)
    (loading : List (Values Reactive.Input))
    (source : I2cLoading.SourceHistory (s.step warmInput) loading)
    (valid : (SramLoading.run (s.step warmInput) SramLoading.Ledger.initial loading).1.registers
      (.core .valid) = 1) :
    Refinement.InstalledSram I2cSource.source I2cCertificate.layout
      (SramLoading.run (s.step warmInput) SramLoading.Ledger.initial loading).1 := by
  apply reset_installed s warmInput _ loading source valid
  simp [Reactive.resetting, Reactive.cold, Reactive.warm, Reactive.both,
    Reactive.either, Reactive.cmd, Expr.eval, cold, warm]

end Pinwheel.Hardware.Buffered.I2cReload
