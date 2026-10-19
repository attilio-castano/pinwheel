import Pinwheel.Hardware.Buffered.ArtifactProgrammableSession
import Pinwheel.Hardware.Buffered.MixedSpiI2cWireSession

/-! The nonempty heterogeneous I²C→warm reload→SPI session also inhabits the
actual descriptor-driven package and TinyTapeout recurrences. Component
certificates and the explicit digital SRAM law remain independent inputs. -/
namespace Pinwheel.Hardware.Buffered.ArtifactPackageWiringSession
open Pinwheel.Hardware Pinwheel.Program

theorem Certified.mixed_i2c_spi_switch {M : Type} (wrapper : Certified)
    {components : ArtifactPackage.Components} (correct : ArtifactPackage.Correct components)
    (memory : Memory.SinglePort.Contract M 6 64) (duration budget : Fin 256) (c : BufferedSPI.Config)
    (before : ArtifactPackage.State M) (previous : Transfer.State)
    (pin : SerialPackage.Pins) (cold : pin.cold = true) (idle : pin.csn = true) :
    ∃ w : MixedSpiI2cWire.Witness duration budget c (before.view memory) previous pin,
      (wrapper.run components memory before w.pins).view memory = w.after ∧
      GenericWireSession.Valid (SpiUpload.programImage c) w.after (.free w.finalLogical 1) .available ∧
      w.finalLogical.epoch = previous.epoch+2 ∧ w.finalLogical.nextSequence = 2 ∧
      w.after.controller.core .generation = 3 ∧ w.after.controller.core .transfer = 2 ∧ w.trace.Observed := by
  obtain ⟨w⟩ := MixedSpiI2cWire.initialized_i2c_spi_switch duration budget c (before.view memory)
    previous pin cold idle
  exact ⟨w,(wrapper.view_run correct memory before w.pins).trans w.run,w.final_valid,
    w.epoch,w.sequence,w.generation,w.transfer,w.observed⟩

end Pinwheel.Hardware.Buffered.ArtifactPackageWiringSession

namespace Pinwheel.Hardware.Buffered.ArtifactTinyTapeoutWiringSession
open Pinwheel.Hardware Pinwheel.Program

theorem Certified.mixed_i2c_spi_switch {M : Type} (wrapper : Certified)
    {components : ArtifactPackage.Components} (correct : ArtifactPackage.Correct components)
    (memory : Memory.SinglePort.Contract M 6 64) (duration budget : Fin 256) (c : BufferedSPI.Config)
    (before : ArtifactPackage.State M) (previous : Transfer.State)
    (pin : SerialPackage.Pins) (cold : pin.cold = true) (idle : pin.csn = true) :
    ∃ w : MixedSpiI2cWire.Witness duration budget c (before.view memory) previous pin,
      (wrapper.run components memory before (w.pins.map ArtifactTinyTapeout.encode)).view memory = w.after ∧
      GenericWireSession.Valid (SpiUpload.programImage c) w.after (.free w.finalLogical 1) .available ∧
      w.finalLogical.epoch = previous.epoch+2 ∧ w.finalLogical.nextSequence = 2 ∧
      w.after.controller.core .generation = 3 ∧ w.after.controller.core .transfer = 2 ∧ w.trace.Observed := by
  obtain ⟨w⟩ := MixedSpiI2cWire.initialized_i2c_spi_switch duration budget c (before.view memory)
    previous pin cold idle
  exact ⟨w,(wrapper.encoded_view_run correct memory before w.pins).trans w.run,w.final_valid,
    w.epoch,w.sequence,w.generation,w.transfer,w.observed⟩

end Pinwheel.Hardware.Buffered.ArtifactTinyTapeoutWiringSession
