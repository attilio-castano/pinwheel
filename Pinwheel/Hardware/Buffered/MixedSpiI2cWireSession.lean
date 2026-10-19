import Pinwheel.Hardware.Buffered.GenericWireSwitchWitness
import Pinwheel.Hardware.Buffered.GenericUploadI2cTiming
import Pinwheel.Hardware.Buffered.I2cTimingSerialWitness
import Pinwheel.Hardware.Buffered.SpiUploadImage
import Pinwheel.Hardware.Buffered.SpiWireRound

/-! A concrete heterogeneous wire witness: an accepted I²C diagnostic round,
actual warm reset and SPI image upload, then accepted SPI entry fault/release.
The same ordinary allocator crosses the image change; warm reset keeps the
hardware transfer counter and rebases the logical epoch-local sequence. -/
namespace Pinwheel.Hardware.Buffered.MixedSpiI2cWire
open Pinwheel.Hardware Pinwheel.Program Refinement
open GenericWireSession (ProgramImage RoundFactory WarmReload)
open GenericLogicalWire.Witness (LogicalRound)
set_option maxRecDepth 10000

noncomputable def i2cFactory (duration budget : Fin 256) : RoundFactory (I2cTiming.programImage duration budget) :=
  I2cTiming.SerialWitness.makeLogicalRound duration budget

noncomputable def spiFactory (c : BufferedSPI.Config) : RoundFactory (SpiUpload.programImage c) :=
  SpiWireDiagnostic.makeLogicalRound c (SpiCertificate.layout c)

structure Witness (duration budget : Fin 256) (c : BufferedSPI.Config)
    (before : SerialPackage.State) (previous : Transfer.State) (pin : SerialPackage.Pins) where
  loading : GenericUpload.Serial.Loading (I2cTiming.uploadImage duration budget) (before.step pin)
  first : LogicalRound (p := I2cTiming.source duration budget) (layout := I2cTiming.layout duration budget)
    loading.after (LogicalSession.resetLogical previous) 0
  reload : WarmReload (I2cTiming.programImage duration budget) (SpiUpload.programImage c)
    first.after first.finalLogical 0
  second : LogicalRound (p := BufferedSPI.program c) (layout := SpiCertificate.layout c)
    reload.after (LogicalSession.resetLogical first.finalLogical) reload.offset
  trace : GenericWireSession.Trace loading.after (I2cTiming.programImage duration budget)
    (.free (LogicalSession.resetLogical previous) 0) .available
    (first.pins ++ (reload.pins ++ second.pins)) second.after (SpiUpload.programImage c)
    (.free second.finalLogical reload.offset) .available
  run : before.run ((pin :: loading.pins) ++ (first.pins ++ (reload.pins ++ second.pins))) = second.after
  valid : GenericWireSession.Valid (SpiUpload.programImage c) second.after
    (.free second.finalLogical reload.offset) .available
  epoch : second.finalLogical.epoch = previous.epoch+2
  sequence : second.finalLogical.nextSequence = 2
  generation : second.after.controller.core .generation = 3
  transfer : second.after.controller.core .transfer = 2
  offset : reload.offset = 1
  observed : trace.Observed

def Witness.pins (w : Witness duration budget c before previous pin) : List SerialPackage.Pins :=
  (pin :: w.loading.pins) ++ (w.first.pins ++ (w.reload.pins ++ w.second.pins))

def Witness.after (w : Witness duration budget c before previous pin) : SerialPackage.State := w.second.after

def Witness.finalLogical (w : Witness duration budget c before previous pin) : Transfer.State := w.second.finalLogical

theorem Witness.final_valid (w : Witness duration budget c before previous pin) :
    GenericWireSession.Valid (SpiUpload.programImage c) w.after (.free w.finalLogical 1) .available := by
  have cursor := congrArg (fun offset => GenericLogicalWire.Cursor.free w.finalLogical offset) w.offset
  exact Eq.mp (congrArg (fun cursor => GenericWireSession.Valid (SpiUpload.programImage c)
    w.after cursor .available) cursor) w.valid

theorem initialized_i2c_spi_switch (duration budget : Fin 256) (c : BufferedSPI.Config)
    (before : SerialPackage.State) (previous : Transfer.State) (pin : SerialPackage.Pins)
    (cold : pin.cold = true) (idle : pin.csn = true) : Nonempty (Witness duration budget c before previous pin) := by
  obtain ⟨loading,first,reload,second,trace,run,valid,epoch,sequence,generation,transfer,offset,observed⟩ :=
    GenericWireSession.initialized_warm_switch_two_rounds (I2cTiming.programImage duration budget)
      (SpiUpload.programImage c) (i2cFactory duration budget) (spiFactory c) before previous pin cold idle
  exact ⟨⟨loading,first,reload,second,trace,run,valid,epoch,sequence,generation,transfer,offset,observed⟩⟩

end Pinwheel.Hardware.Buffered.MixedSpiI2cWire
