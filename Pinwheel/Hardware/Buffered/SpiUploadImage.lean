import Pinwheel.Hardware.Buffered.SpiCertificate
import Pinwheel.Hardware.Buffered.GenericWireSession

/-! The existing compact SPI rows and zero dictionary form a static generic
upload image. Real upload acceptance is supplied by the generic loader proofs. -/
namespace Pinwheel.Hardware.Buffered.SpiUpload
open Pinwheel.Hardware Pinwheel.Program

def image (c : SpiSource.Config) : GenericUpload.Image (BufferedSPI.program c) (SpiCertificate.layout c) where
  word := SpiSource.word c
  control := SpiSource.control c
  branchIndex := fun _ => 0
  dictionary := SpiSource.dictionary
  packed := by
    change SramExecution.residentWords 4 (SpiSource.rows c) SpiSource.dictionary = SpiSource.fullWords c
    exact SpiSource.resident_words c
    done

def programImage (c : SpiSource.Config) : GenericWireSession.ProgramImage :=
  ⟨BufferedSPI.program c, SpiCertificate.layout c, image c⟩

end Pinwheel.Hardware.Buffered.SpiUpload
