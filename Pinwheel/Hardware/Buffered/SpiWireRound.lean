import Pinwheel.Hardware.Buffered.SpiWireDiagnostic

namespace Pinwheel.Hardware.Buffered.SpiWireDiagnostic
open Pinwheel.Hardware Pinwheel.Program SerialWire Serial.Frames
open GenericLogicalWire.Witness (LogicalRound)
open SerialSessionWitness (roundStart roundRelease roundStart_opcode roundRelease_word)
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

noncomputable opaque makeLogicalRound (c : BufferedSPI.Config)
    (layout : GenericCertificate.Layout (BufferedSPI.program c)) (before : SerialPackage.State)
    (logical : Transfer.State) (offset : Nat)
    (installed : Refinement.InstalledSram (BufferedSPI.program c) layout before.controller)
    (aligned : LogicalSession.Aligned before.controller logical offset) (available : Available before.record)
    (room : before.controller.core .transfer ≠ 65535) (startSequence releaseSequence : BitVec 16) :
    LogicalRound (p := BufferedSPI.program c) (layout := layout) before logical offset := by
  let start := roundStart before available startSequence
  let release := roundRelease start.after start.exact.1 releaseSequence
  have accepted : Reactive.starting.eval (start.framed.coreInputs start.dispatch) start.framed.controller.core = 1 := by
    unfold start roundStart
    exact SerialStartAdmission.concrete_admitted before installed ⟨aligned.phase,aligned.retained⟩
      available startSequence 0 0 0 0 room (by decide) (by decide)
  have stopped : (SerialStartAdmission.sourceAfter (BufferedSPI.program c) start).core.control = .stopped .fault := by
    unfold start roundStart
    exact concrete_underflow c before available startSequence 0 0 0
  exact GenericLogicalWire.Witness.assembleStoppedRound before logical offset installed aligned available start release
    accepted (roundStart_opcode before available startSequence) .fault stopped
    releaseSequence (roundRelease_word start.after start.exact.1 releaseSequence)

end Pinwheel.Hardware.Buffered.SpiWireDiagnostic
