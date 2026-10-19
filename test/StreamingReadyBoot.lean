import Pinwheel.Hardware.StreamingReady.BootUpload
import Pinwheel.Hardware.StreamingReady.PublicPins
import Pinwheel.Hardware.StreamingReady.WarmReset
import Pinwheel.Program.StreamingReadyOwnerCut

namespace Pinwheel.Test.StreamingReadyBoot
open Pinwheel.Program.StreamingReady
open Pinwheel.Hardware.StreamingReady

/-- A physical upload, rather than an assumed decoded loader history. -/
example (startup : Package.State 1) :
    ∃ final : Session.State 1, BootCorrespondence.Initialized (i2cImage .standard)
      (startup.run (Package.Components.typed 1)
        (SessionCorrespondence.pins BootPins.coldPin :: BootPins.i2c.map SessionCorrespondence.pins)) final :=
  BootCorrespondence.i2c_initialized startup

example (startup : Package.State 2) :
    ∃ final : Session.State 2, BootCorrespondence.Initialized (i2cImage .standard)
      (startup.run (Package.Components.typed 2)
        (SessionCorrespondence.pins BootPins.coldPin :: BootPins.i2c.map SessionCorrespondence.pins)) final :=
  BootCorrespondence.i2c_initialized startup

example : BootUpload.UploadCut (i2cImage .standard)
    (InitializedSession.coldState 1 (SessionCorrespondence.pins BootPins.coldPin)) BootPins.i2c :=
  BootUpload.i2c_upload

example : 1 + BootPins.i2c.length = 1961 := by rw [BootPins.i2c_length]

example (pins : Session.Pins) :
    SessionCorrespondence.physicalPins (PublicPins.embed pins) = pins := PublicPins.physical_embed pins

#print axioms BootCorrespondence.i2c_initialized
#print axioms BootUpload.i2c_upload
#print axioms WarmReset.warm_step_equal
#print axioms Session.State.Custody.run
#print axioms Session.State.FreeExport.start_empty
end Pinwheel.Test.StreamingReadyBoot
