import Pinwheel.Program.StreamingReadyCompile
import Pinwheel.Program.StreamingReadySession
import Pinwheel.Program.StreamingBootPins

/-! Concrete sampled WRITE/COMMIT waveforms for Ready images. The existing
word-list control certificate is reused; it assumes no delivered command trace. -/
namespace Pinwheel.Program.StreamingReady.BootPins

abbrev Control := Streaming.BootPins.Control
abbrev Certified := Streaming.BootPins.Certified
abbrev Delivery := Streaming.BootPins.Delivery
abbrev CommandSafe := Streaming.BootPins.CommandSafe

def compiled (image : Compiled source idle) (raw : BitVec 2 := 3) : List Session.Pins :=
  Streaming.BootPins.upload image.words idle raw

def coldPin : Session.Pins := Streaming.BootPins.coldPin
def initialControl : Streaming.BootPins.Control := Streaming.BootPins.initialControl

def i2c : List Session.Pins := compiled (i2cImage .standard)

theorem i2c_length : i2c.length = 1960 := by decide +kernel

theorem i2c_check : Streaming.BootPins.check (i2cImage .standard).words ⟨0,0⟩
    initialControl 0 false i2c = true := by
  decide +kernel

theorem i2c_certified : Streaming.BootPins.Certified (i2cImage .standard).words ⟨0,0⟩
    initialControl 0 false i2c :=
  Streaming.BootPins.check_sound _ _ _ _ _ _ i2c_check

end Pinwheel.Program.StreamingReady.BootPins
