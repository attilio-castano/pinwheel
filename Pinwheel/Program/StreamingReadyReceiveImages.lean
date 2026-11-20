import Pinwheel.Program.StreamingReadySegments
import Pinwheel.Program.StreamingCANCore
import Pinwheel.Program.StreamingPS2Core
import Pinwheel.Program.StreamingUART

/-! Receive programs for the checked segment machine. START allocates zero
    TX bits. Explicit COUNT rows supply the receive-only slot counts. -/
namespace Pinwheel.Program.StreamingReadyReceiveImages

open StreamingReadySegments

/-- COUNT occupies one extra edge after SOF. Move one clock from LOW to
    HIGH to keep both the first CAN aperture and the 32-clock cadence. -/
def canRows : List Row :=
  let cell : StreamingReady.Cell := {lowDuration := 12, highDuration := 17, receive := true}
  [.cell StreamingCANCore.waitRow, .count 64, .cell (.stream cell none), .cell .halt]

def can : Image canRows 0 where
  outcomes := [⟨.complete, 0, 64, 2053, 1⟩]
  checked := by decide +kernel

/-- COUNT shifts the initial setup by one clock. The keyboard controls
    the actual capture edges after setup, with the original rearm timing. -/
def ps2Rows : List Row := .count 11 :: StreamingPS2Core.source.map Row.cell

def ps2 : Image ps2Rows 0 where
  outcomes := [⟨.complete, 0, 11, 2423, 11⟩]
  checked := by decide +kernel

/-- The extra COUNT clock replaces one clock of the pulse before data. -/
def uartRows (p : StreamingUART.Profile) : List Row :=
  let beforeData : StreamingReady.Cell := {StreamingUART.pulseB p with
    highDuration := ⟨p.Q - 3, by have := p.Q_le128; omega⟩}
  [.cell (.driveWait {} (StreamingUART.markGuard p)), .cell (.driveWait {} (StreamingUART.startGuard p)),
    .cell (.pulse (StreamingUART.pulseA p)), .cell (.driveWait {} (StreamingUART.checkStart p)),
    .cell (.pulse beforeData), .count 8, .cell (.stream (StreamingUART.cell p) none),
    .cell (.pulse (StreamingUART.pulseA p)), .cell (.driveWait {} (StreamingUART.checkStop p)), .cell .halt]

def uart (p : StreamingUART.Profile) : Except String (Image (uartRows p) 0) := compile (uartRows p) 0

end Pinwheel.Program.StreamingReadyReceiveImages
