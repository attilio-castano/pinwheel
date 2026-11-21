import Pinwheel.Program.StreamingReadySegments
import Pinwheel.Program.StreamingSPI

/-! Bind the legacy full-duplex cells to an explicit stream count in a
    checked segmented image. The clock, pin and sampling instructions
    themselves are unchanged. -/
namespace Pinwheel.Program.StreamingReadyDuplex

open StreamingReadySegments

private def counted (slots : BitVec 16) (source : List StreamingReady.Instruction) : List Row :=
  source.flatMap fun instruction => match instruction with
    | .stream _ _ => [.count slots, .cell instruction]
    | _ => [.cell instruction]

def spiRows (mode : StreamingSPI.Mode) (duration : Fin 256) (slots : BitVec 16) : List Row :=
  counted slots (StreamingSPI.source mode duration)

def jtagRows (duration : Fin 256) (slots : BitVec 16) : List Row :=
  counted slots ((Streaming.jtagSource duration).map StreamingReady.liftInstruction)

def spi (mode : StreamingSPI.Mode) (duration : Fin 256) (slots : BitVec 16) :
    Except String (Image (spiRows mode duration slots) slots.toNat) :=
  compile _ _

def jtag (duration : Fin 256) (slots : BitVec 16) :
    Except String (Image (jtagRows duration slots) slots.toNat) :=
  compile _ _

end Pinwheel.Program.StreamingReadyDuplex
