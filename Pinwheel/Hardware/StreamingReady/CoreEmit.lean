import Pinwheel.Hardware.StreamingReady.Core
import Pinwheel.Hardware.Streaming.CoreEmit

namespace Pinwheel.Hardware.StreamingReady.Core
open Pinwheel.Hardware

def inputs : Array (Sigma Input) := Streaming.Core.inputs
def outputs : Array (Sigma Output) := Streaming.Core.outputs
def registers (a : Nat) : Array (Sigma (Register a)) := Streaming.Core.registers a
def inputLabel : {w : Nat} → Input w → String := Streaming.Core.inputLabel
def outputLabel : {w : Nat} → Output w → String := Streaming.Core.outputLabel
def registerLabel : {w : Nat} → Register a w → String := Streaming.Core.registerLabel
def registerIndex : {w : Nat} → Register a w → Nat := Streaming.Core.registerIndex

def moduleText (a : Nat) : Except String String := Buffered.MemoEmit.moduleText
  s!"pinwheel_streaming_ready_core_d{2^a}" (circuit a) inputs (registers a) outputs
  inputLabel registerLabel outputLabel

end Pinwheel.Hardware.StreamingReady.Core
