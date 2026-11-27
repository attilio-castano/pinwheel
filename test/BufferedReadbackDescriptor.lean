import Pinwheel.Hardware.Buffered.Sram
import Pinwheel.Hardware.Buffered.Serial
import Pinwheel.Hardware.Readback.Descriptor

/-! Write read-back import descriptors for the Buffered chip's SRAM controller
and serial frontend. `Pinwheel.Hardware.Readback.Descriptor` describes the
format; the Streaming cores have their own emitter,
`test/StreamingReadyReadbackDescriptor.lean`, so neither needs the other's
modules built.

The importer reads checked-in copies from `scripts/readback_descriptors`;
`test/test_readback_descriptor.py` fails if they differ from a fresh run.
Regenerate them with

    lake env lean -DwarningAsError=true --run test/BufferedReadbackDescriptor.lean scripts/readback_descriptors
-/

open Lean Pinwheel.Hardware Pinwheel.Hardware.Readback.Descriptor

namespace ReadbackTerms
deriving instance Repr for Pinwheel.Hardware.Buffered.Reactive.Input
deriving instance Repr for Pinwheel.Hardware.Buffered.Reactive.Output
deriving instance Repr for Pinwheel.Hardware.Buffered.Reactive.Register
deriving instance Repr for Pinwheel.Hardware.Buffered.Sram.Input
deriving instance Repr for Pinwheel.Hardware.Buffered.Sram.Register
deriving instance Repr for Pinwheel.Hardware.Buffered.Sram.Port
deriving instance Repr for Pinwheel.Hardware.Buffered.Sram.Output
deriving instance Repr for Pinwheel.Hardware.Buffered.Serial.Input
deriving instance Repr for Pinwheel.Hardware.Buffered.Serial.Register
deriving instance Repr for Pinwheel.Hardware.Buffered.Serial.Output
end ReadbackTerms
open ReadbackTerms

open Pinwheel.Hardware.Buffered in
def bufferedSramDescriptor : Json :=
  descriptor Sram.moduleName (toString ``Sram.Input) (toString ``Sram.Register)
    (toString ``Sram.Output) (toString ``Sram.circuit)
    (Sram.inputs.map fun ⟨w, p⟩ => port (Sram.inputLabel p) w p)
    (Sram.registers.map fun ⟨w, r⟩ => port ("r_" ++ Sram.registerLabel r) w r)
    (Sram.outputs.map fun ⟨w, o⟩ => port (Sram.outputLabel o) w o)

open Pinwheel.Hardware.Buffered in
def bufferedSerialDescriptor : Json :=
  descriptor Serial.moduleName (toString ``Serial.Input) (toString ``Serial.Register)
    (toString ``Serial.Output) (toString ``Serial.circuit)
    (Serial.inputs.map fun ⟨w, p⟩ => port (Serial.inputLabel p) w p)
    (Serial.registers.map fun ⟨w, r⟩ => port ("r_" ++ Serial.registerLabel r) w r)
    (Serial.outputs.map fun ⟨w, o⟩ => port (Serial.outputLabel o) w o)

def main (args : List String) : IO Unit :=
  write (args.headD "build/readback-descriptors")
    [("buffered-sram", bufferedSramDescriptor), ("buffered-serial", bufferedSerialDescriptor)]
