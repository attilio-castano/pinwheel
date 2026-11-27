import Pinwheel.Hardware.StreamingReady.CoreEmit
import Pinwheel.Hardware.Streaming.FrontendEmit
import Pinwheel.Hardware.Readback.Descriptor

/-! Write read-back import descriptors for the Streaming and sampled-ready cores
and their shared frontend. `Pinwheel.Hardware.Readback.Descriptor` describes
the format. All of it comes from the same enumerations and labels the emitter
uses, so the importer no longer keeps hand-typed copies. The Buffered chip's
descriptors have their own emitter, `test/BufferedReadbackDescriptor.lean`, so
neither needs the other's modules built.

The importer reads checked-in copies from `scripts/readback_descriptors`;
`test/test_readback_descriptor.py` fails if they differ from a fresh run.
Regenerate them with

    lake env lean -DwarningAsError=true --run test/StreamingReadyReadbackDescriptor.lean scripts/readback_descriptors
-/

open Lean Pinwheel.Hardware Pinwheel.Hardware.Readback.Descriptor

namespace ReadbackTerms
deriving instance Repr for Pinwheel.Hardware.Streaming.Core.Input
deriving instance Repr for Pinwheel.Hardware.Streaming.Core.Output
deriving instance Repr for Pinwheel.Hardware.Streaming.Core.Register
deriving instance Repr for Pinwheel.Hardware.Streaming.Frontend.Input
deriving instance Repr for Pinwheel.Hardware.Streaming.Frontend.Output
deriving instance Repr for Pinwheel.Hardware.Streaming.Frontend.Register
end ReadbackTerms
open ReadbackTerms

/-- The Streaming and sampled-ready cores share their ports and registers; only
the module and the circuit differ. -/
def coreDescriptor (module : String) (circuit : Lean.Name) (a : Nat) : Json :=
  descriptor module (toString ``Pinwheel.Hardware.Streaming.Core.Input)
    s!"({``Pinwheel.Hardware.Streaming.Core.Register} {a})" (toString ``Pinwheel.Hardware.Streaming.Core.Output)
    s!"({circuit} {a})"
    (StreamingReady.Core.inputs.map fun ⟨w, p⟩ => port (StreamingReady.Core.inputLabel p) w p)
    ((StreamingReady.Core.registers a).map fun ⟨w, r⟩ => port ("r_" ++ StreamingReady.Core.registerLabel r) w r)
    (StreamingReady.Core.outputs.map fun ⟨w, o⟩ => port (StreamingReady.Core.outputLabel o) w o)

def frontendDescriptor : Json :=
  descriptor Streaming.Frontend.moduleName (toString ``Pinwheel.Hardware.Streaming.Frontend.Input)
    (toString ``Pinwheel.Hardware.Streaming.Frontend.Register) (toString ``Pinwheel.Hardware.Streaming.Frontend.Output)
    (toString ``Pinwheel.Hardware.Streaming.Frontend.circuit)
    (Streaming.Frontend.inputs.map fun ⟨w, p⟩ => port (Streaming.Frontend.inputLabel p) w p)
    (Streaming.Frontend.registers.map fun ⟨w, r⟩ => port ("r_" ++ Streaming.Frontend.registerLabel r) w r)
    (Streaming.Frontend.outputs.map fun ⟨w, o⟩ => port (Streaming.Frontend.outputLabel o) w o)

def main (args : List String) : IO Unit :=
  let streaming a := coreDescriptor (Streaming.Core.moduleName a) ``Pinwheel.Hardware.Streaming.Core.circuit a
  let ready a := coreDescriptor (StreamingReady.Core.moduleName a) ``Pinwheel.Hardware.StreamingReady.Core.circuit a
  write (args.headD "build/readback-descriptors")
    [("streaming-core-d2", streaming 1), ("streaming-core-d4", streaming 2),
     ("ready-core-d2", ready 1), ("ready-core-d4", ready 2), ("frontend", frontendDescriptor)]
