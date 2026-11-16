import Pinwheel.Hardware.USB.Emit
import Pinwheel.Hardware.USB.IN
import Lean

open Pinwheel.Hardware

private def ports (ps : Array (Sigma P)) (label : {w : Nat} → P w → String) : Lean.Json :=
  Lean.toJson (ps.map fun ⟨w, p⟩ => Lean.Json.mkObj
    [("name", Lean.toJson (label p)), ("width", Lean.toJson w)])

def main (args : List String) : IO Unit := do
  let out := args.headD "build/usb"
  IO.FS.createDirAll out
  IO.FS.writeFile (out ++ "/core.sv") (← IO.ofExcept USB.coreText)
  IO.FS.writeFile (out ++ "/frontend.sv") (← IO.ofExcept USB.frontendText)
  -- The opt-in core must use the original interface exactly.
  let core := Lean.Json.mkObj [("module", Lean.toJson "pinwheel_streaming_ready_core_d2"),
    ("inputs", ports Streaming.Core.inputs Streaming.Core.inputLabel),
    ("outputs", ports Streaming.Core.outputs Streaming.Core.outputLabel)]
  let frontend := Lean.Json.mkObj [("module", Lean.toJson "pinwheel_streaming_quad_frontend"),
    ("inputs", ports Streaming.Frontend.inputs Streaming.Frontend.inputLabel),
    ("outputs", ports Streaming.Frontend.outputs Streaming.Frontend.outputLabel)]
  IO.FS.writeFile (out ++ "/interface.json") (Lean.toJson (core, frontend)).pretty
  IO.FS.writeFile (out ++ "/in-image.json") (Lean.toJson (USB.inImage.map BitVec.toNat)).compress
