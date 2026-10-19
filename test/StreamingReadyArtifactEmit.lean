import Pinwheel.Hardware.StreamingReady.CoreEmit
import Pinwheel.Hardware.Streaming.FrontendEmit
import Lean

open Pinwheel.Hardware Pinwheel.Hardware.StreamingReady

private def ports (ps : Array (Sigma P)) (label : {w : Nat} → P w → String) : Lean.Json :=
  Lean.toJson (ps.map fun ⟨w, p⟩ => Lean.Json.mkObj
    [("name", Lean.toJson (label p)), ("width", Lean.toJson w)])

def main (args : List String) : IO Unit := do
  let out := args.headD "build/streaming-ready-artifact/emitted"
  let a := (args[1]?.getD "1").toNat?.getD 1
  unless a == 1 || a == 2 do throw (IO.userError "qualified buffer address width must be 1 or 2")
  IO.FS.createDirAll out
  IO.FS.writeFile (out ++ "/core.mlir") (← IO.ofExcept (Core.moduleText a))
  let rs := Lean.toJson ((Core.registers a).map fun ⟨w, r⟩ => Lean.Json.mkObj
    [("name", Lean.toJson ("r_" ++ Core.registerLabel r)),
     ("reference", Lean.toJson ("r_" ++ Core.registerLabel r)), ("width", Lean.toJson w)])
  let assembly := Lean.Json.mkObj
    [("schema", Lean.toJson (1 : Nat)), ("addr_bits", Lean.toJson a),
     ("module", Lean.toJson s!"pinwheel_streaming_ready_core_d{2^a}"),
     ("inputs", ports Core.inputs Core.inputLabel),
     ("registers", rs), ("outputs", ports Core.outputs Core.outputLabel)]
  IO.FS.writeFile (out ++ "/assembly.json") (assembly.pretty ++ "\n")
  IO.FS.writeFile (out ++ "/frontend.mlir") (← IO.ofExcept Streaming.Frontend.moduleText)
  let frontend := Lean.Json.mkObj
    [("schema", Lean.toJson (1 : Nat)),
     ("module", Lean.toJson "pinwheel_streaming_quad_frontend"),
     ("inputs", ports Streaming.Frontend.inputs Streaming.Frontend.inputLabel),
     ("outputs", ports Streaming.Frontend.outputs Streaming.Frontend.outputLabel),
     ("registers", Lean.toJson (Streaming.Frontend.registers.map fun ⟨w,r⟩ => Lean.Json.mkObj
       [("name", Lean.toJson ("r_" ++ Streaming.Frontend.registerLabel r)),
        ("reference", Lean.toJson ("r_" ++ Streaming.Frontend.registerLabel r)),
        ("width", Lean.toJson w)]))]
  IO.FS.writeFile (out ++ "/frontend-assembly.json") (frontend.pretty ++ "\n")
  IO.println s!"Streaming ready depth {2^a}: {(Core.registers a).size} registers; {Core.outputs.size} outputs."
