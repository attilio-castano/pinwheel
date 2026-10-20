import Pinwheel.Hardware.Buffered.Serial
import Lean

/-! Fresh frontend artifact intake. This exports the emitter's actual module and
the typed interface only; no expected execution vectors are used as evidence. -/
open Pinwheel.Hardware Pinwheel.Hardware.Buffered

private def ports (ps : Array (Sigma P)) (label : {w : Nat} → P w → String) : Lean.Json :=
  Lean.toJson (ps.map fun ⟨w, p⟩ => Lean.Json.mkObj
    [("name", Lean.toJson (label p)), ("width", Lean.toJson w)])

def main (args : List String) : IO Unit := do
  let out := args.headD "build/buffered-serial-artifact/emitted"
  IO.FS.createDirAll out
  IO.FS.writeFile (out ++ "/frontend.mlir") (← IO.ofExcept Serial.moduleText)
  let rs := Lean.toJson (Serial.registers.map fun ⟨w, r⟩ => Lean.Json.mkObj
    [("name", Lean.toJson ("r_" ++ Serial.registerLabel r)),
     ("reference", Lean.toJson ("r_" ++ Serial.registerLabel r)),
     ("width", Lean.toJson w)])
  let assembly := Lean.Json.mkObj
    [("schema", Lean.toJson (1 : Nat)),
     ("module", Lean.toJson "pinwheel_buffered_sram_serial_frontend"),
     ("inputs", ports Serial.inputs Serial.inputLabel),
     ("registers", rs), ("outputs", ports Serial.outputs Serial.outputLabel)]
  IO.FS.writeFile (out ++ "/assembly.json") (assembly.pretty ++ "\n")
  IO.println s!"Frontend artifact: {Serial.registers.size} registers; {Serial.outputs.size} outputs."
