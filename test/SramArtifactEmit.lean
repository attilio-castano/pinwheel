import Pinwheel.Hardware.Buffered.Sram
import Lean

/-! Fresh artifact intake only. No test vectors, ideal loader history or physical
qualification are used to emit the actual controller and its exact interface. -/
open Pinwheel.Hardware Pinwheel.Hardware.Buffered

private def ports (ps : Array (Sigma P)) (label : {w : Nat} → P w → String) : Lean.Json :=
  Lean.toJson (ps.map fun ⟨w, p⟩ => Lean.Json.mkObj
    [("name", Lean.toJson (label p)), ("width", Lean.toJson w)])

def main (args : List String) : IO Unit := do
  let out := args.headD "build/buffered-sram-artifact/emitted"
  IO.FS.createDirAll out
  IO.FS.writeFile (out ++ "/core.mlir") (← IO.ofExcept Sram.moduleText)
  let rs := Lean.toJson (Sram.registers.map fun ⟨w, r⟩ => Lean.Json.mkObj
    [("name", Lean.toJson ("r_" ++ Sram.registerLabel r)),
     ("reference", Lean.toJson ("r_" ++ Sram.registerLabel r)),
     ("width", Lean.toJson w)])
  let assembly := Lean.Json.mkObj
    [("schema", Lean.toJson (1 : Nat)),
     ("module", Lean.toJson "pinwheel_buffered_shared_branches_sram_controller"),
     ("inputs", ports Sram.inputs Sram.inputLabel),
     ("registers", rs), ("outputs", ports Sram.outputs Sram.outputLabel)]
  IO.FS.writeFile (out ++ "/assembly.json") (assembly.pretty ++ "\n")
  IO.println s!"Controller artifact: {Sram.registers.size} registers; {Sram.outputs.size} outputs."
